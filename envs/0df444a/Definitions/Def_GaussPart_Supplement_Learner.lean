-- Prove2me | Definitions.Def_GaussPart_Supplement_Learner
-- name    : GaussPart_Supplement_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:03:26.91312+00:00
-- url     : https://prove2.me/theorems/b293bcbc-0cf8-4b07-b0cc-5c025fbc2952
-- title:
--   Learning algorithms on the sampling RAM: labeled samples, cost on every stream, success sets, evaluated hypotheses, partition input
-- statement:
--   The algorithmic theorems are about programs of the published sampling real-RAM (`GaussMixHH`), restricted to arithmetic instructions as in the published Theorem 3.1. This module fixes the conventions.
--
--   1. **Labeled samples.** A labeled example $(x,y)\in\mathbb R^d\times\{\pm1\}$ is the point $(x_1,\dots,x_d,y)\in\mathbb R^{d+1}$; the stream of samples is i.i.d. from the image of $D$.
--   2. **Cost on every stream.** A program $P$ started with an input list in memory *runs within* $(N,T)$ if on every sample stream it halts after reading at most $N$ samples and doing at most $T$ work (one unit per instruction, the dimension per sample read).
--   3. **Success with probability $p$.** There is a measurable set of sample streams of probability at least $p$ on which every halted state satisfies the required property.
--   4. **Hypotheses.** A learner outputs a description; the hypothesis $h:\mathbb R^d\to\{\pm1\}$ is computed from the final state by a second fixed program, the evaluator, with $x$ written into the learner's memory: $h(x)=1$ if the evaluator halts within work $T$ with output $1$, and $h(x)=-1$ otherwise.
--   5. **Testable learners** accept when the final output register is $1$.
--   6. **A partition as input**: the number of cells, then for each cell its number of constraints and the constraint records $(s,w_1,\dots,w_d,b)$ for $w\cdot x\le b$ ($s=0$) or $w\cdot x<b$ ($s=1$).
--
--   **Formalization Note** The time bound on evaluation prevents a learner from deferring its work to the hypothesis; the run is deterministic given the samples, as for the published goal.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorems 4.2, 4.4, 5.3, 5.12, 5.13, 6.2, 1.11, 1.12, F.2, F.3 (pp.6, 36–37, 44, 53–54, 60–63, 79–80); Algorithm 3, p.38; Definition A.5, p.70

import Mathlib
import Definitions.Def_GaussMixHH_Machine
import Definitions.Def_GaussPart_Cell
import Definitions.Def_GaussPart_ArithmeticOnly

open MeasureTheory

namespace GaussPart

namespace Supplement

/-- **Labeled samples on the sampling RAM** (arXiv:2611.05264, sha256 7e0ca6d4…; the learners of
Theorems 4.2, 4.4, 6.2, 1.11, 1.12, F.2, F.3 read i.i.d. samples `(x, y)` of a distribution `D` on
`ℝᵈ × {±1}`): the pair `(x, y)` is the point `(x₁, …, x_d, y)` of `ℝ^{d+1}`, so one `sample`
instruction writes `x` followed by its label.

**Formalization Note.** This is the encoding of a labeled example as one machine sample; the
machine then runs in dimension `d + 1` and a `sample` costs `d + 1`. -/
noncomputable def labeledEnc {d : ℕ} (p : Vec d × ℝ) : Vec (d + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i : Fin d => p.1 i) p.2)

/-- The law of the labeled sample stream: i.i.d. copies of `D` pushed through `labeledEnc`. -/
noncomputable def labeledStream {d : ℕ} (D : Measure (Vec d × ℝ)) : Measure (ℕ → Vec (d + 1)) :=
  Measure.infinitePi (fun _ : ℕ => D.map labeledEnc)

/-- The state after `t` steps of the deterministic (`noCoins`) run of `P` in sample dimension `n`
from the input list `inp`, on the sample stream `xs`. -/
noncomputable def runFrom (P : GaussMixHH.Program) (n : ℕ) (inp : List ℝ) (xs : ℕ → Vec n)
    (t : ℕ) : GaussMixHH.State :=
  GaussMixHH.run P n (GaussMixHH.initState n inp) (noCoins, xs) t

/-- **Complexity on every stream.** On every sample stream the run of `P` from input `inp` halts
after reading at most `N` samples and doing at most `T` work (the cost model of the published
`GaussMixHH` machine: unit cost per instruction, `n` per `sample`). -/
def RunsWithin (P : GaussMixHH.Program) (n : ℕ) (inp : List ℝ) (N T : ℝ) : Prop :=
  ∀ xs : ℕ → Vec n, ∃ t : ℕ, (runFrom P n inp xs t).halted = true ∧
    ((runFrom P n inp xs t).samplesUsed : ℝ) ≤ N ∧ ((runFrom P n inp xs t).work : ℝ) ≤ T

/-- **Success with probability at least `p`.** There is a measurable set of sample streams of
`μ`-measure at least `p` on which every halted state of the run of `P` from `inp` satisfies `Good`
(as in the published `GaussPart.theorem_3_1`). Halted states stutter, so a run has one final
state. -/
def SucceedsWith (P : GaussMixHH.Program) (n : ℕ) (inp : List ℝ) (μ : Measure (ℕ → Vec n))
    (p : ENNReal) (Good : GaussMixHH.State → Prop) : Prop :=
  ∃ E : Set (ℕ → Vec n), MeasurableSet E ∧ p ≤ μ E ∧
    ∀ xs ∈ E, ∀ t : ℕ, (runFrom P n inp xs t).halted = true → Good (runFrom P n inp xs t)

/-- The start state of the **evaluator** on the learner's final state `s` and the query point
`x ∈ ℝᵈ`: the learner's registers, pointers and memory, with `x` written to the memory cells
`p[1], …, p[1] + d − 1` (the learner chooses the address through its pointer register `1`), the
program counter, cursors and counters reset to `0`. -/
noncomputable def evalInit (d : ℕ) (s : GaussMixHH.State) (x : Vec d) : GaussMixHH.State :=
  { core := { s.core with pc := 0, mem := GaussMixHH.writeSample s.core.mem (s.core.ptrs 1) x }
    coinCursor := 0
    samplesUsed := 0
    halted := false
    work := 0 }

open Classical in
/-- **The hypothesis output by a learner.** For an evaluator program `E` and a work budget `T`,
the hypothesis described by the learner's final state `s` is `h(x) = 1` if `E`, started from
`evalInit d s x`, halts within work `T` with output register `r[0] = 1`, and `h(x) = −1`
otherwise. So `h : ℝᵈ → {±1}` is computed from the learner's output in time `T`.

**Formalization Note.** The papers' learners "output a hypothesis `h : ℝᵈ → {±1}`"; a machine
outputs a description, and the hypothesis is the function the fixed evaluator computes from it.
The time bound on evaluation keeps "runs in poly(n) time" from being bypassed by storing the
samples. -/
noncomputable def hyp (E : GaussMixHH.Program) (d : ℕ) (T : ℝ) (s : GaussMixHH.State)
    (x : Vec d) : ℝ :=
  if ∃ t : ℕ, (GaussMixHH.run E d (evalInit d s x) (noCoins, fun _ => 0) t).halted = true ∧
      ((GaussMixHH.run E d (evalInit d s x) (noCoins, fun _ => 0) t).work : ℝ) ≤ T ∧
      GaussMixHH.output (GaussMixHH.run E d (evalInit d s x) (noCoins, fun _ => 0) t) = 1
  then 1 else -1

/-- A testable learner **accepts** when its final output register `r[0]` is `1`; any other value
is `Reject` (Definition A.5, p.70, PDF p.72). -/
def Accepts (s : GaussMixHH.State) : Prop := GaussMixHH.output s = 1

/-- The input encoding of one constraint `w · x ≤ b` (`s = 0`) or `w · x < b` (`s = 1`) as the
`d + 2` reals `(s, w₁, …, w_d, b)`, the record layout of the published `GaussPart.decode`. -/
noncomputable def encodeConstraint {d : ℕ} (c : Constraint d) : List ℝ :=
  (if c.strict then (1 : ℝ) else 0) :: (List.ofFn fun i : Fin d => c.normal i) ++ [c.bound]

/-- A cell: its number `m` of constraints followed by the `m` records. -/
noncomputable def encodeCell {d : ℕ} (R : Cell d) : List ℝ :=
  (R.length : ℝ) :: (R.map encodeConstraint).flatten

/-- **A partition as input** (Theorem 4.4, p.37, PDF p.39: the weak learner is "given the partition
`P`"): the number `N` of cells followed by the `N` encoded cells. No certification flags are
written: Algorithm 3 does not use `G`. -/
noncomputable def encodePartition {d : ℕ} (U : List (Cell d)) : List ℝ :=
  (U.length : ℝ) :: (U.map encodeCell).flatten

end Supplement

end GaussPart


