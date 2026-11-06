-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Prog
-- name    : SparseSDP_TwoSided_Prog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:19.834349+00:00
-- url     : https://prove2.me/theorems/6e2198c2-aee0-4a1b-adf1-442416051801
-- title:
--   Instrumented randomized programs: tape, cursor, operation counter, and the vector kernel
-- statement:
--   The computation model of the mission. A program reads a **random tape** of i.i.d. slots, each a standard Gaussian with a uniform number on $[0,1]$, through a cursor, and it pays into the operation counter of the published `Work` monad.
--
--   The cost model, which pins the paper's idealized real-arithmetic model (§2.2), is this closed list. One unit each: $+,-,\times,\div,\sqrt{\cdot},\exp,\log$, comparison and $\lceil\cdot\rceil$, array read or write, list push, loop dispatch, one draw from the tape, one oracle call. A vector operation of length $d$ (`axpy`, `dotp`, `nrm`, `scale`) costs $d$ such units. The two tridiagonal primitives are in `lanczosProg`.
--
--   `sampleCat` is the scan of §2.3: with $W=\sum_iw_i$ and one uniform draw $r\in[0,W)$, it returns the first index whose cumulative weight exceeds $r$; `sampleCoord` applies it to the weights $|x_i|^2$. The module also holds $\mathrm{softmax}$ and the exponential-weights distribution $\hat p_t=\mathrm{softmax}(-\eta\sum_{\tau<t}\hat c_\tau)$ of §7.6.
--
--   Running time is the final counter (`runCost`) from cursor and counter zero; `runVal` is the returned value. Programs never read the counter.
--
--   **Formalization Note** A Lean program can compute any pure function at no charge, so the guard is the text of the programs: each pure step sits behind `op k` with $k$ the number of listed operations. The moderator reads the programs line by line.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §2.2, p. 15; §2.3, pp. 15–16; §7.6, p. 54

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_SparseSDP_TwoSided_gap

open MeasureTheory ProbabilityTheory Matrix

namespace SparseSDP.TwoSided

open CapacitatedAssort.General (Work charge)

/-- The random tape: i.i.d. slots, each a standard Gaussian together with a uniform number of
`[0, 1]`. A draw reads one component of one slot. -/
abbrev Tape : Type := ℕ → ℝ × unitInterval

/-- The law of the tape: the infinite product of `N(0,1) ⊗ Unif[0,1]`. -/
noncomputable def tapeLaw : Measure Tape :=
  Measure.infinitePi fun _ => (gaussianReal 0 1).prod (volume : Measure unitInterval)

/-- Instrumented randomized real-RAM programs: a read-only tape, a cursor into it, and the operation
counter of the published `Work` monad.

Cost model (paper "idealized real-arithmetic model", §2.2, p. 15). The complete list of operations:

* unit cost: `+, −, ×, ÷, √, exp, log`, comparison and `⌈·⌉` on reals, the same on naturals, array
  read and write, list push, one loop dispatch, one draw from the tape, one oracle call;
* a vector primitive of length `d` (`axpy`, `dotp`, `nrm`, `scale`) is `d` such operations;
* `sampleCat` and `sampleCoord` are the scan of §2.3, charged per step;
* the two tridiagonal primitives `tridiagExpE1`, `tridiagLamMax` (module `lanczosProg`) charge `ℓ²`.

Every line of a program pays through `tick`/`op`. A program never reads the counter. -/
abbrev Prog (α : Type) : Type := ReaderT Tape (StateT ℕ Work) α

variable {α : Type}

/-- Run a program on a tape from a cursor and a counter: `((value, cursor), counter)`. -/
def Prog.exec (p : Prog α) (tape : Tape) (cur cnt : ℕ) : (α × ℕ) × ℕ :=
  StateT.run (StateT.run (p tape) cur) cnt

/-- The value of a run from cursor `0`. -/
def runVal (p : Prog α) (tape : Tape) : α := (p.exec tape 0 0).1.1

/-- The cost of a run: the final counter, from cursor `0` and count `0`. -/
def runCost (p : Prog α) (tape : Tape) : ℕ := (p.exec tape 0 0).2

/-- Pay `k` operations. -/
def tick (k : ℕ) : Prog Unit := fun _ => StateT.lift (charge k)

/-- `k` unit operations computing the value `v`. Each use is a fixed expression of `k` listed
operations, or a vector primitive with `k` its length. -/
def op (k : ℕ) (v : α) : Prog α := do tick k; pure v

/-- One tape slot, at unit cost; the cursor advances. -/
def drawSlot : Prog (ℝ × unitInterval) := do
  tick 1
  fun tape => do
    let c ← (get : StateT ℕ Work ℕ)
    set (σ := ℕ) (c + 1)
    pure (tape c)

/-- One standard Gaussian draw. -/
def drawGauss : Prog ℝ := do
  let x ← drawSlot
  pure x.1

/-- One uniform draw on `[0, 1]`. -/
def drawUnif : Prog ℝ := do
  let x ← drawSlot
  pure (x.2 : ℝ)

/-- Real vectors of length `d`. -/
abbrev Vec (d : ℕ) : Type := Fin d → ℝ

/-- Real `d × d` matrices. -/
abbrev Mat (d : ℕ) : Type := Matrix (Fin d) (Fin d) ℝ

variable {d k : ℕ}

/-- `a x + y`, charged `d`. -/
noncomputable def axpy (a : ℝ) (x y : Vec d) : Prog (Vec d) := op d (a • x + y)

/-- `x ⬝ y`, charged `d`. -/
noncomputable def dotp (x y : Vec d) : Prog ℝ := op d (x ⬝ᵥ y)

/-- `‖x‖₂`, charged `d + 1`. -/
noncomputable def nrm (x : Vec d) : Prog ℝ := op (d + 1) (l2 x)

/-- `a x`, charged `d`. -/
noncomputable def scale (a : ℝ) (x : Vec d) : Prog (Vec d) := op d (a • x)

/-- The scan of §2.3, p. 16, for nonnegative weights `w`: `W := ∑ wᵢ`, one uniform draw gives
`r ∈ [0, W)`, then the coordinates are scanned with the cumulative weight `C_t` of Eq. (26) and the
first index with `C_t > r` is returned.

**Formalization Note.** If no index qualifies (only for `r = W`, a null event, or `W = 0`), index `0`
is returned. -/
noncomputable def sampleCat [NeZero k] (w : Vec k) : Prog (Fin k) := do
  let W ← op k (∑ i, w i)
  let v ← drawUnif
  let rr ← op 1 (v * W)
  let mut cum : ℝ := 0
  let mut res : Fin k := 0
  for i in List.finRange k do
    tick 1
    cum ← op 1 (cum + w i)
    tick 1
    if rr < cum then
      res := i
      break
  pure res

/-- Squared-magnitude sampling `p_x(i) = |xᵢ|²/‖x‖₂²` of Eq. (25) (§2.3, pp. 15–16). -/
noncomputable def sampleCoord [NeZero d] (x : Vec d) : Prog (Fin d) := do
  let w ← op (2 * d) (fun i => x i ^ 2)
  sampleCat w

/-- `softmax(a)ⱼ = e^{aⱼ}/∑ᵢ e^{aᵢ}`. -/
noncomputable def softmaxV (a : Vec k) : Vec k :=
  fun j => Real.exp (a j) / ∑ i, Real.exp (a i)

/-- The charged softmax: `k` exponentials, `k` additions, `k` divisions. -/
noncomputable def softmaxP (a : Vec k) : Prog (Vec k) := op (3 * k) (softmaxV a)

/-- The exponential-weights distribution of round `t`, from the feedback `ĉ₁, …, ĉ_{t−1}`, initialized
uniformly, with learning rate `η` (§7.6, p. 54): `p̂_t = softmax(−η ∑_{τ<t} ĉ_τ)`. -/
noncomputable def expWeights {m : ℕ} (η : ℝ) (chat : ℕ → Vec m) (t : ℕ) : Vec m :=
  softmaxV (-η • ∑ τ ∈ Finset.Ico 1 t, chat τ)

end SparseSDP.TwoSided


