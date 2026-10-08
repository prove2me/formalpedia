-- Prove2me | Definitions.Def_FlowJobHardness_ColoringReduction_Schedule
-- name    : FlowJobHardness_ColoringReduction_Schedule
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:37.57869+00:00
-- url     : https://prove2.me/theorems/fc4986fd-50f4-49a9-8a9b-12e534ea99e5
-- title:
--   Completion times, good long-operations and the interval sets $T_{g,v}$ for S(r, d) (Sections 2.2.2, 3.2.3)
-- statement:
--   Fix the instance $S(r,d)$ built from a graph $G$ on $n$ vertices with a proper colouring into $d$ classes, write $\mathrm{lb} = R = r^{2d}$, and let $s$ assign a start time to every operation.
--
--   1. The **completion time** $C_j$ of a job $j$ is the end of its last operation, i.e. the maximum of $s(o) + p(o)$ over its operations $o$. A job **finishes within** $L\cdot \mathrm{lb}$ if $C_j \le L\cdot r^{2d}$; the number of such jobs is the *finished count*.
--   2. An operation is a **long-operation** if its processing time is positive, and a short-operation otherwise. For a job $j$ of frequency $f$, the **delay** $d_j(i)$ is the time between the end of its $i$-th long-operation and the start of its $(i+1)$-th long-operation ($d_j(i)=\infty$ for the last one). The $i$-th long-operation is **good** if
--   $$
--   d_j(i) \le \frac{r^2}{4}\, r^{2(d-f)}.
--   $$
--   In particular the last long-operation of a job is never good.
--   3. For a group index $g \in \{1,\dots,r^{2d}\}$, a vertex $v$ and a real $L$, the set $T_{g,v}$ consists of the time intervals $[s(o),\, s(o)+p(o)/2)$ (the **first halves**) of all good long-operations $o$ scheduled on the machine $m_{g,v}$ that belong to jobs finishing within $L\cdot\mathrm{lb}$. The jobs that do not finish in time are disregarded.
--   4. $L(T_{g,v})$ is the total time covered by the intervals of $T_{g,v}$.
--
--   These are the quantities of the soundness analysis: good long-operations are frequent (Lemma 3.10), the sets $T_{g,u}$ and $T_{g,v}$ of adjacent vertices are disjoint (Lemma 3.11), and some group covers much time (Lemma 3.12).
--
--   **Formalization Note.** The completion time is a real supremum over the finitely many operations of the job (`0` for a job without operations, which does not occur for $r\ge 1$). Goodness compares the start of the next long-operation of the same job with the end of the current one. $L(T_{g,v})$ is the Lebesgue measure of the union of the intervals, converted to a real number; the union is a finite union of bounded intervals, so the measure is finite. Group indices are 1-based, as in the paper.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, p. 20:10 (Section 2.2.2, good long-operations) and p. 20:18 (Section 3.2.3, proof of Lemma 3.9: T_{g,v}, L(T_{g,v}))

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_ColoringReduction_Construction

open JobShopLTAS.Core

namespace FlowJobHardness.ColoringReduction

/-! # Completion times, good long-operations and the interval sets `T_{g,v}` for `S(r, d)`

Mastrolilli–Svensson, J. ACM 58(5) (2011), Article 20: good long-operations (§2.2.2,
p. 20:10, re-used on p. 20:18), the sets `T_{g,v}` and their covered length `L(T_{g,v})`
(§3.2.3, p. 20:18). Throughout, `s` assigns a start time to every operation of `S(r, d)`. -/

variable {n d : ℕ} (G : SimpleGraph (Fin n)) (c : G.Coloring (Fin d)) (r : ℕ)

/-- The completion time `C_j` of job `q` in `s`: the end of its last operation, written as
the maximum over its operations of `s o + p o` (equal to the end of the last operation for a
feasible schedule; `0` for a job without operations). -/
noncomputable def jobCompletion (s : (inst G c r).Op → ℝ) (q : Fin (size r d n)) : ℝ :=
  ⨆ i : Fin ((inst G c r).μ q), s ⟨q, i⟩ + (inst G c r).p q i

/-- A **long-operation**: an operation requiring more than `0` time units (p. 20:17). The
other operations are **short-operations**. -/
def IsLongOp (o : (inst G c r).Op) : Prop := 0 < (inst G c r).proc o

/-- The operation `o` of job `j` (frequency `f`) is a **good** long-operation of `s`
(§2.2.2, p. 20:10; p. 20:18): it is a long-operation, it is not the last long-operation of
`j`, and the delay `d_j` between its end and the start of the next long-operation of `j` is at
most `(r²/4) · r^{2(d-f)}`. The last long-operation of a job (`d_j = ∞` in the paper) is never
good. -/
def IsGood (s : (inst G c r).Op → ℝ) (o : (inst G c r).Op) : Prop :=
  IsLongOp G c r o ∧
    ∃ i' : Fin ((inst G c r).μ o.1), o.2 < i' ∧ IsLongOp G c r ⟨o.1, i'⟩ ∧
      (∀ i'' : Fin ((inst G c r).μ o.1), o.2 < i'' → i'' < i' →
        ¬ IsLongOp G c r ⟨o.1, i''⟩) ∧
      s ⟨o.1, i'⟩ - (s o + (inst G c r).proc o) ≤
        (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - jobFreq c o.1))

open Classical in
/-- The number of good long-operations of job `q` in `s`. -/
noncomputable def goodCount (s : (inst G c r).Op → ℝ) (q : Fin (size r d n)) : ℕ :=
  (Finset.univ.filter fun i : Fin ((inst G c r).μ q) => IsGood G c r s ⟨q, i⟩).card

open Classical in
/-- The number of jobs of `S(r, d)` whose completion time in `s` is at most `L · r^{2d}`
(the jobs that "finish within `lb · L` time units"). -/
noncomputable def finishedCount (s : (inst G c r).Op → ℝ) (L : ℝ) : ℕ :=
  (Finset.univ.filter fun q : Fin (size r d n) =>
    jobCompletion G c r s q ≤ L * (R r d : ℝ)).card

/-- The first half `[s(o), s(o) + p(o)/2)` of the operation `o` in `s`. -/
def firstHalf (s : (inst G c r).Op → ℝ) (o : (inst G c r).Op) : Set ℝ :=
  Set.Ico (s o) (s o + (inst G c r).proc o / 2)

/-- `T_{g,v}` (§3.2.3, p. 20:18), for the schedule `s` after disregarding the jobs that do not
finish within `L · lb`: the set of time intervals given by the first halves of all good
long-operations of jobs with completion time `≤ L · r^{2d}` scheduled on the machine
`m_{g,v}` (`g` 1-based). -/
def T (s : (inst G c r).Op → ℝ) (L : ℝ) (g : ℕ) (v : Fin n) : Set (Set ℝ) :=
  {I | ∃ o : (inst G c r).Op, IsGood G c r s o ∧
    jobCompletion G c r s o.1 ≤ L * (R r d : ℝ) ∧
    FlowJobHardness.FlowShopGap.machGroup n ((inst G c r).mach o).val = g ∧ machVtx ((inst G c r).mach o) = v ∧
    I = firstHalf G c r s o}

/-- `L(T_{g,v})` (p. 20:18): the total time covered by the intervals of `T_{g,v}`, i.e. the
Lebesgue measure of their union (a finite union of bounded intervals, so the measure is finite
and `toReal` loses nothing). -/
noncomputable def coveredLength (s : (inst G c r).Op → ℝ) (L : ℝ) (g : ℕ) (v : Fin n) : ℝ :=
  (MeasureTheory.volume (⋃₀ T G c r s L g v)).toReal

end FlowJobHardness.ColoringReduction


