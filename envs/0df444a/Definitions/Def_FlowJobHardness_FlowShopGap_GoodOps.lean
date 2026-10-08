-- Prove2me | Definitions.Def_FlowJobHardness_FlowShopGap_GoodOps
-- name    : FlowJobHardness_FlowShopGap_GoodOps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T09:34:09.259908+00:00
-- url     : https://prove2.me/theorems/b6809465-71cb-4404-af30-2dd66a4ed02a
-- title:
--   Good long-operations, the interval sets $T_{g,f}$ and their total length $L(T_{g,f})$ (Section 2.2.2)
-- statement:
--   Fix a schedule $s$ of the flow shop instance $F(r,d)$, i.e. a start time $s(o)$ for every operation $o$.
--
--   **Delays and good long-operations.** Let $j$ be a job of frequency $f$; it has long-operations on $r^{2f}$ machines, each of length $r^{2(d-f)}$. For its $i$-th long-operation, the **delay** $d_j(i)$ is the time between the end of that long-operation and the start of the $(i+1)$-th long-operation of $j$, with $d_j(i)=\infty$ for the last long-operation. The $i$-th long-operation of $j$ is **good** if
--   $$d_j(i)\ \le\ \frac{r^2}{4}\cdot r^{2(d-f)} .$$
--   In particular the last long-operation of a job is never good.
--
--   **Counts.** For a job $j$, `longCount` is the number of its long-operations and `goodCount` the number of its good long-operations in $s$.
--
--   **The sets $T_{g,f}$.** For a machine group $g$ and a frequency $f$, $T_{g,f}$ is the set of time intervals given by the **first halves** $[s(o),\,s(o)+p(o)/2)$ of all good long-operations $o$ scheduled on machine $m_{g,f}$.
--
--   **The covered length.** $L(T_{g,f})$ is the total time covered by the intervals of $T_{g,f}$, that is, the Lebesgue measure of their union.
--
--   These notions are the bookkeeping of the lower-bound argument for $F(r,d)$: Lemma 2.2 counts good long-operations, Lemma 2.3 separates the sets $T_{g,k}$ and $T_{g,\ell}$, and Lemma 2.4 bounds $\sum_f L(T_{g,f})$ from below.
--
--   **Formalization Note** "The next long-operation" of the operation $o=(j,i)$ is the operation $(j,i')$ with $i'>i$ of positive length such that every operation of $j$ strictly between $i$ and $i'$ has length $0$; if there is none, $o$ is not good (the paper's $d_j=\infty$). The threshold uses the frequency $f$ of the job through `jobFreq`. $L$ is `(volume (⋃₀ T)).toReal`; $T_{g,f}$ is a finite set of bounded intervals, so the measure is finite and the conversion to a real number loses nothing. The counts use classical decidability.
-- source:
--   Mastrolilli, Svensson, Hardness of Approximating Flow and Job Shop Scheduling Problems, J. ACM 58(5) (2011), Article 20, pp. 20:10-20:11, Section 2.2.1 (long- and short-operations) and Section 2.2.2 (d_j(i), good long-operations, T_{g,f}, L(T_{g,f}))

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_FlowJobHardness_FlowShopGap_Construction

open JobShopLTAS.Core

namespace FlowJobHardness.FlowShopGap

/-! # Good long-operations, the interval sets `T_{g,f}` and `L(T_{g,f})`

Mastrolilli–Svensson, J. ACM 58(5) (2011), Article 20, §2.2.1 (p. 20:10, long- and
short-operations) and §2.2.2 (pp. 20:10–20:11). All notions are relative to a schedule `s`
(start times) of the instance `inst r d = F(r, d)`. -/

/-- A **long-operation**: an operation of `F(r, d)` requiring more than `0` time units
(p. 20:10). The other operations are **short-operations**. -/
def IsLongOp (r d : ℕ) (o : (inst r d).Op) : Prop := 0 < (inst r d).proc o

/-- The operation `o` of job `j` (frequency `f`) is a **good** long-operation of the schedule
`s` (§2.2.2, p. 20:10): it is a long-operation, it is not the last long-operation of `j`, and
the delay `d_j(o)` between its end and the start of the next long-operation of `j` is at most
`(r²/4) · r^{2(d-f)}`. The last long-operation of a job (`d_j = ∞` in the paper) is never
good. -/
def IsGood (r d : ℕ) (s : (inst r d).Op → ℝ) (o : (inst r d).Op) : Prop :=
  IsLongOp r d o ∧
    ∃ i' : Fin ((inst r d).μ o.1), o.2 < i' ∧ IsLongOp r d ⟨o.1, i'⟩ ∧
      (∀ i'' : Fin ((inst r d).μ o.1), o.2 < i'' → i'' < i' → ¬ IsLongOp r d ⟨o.1, i''⟩) ∧
      s ⟨o.1, i'⟩ - (s o + (inst r d).proc o) ≤
        (r : ℝ) ^ 2 / 4 * (r : ℝ) ^ (2 * (d - jobFreq r d o.1.val))

open Classical in
/-- The number of long-operations of job `q`. -/
noncomputable def longCount (r d : ℕ) (q : Fin (size r d)) : ℕ :=
  (Finset.univ.filter fun i : Fin ((inst r d).μ q) => IsLongOp r d ⟨q, i⟩).card

open Classical in
/-- The number of good long-operations of job `q` in the schedule `s`. -/
noncomputable def goodCount (r d : ℕ) (s : (inst r d).Op → ℝ) (q : Fin (size r d)) : ℕ :=
  (Finset.univ.filter fun i : Fin ((inst r d).μ q) => IsGood r d s ⟨q, i⟩).card

open Classical in
/-- The good long-operations of `s` scheduled on machine `m_{g,f}`. -/
noncomputable def goodOpsOn (r d : ℕ) (s : (inst r d).Op → ℝ) (g f : ℕ) :
    Finset (inst r d).Op :=
  Finset.univ.filter fun o =>
    IsGood r d s o ∧ machGroup d ((inst r d).mach o) = g ∧ machFreq d ((inst r d).mach o) = f

/-- The first half `[s(o), s(o) + p(o)/2)` of the operation `o` in the schedule `s`. -/
def firstHalf (r d : ℕ) (s : (inst r d).Op → ℝ) (o : (inst r d).Op) : Set ℝ :=
  Set.Ico (s o) (s o + (inst r d).proc o / 2)

/-- `T_{g,f}` (§2.2.2, p. 20:10): the set of time intervals given by the first halves of all
good long-operations of `s` scheduled on machine `m_{g,f}`. -/
def T (r d : ℕ) (s : (inst r d).Op → ℝ) (g f : ℕ) : Set (Set ℝ) :=
  {I | ∃ o ∈ goodOpsOn r d s g f, I = firstHalf r d s o}

/-- `L(T_{g,f})` (p. 20:11): the total time covered by the intervals of `T_{g,f}`, i.e. the
Lebesgue measure of their union (a finite union of bounded intervals, so the measure is
finite and `toReal` loses nothing). -/
noncomputable def L (r d : ℕ) (s : (inst r d).Op → ℝ) (g f : ℕ) : ℝ :=
  (MeasureTheory.volume (⋃₀ T r d s g f)).toReal

end FlowJobHardness.FlowShopGap


