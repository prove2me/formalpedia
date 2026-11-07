-- Prove2me | Definitions.Def_DynSetCover_Rounding
-- name    : DynSetCover_Rounding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:34.766446+00:00
-- url     : https://prove2.me/theorems/ac1fabea-4242-42d6-aed9-1ff471ac2386
-- title:
--   §3.1.3 and (24) — rounded costs $c(S)=2^{H(S)}$, bases $b(e)$, $\mathrm{OPT}$, $A^{\ge j}$ and the augmented covering optimum $g_j$
-- statement:
--   Costs are rounded up to powers of two: for $S\in\mathcal F$,
--   $$H(S)=\lceil\log_2 c_0(S)\rceil,\qquad c(S)=2^{H(S)},$$
--   so $c_0(S)\le c(S)<2c_0(S)$. $\mathrm{OPT}(A)$ is the minimum rounded cost of a subfamily covering $A$. For each element $e$, a **cheapest set** $S_e$ is a set containing $e$ of minimum rounded cost, and the **base level** of $e$ is $b(e)=H(S_e)$, so $c(S_e)=2^{b(e)}$; the base does not depend on which cheapest set is chosen.
--
--   For $A\subseteq U$ and an integer $j$, let $A^{\ge j}=\{e\in A: b(e)\ge j\}$. The **augmented covering optimum at scale $j$** is
--   $$g_j(A)=\min_{\mathcal T\subseteq\mathcal F}\Big\{2^{-j}\sum_{S\in\mathcal T}c(S)+\Big|A^{\ge j}\setminus\bigcup_{S\in\mathcal T}S\Big|\Big\},$$
--   the optimum of covering $A^{\ge j}$ with the real sets at cost $c(S)2^{-j}$ and virtual singletons at cost one.
--
--   These quantities drive the approximation analysis: the retained costs are compared scale by scale with $g_j$.
--
--   **Formalization Note** $\lceil\log_2 x\rceil$ is `Int.clog 2 x`, the least integer $k$ with $x\le 2^k$, which equals $\lceil\log_2x\rceil$ for $x>0$. A choice of cheapest sets is a function `ce` with $e\in S_{ce(e)}$ and $H(S_{ce(e)})\le H(S)$ for every $S\ni e$.
-- source:
--   Paul, Solomon, Weighted Set Cover with Constant Worst-Case Recourse: From Exponential to Best-Known Update Time (STOC 2027 submission, preprint, sha256 a671756b983353737f48798343a4d176654843ba40cd482f54283402087c5cb0), §3.1.3, p.17 (PDF 19), rounding and bases; §4, p.24 (PDF 26), OPT; p.25–26 (PDF 27–28), A^{≥j}_t and (24)

import Mathlib
import Definitions.Def_DynSetCover_Instance

namespace DynSetCover

namespace Instance

variable (inst : Instance)

/-- **Rounded costs, bases and the augmented covering optimum** (Paul, Solomon, STOC 2027
submission, sha256 a671756b…, §3.1.3, p.17 (PDF 19), and (24), p.26 (PDF 28)).

`H(S) = ⌈log₂ c0(S)⌉`, the rounded-cost exponent.

**Formalization Note.** `⌈log₂ x⌉` is `Int.clog 2 x`, the least integer `k` with `x ≤ 2^k`;
for `x > 0` this is exactly `⌈log₂ x⌉`, and every cost is positive. -/
noncomputable def H (s : Fin inst.m) : ℤ := Int.clog 2 (inst.c0 s)

/-- The rounded cost `c(S) = 2^{H(S)}` (p.17). -/
noncomputable def c (s : Fin inst.m) : ℝ := (2 : ℝ) ^ (inst.H s)

/-- `OPT(A)`, the minimum rounded cost of a subfamily covering `A` (p.24). -/
noncomputable def OPT (A : Finset (Fin inst.u)) : ℝ :=
  (inst.coversOf A).inf' (inst.coversOf_nonempty A) (fun T => ∑ s ∈ T, inst.c s)

/-- The rounded exponents of the sets containing `e`; nonempty because the union of the
family is the universe. -/
noncomputable def baseCandidates (e : Fin inst.u) : Finset ℤ :=
  (Finset.univ.filter (fun s => e ∈ inst.S s)).image inst.H

theorem baseCandidates_nonempty (e : Fin inst.u) : (inst.baseCandidates e).Nonempty := by
  obtain ⟨s, hs⟩ := inst.covers e
  exact ⟨inst.H s, Finset.mem_image.2 ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩, rfl⟩⟩

/-- The base level `b(e) = H(S_e)`, the rounded exponent of a cheapest (rounded-cost) set
containing `e`, so that `c(S_e) = 2^{b(e)}` (p.17). It does not depend on which cheapest set is
fixed. -/
noncomputable def base (e : Fin inst.u) : ℤ := (inst.baseCandidates e).min' (inst.baseCandidates_nonempty e)

/-- `ce` is a choice of cheapest sets: `e ∈ S_e = S (ce e)` and `c(S_e)` is minimal among the
rounded costs of the sets containing `e` ("Fix a cheapest set `S_e` deterministically", p.17). -/
noncomputable def IsCheapest (ce : Fin inst.u → Fin inst.m) : Prop :=
  ∀ e, e ∈ inst.S (ce e) ∧ ∀ s, e ∈ inst.S s → inst.H (ce e) ≤ inst.H s

/-- `A^{≥j} = {e ∈ A : b(e) ≥ j}` (p.25). -/
noncomputable def above (A : Finset (Fin inst.u)) (j : ℤ) : Finset (Fin inst.u) :=
  A.filter (fun e => j ≤ inst.base e)

/-- The augmented covering optimum at scale `j`, (24), p.26:
`g_j(A) = min_{T ⊆ F} { 2^{−j} Σ_{S∈T} c(S) + |A^{≥j} ∖ ⋃_{S∈T} S| }`. -/
noncomputable def g (j : ℤ) (A : Finset (Fin inst.u)) : ℝ :=
  (Finset.univ : Finset (Finset (Fin inst.m))).inf' Finset.univ_nonempty
    (fun T => (2 : ℝ) ^ (-j) * (∑ s ∈ T, inst.c s) + ((inst.above A j \ T.biUnion inst.S).card : ℝ))

end Instance

end DynSetCover


