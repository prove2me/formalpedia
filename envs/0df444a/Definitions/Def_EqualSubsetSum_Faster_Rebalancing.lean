-- Prove2me | Definitions.Def_EqualSubsetSum_Faster_Rebalancing
-- name    : EqualSubsetSum_Faster_Rebalancing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:22:07.945552+00:00
-- url     : https://prove2.me/theorems/8216674d-4a15-46d6-b048-e4d40d3d8acc
-- title:
--   The rebalancing recursion V and F_t of Lemma 5.4
-- statement:
--   Let $(L_i)_{i\in\iota}$ be a finite nonempty family of finite lists of pairs $(a,b)$ of reals. Put
--   $$\mathcal V(\tau)=\min_i\sum_{(a,b)\in L_i}a^\tau b^{1-\tau},\qquad F_0(u)=1+u,\qquad F_{t+1}(u)=\min_i\sum_{(a,b)\in L_i}a\,F_t(ub/a).$$
--   Sums over a list count repeated pairs with multiplicity; powers are real powers.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 35, Lemma 5.4

import Mathlib

namespace EqualSubsetSum.Faster

/-! The rebalancing recursion of Lemma 5.4 (§5.4, p. 35). A finite family `(Lᵢ)_{i ∈ ι}` of
finite lists of pairs `(a, b)` of reals; the minimum over the family is `Finset.inf'` over a
nonempty finite index type. -/

/-- `V(τ) = min_i ∑_{(a,b) ∈ Lᵢ} a^τ b^{1-τ}` (real powers). -/
noncomputable def Vfun {ι : Type} [Fintype ι] [Nonempty ι] (L : ι → List (ℝ × ℝ)) (τ : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i => ((L i).map fun ab => ab.1 ^ τ * ab.2 ^ (1 - τ)).sum

/-- `F₀(u) = 1 + u`, `F_{t+1}(u) = min_i ∑_{(a,b) ∈ Lᵢ} a F_t(u b / a)`. -/
noncomputable def Ffun {ι : Type} [Fintype ι] [Nonempty ι] (L : ι → List (ℝ × ℝ)) : ℕ → ℝ → ℝ
  | 0, u => 1 + u
  | t + 1, u => Finset.univ.inf' Finset.univ_nonempty fun i =>
      ((L i).map fun ab => ab.1 * Ffun L t (u * ab.2 / ab.1)).sum

end EqualSubsetSum.Faster


