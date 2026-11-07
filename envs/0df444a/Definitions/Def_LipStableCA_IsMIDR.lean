-- Prove2me | Definitions.Def_LipStableCA_IsMIDR
-- name    : LipStableCA_IsMIDR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:09.585213+00:00
-- url     : https://prove2.me/theorems/9b2d374c-5046-4b2d-923c-2f62db36c969
-- title:
--   Maximal-in-distributional-range rules
-- statement:
--   Let $D$ be a set of distributions on allocations, fixed before the reports are seen. A randomized rule is maximal in distributional range with range $D$ if its law at every profile $v$ lies in $D$ and maximizes the expected welfare $W_v(\lambda)$ over $\lambda\in D$. The module also defines $\mathbb E_{S\sim\lambda}[\sum_{h\ne i}v_h(S_h)]$, the term in Fact 2.10.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Def. 2.9, p.9; Fact 2.10, p.9

import Definitions.Def_LipStableCA_emd

namespace LipStableCA

variable {n m : ℕ}

/-- Maximal in distributional range, Definition 2.9, p.9: the rule's law at every profile lies in the
report-independent set `D` of laws and maximizes the expected welfare over `D`. -/
def IsMIDR (P : Profile n m → Alloc n m → ℝ) (D : Set (Alloc n m → ℝ)) : Prop :=
  ∀ v : Profile n m, IsProfile v → P v ∈ D ∧ ∀ l ∈ D, expectedWelfare v l ≤ expectedWelfare v (P v)

/-- `E_{S∼λ}[Σ_{h≠i} v_h(S_h)]`, the term of Fact 2.10, p.9. -/
noncomputable def othersWelfare (v : Profile n m) (i : Fin n) (l : Alloc n m → ℝ) : ℝ :=
  ∑ T, l T * ∑ h ∈ Finset.univ.erase i, v h (T.1 h)

end LipStableCA


