-- Prove2me | Definitions.Def_LipStableCA_offerBundle
-- name    : LipStableCA_offerBundle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:20.833212+00:00
-- url     : https://prove2.me/theorems/3f97d634-85c5-40ba-ac29-808940cf296c
-- title:
--   Attained bundles and the offer $B_\omega$
-- statement:
--   For a deterministic rule $S$, a bidder $i$ and reports $v_{-i}$, a bundle $Q$ is attained if $S_i(v_i',v_{-i})=Q$ for some $v_i'\in\mathcal V$. The offer is the union of the nonempty attained bundles, $B=\bigcup_{Q\in R^+}Q$, and is $\emptyset$ if there is none.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.3, p.21; p.22

import Definitions.Def_LipStableCA_Alloc

namespace LipStableCA

variable {n m : ℕ}

/-- `Q` is attained, Lemma 5.3, p.21: `Sᵢ(v′ᵢ, v₋ᵢ) = Q` for some `v′ᵢ ∈ V`. The reports `v₋ᵢ` are the
coordinates of `v` other than `i`. -/
def IsAttained (S : Profile n m → Alloc n m) (i : Fin n) (v : Profile n m)
    (Q : Finset (Fin m)) : Prop :=
  ∃ u, IsValuation u ∧ (S (Function.update v i u)).1 i = Q

open Classical in
/-- `B_ω = ⋃_{Q ∈ R⁺_ω} Q`, p.22, for the deterministic rule at the seed `ω`: the union of the nonempty
attained bundles, and `∅` if there is none. -/
noncomputable def offerBundle (S : Profile n m → Alloc n m) (i : Fin n) (v : Profile n m) :
    Finset (Fin m) :=
  (Finset.univ.filter fun Q => Q ≠ ∅ ∧ IsAttained S i v Q).biUnion id

end LipStableCA


