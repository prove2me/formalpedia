-- Prove2me | solution 1 for AlgebraicClosure.monoidHom_eq_one_of_inertiaSubgroupIn_le_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/24497c4a-34ca-5d85-a6e8-643c0bf8a9aa

import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_AlgebraicClosure_subgroup_eq_top_of_inertiaSubgroupIn_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker

theorem solution {Γ : Type*} [Group Γ]
    (χ : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) →* Γ)
    (hopen : IsOpen (χ.ker : Set ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))))
    (hunr : ∀ q : ℕ, q.Prime → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      A.inertiaSubgroupIn ℚ ≤ χ.ker) :
    χ = 1 := by
  have hker : χ.ker = ⊤ :=
    AlgebraicClosure.subgroup_eq_top_of_inertiaSubgroupIn_le χ.ker hopen hunr
  ext σ
  have hσ : σ ∈ χ.ker := hker ▸ Subgroup.mem_top σ
  simpa [MonoidHom.mem_ker] using hσ

end S_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker
end P2MW
export P2MW.S_AlgebraicClosure_monoidHom_eq_one_of_inertiaSubgroupIn_le_ker (solution)
