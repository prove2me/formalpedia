-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.hom_ext_of_isIso_fromTildeGamma
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7be00ee4-6ba7-5185-a234-56996df1215d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem solution {R : CommRingCat.{u}}
    {M N : (Spec (.of R)).Modules} [IsIso (Scheme.Modules.fromTildeΓ M)] (φ ψ : M ⟶ N)
    (h : ∀ m : Γ(M, ⊤), φ.app ⊤ m = ψ.app ⊤ m) : φ = ψ := by
  have hΓ : (moduleSpecΓFunctor (R := R)).map φ = (moduleSpecΓFunctor (R := R)).map ψ := by
    ext m
    exact h m
  have n1 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have n2 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at n1 n2
  rw [← cancel_epi (Scheme.Modules.fromTildeΓ M)]
  change (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ φ =
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ ψ
  refine n1.symm.trans ?_
  rw [hΓ]
  exact n2

end S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma (solution)
