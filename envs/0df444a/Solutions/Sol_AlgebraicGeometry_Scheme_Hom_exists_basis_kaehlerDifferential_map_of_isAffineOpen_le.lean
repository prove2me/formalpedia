-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a76d8fbb-b7fd-55be-a456-71c18255397c

import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

theorem solution
    {B : Type u} [CommRing B] {X : Scheme.{u}} (gX : X ⟶ Spec (CommRingCat.of B))
    {W W' : X.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W) {ι : Type v} :
    letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra W'
    letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
    ∀ [IsScalarTower B Γ(X, W) Γ(X, W')] (b : Module.Basis ι Γ(X, W) (Ω[Γ(X, W)⁄B])),
      ∃ b' : Module.Basis ι Γ(X, W') (Ω[Γ(X, W')⁄B]),
        ∀ i, b' i = KaehlerDifferential.map B B Γ(X, W) Γ(X, W') (b i) := by
  letI := gX.sectionsAlgebra W; letI := gX.sectionsAlgebra W'
  letI : Algebra Γ(X, W) Γ(X, W') := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra
  intro _inst b

  have hEt : RingHom.Etale (X.presheaf.map (homOfLE hle).op).hom := by
    have h := HasRingHomProperty.appLE (P := @Etale) (Q := @RingHom.Etale) (𝟙 X) inferInstance
      ⟨W, hW⟩ ⟨W', hW'⟩ (by simpa using hle)
    simp [Scheme.Hom.appLE] at h
    exact h
  haveI : Algebra.FormallyEtale Γ(X, W) Γ(X, W') := hEt.formallyEtale
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale B Γ(X, W) Γ(X, W')
  refine ⟨(Algebra.TensorProduct.basis Γ(X, W') b).map e, fun i => ?_⟩
  rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]

end S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le (solution)
