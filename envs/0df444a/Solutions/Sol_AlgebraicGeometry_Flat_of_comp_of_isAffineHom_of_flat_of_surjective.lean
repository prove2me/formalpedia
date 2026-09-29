-- Prove2me | solution 1 for AlgebraicGeometry.Flat.of_comp_of_isAffineHom_of_flat_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/3beddf4e-de5e-58b7-8c59-e8349a449552

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Theorems.Thm_Module_Flat_of_flat_of_faithfullyFlat_right
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective.AlgebraicGeometry TensorProduct"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom Scheme.Hom.appLE_comp_appLE IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme Flat HasRingHomProperty.appLE HasRingHomProperty.iff_appLE IsAffineOpen IsAffineHom HasRingHomProperty Scheme.Hom.comp_apply"
p2m_open "AlgebraicGeometry"

namespace Flat p2m_export "AlgebraicGeometry.Flat" "comp" end Flat
p2m_open_scoped "AlgebraicGeometry.Flat" in
set_option backward.isDefEq.respectTransparency false in

theorem Flat.of_comp_aux {X Y S : Scheme.{u}} (σ : X ⟶ Y) (y : Y ⟶ S)
    [hc : Flat (σ ≫ y)] [IsAffineHom σ] [Flat σ] [Surjective σ] : Flat y := by
  rw [HasRingHomProperty.iff_appLE (P := @Flat)]
  intro W V e

  let U : X.affineOpens := ⟨σ ⁻¹ᵁ (V : Y.Opens), V.2.preimage σ⟩
  have eU : (U : X.Opens) ≤ σ ⁻¹ᵁ (V : Y.Opens) := le_rfl
  have eWU : (U : X.Opens) ≤ (σ ≫ y) ⁻¹ᵁ (W : S.Opens) := fun x hx => e hx
  let φ := y.appLE W V e
  let ψ := σ.appLE V U eU
  have hcomp : φ ≫ ψ = (σ ≫ y).appLE W U eWU := Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  have hAC : ((σ ≫ y).appLE W U eWU).hom.Flat := HasRingHomProperty.appLE @Flat (σ ≫ y) hc W U eWU
  have hψflat : ψ.hom.Flat := HasRingHomProperty.appLE @Flat σ inferInstance V U eU

  have hψsurj : Function.Surjective (PrimeSpectrum.comap ψ.hom) := by
    intro p
    obtain ⟨x, hx⟩ := σ.surjective (V.2.fromSpec p)
    have hxU : x ∈ (U : X.Opens) := by
      change σ x ∈ (V : Y.Opens)
      rw [hx]
      exact V.2.range_fromSpec.le ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := U.2.range_fromSpec.ge hxU
    refine ⟨q, V.2.isOpenImmersion_fromSpec.base_open.injective ?_⟩
    change V.2.fromSpec (Spec.map ψ q) = V.2.fromSpec p
    rw [← hx, ← Scheme.Hom.comp_apply, IsAffineOpen.SpecMap_appLE_fromSpec σ V.2 U.2 eU,
      Scheme.Hom.comp_apply]
  have hψ : ψ.hom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr ⟨hψflat, hψsurj⟩

  rw [← hcomp, CommRingCat.hom_comp] at hAC
  algebraize [φ.hom, ψ.hom, ψ.hom.comp φ.hom]
  exact Module.Flat.of_flat_of_faithfullyFlat_right Γ(S, W) Γ(Y, V) Γ(X, U)

end AlgebraicGeometry

theorem solution {X Y S : Scheme.{u}}
    (σ : X ⟶ Y) (y : Y ⟶ S) [Flat (σ ≫ y)] [IsAffineHom σ] [Flat σ] [Surjective σ] : Flat y :=
  AlgebraicGeometry.Flat.of_comp_aux σ y

end S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_Flat_of_comp_of_isAffineHom_of_flat_of_surjective (solution)
