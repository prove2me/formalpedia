-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/f619e85f-8590-5064-ae58-9668f365c6eb

import Mathlib
import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation
open scoped BigOperators TensorProduct

namespace AFAux

theorem mem_finset_inf {X : Scheme.{0}} {ι : Type} (s : Finset ι) (f : ι → X.Opens) (x : X) :
    x ∈ s.inf f ↔ ∀ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.inf_insert, TopologicalSpace.Opens.mem_inf, ih]
    simp only [Finset.mem_insert, forall_eq_or_imp]

theorem preimage_finset_inf {X Y : Scheme.{0}} (φ : X ⟶ Y) {ι : Type} (s : Finset ι) (f : ι → Y.Opens) :
    φ ⁻¹ᵁ (s.inf f) = s.inf fun i => φ ⁻¹ᵁ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf, ih]

end AFAux

theorem solution
    {B : Type} [CommRing B] {X : Scheme.{0}} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
    (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut X) (F : Finset X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ (∀ x ∈ F, x ∈ U) ∧ ∀ g : G, (ρ g).hom ⁻¹ᵁ U = U  := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : IsSeparated πX := hsep
  haveI : IsSeparated (terminal.from X) := by rw [← terminal.comp_from πX]; infer_instance
  haveI : X.IsSeparated := ⟨inferInstance⟩

  obtain ⟨W, hW, hFW⟩ := hAF (Finset.univ.biUnion fun g : G => F.image fun x => (ρ g).hom.base x)
  refine ⟨Finset.univ.inf fun g : G => (ρ g).hom ⁻¹ᵁ W, ?_, ?_, ?_⟩
  · rw [Finset.inf_univ_eq_iInf]
    exact IsAffineOpen.iInf fun g => hW.preimage (ρ g).hom
  · intro x hx
    rw [AFAux.mem_finset_inf]
    intro g _
    show (ρ g).hom.base x ∈ W
    exact hFW _ (Finset.mem_biUnion.2 ⟨g, Finset.mem_univ g, Finset.mem_image_of_mem _ hx⟩)
  · intro h
    rw [AFAux.preimage_finset_inf]
    apply le_antisymm
    · apply Finset.le_inf
      intro g _
      have hmul : (ρ h).hom ⁻¹ᵁ ((ρ (g * h⁻¹)).hom ⁻¹ᵁ W) = (ρ g).hom ⁻¹ᵁ W := by
        have e : (ρ h).hom ≫ (ρ (g * h⁻¹)).hom = (ρ g).hom := by
          rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, inv_mul_cancel_right]
        rw [← Scheme.Hom.comp_preimage, e]
      rw [← hmul]
      exact Finset.inf_le (Finset.mem_univ (g * h⁻¹))
    · apply Finset.le_inf
      intro g _
      have hmul : (ρ h).hom ⁻¹ᵁ ((ρ g).hom ⁻¹ᵁ W) = (ρ (g * h)).hom ⁻¹ᵁ W := by
        have e : (ρ h).hom ≫ (ρ g).hom = (ρ (g * h)).hom := by
          rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul]
        rw [← Scheme.Hom.comp_preimage, e]
      rw [hmul]
      exact Finset.inf_le (Finset.mem_univ (g * h))

end S_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isAffineOpen_forall_mem_forall_preimage_eq_of_isSeparated_of_finset (solution)
