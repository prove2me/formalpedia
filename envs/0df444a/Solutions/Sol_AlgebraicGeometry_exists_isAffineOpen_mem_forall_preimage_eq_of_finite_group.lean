-- Prove2me | solution 1 for AlgebraicGeometry.exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/730a7585-74d1-5140-906f-b454ab97a6ec

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (A : Type) [CommRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f]
    (haff : ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ (U : Set X))
    (G : Type) [Group G] [Finite G] (a : G →* Aut X) (ha : ∀ g : G, (a g).hom ≫ f = f) (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, (a g).hom ⁻¹ᵁ U = U := by
  classical
  letI : Fintype G := Fintype.ofFinite G

  obtain ⟨V, hV, hSV⟩ := haff (Set.range fun g : G => (a g).hom.base x) (Set.finite_range _)

  haveI : IsSeparated (terminal.from X) := by rw [← terminal.comp_from f]; infer_instance
  haveI : IsAffineHom (pullback.diagonal (terminal.from X)) := inferInstance
  let W : G → X.Opens := fun g => (a g).hom ⁻¹ᵁ V
  have hW : ∀ g, IsAffineOpen (W g) := fun g => hV.preimage_of_isIso (a g).hom

  have memU : ∀ y : X, y ∈ (⨅ g, W g) ↔ ∀ g, (a g).hom.base y ∈ V := by
    intro y
    rw [← Finset.inf_univ_eq_iInf, ← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simp only [Finset.mem_univ, Set.iInter_true, Set.mem_iInter, Function.comp_apply, SetLike.mem_coe]
    exact Iff.rfl
  refine ⟨⨅ g, W g, IsAffineOpen.iInf hW, (memU x).2 fun g => hSV ⟨g, rfl⟩, fun g => ?_⟩
  ext y
  show y ∈ (a g).hom ⁻¹ᵁ (⨅ h, W h) ↔ y ∈ ⨅ h, W h
  rw [show (y ∈ (a g).hom ⁻¹ᵁ (⨅ h, W h)) ↔ (a g).hom.base y ∈ ⨅ h, W h from Iff.rfl, memU, memU]
  constructor
  · intro hy h
    have := hy (h * g⁻¹)
    rw [map_mul, map_inv] at this

    have e : ((a h * (a g)⁻¹).hom.base) ((a g).hom.base y) = (a h).hom.base y := by
      show (((a g).hom ≫ (a h * (a g)⁻¹).hom).base) y = (a h).hom.base y
      congr 2
      rw [Aut.Aut_mul_def, Aut.Aut_inv_def, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [e] at this; exact this
  · intro hy h
    have := hy (h * g)
    rw [map_mul] at this
    have e : (a (h) * a g).hom.base y = (a h).hom.base ((a g).hom.base y) := by
      show ((a h * a g).hom.base) y = ((a g).hom ≫ (a h).hom).base y
      congr 2
    rw [e] at this; exact this

end S_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isAffineOpen_mem_forall_preimage_eq_of_finite_group (solution)
