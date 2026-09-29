-- Prove2me | solution 1 for AlgebraicGeometry.exists_coaction_affineOpens_eq_comp_appLE_of_preimage_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7b859663-a015-5b26-b188-4e2d3827edd5

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_coaction_affineOpens_eq_comp_appLE_of_preimage_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

namespace CoactionBasicBody

theorem appLE_congr_hom {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst h; rfl

end CoactionBasicBody

open CoactionBasicBody in
theorem solution
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    (N : A ⟶ A) (hN : N ≫ f = f)
    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A) (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (hsh : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ N = act ≫ N) :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
      Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
    ∀ (hNaff : ∀ U : A.affineOpens, IsAffineOpen (N ⁻¹ᵁ (U : A.Opens)))
    (ε : ∀ (V : A.Opens) (_ : IsAffineOpen V), Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V) ≃ₐ[K] Γ(A, V) ⊗[K] H)
    (hε_fst : ∀ (V : A.Opens) (hV : IsAffineOpen V) (a : Γ(A, V)),
      ε V hV (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app V).hom a) = a ⊗ₜ[K] (1 : H))
    (hε_res : ∀ (V V' : A.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (hle : V' ≤ V)
        (s : Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ V)),
      Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ε V hV s) =
        ε V' hV' (((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle)).op).hom s))
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))),
    ∃ ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H,
      (∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
        ρ U s = ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s)) ∧
      (∀ (U U' : A.affineOpens) (hle' : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
            (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
            Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle') (AlgHom.id K H) (ρ U s) =
              ρ U' ((A.presheaf.map (homOfLE hle').op).hom s)) ∧
      (∀ U : A.affineOpens,
        letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := (N.app (U : A.Opens)).hom.toAlgebra
        IsScalarTower K Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens))) ∧
      (∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
        ρ U ((N.app (U : A.Opens)).hom r) = (N.app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H))  := by
  intro hNaff ε hε_fst hε_res hle
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
  letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W

  let r : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →+* Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H := fun U =>
    (ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U)).toRingEquiv.toRingHom.comp
      (act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom

  have hK : ∀ (U : A.affineOpens) (k : K),
      r U (algebraMap K Γ(A, N ⁻¹ᵁ (U : A.Opens)) k) = algebraMap K (Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H) k := by
    intro U k
    have h1 : (act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom
        (algebraMap K Γ(A, N ⁻¹ᵁ (U : A.Opens)) k) =
        algebraMap K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) k := by
      change (f.appLE ⊤ (N ⁻¹ᵁ (U : A.Opens)) le_top ≫
          act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) =
        (((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f).appLE ⊤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) le_top).hom
          ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)
      rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hact]
    change (ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U)) ((act.appLE (N ⁻¹ᵁ (U : A.Opens))
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom (algebraMap K Γ(A, N ⁻¹ᵁ (U : A.Opens)) k)) = _
    rw [h1, AlgEquiv.commutes]
  let ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H :=
    fun U => AlgHom.mk (r U) (hK U)
  refine ⟨ρ, fun U s => rfl, ?_, ?_, ?_⟩
  ·
    intro U U' hle' s
    change Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle') (AlgHom.id K H)
        (ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE (N ⁻¹ᵁ (U : A.Opens))
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s)) =
      ε (N ⁻¹ᵁ (U' : A.Opens)) (hNaff U') ((act.appLE (N ⁻¹ᵁ (U' : A.Opens))
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U' : A.Opens))) (hle U')).hom ((A.presheaf.map (homOfLE hle').op).hom s))
    rw [hε_res _ _ (hNaff U) (hNaff U') hle']
    congr 1
    change (act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U) ≫
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).presheaf.map (homOfLE ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).preimage_mono hle')).op).hom s =
      (A.presheaf.map (homOfLE hle').op ≫
        act.appLE (N ⁻¹ᵁ (U' : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U' : A.Opens))) (hle U')).hom s
    rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  ·
    intro U
    letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := (N.app (U : A.Opens)).hom.toAlgebra
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine RingHom.ext fun k => ?_
    change (f.appLE ⊤ (N ⁻¹ᵁ (U : A.Opens)) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k) =
      (f.appLE ⊤ (U : A.Opens) le_top ≫ N.app (U : A.Opens)).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom k)
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hN]
  ·
    intro U r'
    change (ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U)) ((N.app (U : A.Opens) ≫ act.appLE (N ⁻¹ᵁ (U : A.Opens))
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom r') = _
    have h2 : N.app (U : A.Opens) ≫ act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U) =
        N.app (U : A.Opens) ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app (N ⁻¹ᵁ (U : A.Opens)) := by
      rw [Scheme.Hom.app_eq_appLE N, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hsh.symm (U : A.Opens) _ _
        (show (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ N) ⁻¹ᵁ (U : A.Opens) by
          rw [Scheme.Hom.comp_preimage]),
        ← Scheme.Hom.appLE_comp_appLE _ _ _ (N ⁻¹ᵁ (U : A.Opens)) _ le_rfl le_rfl, ← Scheme.Hom.app_eq_appLE,
        ← Scheme.Hom.app_eq_appLE]
    rw [h2, CommRingCat.comp_apply, hε_fst]

end S_AlgebraicGeometry_exists_coaction_affineOpens_eq_comp_appLE_of_preimage_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_exists_coaction_affineOpens_eq_comp_appLE_of_preimage_comp_eq (solution)
