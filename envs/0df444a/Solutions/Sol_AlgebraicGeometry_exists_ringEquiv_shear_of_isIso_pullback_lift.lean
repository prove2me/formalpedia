-- Prove2me | solution 1 for AlgebraicGeometry.exists_ringEquiv_shear_of_isIso_pullback_lift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/06913c56-48bc-50c9-90f6-a4343ef52e6c

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

namespace P2MW.S_AlgebraicGeometry_exists_ringEquiv_shear_of_isIso_pullback_lift

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct

namespace ShearBody

theorem appLE_congr_hom {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst h; rfl

theorem isIso_appLE_of_isIso {X Y : Scheme.{u}} (φ : X ⟶ Y) [IsIso φ] (U : Y.Opens) (V : X.Opens)
    (hV : V = φ ⁻¹ᵁ U) : IsIso (φ.appLE U V hV.le) := by
  subst hV
  rw [Scheme.Hom.appLE_eq_app]
  infer_instance

end ShearBody

open ShearBody in
theorem solution
    (K : Type u) [CommRing K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (H : Type u) [CommRing H] [Algebra K H]
    (N : A ⟶ A) (hN : N ≫ f = f)
    (act : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⟶ A) (hact : act ≫ f = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f)
    (hsh : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ N = act ≫ N)
    (hiso : IsIso (pullback.lift (f := N) (g := N) (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh)) :
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
    (hle : ∀ U : A.affineOpens, (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ act ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)))
    (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
    (hρ : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
      ρ U s = ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U) ((act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s))
    (U : A.affineOpens)
    (τ : letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := ((N).app (U : A.Opens)).hom.toAlgebra
      Γ(pullback N N, (pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) ≃+*
        Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, N ⁻¹ᵁ (U : A.Opens)))
    (hle₂ : (pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) ≤ (pullback.snd N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)))
    (hτ₁ : letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := ((N).app (U : A.Opens)).hom.toAlgebra
      ∀ s, τ (((pullback.fst N N).app (N ⁻¹ᵁ (U : A.Opens))).hom s) = s ⊗ₜ 1)
    (hτ₂ : letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := ((N).app (U : A.Opens)).hom.toAlgebra
      ∀ s, τ (((pullback.snd N N).appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hle₂).hom s) = 1 ⊗ₜ s),
    letI : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := (N.app (U : A.Opens)).hom.toAlgebra
    ∃ σ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, N ⁻¹ᵁ (U : A.Opens)) →+* Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H,
      Function.Bijective σ ∧ (∀ s, σ (s ⊗ₜ 1) = s ⊗ₜ[K] (1 : H)) ∧ (∀ s, σ (1 ⊗ₜ s) = ρ U s)  := by
  intro hNaff ε hε_fst hε_res hle ρ hρ U τ hle₂ hτ₁ hτ₂
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
  letI instKP : ∀ W : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).Opens, Algebra K Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), W) := fun W =>
    Scheme.TwoAffineOpenCover.algebraOfHom ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ≫ f) W
  letI iRS : Algebra Γ(A, (U : A.Opens)) Γ(A, N ⁻¹ᵁ (U : A.Opens)) := (N.app (U : A.Opens)).hom.toAlgebra
  haveI := hiso

  set Φ := pullback.lift (f := N) (g := N) (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) act hsh with hΦ
  have hΦfst : Φ ≫ pullback.fst N N = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) := pullback.lift_fst _ _ _
  have hΦsnd : Φ ≫ pullback.snd N N = act := pullback.lift_snd _ _ _
  have hWP : (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens)) = Φ ⁻¹ᵁ ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) := by
    rw [← hΦfst, Scheme.Hom.comp_preimage]
  haveI hI : IsIso (Φ.appLE ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hWP.le) :=
    isIso_appLE_of_isIso Φ _ _ hWP
  let β : Γ(pullback N N, (pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) →+* Γ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap K H)))), (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) :=
    (Φ.appLE ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hWP.le).hom
  have hβ : Function.Bijective β := ConcreteCategory.bijective_of_isIso
    (Φ.appLE ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hWP.le)
  let σ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[Γ(A, (U : A.Opens))] Γ(A, N ⁻¹ᵁ (U : A.Opens)) →+* Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H :=
    (ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U)).toRingEquiv.toRingHom.comp (β.comp τ.symm.toRingHom)
  refine ⟨σ, ?_, ?_, ?_⟩
  · exact (ε (N ⁻¹ᵁ (U : A.Opens)) (hNaff U)).bijective.comp (hβ.comp τ.symm.bijective)
  · intro s
    have h1 : τ.symm.toRingHom (s ⊗ₜ 1) = ((pullback.fst N N).app (N ⁻¹ᵁ (U : A.Opens))).hom s := by
      change τ.symm (s ⊗ₜ 1) = _
      rw [RingEquiv.symm_apply_eq]; exact (hτ₁ s).symm
    have h2 : β (((pullback.fst N N).app (N ⁻¹ᵁ (U : A.Opens))).hom s) = ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))).app (N ⁻¹ᵁ (U : A.Opens))).hom s := by
      change ((pullback.fst N N).app (N ⁻¹ᵁ (U : A.Opens)) ≫ Φ.appLE _ _ hWP.le).hom s = _
      rw [Scheme.Hom.app_eq_appLE (pullback.fst N N), Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hΦfst _ _ _ le_rfl,
        ← Scheme.Hom.app_eq_appLE]
    simp only [σ, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2]
    exact hε_fst _ _ s
  · intro s
    have h1 : τ.symm.toRingHom (1 ⊗ₜ s) = ((pullback.snd N N).appLE (N ⁻¹ᵁ (U : A.Opens))
        ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hle₂).hom s := by
      change τ.symm (1 ⊗ₜ s) = _
      rw [RingEquiv.symm_apply_eq]; exact (hτ₂ s).symm
    have h2 : β (((pullback.snd N N).appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst N N) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) hle₂).hom s) =
        (act.appLE (N ⁻¹ᵁ (U : A.Opens)) ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap K H)))) ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))) (hle U)).hom s := by
      change ((pullback.snd N N).appLE (N ⁻¹ᵁ (U : A.Opens)) _ hle₂ ≫ Φ.appLE _ _ hWP.le).hom s = _
      rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hΦsnd _ _ _ (hle U)]
    simp only [σ, RingHom.coe_comp, Function.comp_apply]
    rw [h1, h2]
    exact (hρ U s).symm

end S_AlgebraicGeometry_exists_ringEquiv_shear_of_isIso_pullback_lift
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ringEquiv_shear_of_isIso_pullback_lift (solution)
