-- Prove2me | solution 1 for Algebra.H1Cotangent.liftBaseChange_map_injective_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/79a5d51a-481f-5d53-91d4-5ca5e6164d03

import Mathlib
import Theorems.Thm_Algebra_H1Cotangent_liftBaseChange_map_injective_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

universe u

open TensorProduct

namespace JZInj

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)

noncomputable def algPoly : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
  (MvPolynomial.map (σ := Fin n) (algebraMap R S)).toAlgebra

attribute [local instance] algPoly

scoped instance isScalarTower_poly : IsScalarTower R (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) S) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R (MvPolynomial (Fin n) S) r = MvPolynomial.map (algebraMap R S) (algebraMap R _ r)
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
    rfl

noncomputable def polyEquiv :
    MvPolynomial (Fin n) R ⊗[R] S ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) S :=
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) S).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) R S).toRingEquiv) (by
    intro p
    simp only [RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    rfl)

theorem polyEquiv_tmul (p : MvPolynomial (Fin n) R) (s : S) :
    polyEquiv R S n (p ⊗ₜ s) = s • MvPolynomial.map (algebraMap R S) p := by
  simp only [polyEquiv, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply, AlgEquiv.toRingEquiv_eq_coe,
    AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul, MvPolynomial.algebraTensorAlgEquiv_tmul]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option maxHeartbeats 1600000 in

theorem poly_step :
    Function.Injective ((Algebra.H1Cotangent.map R R S (MvPolynomial (Fin n) S)).liftBaseChange
      (MvPolynomial (Fin n) S)) := by

  let R' := MvPolynomial (Fin n) R
  let D := MvPolynomial (Fin n) S
  let H := Algebra.H1Cotangent R S
  let e₀ : R' ⊗[R] S ≃ₐ[R'] D := polyEquiv R S n
  letI algD : Algebra (R' ⊗[R] S) D := e₀.toRingHom.toAlgebra
  have he₀ : ∀ y : R' ⊗[R] S, algebraMap (R' ⊗[R] S) D y = e₀ y := fun _ => rfl
  have he₁ : ∀ s : S, e₀ (algebraMap S (R' ⊗[R] S) s) = algebraMap S D s := by
    intro s
    change e₀ ((1 : R') ⊗ₜ[R] s) = algebraMap S D s
    rw [polyEquiv_tmul, map_one, Algebra.smul_def, mul_one]
  haveI : IsScalarTower R' (R' ⊗[R] S) D := ⟨fun p y d => by
    change e₀ (p • y) * d = p • (e₀ y * d)
    rw [map_smul, Algebra.smul_def, Algebra.smul_def, mul_assoc]⟩
  haveI : IsScalarTower S (R' ⊗[R] S) D := ⟨fun s y d => by
    change e₀ (s • y) * d = s • (e₀ y * d)
    rw [Algebra.smul_def, map_mul, he₁, Algebra.smul_def, mul_assoc]⟩
  haveI : IsScalarTower R (R' ⊗[R] S) D := ⟨fun r y d => by
    rw [← algebraMap_smul S r y, ← algebraMap_smul S r, smul_assoc]⟩

  let c₀ : D ⊗[S] H →ₗ[D] Algebra.H1Cotangent R D := (Algebra.H1Cotangent.map R R S D).liftBaseChange D
  let g : Algebra.H1Cotangent R D →ₗ[D] Algebra.H1Cotangent R' D := Algebra.H1Cotangent.map R R' D D
  let Φ : R' ⊗[R] H ≃ₗ[R'] Algebra.H1Cotangent R' (R' ⊗[R] S) := Algebra.tensorH1CotangentOfFlat R S R'
  let ψ : Algebra.H1Cotangent R' (R' ⊗[R] S) →ₗ[R' ⊗[R] S] Algebra.H1Cotangent R' D :=
    Algebra.H1Cotangent.map R' R' (R' ⊗[R] S) D
  have hψ : Function.Injective ψ := (Algebra.H1Cotangent.mapEquiv R' (R' ⊗[R] S) D e₀).injective

  have key₁ : ∀ x : H, g (Algebra.H1Cotangent.map R R S D x) = Algebra.H1Cotangent.map R R' S D x := by
    intro x
    simp only [g]
    rw [Algebra.H1Cotangent.map, Algebra.H1Cotangent.map, Algebra.H1Cotangent.map,
      ← Algebra.Extension.H1Cotangent.map_comp_apply, Algebra.Extension.H1Cotangent.map_eq]
  have key₂ : ∀ x : H, ψ (Algebra.H1Cotangent.map R R' S (R' ⊗[R] S) x) = Algebra.H1Cotangent.map R R' S D x := by
    intro x
    simp only [ψ]
    rw [Algebra.H1Cotangent.map, Algebra.H1Cotangent.map, Algebra.H1Cotangent.map,
      ← Algebra.Extension.H1Cotangent.map_comp_apply, Algebra.Extension.H1Cotangent.map_eq]

  let θ' : R' ⊗[R] H →ₗ[R] D ⊗[S] H :=
    TensorProduct.lift (LinearMap.mk₂ R (fun (p : R') (x : H) => algebraMap R' D p ⊗ₜ[S] x)
      (fun p q x => by simp only [map_add, TensorProduct.add_tmul])
      (fun r p x => by
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def,
          TensorProduct.smul_tmul'])
      (fun p x y => by simp only [TensorProduct.tmul_add])
      (fun r p x => by simp only [TensorProduct.tmul_smul]))
  have hθ' : ∀ (p : R') (x : H), θ' (p ⊗ₜ x) = algebraMap R' D p ⊗ₜ[S] x := fun p x => rfl

  have hsq : ∀ y : R' ⊗[R] H, g (c₀ (θ' y)) = ψ (Φ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul p x =>
      rw [hθ']
      simp only [c₀, Φ, LinearMap.liftBaseChange_tmul, map_smul, key₁]
      have htm := Algebra.tensorH1CotangentOfFlat_tmul R S R' p x
      have i1 : IsScalarTower (R' ⊗[R] S) D (Algebra.H1Cotangent R' D) := inferInstance
      have i2 : IsScalarTower R' D (Algebra.H1Cotangent R' D) := inferInstance
      rw [htm, ← algebraMap_smul (R' ⊗[R] S) p, map_smul, key₂]
      calc algebraMap R' D p • Algebra.H1Cotangent.map R R' S D x
          = algebraMap (R' ⊗[R] S) D (algebraMap R' (R' ⊗[R] S) p) •
              Algebra.H1Cotangent.map R R' S D x := by
            rw [← IsScalarTower.algebraMap_apply]
        _ = algebraMap R' (R' ⊗[R] S) p • Algebra.H1Cotangent.map R R' S D x :=
            IsScalarTower.algebraMap_smul D _ _

  have hθ's : Function.Surjective θ' := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | add z w hz hw =>
      obtain ⟨y, rfl⟩ := hz; obtain ⟨y', rfl⟩ := hw
      exact ⟨y + y', map_add _ _ _⟩
    | tmul d x =>
      induction d using MvPolynomial.induction_on with
      | C s =>
        refine ⟨1 ⊗ₜ (s • x), ?_⟩
        rw [hθ', map_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
          MvPolynomial.algebraMap_eq]
      | add p q hp hq =>
        obtain ⟨y, hy⟩ := hp; obtain ⟨y', hy'⟩ := hq
        exact ⟨y + y', by rw [map_add, hy, hy', TensorProduct.add_tmul]⟩
      | mul_X p i hp =>
        obtain ⟨y, hy⟩ := hp
        refine ⟨(MvPolynomial.X i : R') • y, ?_⟩
        have hsm : ∀ y : R' ⊗[R] H, θ' ((MvPolynomial.X i : R') • y) = algebraMap R' D (MvPolynomial.X i) • θ' y := by
          intro y
          induction y using TensorProduct.induction_on with
          | zero => simp
          | add y z hy hz => simp only [smul_add, map_add, hy, hz]
          | tmul q x' =>
            rw [TensorProduct.smul_tmul', hθ', hθ', smul_eq_mul, map_mul, TensorProduct.smul_tmul',
              smul_eq_mul]
        rw [hsm, hy, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
        simp only [Algebra.algebraMap_self, RingHom.id_apply]
        congr 1
        change p * MvPolynomial.map (algebraMap R S) (MvPolynomial.X i) = _
        rw [MvPolynomial.map_X]

  intro z₁ z₂ hz
  obtain ⟨y₁, rfl⟩ := hθ's z₁
  obtain ⟨y₂, rfl⟩ := hθ's z₂
  have : ψ (Φ y₁) = ψ (Φ y₂) := by rw [← hsq, ← hsq]; exact congrArg g hz
  rw [Φ.injective (hψ this)]

set_option maxHeartbeats 1600000 in

theorem chart_step (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] (m : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension m S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial m S T
  let D := MvPolynomial (Fin m) S
  letI algDT : Algebra D T := g.toRingHom.toAlgebra
  haveI : IsScalarTower S D T := IsScalarTower.of_algebraMap_eq fun s => (g.commutes s).symm
  haveI : IsScalarTower R D T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S D, IsScalarTower.algebraMap_apply R S T,
      IsScalarTower.algebraMap_apply S D T]
  haveI : Algebra.Etale D T := by
    have : (algebraMap D T).Etale := hg
    exact RingHom.etale_algebraMap.mp this
  haveI : Module.Flat D T := inferInstance
  let H := Algebra.H1Cotangent R S
  let cD : D ⊗[S] H →ₗ[D] Algebra.H1Cotangent R D := (Algebra.H1Cotangent.map R R S D).liftBaseChange D
  let E : T ⊗[D] Algebra.H1Cotangent R D →ₗ[T] Algebra.H1Cotangent R T :=
    (Algebra.H1Cotangent.map R R D T).liftBaseChange T
  let PB : T ⊗[S] H →ₗ[T] T ⊗[D] Algebra.H1Cotangent R D :=
    (cD.baseChange T) ∘ₗ (TensorProduct.AlgebraTensorModule.cancelBaseChange S D T T H).symm.toLinearMap
  have hfun : ∀ x : H, Algebra.H1Cotangent.map R R D T (Algebra.H1Cotangent.map R R S D x) =
      Algebra.H1Cotangent.map R R S T x := by
    intro x
    rw [Algebra.H1Cotangent.map, Algebra.H1Cotangent.map, Algebra.H1Cotangent.map,
      ← Algebra.Extension.H1Cotangent.map_comp_apply, Algebra.Extension.H1Cotangent.map_eq]
  have hfac : ∀ y : T ⊗[S] H, (Algebra.H1Cotangent.map R R S T).liftBaseChange T y = E (PB y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul t x =>
      simp only [E, PB, cD, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      rw [show (TensorProduct.AlgebraTensorModule.cancelBaseChange S D T T H).symm (t ⊗ₜ x) = t ⊗ₜ ((1 : D) ⊗ₜ x)
        from by rw [LinearEquiv.symm_apply_eq, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]]
      rw [LinearMap.baseChange_tmul]
      simp only [LinearMap.liftBaseChange_tmul, one_smul, hfun]
  intro y₁ y₂ h
  rw [hfac, hfac] at h
  have hPB : Function.Injective PB :=
    (Module.Flat.lTensor_preserves_injective_linearMap _ (poly_step R S m)).comp
      (TensorProduct.AlgebraTensorModule.cancelBaseChange S D T T H).symm.injective
  exact hPB (Algebra.H1Cotangent.liftBaseChange_map_injective_of_etale R D T h)

set_option maxHeartbeats 3200000 in

theorem main (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] [Algebra.Smooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) := by
  classical
  let H := Algebra.H1Cotangent R S
  let c : T ⊗[S] H →ₗ[T] Algebra.H1Cotangent R T := (Algebra.H1Cotangent.map R R S T).liftBaseChange T

  have hloc : RingHom.Locally RingHom.IsStandardSmooth (algebraMap S T) := by
    rw [← RingHom.smooth_iff_locally_isStandardSmooth, RingHom.smooth_algebraMap]; infer_instance
  obtain ⟨s, hs, hstd⟩ := hloc

  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  refine Module.eq_zero_of_isLocalized_span s hs (fun r => Localization.Away r.1 ⊗[T] (T ⊗[S] H))
    (fun r => TensorProduct.mk T (Localization.Away r.1) (T ⊗[S] H) 1) x fun r => ?_

  let Tr := Localization.Away r.1
  haveI : Algebra.IsStandardSmooth S Tr := by
    have := hstd r.1 r.2
    rwa [← IsScalarTower.algebraMap_eq (R := S) (S := T) (A := Tr), RingHom.isStandardSmooth_algebraMap] at this
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth S Tr)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension P.dimension S Tr := P.isStandardSmoothOfRelativeDimension rfl
  have hchart := chart_step R S Tr P.dimension

  let e : Tr ⊗[T] (T ⊗[S] H) ≃ₗ[Tr] Tr ⊗[S] H := TensorProduct.AlgebraTensorModule.cancelBaseChange S T Tr Tr H
  let cr : Tr ⊗[S] H →ₗ[Tr] Algebra.H1Cotangent R Tr := (Algebra.H1Cotangent.map R R S Tr).liftBaseChange Tr
  let ℓ : Algebra.H1Cotangent R T →ₗ[T] Algebra.H1Cotangent R Tr := Algebra.H1Cotangent.map R R T Tr
  have hfun : ∀ y : H, ℓ (Algebra.H1Cotangent.map R R S T y) = Algebra.H1Cotangent.map R R S Tr y := by
    intro y
    simp only [ℓ]
    rw [Algebra.H1Cotangent.map, Algebra.H1Cotangent.map, Algebra.H1Cotangent.map,
      ← Algebra.Extension.H1Cotangent.map_comp_apply, Algebra.Extension.H1Cotangent.map_eq]
  have hsq : ∀ y : T ⊗[S] H, cr (e ((1 : Tr) ⊗ₜ[T] y)) = ℓ (c y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
    | tmul t y =>
      simp only [e, cr, c, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        LinearMap.map_smul_of_tower, hfun]
      rw [smul_assoc, one_smul]
  have h0 : cr (e ((1 : Tr) ⊗ₜ[T] x)) = 0 := by rw [hsq]; change ℓ (c x) = 0; rw [hx, map_zero]
  have h1 : e ((1 : Tr) ⊗ₜ[T] x) = 0 := hchart (by rw [h0, map_zero])
  simpa using h1

end JZInj
p2m_reactivate "P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth.JZInj"

theorem solution (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Algebra.Smooth S T] :
    Function.Injective ((Algebra.H1Cotangent.map R R S T).liftBaseChange T) :=
  JZInj.main R S T

#print axioms solution

end S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth
end P2MW
export P2MW.S_Algebra_H1Cotangent_liftBaseChange_map_injective_of_smooth (solution)
