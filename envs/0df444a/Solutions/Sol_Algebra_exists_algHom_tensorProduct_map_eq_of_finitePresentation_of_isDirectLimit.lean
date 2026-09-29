-- Prove2me | solution 1 for Algebra.exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/816f8636-9d95-551b-b213-6041b99efd1e

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct

universe u₀ u v w w₁ w₂

namespace AlgHomSpreadDirected

open TensorProduct

variable {R₀ : Type u₀} [CommRing R₀]
  {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι] [DecidableEq ι]
  {G : ι → Type v} [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
  (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
  {R : Type w} [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
  (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))

abbrev F (i j : ι) (h : i ≤ j) : G i →ₗ[R₀] G j := (f i j h).toLinearMap

scoped instance directedSystem_F : DirectedSystem G fun i j h => ⇑(F f i j h) := by
  change DirectedSystem G fun i j h => ⇑(f i j h)
  infer_instance

abbrev toR (i : ι) : G i →ₐ[R₀] R := IsScalarTower.toAlgHom R₀ (G i) R

theorem toR_apply (i : ι) (x : G i) : toR (R₀ := R₀) (R := R) i x = algebraMap (G i) R x := rfl

include hR in
theorem toR_f {i j : ι} (hij : i ≤ j) (x : G i) :
    toR (R₀ := R₀) (R := R) j (f i j hij x) = toR (R₀ := R₀) (R := R) i x :=
  hR.compatibility i j hij x

noncomputable def limToR : Module.DirectLimit G (F f) →ₗ[R₀] R :=
  Module.DirectLimit.lift R₀ ι G (F f) (fun i => (toR i).toLinearMap) (fun i j hij x => hR.compatibility i j hij x)

theorem limToR_of (i : ι) (x : G i) :
    limToR f hR (Module.DirectLimit.of R₀ ι G (F f) i x) = algebraMap (G i) R x :=
  Module.DirectLimit.lift_of _ _ x

theorem limToR_bijective : Function.Bijective (limToR f hR) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    induction z using Module.DirectLimit.induction_on with
    | ih i x =>
      rw [limToR_of] at hz
      have h0 : algebraMap (G i) R x = algebraMap (G i) R 0 := by rw [hz, map_zero]
      obtain ⟨k, hik, hik', hk⟩ := hR.inj i i x 0 h0
      have hk' : f i k hik x = 0 := by
        have : f i k hik' (0 : G i) = 0 := map_zero _
        rw [← this]; exact hk
      rw [← Module.DirectLimit.of_f (f := F f) (hij := hik)]
      change Module.DirectLimit.of R₀ ι G (F f) k (f i k hik x) = 0
      rw [hk', map_zero]
  · intro r
    obtain ⟨i, x, hx⟩ := hR.surj r
    exact ⟨Module.DirectLimit.of R₀ ι G (F f) i x, by rw [limToR_of]; exact hx⟩

noncomputable def limEquiv : Module.DirectLimit G (F f) ≃ₗ[R₀] R :=
  LinearEquiv.ofBijective (limToR f hR) (limToR_bijective f hR)

theorem limEquiv_symm_algebraMap (i : ι) (x : G i) :
    (limEquiv f hR).symm (algebraMap (G i) R x) = Module.DirectLimit.of R₀ ι G (F f) i x := by
  rw [LinearEquiv.symm_apply_eq]
  exact (limToR_of f hR i x).symm

section Tensor

variable (B : Type w₂) [CommRing B] [Algebra R₀ B]

abbrev mapT (i : ι) : G i ⊗[R₀] B →ₐ[R₀] R ⊗[R₀] B :=
  Algebra.TensorProduct.map (toR i) (AlgHom.id R₀ B)

abbrev stepT {i j : ι} (hij : i ≤ j) : G i ⊗[R₀] B →ₐ[R₀] G j ⊗[R₀] B :=
  Algebra.TensorProduct.map (f i j hij) (AlgHom.id R₀ B)

theorem mapT_eq_rTensor (i : ι) (x : G i ⊗[R₀] B) :
    mapT (R := R) B i x = (toR (R₀ := R₀) (R := R) i).toLinearMap.rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem stepT_eq_rTensor {i j : ι} (hij : i ≤ j) (x : G i ⊗[R₀] B) :
    stepT f B hij x = (F f i j hij).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

include hR in
theorem mapT_stepT {i j : ι} (hij : i ≤ j) (x : G i ⊗[R₀] B) :
    mapT (R := R) B j (stepT f B hij x) = mapT B i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, toR_f f hR]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem stepT_stepT {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G i ⊗[R₀] B) :
    stepT f B hjk (stepT f B hij x) = stepT f B (hij.trans hjk) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
    congr 1
    exact DirectedSystem.map_map (f := fun i j h => ⇑(f i j h)) hij hjk g
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

noncomputable def Φ :
    R ⊗[R₀] B ≃ₗ[R₀] Module.DirectLimit (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) :=
  (limEquiv f hR).symm.rTensor B ≪≫ₗ TensorProduct.directLimitLeft (F f) B

theorem Φ_mapT (i : ι) (x : G i ⊗[R₀] B) :
    Φ f hR B (mapT B i x) =
      Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul g b =>
    rw [Algebra.TensorProduct.map_tmul]
    change TensorProduct.directLimitLeft (F f) B (((limEquiv f hR).symm.rTensor B) (toR i g ⊗ₜ[R₀] b)) = _
    rw [LinearEquiv.rTensor_tmul, toR_apply, limEquiv_symm_algebraMap, TensorProduct.directLimitLeft_tmul_of]
  | add x y hx hy => simp only [map_add, hx, hy]

include hR in

theorem exists_mapT_eq (z : R ⊗[R₀] B) : ∃ (i : ι) (x : G i ⊗[R₀] B), mapT B i x = z := by
  obtain ⟨i, y, hy⟩ := Module.DirectLimit.exists_of (Φ f hR B z)
  refine ⟨i, y, (Φ f hR B).injective ?_⟩
  rw [Φ_mapT, hy]

include hR in

theorem exists_stepT_eq_zero {i : ι} (x : G i ⊗[R₀] B) (hx : mapT (R := R) B i x = 0) :
    ∃ (j : ι) (hij : i ≤ j), stepT f B hij x = 0 := by
  have h0 : Module.DirectLimit.of R₀ ι (fun i => G i ⊗[R₀] B) (fun i j h => (F f i j h).rTensor B) i x = 0 := by
    rw [← Φ_mapT f hR, hx, map_zero]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact h0
  exact ⟨j, hij, by rw [stepT_eq_rTensor]; exact hj⟩

include hR in

theorem exists_common_lift {n : ℕ} (b : Fin n → R ⊗[R₀] B) :
    ∃ (i : ι) (y : Fin n → G i ⊗[R₀] B), ∀ k, mapT B i (y k) = b k := by
  choose idx x hx using fun k => exists_mapT_eq f hR B (b k)
  obtain ⟨M, hM⟩ := Finset.exists_le (Finset.univ.image idx)
  have hle : ∀ k, idx k ≤ M := fun k => hM _ (Finset.mem_image_of_mem idx (Finset.mem_univ k))
  refine ⟨M, fun k => stepT f B (hle k) (x k), fun k => ?_⟩
  rw [mapT_stepT f hR, hx]

include hR in

theorem exists_common_kill {i : ι} {m : ℕ} (x : Fin m → G i ⊗[R₀] B) (hx : ∀ l, mapT (R := R) B i (x l) = 0) :
    ∃ (j : ι) (hij : i ≤ j), ∀ l, stepT f B hij (x l) = 0 := by
  choose idx hidx hzero using fun l => exists_stepT_eq_zero f hR B (x l) (hx l)
  obtain ⟨M, hM⟩ := Finset.exists_le (insert i (Finset.univ.image idx))
  have hiM : i ≤ M := hM _ (Finset.mem_insert_self _ _)
  have hle : ∀ l, idx l ≤ M := fun l =>
    hM _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem idx (Finset.mem_univ l)))
  refine ⟨M, hiM, fun l => ?_⟩
  have : stepT f B hiM (x l) = stepT f B (hle l) (stepT f B (hidx l) (x l)) := by
    rw [stepT_stepT]
  rw [this, hzero, map_zero]

end Tensor

open MvPolynomial in
include hR in
theorem exists_algHom
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    (φ : R ⊗[R₀] A →ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (φ₀ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A,
        φ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ A) x) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₀ x) := by
  classical

  let P := Algebra.Presentation.ofFinitePresentation R₀ A
  set n := Algebra.Presentation.ofFinitePresentationVars R₀ A
  set m := Algebra.Presentation.ofFinitePresentationRels R₀ A

  let θ : MvPolynomial (Fin n) R₀ →ₐ[R₀] R ⊗[R₀] B :=
    (φ.restrictScalars R₀).comp
      ((Algebra.TensorProduct.includeRight (R := R₀) (A := R) (B := A)).comp (MvPolynomial.aeval P.val))
  have hθ : ∀ p, θ p = φ ((1 : R) ⊗ₜ[R₀] MvPolynomial.aeval P.val p) := fun p => rfl

  obtain ⟨i₁, y, hy⟩ := exists_common_lift f hR B fun k : Fin n => φ ((1 : R) ⊗ₜ[R₀] P.val k)
  let ψ₁ : MvPolynomial (Fin n) R₀ →ₐ[R₀] G i₁ ⊗[R₀] B := MvPolynomial.aeval y
  have hψ₁ : (mapT B i₁).comp ψ₁ = θ := by
    refine MvPolynomial.algHom_ext fun k => ?_
    rw [AlgHom.comp_apply, hθ]
    change mapT B i₁ (MvPolynomial.aeval y (X k)) = _
    rw [MvPolynomial.aeval_X, hy, MvPolynomial.aeval_X]

  have hrel : ∀ l : Fin m, mapT (R := R) B i₁ (ψ₁ (P.relation l)) = 0 := by
    intro l
    have := AlgHom.congr_fun hψ₁ (P.relation l)
    rw [AlgHom.comp_apply] at this
    rw [this, hθ, P.aeval_val_relation l, TensorProduct.tmul_zero, map_zero]
  obtain ⟨j, hij, hkill⟩ := exists_common_kill f hR B (fun l => ψ₁ (P.relation l)) hrel

  let ψ : MvPolynomial (Fin n) R₀ →ₐ[R₀] G j ⊗[R₀] B := (stepT f B hij).comp ψ₁
  have hψker : ∀ a ∈ RingHom.ker (MvPolynomial.aeval (R := R₀) P.val), ψ a = 0 := by
    have hle : RingHom.ker (MvPolynomial.aeval (R := R₀) P.val) ≤ RingHom.ker ψ.toRingHom := by
      rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨l, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact hkill l
    intro a ha
    exact hle ha
  have hsurj : Function.Surjective (MvPolynomial.aeval (R := R₀) P.val) := P.aeval_val_surjective
  let e : (MvPolynomial (Fin n) R₀ ⧸ RingHom.ker (MvPolynomial.aeval (R := R₀) P.val)) ≃ₐ[R₀] A :=
    Ideal.quotientKerAlgEquivOfSurjective hsurj
  let ψA : A →ₐ[R₀] G j ⊗[R₀] B :=
    (Ideal.Quotient.liftₐ (RingHom.ker (MvPolynomial.aeval (R := R₀) P.val)) ψ hψker).comp (e.symm : A →ₐ[R₀] _)
  have hψA : ∀ p : MvPolynomial (Fin n) R₀, ψA (MvPolynomial.aeval P.val p) = ψ p := by
    intro p
    change Ideal.Quotient.liftₐ _ ψ hψker (e.symm (MvPolynomial.aeval P.val p)) = ψ p
    rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply hsurj p, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl

  let φ₀ : G j ⊗[R₀] A →ₐ[G j] G j ⊗[R₀] B :=
    Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := G j) (R := R₀) (A := G j) (B := B)) ψA
      (fun _ _ => Commute.all _ _)
  have hφ₀ : ∀ (g : G j) (a : A), φ₀ (g ⊗ₜ[R₀] a) = (g ⊗ₜ[R₀] (1 : B)) * ψA a := fun g a =>
    Algebra.TensorProduct.lift_tmul _ _ _ g a
  refine ⟨j, φ₀, ?_⟩

  let H₁ : G j ⊗[R₀] A →ₐ[R₀] R ⊗[R₀] B := (φ.restrictScalars R₀).comp (mapT A j)
  let H₂ : G j ⊗[R₀] A →ₐ[R₀] R ⊗[R₀] B := (mapT B j).comp (φ₀.restrictScalars R₀)
  suffices hH : H₁ = H₂ by
    intro x
    exact AlgHom.congr_fun hH x
  apply Algebra.TensorProduct.ext
  ·
    ext g
    change φ (mapT A j (g ⊗ₜ[R₀] (1 : A))) = mapT B j (φ₀ (g ⊗ₜ[R₀] (1 : A)))
    rw [hφ₀, map_one, mul_one, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one,
      AlgHom.id_apply]
    have h1 : (toR (R₀ := R₀) (R := R) j g) ⊗ₜ[R₀] (1 : A) = algebraMap R (R ⊗[R₀] A) (toR (R₀ := R₀) (R := R) j g) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    have h2 : (toR (R₀ := R₀) (R := R) j g) ⊗ₜ[R₀] (1 : B) = algebraMap R (R ⊗[R₀] B) (toR (R₀ := R₀) (R := R) j g) := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h1, AlgHom.commutes, ← h2]
  ·
    have key : ((H₁.restrictScalars R₀).comp Algebra.TensorProduct.includeRight).comp (MvPolynomial.aeval P.val) =
        ((H₂.restrictScalars R₀).comp Algebra.TensorProduct.includeRight).comp (MvPolynomial.aeval P.val) := by
      refine MvPolynomial.algHom_ext fun k => ?_
      change φ (mapT A j ((1 : G j) ⊗ₜ[R₀] MvPolynomial.aeval P.val (X k))) =
        mapT B j (φ₀ ((1 : G j) ⊗ₜ[R₀] MvPolynomial.aeval P.val (X k)))
      rw [hφ₀, hψA, Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, MvPolynomial.aeval_X]
      change φ ((1 : R) ⊗ₜ[R₀] P.val k) = mapT B j (((1 : G j) ⊗ₜ[R₀] (1 : B)) * ψ (X k))
      rw [show ((1 : G j) ⊗ₜ[R₀] (1 : B)) = 1 from rfl, one_mul]
      change _ = mapT B j (stepT f B hij (MvPolynomial.aeval y (X k)))
      rw [MvPolynomial.aeval_X, mapT_stepT f hR, hy]
    apply AlgHom.ext
    intro a
    obtain ⟨p, rfl⟩ := hsurj a
    exact AlgHom.congr_fun key p

end AlgHomSpreadDirected
p2m_reactivate "P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit.AlgHomSpreadDirected"

theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (R₀ : Type u₀) [CommRing R₀]
    (G : ι → Type v) [∀ i, CommRing (G i)] [∀ i, Algebra R₀ (G i)]
    (f : ∀ i j : ι, i ≤ j → G i →ₐ[R₀] G j) [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [Algebra R₀ R] [∀ i, Algebra (G i) R] [∀ i, IsScalarTower R₀ (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w₁) [CommRing A] [Algebra R₀ A] [Algebra.FinitePresentation R₀ A]
    (B : Type w₂) [CommRing B] [Algebra R₀ B]
    (φ : R ⊗[R₀] A →ₐ[R] R ⊗[R₀] B) :
    ∃ (i : ι) (φ₀ : G i ⊗[R₀] A →ₐ[G i] G i ⊗[R₀] B),
      ∀ x : G i ⊗[R₀] A,
        φ (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ A) x) =
          Algebra.TensorProduct.map (IsScalarTower.toAlgHom R₀ (G i) R) (AlgHom.id R₀ B) (φ₀ x) := by
  classical
  exact AlgHomSpreadDirected.exists_algHom f hR A B φ

end S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit
end P2MW
export P2MW.S_Algebra_exists_algHom_tensorProduct_map_eq_of_finitePresentation_of_isDirectLimit (solution)
