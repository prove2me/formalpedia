-- Prove2me | solution 1 for AutomorphicForm.exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3beac789-21f8-54e4-9d15-b0b2b1683a2b

import Definitions.Def_AutomorphicForm_TwistedCommutant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent

set_option autoImplicit false

open TensorProduct
open scoped TensorProduct.RightActions

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "twistedCommutant mem_twistedCommutant_iff isTopologicalRing_tensor sigmaTensor"
p2m_open "AutomorphicForm"
namespace TwistedCommutantBC

section Algebra

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (A : Type) [CommRing A] [Algebra K A]

local notation "V" => Matrix (Fin 2) (Fin 2) L
local notation "MA" => Matrix (Fin 2) (Fin 2) (L ⊗[K] A)

def theta : (V) ⊗[K] A →ₗ[K] MA :=
  TensorProduct.lift
    (LinearMap.mk₂ K (fun (x : V) (a : A) => x.map fun l : L => l ⊗ₜ[K] a)
      (by intro x y a; ext j k; simp [TensorProduct.add_tmul])
      (by intro r x a; ext j k; simp [TensorProduct.smul_tmul'])
      (by intro x a a'; ext j k; simp [TensorProduct.tmul_add])
      (by intro r x a; ext j k; simp))

theorem theta_tmul (x : V) (a : A) :
    theta K L A (x ⊗ₜ[K] a) = x.map fun l : L => l ⊗ₜ[K] a := by
  simp [theta]

def thetaInv : (MA) →ₗ[K] (V) ⊗[K] A :=
  ∑ j : Fin 2, ∑ k : Fin 2,
    (TensorProduct.map (Matrix.singleLinearMap K j k) LinearMap.id) ∘ₗ
      (Matrix.entryLinearMap K (L ⊗[K] A) j k)

theorem thetaInv_apply (Y : MA) :
    thetaInv K L A Y = ∑ j : Fin 2, ∑ k : Fin 2,
      TensorProduct.map (Matrix.singleLinearMap K j k) (LinearMap.id : A →ₗ[K] A) (Y j k) := by
  simp [thetaInv]

theorem thetaInv_theta : (thetaInv K L A) ∘ₗ (theta K L A) = LinearMap.id := by
  apply TensorProduct.ext'
  intro x a
  rw [LinearMap.comp_apply, theta_tmul, thetaInv_apply, LinearMap.id_apply]
  have : ∀ j k, TensorProduct.map (Matrix.singleLinearMap K j k) (LinearMap.id : A →ₗ[K] A)
      ((x.map fun l : L => l ⊗ₜ[K] a) j k) = (Matrix.single j k (x j k)) ⊗ₜ[K] a := by
    intro j k
    simp [Matrix.map_apply, TensorProduct.map_tmul]
  simp_rw [this, ← TensorProduct.sum_tmul]
  rw [← Matrix.matrix_eq_sum_single]

theorem theta_thetaInv : (theta K L A) ∘ₗ (thetaInv K L A) = LinearMap.id := by
  apply LinearMap.ext
  intro Y
  rw [LinearMap.comp_apply, thetaInv_apply, map_sum, LinearMap.id_apply]
  conv_rhs => rw [Matrix.matrix_eq_sum_single Y]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_

  have key : (theta K L A) ∘ₗ (TensorProduct.map (Matrix.singleLinearMap K j k)
      (LinearMap.id : A →ₗ[K] A)) =
      (Matrix.singleLinearMap K j k : L ⊗[K] A →ₗ[K] MA) := by
    apply TensorProduct.ext'
    intro l a
    rw [LinearMap.comp_apply, TensorProduct.map_tmul, Matrix.singleLinearMap_apply,
      LinearMap.id_apply, theta_tmul, Matrix.singleLinearMap_apply]
    ext j' k'
    by_cases h : j = j' ∧ k = k'
    · obtain ⟨rfl, rfl⟩ := h
      simp
    · rw [Matrix.map_apply, Matrix.single_apply_of_ne _ _ _ _ _ h, Matrix.single_apply_of_ne _ _ _ _ _ h,
        TensorProduct.zero_tmul]
  have := congrArg (fun φ => φ (Y j k)) key
  simpa using this

theorem theta_thetaInv_apply (Y : MA) : theta K L A (thetaInv K L A Y) = Y := by
  have := congrArg (fun φ => φ Y) (theta_thetaInv K L A)
  simpa using this

theorem thetaInv_theta_apply (z : (V) ⊗[K] A) : thetaInv K L A (theta K L A z) = z := by
  have := congrArg (fun φ => φ z) (thetaInv_theta K L A)
  simpa using this

theorem theta_injective : Function.Injective (theta K L A) :=
  Function.LeftInverse.injective (g := thetaInv K L A) (thetaInv_theta_apply K L A)

theorem theta_tmul_mul_left (x y : V) (a : A) :
    theta K L A ((y * x) ⊗ₜ[K] a) = (y.map fun l : L => l ⊗ₜ[K] (1 : A)) * theta K L A (x ⊗ₜ[K] a) := by
  rw [theta_tmul, theta_tmul]
  ext j k
  simp [Matrix.mul_apply, Matrix.map_apply, TensorProduct.add_tmul, Algebra.TensorProduct.tmul_mul_tmul]

theorem theta_tmul_mul_right (x y : V) (a : A) :
    theta K L A ((x * y) ⊗ₜ[K] a) = theta K L A (x ⊗ₜ[K] a) * (y.map fun l : L => l ⊗ₜ[K] (1 : A)) := by
  rw [theta_tmul, theta_tmul]
  ext j k
  simp [Matrix.mul_apply, Matrix.map_apply, TensorProduct.add_tmul, Algebra.TensorProduct.tmul_mul_tmul]

variable (σ : L ≃ₐ[K] L)

theorem map_sigmaTensor_theta_tmul (x : V) (a : A) :
    (theta K L A (x ⊗ₜ[K] a)).map (sigmaTensor K L A σ) = theta K L A ((x.map σ) ⊗ₜ[K] a) := by
  rw [theta_tmul, theta_tmul]
  ext j k
  simp only [Matrix.map_apply]
  show Algebra.TensorProduct.map σ.toAlgHom (AlgHom.id K A) (x j k ⊗ₜ[K] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

def fMap (δ₀ : V) : (V) →ₗ[K] V where
  toFun x := x * δ₀ - δ₀ * x.map σ
  map_add' x y := by
    have : (x + y).map σ = x.map σ + y.map σ := Matrix.map_add σ (map_add σ) _ _
    rw [this, add_mul, mul_add]; abel
  map_smul' r x := by
    have : (r • x).map σ = r • x.map σ := by
      ext j k; simp [Matrix.map_apply]
    rw [this, Matrix.smul_mul, Matrix.mul_smul, RingHom.id_apply, smul_sub]

theorem fMap_apply (δ₀ x : V) : fMap K L σ δ₀ x = x * δ₀ - δ₀ * x.map σ := rfl

def fMapA (δ₀ : V) (Y : MA) : MA :=
  Y * δ₀.map (fun l : L => l ⊗ₜ[K] (1 : A)) - δ₀.map (fun l : L => l ⊗ₜ[K] (1 : A)) * Y.map (sigmaTensor K L A σ)

theorem theta_rTensor_fMap (δ₀ : V) (z : (V) ⊗[K] A) :
    theta K L A ((fMap K L σ δ₀).rTensor A z) = fMapA K L A σ δ₀ (theta K L A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [fMapA, Matrix.map_zero]
  | tmul x a =>
      rw [LinearMap.rTensor_tmul, fMap_apply, TensorProduct.sub_tmul, map_sub, theta_tmul_mul_right,
        theta_tmul_mul_left, ← map_sigmaTensor_theta_tmul]
      rfl
  | add z w hz hw =>
      rw [map_add, map_add, hz, hw, map_add]
      simp only [fMapA]
      rw [Matrix.map_add _ (map_add _), add_mul, mul_add]
      abel

theorem coe_map_includeLeft (δ₀ : GL (Fin 2) L) :
    ((Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ : GL (Fin 2) (L ⊗[K] A)) :
        MA) = (δ₀ : V).map fun l : L => l ⊗ₜ[K] (1 : A) := by
  ext j k
  rfl

theorem coe_scalar (c : (L ⊗[K] A)ˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (L ⊗[K] A)) : MA) =
      (c : L ⊗[K] A) • (1 : MA) := by
  ext j k
  simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply]

theorem mem_twistedCommutant_map_mul_scalar_iff (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ) (X : MA) :
    X ∈ twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) ↔
      fMapA K L A σ (δ₀ : V) X = 0 := by
  rw [mem_twistedCommutant_iff, Matrix.GeneralLinearGroup.coe_mul, coe_map_includeLeft, coe_scalar,
    fMapA, sub_eq_zero]
  set D : MA := (δ₀ : V).map fun l : L => l ⊗ₜ[K] (1 : A)
  simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

  constructor
  · intro h
    have := congrArg (fun Y : MA => ((c⁻¹ : (L ⊗[K] A)ˣ) : L ⊗[K] A) • Y) h
    simpa only [smul_smul, Units.inv_mul, one_smul] using this
  · intro h
    rw [h]

variable {ι : Type} [Fintype ι]

def E (b : ι → V) (a : ι → A) : MA := ∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i

theorem E_eq_theta (b : ι → V) (a : ι → A) : E K L A b a = theta K L A (∑ i, b i ⊗ₜ[K] a i) := by
  simp [E, map_sum, theta_tmul]

theorem fMapA_E (δ₀ : V) (b : ι → V) (hb : ∀ i, fMap K L σ δ₀ (b i) = 0) (a : ι → A) :
    fMapA K L A σ δ₀ (E K L A b a) = 0 := by
  rw [E_eq_theta, ← theta_rTensor_fMap, map_sum]
  simp [LinearMap.rTensor_tmul, hb]

theorem exists_E_eq_of_fMapA_eq_zero (δ₀ : V) (b : ι → V)
    (hspan : ∀ x : V, fMap K L σ δ₀ x = 0 → x ∈ Submodule.span K (Set.range b))
    (Y : MA) (hY : fMapA K L A σ δ₀ Y = 0) : ∃ a : ι → A, E K L A b a = Y := by
  set z := thetaInv K L A Y with hzdef
  have hz : (fMap K L σ δ₀).rTensor A z = 0 := by
    apply theta_injective
    rw [theta_rTensor_fMap, hzdef, theta_thetaInv_apply, hY, map_zero]
  set D := LinearMap.ker (fMap K L σ δ₀) with hDdef
  have hex : Function.Exact (D.subtype.rTensor A) ((fMap K L σ δ₀).rTensor A) :=
    Module.Flat.rTensor_exact A (LinearMap.exact_subtype_ker_map _)
  obtain ⟨w, hw⟩ := (hex z).1 hz
  have key : ∀ w : D ⊗[K] A, ∃ a : ι → A, (D.subtype.rTensor A) w = ∑ i, b i ⊗ₜ[K] a i := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul d a =>
        have hd : (d : V) ∈ Submodule.span K (Set.range b) := hspan _ (LinearMap.mem_ker.1 d.2)
        obtain ⟨q, hq⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hd
        refine ⟨fun i => q i • a, ?_⟩
        rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hq, TensorProduct.sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [TensorProduct.smul_tmul]
    | add w₁ w₂ h₁ h₂ =>
        obtain ⟨a₁, ha₁⟩ := h₁
        obtain ⟨a₂, ha₂⟩ := h₂
        refine ⟨a₁ + a₂, ?_⟩
        rw [map_add, ha₁, ha₂, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Pi.add_apply, TensorProduct.tmul_add]
  obtain ⟨a, ha⟩ := key w
  refine ⟨a, ?_⟩
  rw [E_eq_theta, ← ha, hw, hzdef, theta_thetaInv_apply]

def contrK (ψ : L →ₗ[K] K) : L ⊗[K] A →ₗ[K] A :=
  TensorProduct.lift ((LinearMap.lsmul K A).comp ψ)

theorem contrK_tmul (ψ : L →ₗ[K] K) (l : L) (a : A) : contrK K L A ψ (l ⊗ₜ[K] a) = ψ l • a := by
  simp [contrK]

theorem rightActions_smul_tmul (r : A) (l : L) (a : A) : r • (l ⊗ₜ[K] a) = l ⊗ₜ[K] (r * a) := by
  simp [TensorProduct.RightActions.smul_def, TensorProduct.smul_tmul']

def contrA (ψ : L →ₗ[K] K) : L ⊗[K] A →ₗ[A] A where
  toFun := contrK K L A ψ
  map_add' := map_add _
  map_smul' r t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
        rw [rightActions_smul_tmul, contrK_tmul, contrK_tmul, RingHom.id_apply, smul_eq_mul,
          Algebra.smul_def, Algebra.smul_def, mul_left_comm]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem contrA_apply (ψ : L →ₗ[K] K) (t : L ⊗[K] A) : contrA K L A ψ t = contrK K L A ψ t := rfl

def GA (G : (V) →ₗ[K] (ι → K)) (Y : MA) : ι → A :=
  fun i => ∑ j : Fin 2, ∑ k : Fin 2,
    contrK K L A ((LinearMap.proj i) ∘ₗ G ∘ₗ (Matrix.singleLinearMap K j k)) (Y j k)

theorem GA_E [DecidableEq ι] (b : ι → V) (G : (V) →ₗ[K] (ι → K)) (hG : ∀ i, G (b i) = Pi.single i 1)
    (a : ι → A) : GA K L A G (E K L A b a) = a := by
  funext i
  have h1 : ∀ j k : Fin 2, contrK K L A ((LinearMap.proj i) ∘ₗ G ∘ₗ (Matrix.singleLinearMap K j k))
      (E K L A b a j k) = ∑ i', G (Matrix.single j k (b i' j k)) i • a i' := by
    intro j k
    simp only [E, Matrix.sum_apply, Matrix.map_apply, map_sum, contrK_tmul, LinearMap.comp_apply,
      Matrix.singleLinearMap_apply, LinearMap.proj_apply]
  have h3 : ∀ i', ∑ j : Fin 2, ∑ k : Fin 2, G (Matrix.single j k (b i' j k)) i = G (b i') i := by
    intro i'
    conv_rhs => rw [Matrix.matrix_eq_sum_single (b i')]
    simp only [map_sum, Finset.sum_apply]
  calc GA K L A G (E K L A b a) i
      = ∑ j : Fin 2, ∑ k : Fin 2, ∑ i', G (Matrix.single j k (b i' j k)) i • a i' := by
        simp only [GA, h1]
    _ = ∑ j : Fin 2, ∑ i', ∑ k : Fin 2, G (Matrix.single j k (b i' j k)) i • a i' :=
        Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i', ∑ j : Fin 2, ∑ k : Fin 2, G (Matrix.single j k (b i' j k)) i • a i' := Finset.sum_comm
    _ = ∑ i', (∑ j : Fin 2, ∑ k : Fin 2, G (Matrix.single j k (b i' j k)) i) • a i' := by
        simp only [Finset.sum_smul]
    _ = ∑ i', G (b i') i • a i' := by simp only [h3]
    _ = a i := by
        simp only [hG, Pi.single_apply, ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq Finset.univ i]
        simp

theorem exists_dual [DecidableEq ι] (b : ι → V) (hb : LinearIndependent K b) :
    ∃ G : (V) →ₗ[K] (ι → K), ∀ i, G (b i) = Pi.single i 1 := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    ((Module.Basis.span hb).equivFun.toLinearMap : Submodule.span K (Set.range b) →ₗ[K] (ι → K))
  refine ⟨G, fun i => ?_⟩
  have h := LinearMap.congr_fun hG (Module.Basis.span hb i)
  rw [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_toLinearMap] at h
  have hc : ((Module.Basis.span hb i : Submodule.span K (Set.range b)) : V) = b i := by
    rw [Module.Basis.span_apply]
  rw [hc] at h
  rw [h]
  funext j
  rw [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
  simp only [eq_comm]

end Algebra

section Topology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

local notation "V" => Matrix (Fin 2) (Fin 2) L
local notation "MA" => Matrix (Fin 2) (Fin 2) (L ⊗[K] A)

theorem continuous_tmul_right (l : L) : Continuous fun a : A => l ⊗ₜ[K] a := by
  let φ : A →ₗ[A] L ⊗[K] A :=
    { toFun := fun a => l ⊗ₜ[K] a
      map_add' := fun x y => TensorProduct.tmul_add _ _ _
      map_smul' := fun r a => by
        rw [RingHom.id_apply, rightActions_smul_tmul, smul_eq_mul] }
  exact IsModuleTopology.continuous_of_linearMap φ

theorem continuous_contrK (ψ : L →ₗ[K] K) : Continuous (contrK K L A ψ) :=
  IsModuleTopology.continuous_of_linearMap (contrA K L A ψ)

variable {ι : Type} [Fintype ι]

theorem continuous_E (b : ι → V) : Continuous (E K L A b) := by
  haveI := isTopologicalRing_tensor K L A
  unfold E
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact (continuous_tmul_right K L A (b i j k)).comp (continuous_apply i)

omit [Fintype ι] in
theorem continuous_GA [Fintype ι] (G : (V) →ₗ[K] (ι → K)) : Continuous (GA K L A G) := by
  refine continuous_pi fun i => ?_
  refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
  exact (continuous_contrK K L A _).comp (continuous_id.matrix_elem j k)

theorem exists_homeomorph (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ)
    (b : ι → V) (hb : LinearIndependent K b)
    (hspan : ∀ x : V, x * (δ₀ : V) = (δ₀ : V) * x.map σ ↔ x ∈ Submodule.span K (Set.range b)) :
    ∃ e : (ι → A) ≃ₜ ↥(twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ∀ a : ι → A, ((e a : twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)) : MA) =
        ∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i := by
  classical
  have hb0 : ∀ i, fMap K L σ (δ₀ : V) (b i) = 0 := fun i => by
    rw [fMap_apply, sub_eq_zero]
    exact (hspan _).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hspan' : ∀ x : V, fMap K L σ (δ₀ : V) x = 0 → x ∈ Submodule.span K (Set.range b) :=
    fun x hx => (hspan x).1 (sub_eq_zero.1 hx)
  obtain ⟨G, hG⟩ := exists_dual K L b hb
  set T := twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c) with hT
  have hmem : ∀ a, E K L A b a ∈ T := fun a =>
    (mem_twistedCommutant_map_mul_scalar_iff K L A σ δ₀ c _).2 (fMapA_E K L A σ _ b hb0 a)
  have hsurj : ∀ t : T, ∃ a, E K L A b a = (t : MA) := fun t =>
    exists_E_eq_of_fMapA_eq_zero K L A σ _ b hspan' _
      ((mem_twistedCommutant_map_mul_scalar_iff K L A σ δ₀ c _).1 t.2)
  let e : (ι → A) ≃ T :=
    { toFun := fun a => ⟨E K L A b a, hmem a⟩
      invFun := fun t => GA K L A G (t : MA)
      left_inv := fun a => GA_E K L A b G hG a
      right_inv := fun t => by
        obtain ⟨a, ha⟩ := hsurj t
        apply Subtype.ext
        simp only [← ha, GA_E K L A b G hG a] }
  refine ⟨{ toEquiv := e
            continuous_toFun := (continuous_E K L A b).subtype_mk _
            continuous_invFun := (continuous_GA K L A G).comp continuous_subtype_val }, fun a => rfl⟩

end Topology

end TwistedCommutantBC
end AutomorphicForm

end

open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L) (c : (L ⊗[K] A)ˣ)
    (ι : Type) [Fintype ι] (b : ι → Matrix (Fin 2) (Fin 2) L) (hb : LinearIndependent K b)
    (hspan : ∀ x : Matrix (Fin 2) (Fin 2) L,
      x * (δ₀ : Matrix (Fin 2) (Fin 2) L) = (δ₀ : Matrix (Fin 2) (Fin 2) L) * x.map σ ↔
        x ∈ Submodule.span K (Set.range b)) :
    ∃ e : (ι → A) ≃ₜ ↥(AutomorphicForm.twistedCommutant K L A σ
        (Matrix.GeneralLinearGroup.map
            (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
          Matrix.GeneralLinearGroup.scalar (Fin 2) c)),
      ∀ a : ι → A,
        ((e a : AutomorphicForm.twistedCommutant K L A σ
            (Matrix.GeneralLinearGroup.map
                (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A) δ₀ *
              Matrix.GeneralLinearGroup.scalar (Fin 2) c)) :
          Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
        ∑ i, (b i).map fun l : L => l ⊗ₜ[K] a i :=
  AutomorphicForm.TwistedCommutantBC.exists_homeomorph K L A σ δ₀ c b hb hspan

end S_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent
end P2MW
export P2MW.S_AutomorphicForm_exists_homeomorph_twistedCommutant_map_mul_scalar_forall_coe_eq_sum_map_tmul_of_linearIndependent (solution)
