-- Prove2me | solution 1 for AutomorphicForm.exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/98555c9c-3e25-5d13-a3ba-227d6ad810b0

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Theorems.Thm_AutomorphicForm_exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
import Theorems.Thm_AutomorphicForm_exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
import Theorems.Thm_AutomorphicForm_exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul
import Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_exists_of_isRegularSemisimple_normString_of_finrank_eq_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory TopologicalSpace Topology Filter Set MulAction
open scoped TensorProduct TensorProduct.RightActions Pointwise

noncomputable section

namespace FinTransportCC

section Algebra

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

end Algebra

section Twist

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
  (σ : L ≃ₐ[K] L)

local notation "sT" => AutomorphicForm.sigmaTensor K L A σ
local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "ι" => AutomorphicForm.toTensorGL K L A
local notation "incl" => (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A)

theorem sigmaTensor_tmul (l : L) (a : A) : sT (l ⊗ₜ[K] a) = σ l ⊗ₜ[K] a := by
  simp [AutomorphicForm.sigmaTensor]

theorem sigmaTensor_one_tmul (a : A) : sT ((1 : L) ⊗ₜ[K] a) = (1 : L) ⊗ₜ[K] a := by
  rw [sigmaTensor_tmul, map_one]

theorem sigmaTensor_includeRight (a : A) : sT (incl a) = incl a :=
  sigmaTensor_one_tmul K L A σ a

theorem sigmaTensor_sigmaTensor (hσ : ∀ l : L, σ (σ l) = l) (b : L ⊗[K] A) : sT (sT b) = b := by
  induction b using TensorProduct.induction_on with
  | zero => simp
  | tmul l a => rw [sigmaTensor_tmul, sigmaTensor_tmul, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem sigmaGL_apply (g : GL (Fin 2) (L ⊗[K] A)) (i j : Fin 2) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      sT ((g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).map sT := by
  ext i j
  exact sigmaGL_apply K L A σ g i j

theorem sigmaGL_sigmaGL (hσ : ∀ l : L, σ (σ l) = l) (g : GL (Fin 2) (L ⊗[K] A)) : sG (sG g) = g := by
  ext i j
  rw [sigmaGL_apply, sigmaGL_apply, sigmaTensor_sigmaTensor K L A σ hσ]

theorem toTensorGL_apply (γ : GL (Fin 2) A) (i j : Fin 2) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j =
      (1 : L) ⊗ₜ[K] ((γ : Matrix (Fin 2) (Fin 2) A) i j) :=
  Matrix.GeneralLinearGroup.map_apply _ _ _ _

theorem coe_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
      (γ : Matrix (Fin 2) (Fin 2) A).map incl := rfl

theorem sigmaGL_toTensorGL (γ : GL (Fin 2) A) : sG (ι γ) = ι γ := by
  ext i j
  rw [sigmaGL_apply, toTensorGL_apply, sigmaTensor_one_tmul]

theorem trace_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      incl (γ : Matrix (Fin 2) (Fin 2) A).trace := by
  rw [coe_toTensorGL, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.map_apply, map_add]

theorem det_toTensorGL (γ : GL (Fin 2) A) :
    ((ι γ : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      incl (γ : Matrix (Fin 2) (Fin 2) A).det := by
  rw [coe_toTensorGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem trace_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      sT (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [coe_sigmaGL, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.map_apply, map_add]

theorem det_sigmaGL (g : GL (Fin 2) (L ⊗[K] A)) :
    ((sG g : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      sT (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [coe_sigmaGL, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.map_apply, map_sub, map_mul]

theorem isRegularSemisimple_toTensorGL (γ : GL (Fin 2) A) (hγ : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.IsRegularSemisimple (ι γ) := by
  unfold AutomorphicForm.IsRegularSemisimple at hγ ⊢
  rw [trace_toTensorGL, det_toTensorGL]
  have : incl (γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * incl (γ : Matrix (Fin 2) (Fin 2) A).det =
      incl ((γ : Matrix (Fin 2) (Fin 2) A).trace ^ 2 - 4 * (γ : Matrix (Fin 2) (Fin 2) A).det) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [this]
  exact hγ.map _

theorem trace_units_conj' (x g : GL (Fin 2) (L ⊗[K] A)) :
    ((x⁻¹ * g * x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.one_mul]

theorem det_units_conj' (x g : GL (Fin 2) (L ⊗[K] A)) :
    ((x⁻¹ * g * x : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
    ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]

theorem normString_two (h2 : Module.finrank K L = 2) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ δ = δ * sG δ := by
  simp [AutomorphicForm.normString, h2, List.range_succ]

theorem mem_twistedCentralizer_iff (δ t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ ↔ t * δ = δ * sG t := by
  rw [AutomorphicForm.twistedCentralizer, AutomorphicForm.mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul]

variable (h2 : Module.finrank K L = 2) (hσ : ∀ l : L, σ (σ l) = l)
include h2 hσ

theorem sigmaGL_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sG (AutomorphicForm.normString K L A σ δ) = sG δ * δ := by
  rw [normString_two K L A σ h2, map_mul, sigmaGL_sigmaGL K L A σ hσ]

theorem normString_conj (δ x : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.normString K L A σ (x⁻¹ * δ * sG x) =
      x⁻¹ * AutomorphicForm.normString K L A σ δ * x := by
  rw [normString_two K L A σ h2, normString_two K L A σ h2, map_mul, map_mul, map_inv,
    sigmaGL_sigmaGL K L A σ hσ]
  group

theorem sigmaTensor_trace_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sT ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace =
      ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).trace := by
  rw [← trace_sigmaGL, sigmaGL_normString K L A σ h2 hσ, normString_two K L A σ h2, Units.val_mul,
    Units.val_mul, Matrix.trace_mul_comm]

theorem sigmaTensor_det_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    sT ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det =
      ((AutomorphicForm.normString K L A σ δ : GL (Fin 2) (L ⊗[K] A)) :
        Matrix (Fin 2) (Fin 2) (L ⊗[K] A)).det := by
  rw [← det_sigmaGL, sigmaGL_normString K L A σ h2 hσ, normString_two K L A σ h2, Units.val_mul,
    Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm]

theorem twistedCentralizer_le_centralizer_normString (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ δ ≤
      Subgroup.centralizer ({AutomorphicForm.normString K L A σ δ} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  intro t ht
  rw [mem_twistedCentralizer_iff] at ht
  rw [Subgroup.mem_centralizer_singleton_iff, normString_two K L A σ h2]
  have h1 : sG t * sG δ = sG δ * t := by
    have := congrArg sG ht
    rwa [map_mul, map_mul, sigmaGL_sigmaGL K L A σ hσ] at this
  symm
  calc δ * sG δ * t = δ * (sG δ * t) := by rw [mul_assoc]
    _ = δ * (sG t * sG δ) := by rw [h1]
    _ = (δ * sG t) * sG δ := by rw [mul_assoc]
    _ = t * δ * sG δ := by rw [← ht]
    _ = t * (δ * sG δ) := by rw [mul_assoc]

theorem mem_twistedCentralizer_conj_iff (δ x t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ (x⁻¹ * δ * sG x) ↔
      x * t * x⁻¹ ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  rw [mem_twistedCentralizer_iff, mem_twistedCentralizer_iff, map_mul, map_mul, map_inv]
  constructor
  · intro h
    calc x * t * x⁻¹ * δ = x * (t * (x⁻¹ * δ * sG x)) * (sG x)⁻¹ := by group
      _ = x * (x⁻¹ * δ * sG x * sG t) * (sG x)⁻¹ := by rw [h]
      _ = δ * (sG x * sG t * (sG x)⁻¹) := by group
  · intro h
    calc t * (x⁻¹ * δ * sG x) = x⁻¹ * (x * t * x⁻¹ * δ) * sG x := by group
      _ = x⁻¹ * (δ * (sG x * sG t * (sG x)⁻¹)) * sG x := by rw [h]
      _ = x⁻¹ * δ * sG x * sG t := by group

end Twist

section Injective

variable (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]

private theorem _root_.FinTransportCC.includeRight_injective :
    Function.Injective (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

p2m_export "FinTransportCC" "includeRight_injective"

theorem toTensorGL_injective : Function.Injective (AutomorphicForm.toTensorGL K L A) := by
  intro g g' h
  apply Units.ext
  ext i j
  have := congrArg (fun m : GL (Fin 2) (L ⊗[K] A) => (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) h
  simp only [toTensorGL_apply] at this
  exact includeRight_injective K L A this

end Injective

section Galois

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]

theorem sigma_involutive_and_ne_one (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    (∀ l : L, σ (σ l) = l) ∧ ∃ ℓ : L, σ ℓ ≠ ℓ := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := (IsGalois.card_aut_eq_finrank K L).trans h2
  refine ⟨fun l => ?_, ?_⟩
  · have hpow : σ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
    have := AlgEquiv.congr_fun hpow l
    rwa [pow_two, AlgEquiv.mul_apply] at this
  · by_contra h
    push Not at h
    have hσ1 : σ = 1 := AlgEquiv.ext h
    have hall : ∀ τ : L ≃ₐ[K] L, τ = 1 := fun τ => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      rw [← hk, hσ1, one_zpow]
    have h1 : Nat.card (L ≃ₐ[K] L) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega

theorem exists_algebraMap_eq_of_fixed (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {l : L} (hl : σ l = l) :
    ∃ k : K, algebraMap K L k = l := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension K L := { finrank_eq_two' := h2 }
  haveI : IsGalois K L := inferInstance
  have hzpow : ∀ k : ℤ, (σ ^ k) l = l := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [zpow_add_one, AlgEquiv.mul_apply, hl, ih]
    | pred k ih =>
        have hinv : σ⁻¹ l = l := by
          rw [AlgEquiv.aut_inv]
          conv_lhs => rw [← hl]
          exact σ.symm_apply_apply l
        rw [zpow_sub_one, AlgEquiv.mul_apply, hinv, ih]
  have hfix : ∀ f : L ≃ₐ[K] L, f l = l := fun f => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen f)
    rw [← hk]
    exact hzpow k
  exact (IsGalois.mem_range_algebraMap_iff_fixed l).mpr hfix

variable (A : Type) [CommRing A] [Algebra K A]

theorem exists_one_tmul_of_sigmaTensor_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {b : L ⊗[K] A}
    (hb : AutomorphicForm.sigmaTensor K L A σ b = b) : ∃ a : A, b = (1 : L) ⊗ₜ[K] a := by

  have hsym : ∀ b : L ⊗[K] A, ∃ a : A, b + AutomorphicForm.sigmaTensor K L A σ b = (1 : L) ⊗ₜ[K] a := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l a =>
        obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_fixed K L h2 σ hgen (l := l + σ l)
          (by rw [map_add, (sigma_involutive_and_ne_one K L h2 σ hgen).1 l, add_comm])
        refine ⟨k • a, ?_⟩
        rw [sigmaTensor_tmul, ← TensorProduct.add_tmul, ← hk, Algebra.algebraMap_eq_smul_one,
          TensorProduct.smul_tmul]
    | add x y hx hy =>
        obtain ⟨a, ha⟩ := hx
        obtain ⟨a', ha'⟩ := hy
        refine ⟨a + a', ?_⟩
        rw [map_add, TensorProduct.tmul_add, ← ha, ← ha']
        abel
  obtain ⟨a, ha⟩ := hsym b
  rw [hb, ← two_smul K b] at ha
  refine ⟨(2 : K)⁻¹ • a, ?_⟩
  rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul', ← ha, smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul]

theorem exists_toTensorGL_eq_of_sigmaGL_eq (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) {g : GL (Fin 2) (L ⊗[K] A)}
    (hg : AutomorphicForm.sigmaGL K L A σ g = g) : ∃ m : GL (Fin 2) A, AutomorphicForm.toTensorGL K L A m = g := by
  set incl : A →ₐ[K] L ⊗[K] A := Algebra.TensorProduct.includeRight with hincl
  have hginv : AutomorphicForm.sigmaGL K L A σ g⁻¹ = g⁻¹ := by rw [map_inv, hg]
  have hent : ∀ (u : GL (Fin 2) (L ⊗[K] A)), AutomorphicForm.sigmaGL K L A σ u = u →
      ∃ m : Matrix (Fin 2) (Fin 2) A, m.map incl = (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := by
    intro u hu
    have hij : ∀ i j, ∃ a : A, (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j = (1 : L) ⊗ₜ[K] a := by
      intro i j
      apply exists_one_tmul_of_sigmaTensor_eq K L A h2 σ hgen
      have := congrArg (fun m : GL (Fin 2) (L ⊗[K] A) => (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) i j) hu
      simpa only [sigmaGL_apply] using this
    choose a ha using hij
    refine ⟨Matrix.of fun i j => a i j, ?_⟩
    ext i j
    rw [ha i j]
    rfl
  obtain ⟨m, hm⟩ := hent g hg
  obtain ⟨m', hm'⟩ := hent g⁻¹ hginv
  have hmapinj : Function.Injective fun x : Matrix (Fin 2) (Fin 2) A => x.map incl := by
    intro x y hxy
    ext i j
    exact includeRight_injective K L A (congrFun (congrFun hxy i) j)
  have hmm' : m * m' = 1 := by
    apply hmapinj
    change (m * m').map incl.toRingHom = (1 : Matrix (Fin 2) (Fin 2) A).map incl.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change m.map incl * m'.map incl = 1
    rw [hm, hm', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hm'm : m' * m = 1 := by
    apply hmapinj
    change (m' * m).map incl.toRingHom = (1 : Matrix (Fin 2) (Fin 2) A).map incl.toRingHom
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    change m'.map incl * m.map incl = 1
    rw [hm, hm', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨⟨m, m', hmm', hm'm⟩, Units.ext ?_⟩
  exact hm

end Galois

section Torus

variable (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L]
  (A : Type) [Field A] [Algebra K A]
  (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)

local notation "sG" => AutomorphicForm.sigmaGL K L A σ
local notation "ι" => AutomorphicForm.toTensorGL K L A
local notation "Nm" => AutomorphicForm.normString K L A σ

theorem comm_of_mem_centralizer_toTensorGL {γ₁ : GL (Fin 2) A} (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁)
    {a b : GL (Fin 2) (L ⊗[K] A)}
    (ha : a ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))))
    (hb : b ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A)))) : a * b = b * a :=
  mul_comm_of_mem_centralizer (isRegularSemisimple_toTensorGL K L A γ₁ hγ₁) ha hb

theorem toTensorGL_mem_centralizer_iff {γ₁ m : GL (Fin 2) A} :
    ι m ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) ↔
      m ∈ Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) A)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  exact ⟨fun h => toTensorGL_injective K L A h, fun h => by rw [h]⟩

theorem mem_twistedCentralizer_mul_self {δ u : GL (Fin 2) (L ⊗[K] A)}
    (hu : u ∈ AutomorphicForm.twistedCentralizer K L A σ δ) :
    u ∈ AutomorphicForm.twistedCentralizer K L A σ (u * δ) := by
  rw [mem_twistedCentralizer_iff] at hu ⊢
  rw [mul_assoc, ← hu]

theorem mem_twistedCentralizer_of_commute {δ u t : GL (Fin 2) (L ⊗[K] A)}
    (ht : t ∈ AutomorphicForm.twistedCentralizer K L A σ (u * δ)) (hc : t * u = u * t) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ := by
  rw [mem_twistedCentralizer_iff] at ht ⊢
  rw [← mul_assoc, hc, mul_assoc, mul_assoc] at ht
  exact mul_left_cancel ht

include h2 hgen

theorem mem_centralizer_of_normString_eq {δ₀ : GL (Fin 2) (L ⊗[K] A)} {γ₁ : GL (Fin 2) A}
    (hN : Nm δ₀ = ι γ₁) : δ₀ ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  have h1 : sG δ₀ * δ₀ = δ₀ * sG δ₀ := by
    have := sigmaGL_normString K L A σ h2 hσ δ₀
    rw [hN, sigmaGL_toTensorGL, ← hN, normString_two K L A σ h2] at this
    exact this.symm
  rw [Subgroup.mem_centralizer_singleton_iff, ← hN, normString_two K L A σ h2]
  symm
  calc δ₀ * sG δ₀ * δ₀ = δ₀ * (sG δ₀ * δ₀) := by rw [mul_assoc]
    _ = δ₀ * (δ₀ * sG δ₀) := by rw [h1]

theorem mem_twistedCentralizer_iff_of_normString_eq {δ₀ : GL (Fin 2) (L ⊗[K] A)} {γ₁ : GL (Fin 2) A}
    (hγ₁ : AutomorphicForm.IsRegularSemisimple γ₁) (hN : Nm δ₀ = ι γ₁) (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₀ ↔
      ∃ m ∈ Subgroup.centralizer ({γ₁} : Set (GL (Fin 2) A)), ι m = t := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1
  have hδ₀ := mem_centralizer_of_normString_eq K L A h2 σ hgen hN
  constructor
  · intro ht
    have htC : t ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) := by
      rw [← hN]
      exact twistedCentralizer_le_centralizer_normString K L A σ h2 hσ δ₀ ht
    rw [mem_twistedCentralizer_iff] at ht
    have hcomm : t * δ₀ = δ₀ * t := comm_of_mem_centralizer_toTensorGL K L A hγ₁ htC hδ₀
    have hfix : sG t = t := by
      rw [hcomm] at ht
      exact (mul_left_cancel ht).symm
    obtain ⟨m, hm⟩ := exists_toTensorGL_eq_of_sigmaGL_eq K L A h2 σ hgen hfix
    refine ⟨m, ?_, hm⟩
    rw [← toTensorGL_mem_centralizer_iff K L A, hm]
    exact htC
  · rintro ⟨m, hm, rfl⟩
    have htC : ι m ∈ Subgroup.centralizer ({ι γ₁} : Set (GL (Fin 2) (L ⊗[K] A))) :=
      (toTensorGL_mem_centralizer_iff K L A).2 hm
    rw [mem_twistedCentralizer_iff, sigmaGL_toTensorGL]
    exact comm_of_mem_centralizer_toTensorGL K L A hγ₁ htC hδ₀

theorem mem_twistedCentralizer_iff_of_isNormConjugator {γ : GL (Fin 2) A}
    (hγ : AutomorphicForm.IsRegularSemisimple γ) {δ₁ y : GL (Fin 2) (L ⊗[K] A)}
    (hy : AutomorphicForm.IsNormConjugator K L A σ γ δ₁ y) (t : GL (Fin 2) (L ⊗[K] A)) :
    t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₁ ↔
      ∃ m ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)), y * ι m * y⁻¹ = t := by
  have hσ := (sigma_involutive_and_ne_one K L h2 σ hgen).1

  have hN : Nm (y⁻¹ * δ₁ * sG y) = ι γ := by
    rw [normString_conj K L A σ h2 hσ]
    exact hy.symm
  have key := mem_twistedCentralizer_iff_of_normString_eq K L A h2 σ hgen hγ hN (y⁻¹ * t * y)
  have hconj : y⁻¹ * t * y ∈ AutomorphicForm.twistedCentralizer K L A σ (y⁻¹ * δ₁ * sG y) ↔
      t ∈ AutomorphicForm.twistedCentralizer K L A σ δ₁ := by
    rw [mem_twistedCentralizer_conj_iff K L A σ h2 hσ]
    have : y * (y⁻¹ * t * y) * y⁻¹ = t := by group
    rw [this]
  rw [← hconj, key]
  constructor
  · rintro ⟨m, hm, hmt⟩
    exact ⟨m, hm, by rw [hmt]; group⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, by group⟩

end Torus

section Topology

variable (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

theorem t2Space_GL [T2Space A] : T2Space (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  exact Units.isEmbedding_embedProduct.t2Space

theorem secondCountableTopology_GL [SecondCountableTopology A] :
    SecondCountableTopology (GL (Fin 2) A) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → A))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) A)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem locallyCompactSpace_GL [T2Space A] [LocallyCompactSpace A] :
    LocallyCompactSpace (GL (Fin 2) A) := by
  haveI : T2Space (Matrix (Fin 2) (Fin 2) A) := inferInstanceAs (T2Space (Fin 2 → Fin 2 → A))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) A) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → A))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

end Topology

section TensorTopology

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

theorem continuous_sigmaTensor (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaTensor K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have h := IsModuleTopology.continuous_of_linearMap
    (TensorProduct.RightActions.AlgebraMap.baseChange K L L A σ.toAlgHom).toLinearMap
  exact h

theorem continuous_sigmaGL (σ : L ≃ₐ[K] L) : Continuous (AutomorphicForm.sigmaGL K L A σ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map (continuous_sigmaTensor K L A σ)

theorem continuous_toTensorGL : Continuous (AutomorphicForm.toTensorGL K L A) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  have hincl : Continuous
      ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom) := by
    have h := IsModuleTopology.continuous_of_linearMap (Algebra.linearMap A (L ⊗[K] A))
    exact h
  refine Continuous.units_map _ ?_
  exact continuous_id.matrix_map hincl

theorem isClosed_twistedCentralizer [T2Space A] (σ : L ≃ₐ[K] L) (δ : GL (Fin 2) (L ⊗[K] A)) :
    IsClosed ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) := by
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  have hc : Continuous fun t : GL (Fin 2) (L ⊗[K] A) =>
      t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹ :=
    (continuous_id.mul continuous_const).mul (continuous_sigmaGL K L A σ).inv
  have : ((AutomorphicForm.twistedCentralizer K L A σ δ : Subgroup (GL (Fin 2) (L ⊗[K] A))) :
      Set (GL (Fin 2) (L ⊗[K] A))) =
      (fun t : GL (Fin 2) (L ⊗[K] A) => t * δ * (AutomorphicForm.sigmaGL K L A σ t)⁻¹) ⁻¹' {δ} := by
    ext t
    exact AutomorphicForm.mem_sigmaCentralizer_iff
  rw [this]
  exact (isClosed_singleton).preimage hc

theorem exists_continuousMulEquiv [T2Space A] [LocallyCompactSpace A] [SecondCountableTopology A]
    (P : Subgroup (GL (Fin 2) A)) (hP : IsClosed (P : Set (GL (Fin 2) A)))
    (Q : Subgroup (GL (Fin 2) (L ⊗[K] A))) (hQ : IsClosed (Q : Set (GL (Fin 2) (L ⊗[K] A))))
    (y : GL (Fin 2) (L ⊗[K] A))
    (hPQ : ∀ q, q ∈ Q ↔ ∃ p ∈ P, y * AutomorphicForm.toTensorGL K L A p * y⁻¹ = q) :
    ∃ e : P ≃ₜ* Q, ∀ p : P, ((e p : Q) : GL (Fin 2) (L ⊗[K] A)) = y * AutomorphicForm.toTensorGL K L A p * y⁻¹ := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  haveI := AutomorphicForm.t2Space_tensorGL K L A
  haveI := AutomorphicForm.locallyCompactSpace_tensorGL K L A
  haveI := t2Space_GL A
  haveI := secondCountableTopology_GL A
  haveI := locallyCompactSpace_GL A
  haveI : SigmaCompactSpace (GL (Fin 2) A) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : SigmaCompactSpace P := hP.isClosedEmbedding_subtypeVal.sigmaCompactSpace
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  set ι := AutomorphicForm.toTensorGL K L A with hιdef
  let f : P →* Q :=
    { toFun := fun p => ⟨y * ι p * y⁻¹, (hPQ _).2 ⟨p, p.2, rfl⟩⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun p p' => Subtype.ext (by
        change y * ι ((p : GL (Fin 2) A) * (p' : GL (Fin 2) A)) * y⁻¹ = y * ι p * y⁻¹ * (y * ι p' * y⁻¹)
        rw [map_mul]
        group) }
  have hfval : ∀ p : P, ((f p : Q) : GL (Fin 2) (L ⊗[K] A)) = y * ι p * y⁻¹ := fun p => rfl
  have hfc : Continuous f := by
    have : Continuous fun p : P => y * ι (p : GL (Fin 2) A) * y⁻¹ :=
      (continuous_const.mul ((continuous_toTensorGL K L A).comp continuous_subtype_val)).mul continuous_const
    exact this.subtype_mk _
  have hfinj : Function.Injective f := by
    intro p p' h
    have h' : y * ι p * y⁻¹ = y * ι p' * y⁻¹ := by
      rw [← hfval, ← hfval, h]
    have h'' : ι p = ι p' := by
      have := congrArg (fun g => y⁻¹ * g * y) h'
      simpa [mul_assoc] using this
    exact Subtype.ext (toTensorGL_injective K L A h'')
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨p, hp, hpq⟩ := (hPQ q).1 q.2
    exact ⟨⟨p, hp⟩, Subtype.ext hpq⟩
  have hopen : IsOpenMap f := MonoidHom.isOpenMap_of_sigmaCompact f hfsurj hfc
  let e₀ : P ≃ Q := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let h : P ≃ₜ Q := e₀.toHomeomorphOfContinuousOpen hfc hopen
  refine ⟨{ MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩ with
      continuous_toFun := hfc
      continuous_invFun := h.symm.continuous }, fun p => rfl⟩

end TensorTopology

section Transport

theorem map_val_map_eq
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    [MeasurableSpace (GL (Fin 2) A)] [BorelSpace (GL (Fin 2) A)]
    [MeasurableSpace (GL (Fin 2) (L ⊗[K] A))] [BorelSpace (GL (Fin 2) (L ⊗[K] A))]
    (P : Subgroup (GL (Fin 2) A)) (Q : Subgroup (GL (Fin 2) (L ⊗[K] A)))
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace Q] [BorelSpace Q]
    (y : GL (Fin 2) (L ⊗[K] A)) (e : P ≃ₜ* Q)
    (he : ∀ p : P, ((e p : Q) : GL (Fin 2) (L ⊗[K] A)) = y * AutomorphicForm.toTensorGL K L A p * y⁻¹)
    (τ : Measure P) :
    Measure.map Subtype.val (Measure.map e τ) =
      Measure.map (fun g : GL (Fin 2) A => y * AutomorphicForm.toTensorGL K L A g * y⁻¹)
        (Measure.map Subtype.val τ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  have hcj : Measurable fun g : GL (Fin 2) A => y * AutomorphicForm.toTensorGL K L A g * y⁻¹ :=
    ((continuous_const.mul (continuous_toTensorGL K L A)).mul continuous_const).measurable
  have hme : Measurable (e : P → Q) := (map_continuous e).measurable
  have hvQ : Measurable (Subtype.val : Q → GL (Fin 2) (L ⊗[K] A)) := continuous_subtype_val.measurable
  have hvP : Measurable (Subtype.val : P → GL (Fin 2) A) := continuous_subtype_val.measurable
  rw [Measure.map_map hvQ hme, Measure.map_map hcj hvP]
  congr 1
  funext t
  simp only [Function.comp_apply, he]

theorem coupled_map
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    (γ : GL (Fin 2) A) (δ₁ y : GL (Fin 2) (L ⊗[K] A))
    (e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) ≃ₜ* AutomorphicForm.twistedCentralizer K L A σ δ₁)
    (he : ∀ p, ((e p : AutomorphicForm.twistedCentralizer K L A σ δ₁) : GL (Fin 2) (L ⊗[K] A)) =
      y * AutomorphicForm.toTensorGL K L A p * y⁻¹)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ)) :
    AutomorphicForm.Coupled K L A σ γ δ₁ y τ
      (@Measure.map _ _ (AutomorphicForm.centralizerBorel A γ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ₁)
        e τ) := by
  haveI := AutomorphicForm.isTopologicalRing_tensor K L A
  haveI := AutomorphicForm.isTopologicalGroup_tensorGL K L A
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.glBorelOf (L ⊗[K] A)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] A)) := AutomorphicForm.borelSpace_glBorelOf (L ⊗[K] A)
  letI : MeasurableSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := AutomorphicForm.centralizerBorel A γ
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) := ⟨rfl⟩
  letI : MeasurableSpace (AutomorphicForm.twistedCentralizer K L A σ δ₁) :=
    AutomorphicForm.twistedCentralizerBorel K L A σ δ₁
  haveI : BorelSpace (AutomorphicForm.twistedCentralizer K L A σ δ₁) := ⟨rfl⟩
  unfold AutomorphicForm.Coupled
  have hm1 : Measurable fun t : AutomorphicForm.twistedCentralizer K L A σ δ₁ =>
      y⁻¹ * (t : GL (Fin 2) (L ⊗[K] A)) * y :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
  have hme : Measurable (e : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) → AutomorphicForm.twistedCentralizer K L A σ δ₁) :=
    (map_continuous e).measurable
  rw [Measure.map_map hm1 hme]
  congr 1
  funext t
  simp only [Function.comp_apply, he]
  group

end Transport

section Main

open NumberField IsDedekindDomain AutomorphicForm

end Main

end FinTransportCC

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory NumberField Topology Filter
open IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

namespace FinTransportAlg

section Algebra

variable {A : Type*} [CommRing A]

theorem entries_of_commute (g X : Matrix (Fin 2) (Fin 2) A) (h : X * g = g * X) (u : A)
    (hu : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1) :
    X 0 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 0 1 ∧
    X 1 0 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * g 1 0 ∧
    X 0 0 - X 1 1 = u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1)) * (g 0 0 - g 1 1) := by
  have e00 := congr_fun (congr_fun h 0) 0
  have e01 := congr_fun (congr_fun h 0) 1
  have e10 := congr_fun (congr_fun h 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (-(X 0 1)) * hu + (-(u * (g 0 0 - g 1 1))) * e01
  · linear_combination (-(X 1 0)) * hu + (u * (g 0 0 - g 1 1)) * e10 +
      (-(4 * u * g 1 0)) * e00
  · linear_combination (-(X 0 0 - X 1 1)) * hu + (4 * u * g 1 0) * e01

theorem mul_comm_of_mem_centralizer {γ : GL (Fin 2) A} (hγ : AutomorphicForm.IsRegularSemisimple γ)
    {s t : GL (Fin 2) A} (hs : s ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)))
    (ht : t ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) : s * t = t * s := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hs ht
  obtain ⟨u, hu⟩ := IsUnit.exists_left_inv hγ
  set g : Matrix (Fin 2) (Fin 2) A := (γ : Matrix (Fin 2) (Fin 2) A) with hg
  have hu' : u * ((g 0 0 - g 1 1) ^ 2 + 4 * g 0 1 * g 1 0) = 1 := by
    rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hu
    linear_combination hu
  have hsX : (s : Matrix (Fin 2) (Fin 2) A) * g = g * s := by
    simpa [hg] using congrArg Units.val hs
  have htX : (t : Matrix (Fin 2) (Fin 2) A) * g = g * t := by
    simpa [hg] using congrArg Units.val ht
  obtain ⟨a1, a2, a3⟩ := entries_of_commute g s hsX u hu'
  obtain ⟨b1, b2, b3⟩ := entries_of_commute g t htX u hu'
  set X : Matrix (Fin 2) (Fin 2) A := (s : Matrix (Fin 2) (Fin 2) A)
  set Y : Matrix (Fin 2) (Fin 2) A := (t : Matrix (Fin 2) (Fin 2) A)
  set p := u * (4 * g 1 0 * X 0 1 + (g 0 0 - g 1 1) * (X 0 0 - X 1 1))
  set q := u * (4 * g 1 0 * Y 0 1 + (g 0 0 - g 1 1) * (Y 0 0 - Y 1 1))
  apply Units.ext
  change X * Y = Y * X
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta,
    Fin.mk_one]
  · linear_combination (Y 1 0) * a1 + (p * g 0 1) * b2 - (X 1 0) * b1 - (q * g 0 1) * a2
  · linear_combination (X 0 0 - X 1 1) * b1 + (q * g 0 1) * a3 - (Y 0 0 - Y 1 1) * a1 -
      (p * g 0 1) * b3
  · linear_combination (Y 0 0 - Y 1 1) * a2 + (p * g 1 0) * b3 - (X 0 0 - X 1 1) * b2 -
      (q * g 1 0) * a3
  · linear_combination (Y 0 1) * a2 + (p * g 1 0) * b1 - (X 0 1) * b2 - (q * g 1 0) * a1

theorem forall_not_diagonal_of_not_isSquare {F : Type*} [Field F] (γ₀ : GL (Fin 2) F)
    (hns : ¬ IsSquare (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F))) :
    ∀ g : GL (Fin 2) F,
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) := by
  intro g ⟨h01, h10⟩
  apply hns
  have htr : Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) = Matrix.trace ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hdet : Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F) = Matrix.det ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) (Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F)),
      mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]
  rw [htr, hdet, Matrix.trace_fin_two, Matrix.det_fin_two, h01, h10]
  exact ⟨((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 -
    ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1, by ring⟩

end Algebra

theorem ellipticData (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z)) :
    ∃ (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (γ₀ : GL (Fin 2) (v.adicCompletion K)),
      u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ∧ AutomorphicForm.IsRegularSemisimple γ₀ ∧
      (∀ g : GL (Fin 2) (v.adicCompletion K),
        ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
           ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) ∧
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ₀ (u₀ * δ) := by
  obtain ⟨u₀, hu₀, γ₀, hreg, hns, hN⟩ :=
    AutomorphicForm.exists_mem_twistedCentralizer_isRegularSemisimple_not_isSquare_isNormOf_mul_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
      K L h2 σ hgen v c δ hδ hδq
  exact ⟨u₀, γ₀, hu₀, hreg, forall_not_diagonal_of_not_isSquare γ₀ hns, hN⟩

theorem approx (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (c : (v.adicCompletion K)ˣ)
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) :
    ∀ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
      ∃ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ ∧ AutomorphicForm.IsRegularSemisimple γ := by
  intro W hW
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K v
  have hϖ : Valued.v ((π : K) : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]; rfl
  obtain ⟨Y, γ, -, -, hγ, htend⟩ :=
    AutomorphicForm.exists_generator_and_seq_mem_localCentralizer_tendsto_scalar_of_forall_not_diagonal
      K v c _ hϖ γ₀ hγ₀ hns
  have hev : ∀ᶠ m in Filter.atTop, γ m ∈ W := htend hW
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨γ (max N 1), hN _ (le_max_left _ _), (hγ _ (le_max_right _ _)).1, (hγ _ (le_max_right _ _)).2.1⟩

theorem localCentralizer_eq (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (γ₀ γ : GL (Fin 2) (v.adicCompletion K)) (hγ₀ : AutomorphicForm.IsRegularSemisimple γ₀)
    (hγ : γ ∈ AutomorphicForm.localCentralizer K v γ₀) (hγreg : AutomorphicForm.IsRegularSemisimple γ) :
    AutomorphicForm.localCentralizer K v γ = AutomorphicForm.localCentralizer K v γ₀ := by
  have hγ₀' : γ₀ ∈ AutomorphicForm.localCentralizer K v γ := by
    show γ₀ ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (Subgroup.mem_centralizer_singleton_iff.mp hγ)
    exact this.symm
  have hγ₀'' : γ₀ ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) := hγ₀'
  have hγ'' : γ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) (v.adicCompletion K))) := hγ
  ext x
  constructor
  · intro hx
    have hx' : x ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))) := hx
    show x ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) (v.adicCompletion K)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_mem_centralizer hγreg hx' hγ₀''
  · intro hx
    have hx' : x ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) (v.adicCompletion K))) := hx
    show x ∈ Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_comm_of_mem_centralizer hγ₀ hx' hγ''

end FinTransportAlg

namespace FinTransport
open NumberField IsDedekindDomain AutomorphicForm FinTransportCC

section CongrT
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def congrCME {H H' : Subgroup G} (h : H = H') : H ≃ₜ* H' := by subst h; exact ContinuousMulEquiv.refl _

omit [IsTopologicalGroup G] in
theorem congrCME_coe {H H' : Subgroup G} (h : H = H') (x : H) : ((congrCME h x : H') : G) = (x : G) := by
  subst h; rfl

omit [IsTopologicalGroup G] in
theorem map_map_congrCME {H H' : Subgroup G} (h : H = H') {β : Type*} [MeasurableSpace β] (F : H' → β)
    (μ : @Measure H (borel H)) :
    @Measure.map H' β (borel H') _ F (@Measure.map H H' (borel H) (borel H') (congrCME h) μ) =
      @Measure.map H β (borel H) _ (F ∘ congrCME h) μ := by
  subst h
  have : (⇑(congrCME (rfl : H = H)) : H → H) = id := rfl
  rw [this, @Measure.map_id]
  rfl

end CongrT

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 3200000 in
theorem mainFT
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ') :
    ∃ (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (γ₀ : GL (Fin 2) (v.adicCompletion K))
      (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
      (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀)),
      u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ∧
      AutomorphicForm.IsRegularSemisimple γ₀ ∧
      (∀ g : GL (Fin 2) (v.adicCompletion K),
        ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
           ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) ∧
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ₀ (u₀ * δ) ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τS ∧
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT ∧

      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       ∀ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
       ∀ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
         ∃ u ∈ V, u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ∧
           AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) ∧
           ∃ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ ∧ AutomorphicForm.IsRegularSemisimple γ ∧
             AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ (u * δ) y₁ ∧
             ∃ (τγ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
               (τu : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u * δ))
                 (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ))),
               @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τγ ∧
               @Measure.IsHaarMeasure _ _ _
                 (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)) τu ∧
               (letI := AutomorphicForm.localCentralizerBorel K v γ
                letI := AutomorphicForm.localCentralizerBorel K v γ₀
                Measure.map Subtype.val τγ = Measure.map Subtype.val τT) ∧
               (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)
                letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
                Measure.map Subtype.val τu = Measure.map Subtype.val τS) ∧
               AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ (u * δ) y₁ τγ τu ∧
               (∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
                 ∃ J : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (u * δ) τu φv J)) ∧

      AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁ ∧
      (∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
            AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
          ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
            y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t) ∧
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT) := by

  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI : BorelSpace (GL (Fin 2) (v.adicCompletion K)) := borelSpace_localGLBorel K v
  haveI := t2Space_GL (v.adicCompletion K)
  haveI := secondCountableTopology_GL (v.adicCompletion K)
  haveI := locallyCompactSpace_GL (v.adicCompletion K)
  haveI := isTopologicalRing_tensor K L (v.adicCompletion K)
  haveI := t2Space_tensor K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensor K L (v.adicCompletion K)
  haveI := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI : BorelSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)

  obtain ⟨u₀, γ₀, hu₀, hγ₀, hns, hγ₀δ⟩ := FinTransportAlg.ellipticData K L h2 σ hgen v c δ hδ hδq
  obtain ⟨y₀, hy₀⟩ := hγ₀δ

  have hB₀ := mem_twistedCentralizer_iff_of_isNormConjugator K L (v.adicCompletion K) h2 σ hgen hγ₀ hy₀
  have hu₀' : u₀ ∈ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) :=
    mem_twistedCentralizer_mul_self K L (v.adicCompletion K) σ hu₀
  have hSle : twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ≤ twistedCentralizer K L (v.adicCompletion K) σ δ := by
    intro t ht
    obtain ⟨m, hm, rfl⟩ := (hB₀ t).1 ht
    obtain ⟨m₀, hm₀, hu₀eq⟩ := (hB₀ u₀).1 hu₀'
    refine mem_twistedCentralizer_of_commute K L (v.adicCompletion K) σ ht ?_
    rw [← hu₀eq]
    have hmm₀ : m * m₀ = m₀ * m := mul_comm_of_mem_centralizer hγ₀ hm hm₀
    calc y₀ * toTensorGL K L (v.adicCompletion K) m * y₀⁻¹ * (y₀ * toTensorGL K L (v.adicCompletion K) m₀ * y₀⁻¹)
        = y₀ * toTensorGL K L (v.adicCompletion K) (m * m₀) * y₀⁻¹ := by rw [map_mul]; group
      _ = y₀ * toTensorGL K L (v.adicCompletion K) (m₀ * m) * y₀⁻¹ := by rw [hmm₀]
      _ = y₀ * toTensorGL K L (v.adicCompletion K) m₀ * y₀⁻¹ * (y₀ * toTensorGL K L (v.adicCompletion K) m * y₀⁻¹) := by
          rw [map_mul]; group
  have hS : ∀ t, t ∈ twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
      ∃ m ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) (v.adicCompletion K))), y₀ * toTensorGL K L (v.adicCompletion K) m * y₀⁻¹ = t := by
    intro t
    rw [Subgroup.mem_inf, ← hB₀ t]
    exact ⟨fun h => h.2, fun h => ⟨hSle h, h⟩⟩
  have hTc : IsClosed ((localCentralizer K v γ₀ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := by
    show IsClosed (({γ₀} : Set (GL (Fin 2) (v.adicCompletion K))).centralizer)
    exact Set.isClosed_centralizer _
  have hScl : IsClosed ((twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) :
      Subgroup (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) : Set (GL (Fin 2) (L ⊗[K] v.adicCompletion K))) := by
    rw [Subgroup.coe_inf]
    exact (isClosed_twistedCentralizer K L (v.adicCompletion K) σ δ).inter (isClosed_twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ))
  obtain ⟨e₀, he₀⟩ := exists_continuousMulEquiv K L (v.adicCompletion K) (localCentralizer K v γ₀) hTc _ hScl y₀ hS

  letI mT : MeasurableSpace (localCentralizer K v γ₀) := localCentralizerBorel K v γ₀
  haveI : BorelSpace (localCentralizer K v γ₀) := ⟨rfl⟩
  letI mS : MeasurableSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
  haveI : BorelSpace ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (localCentralizer K v γ₀) := hTc.locallyCompactSpace
  set τT : Measure (localCentralizer K v γ₀) := Measure.haar with hτT
  set τS : Measure ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) :=
    Measure.map e₀ τT with hτSdef
  haveI hτS : τS.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τT e₀
  refine ⟨u₀, γ₀, y₀, τS, τT, hu₀, hγ₀, hns, ⟨y₀, hy₀⟩, hτS, inferInstance, ?_, hy₀, hS, ?_⟩
  ·
    intro W hW V hV
    obtain ⟨W₀, hW₀, hsweep⟩ :=
      AutomorphicForm.exists_nhds_forall_mem_localCentralizer_isNormConjugator_mul_of_isNormConjugator_mul
        K L σ v c δ hδ u₀ hu₀ γ₀ hγ₀ y₀ hy₀ V hV
    obtain ⟨γ, hγWW, hγT, hγreg⟩ := FinTransportAlg.approx K v c γ₀ hγ₀ hns (W ∩ W₀) (Filter.inter_mem hW hW₀)
    obtain ⟨u, huV, huδ, huu₀, hNreg, hNormu⟩ := hsweep γ hγWW.2 hγT hγreg
    refine ⟨u, huV, Subgroup.mem_inf.2 ⟨huδ, huu₀⟩, hNreg, γ, hγWW.1, hγT, hγreg, hNormu, ?_⟩

    have hTeq : localCentralizer K v γ = localCentralizer K v γ₀ := FinTransportAlg.localCentralizer_eq K v γ₀ γ hγ₀ hγT hγreg
    letI mγ : MeasurableSpace (localCentralizer K v γ) := localCentralizerBorel K v γ
    haveI : BorelSpace (localCentralizer K v γ) := ⟨rfl⟩
    set τγ : Measure (localCentralizer K v γ) := Measure.map (congrCME hTeq.symm) τT with hτγdef
    haveI hτγ : τγ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τT _

    have hBu := mem_twistedCentralizer_iff_of_isNormConjugator K L (v.adicCompletion K) h2 σ hgen hγreg hNormu
    have hTγc : IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := by
      show IsClosed (({γ} : Set (GL (Fin 2) (v.adicCompletion K))).centralizer)
      exact Set.isClosed_centralizer _
    have hTuc := isClosed_twistedCentralizer K L (v.adicCompletion K) σ (u * δ)
    obtain ⟨eu, heu⟩ := exists_continuousMulEquiv K L (v.adicCompletion K) (localCentralizer K v γ) hTγc _ hTuc y₀ hBu
    letI mu : MeasurableSpace (twistedCentralizer K L (v.adicCompletion K) σ (u * δ)) := twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)
    haveI : BorelSpace (twistedCentralizer K L (v.adicCompletion K) σ (u * δ)) := ⟨rfl⟩
    set τu : Measure (twistedCentralizer K L (v.adicCompletion K) σ (u * δ)) := Measure.map eu τγ with hτudef
    haveI hτu : τu.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τγ eu
    have hcompat : Measure.map Subtype.val τγ = Measure.map Subtype.val τT := by
      rw [hτγdef, map_map_congrCME]
      congr 1
      funext x
      exact congrCME_coe _ x
    refine ⟨τγ, τu, hτγ, hτu, hcompat, ?_, coupled_map K L (v.adicCompletion K) σ γ (u * δ) y₀ eu heu τγ, ?_⟩
    · rw [hτudef, hτSdef, map_val_map_eq K L (v.adicCompletion K) _ _ y₀ eu heu τγ,
        map_val_map_eq K L (v.adicCompletion K) _ _ y₀ e₀ he₀ τT, hcompat]
    · intro φv hφv
      exact AutomorphicForm.IsTwistedOrbitalIntegralOn.exists_of_isRegularSemisimple_normString_of_finrank_eq_two
        K L h2 σ hgen (v.adicCompletion K) (semiLocalHaar K L v) (u * δ) hNreg τu hτu φv hφv.2
  ·
    rw [hτSdef]
    have hm1 : Measurable fun t : ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
        y₀⁻¹ * (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₀ :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).measurable
    have hme₀ : Continuous (⇑e₀ : ↥(localCentralizer K v γ₀) → ↥(twistedCentralizer K L (v.adicCompletion K) σ δ ⊓ twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ))) := e₀.continuous
    rw [Measure.map_map hm1 hme₀.measurable]
    congr 1
    funext m
    simp only [Function.comp_apply, he₀]
    group

end FinTransport

end

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 800000

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ : AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ)
    (hδq : ∀ z : (L ⊗[K] v.adicCompletion K)ˣ,
      ¬ AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ') :
    ∃ (u₀ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (γ₀ : GL (Fin 2) (v.adicCompletion K))
      (y₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
      (τS : @Measure ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
          AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) (borel _))
      (τT : @Measure (AutomorphicForm.localCentralizer K v γ₀) (AutomorphicForm.localCentralizerBorel K v γ₀)),
      u₀ ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ∧
      AutomorphicForm.IsRegularSemisimple γ₀ ∧
      (∀ g : GL (Fin 2) (v.adicCompletion K),
        ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
           ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) ∧
      AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ₀ (u₀ * δ) ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τS ∧
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ₀) τT ∧

      (letI := AutomorphicForm.localGLBorel K v
       letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       ∀ W ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c : GL (Fin 2) (v.adicCompletion K)),
       ∀ V ∈ nhds (1 : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
         ∃ u ∈ V, u ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ∧
           AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ (u * δ)) ∧
           ∃ γ ∈ W, γ ∈ AutomorphicForm.localCentralizer K v γ₀ ∧ AutomorphicForm.IsRegularSemisimple γ ∧
             AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ (u * δ) y₁ ∧
             ∃ (τγ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
               (τu : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u * δ))
                 (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ))),
               @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τγ ∧
               @Measure.IsHaarMeasure _ _ _
                 (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)) τu ∧
               (letI := AutomorphicForm.localCentralizerBorel K v γ
                letI := AutomorphicForm.localCentralizerBorel K v γ₀
                Measure.map Subtype.val τγ = Measure.map Subtype.val τT) ∧
               (letI := AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (u * δ)
                letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
                    AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
                Measure.map Subtype.val τu = Measure.map Subtype.val τS) ∧
               AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ (u * δ) y₁ τγ τu ∧
               (∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
                 ∃ J : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ (u * δ) τu φv J)) ∧

      AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ₀ (u₀ * δ) y₁ ∧
      (∀ t : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        t ∈ AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
            AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ) ↔
          ∃ m ∈ AutomorphicForm.localCentralizer K v γ₀,
            y₁ * AutomorphicForm.toTensorGL K L (v.adicCompletion K) m * y₁⁻¹ = t) ∧
      (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
       letI := AutomorphicForm.localCentralizerBorel K v γ₀
       letI : MeasurableSpace ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
           AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) := borel _
       Measure.map (fun s : ↥(AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ ⊓
             AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (u₀ * δ)) =>
           y₁⁻¹ * (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * y₁) τS =
         Measure.map (fun m : ↥(AutomorphicForm.localCentralizer K v γ₀) =>
           AutomorphicForm.toTensorGL K L (v.adicCompletion K) (m : GL (Fin 2) (v.adicCompletion K))) τT) := FinTransport.mainFT K L h2 σ hgen v c δ hδ hδq τ' hτ'

end S_AutomorphicForm_exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two
end P2MW
export P2MW.S_AutomorphicForm_exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two (solution)
