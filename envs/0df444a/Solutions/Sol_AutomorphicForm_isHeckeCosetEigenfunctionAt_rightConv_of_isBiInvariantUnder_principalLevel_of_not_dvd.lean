-- Prove2me | solution 1 for AutomorphicForm.isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c7eb93b9-2854-5483-8589-c3da39f544e6

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_GelfandInvolution
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_localRep_heckeGen
import Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Theorems.Thm_LocalGL2_existsUnique_mem_doubleCoset_zpow
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd

set_option autoImplicit false

open HeckePair HeckeIntegralSeam

namespace P2mConvHecke

section Abstract

variable {G : Type*} [Group G] {U : Subgroup G}

theorem inv_mem_doubleCoset_inv {g x : G} (hx : x ∈ doubleCoset U g) : x⁻¹ ∈ doubleCoset U g⁻¹ := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  exact mem_doubleCoset_iff.mpr ⟨v⁻¹, inv_mem hv, u⁻¹, inv_mem hu, by group⟩

theorem isHeckeCosetSystem_of_doubleCoset_eq {g g' : G} {ι : Type*} {r : ι → G}
    (h : doubleCoset U g = doubleCoset U g') (hr : IsHeckeCosetSystem U g r) :
    IsHeckeCosetSystem U g' r := by
  refine ⟨fun i => ?_, fun x hx => ?_, hr.mk_injective⟩
  · rw [← h]; exact hr.mem_doubleCoset i
  · rw [← h] at hx; exact hr.covers x hx

theorem cosetSystem_comp_equiv {g : G} {ι κ : Type*} {r : ι → G} (hr : IsHeckeCosetSystem U g r)
    (e : κ ≃ ι) : IsHeckeCosetSystem U g (r ∘ e) := by
  refine ⟨fun i => hr.mem_doubleCoset (e i), fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨i, hi⟩ := hr.covers x hx
    exact ⟨e.symm i, by simpa using hi⟩
  · exact e.injective (hr.mk_injective hij)

theorem cosetSystem_const_mul {g : G} {ι : Type*} {r : ι → G} (hr : IsHeckeCosetSystem U g r)
    {u : G} (hu : u ∈ U) : IsHeckeCosetSystem U g (fun i => u * r i) := by
  refine ⟨fun i => mul_mem_doubleCoset (hr.mem_doubleCoset i) hu, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨i, hi⟩ := hr.covers (u⁻¹ * x) (mul_mem_doubleCoset hx (inv_mem hu))
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi
  · apply hr.mk_injective
    have hij' : (QuotientGroup.mk (u * r i) : G ⧸ U) = QuotientGroup.mk (u * r j) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hij'

theorem mem_doubleCoset_central_mul_iff {c g x : G} (hc : c ∈ Subgroup.center G) :
    x ∈ doubleCoset U (c * g) ↔ c⁻¹ * x ∈ doubleCoset U g := by
  have hc' : ∀ y : G, y * c = c * y := Subgroup.mem_center_iff.mp hc
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
    refine mem_doubleCoset_iff.mpr ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, hc' u]; simp only [mul_assoc],
      inv_mul_cancel_left]
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := mem_doubleCoset_iff.mp hx
    refine mem_doubleCoset_iff.mpr ⟨u, hu, v, hv, ?_⟩
    rw [show u * (c * g) * v = c * (u * g * v) by rw [← mul_assoc, hc' u]; simp only [mul_assoc], huv,
      mul_inv_cancel_left]

theorem cosetSystem_central_mul {g c : G} (hc : c ∈ Subgroup.center G) {ι : Type*} {r : ι → G}
    (hr : IsHeckeCosetSystem U g r) : IsHeckeCosetSystem U (c * g) (fun i => c * r i) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  · rw [mem_doubleCoset_central_mul_iff hc, inv_mul_cancel_left]; exact hr.mem_doubleCoset i
  · rw [mem_doubleCoset_central_mul_iff hc] at hx
    obtain ⟨i, hi⟩ := hr.covers _ hx
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hi
  · apply hr.mk_injective
    have hij' : (QuotientGroup.mk (c * r i) : G ⧸ U) = QuotientGroup.mk (c * r j) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hij'

theorem cosetSystem_tau_inv {τ : G → G} (hτ : IsGelfandInvolution U τ) {g : G} {ι : Type*}
    {r : ι → G} (hr : IsHeckeCosetSystem U g r) :
    IsHeckeCosetSystem U g⁻¹ (fun i => (τ (r i))⁻¹) := by
  have hτg : ∀ {x}, x ∈ doubleCoset U g → τ x ∈ doubleCoset U g := fun {x} hx => by
    rw [← doubleCoset_eq_of_mem hx]; exact hτ.mem_doubleCoset x
  refine ⟨fun i => inv_mem_doubleCoset_inv (hτg (hr.mem_doubleCoset i)), fun y hy => ?_, fun i j hij => ?_⟩
  · have hy' : τ y⁻¹ ∈ doubleCoset U g := by
      have := inv_mem_doubleCoset_inv hy
      rw [inv_inv] at this
      exact hτg this
    obtain ⟨i, hi⟩ := hr.covers _ hy'
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢

    have h1 : τ (r i) * y ∈ U := by
      have := hτ.map_mem _ hi
      rwa [hτ.map_mul, hτ.map_inv, hτ.involutive, inv_inv] at this
    have h2 : y⁻¹ * (τ (r i))⁻¹ = (τ (r i) * y)⁻¹ := by rw [mul_inv_rev]
    rw [h2]
    exact inv_mem h1
  · apply hr.mk_injective
    have hij' : (QuotientGroup.mk (τ (r i))⁻¹ : G ⧸ U) = QuotientGroup.mk (τ (r j))⁻¹ := hij
    rw [QuotientGroup.eq] at hij' ⊢
    rw [inv_inv, ← hτ.map_inv, ← hτ.map_mul] at hij'
    have := hτ.map_mem _ hij'
    rw [hτ.involutive] at this

    have h3 : (r i)⁻¹ * r j = ((r j)⁻¹ * r i)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [h3]
    exact inv_mem this

theorem apply_tau_of_biInvariant {τ : G → G} (hτ : IsGelfandInvolution U τ) {M : Type*} (ψ : G → M)
    (hl : ∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) (hr : ∀ u ∈ U, ∀ x, ψ (x * u) = ψ x) (x : G) :
    ψ (τ x) = ψ x := by
  obtain ⟨u, hu, v, hv, huv⟩ := mem_doubleCoset_iff.mp (hτ.mem_doubleCoset x)
  rw [← huv, hr v hv, hl u hu]

theorem sum_apply_inv_mul_eq_sum_apply_mul_inv {τ : G → G} (hτ : IsGelfandInvolution U τ) {t : G}
    {n : ℕ} {ε : Fin n → G} (hε : IsHeckeCosetSystem U t ε)
    (hε' : IsHeckeCosetSystem U t⁻¹ (fun i => (ε i)⁻¹))
    (ψ : G → ℂ) (hl : ∀ u ∈ U, ∀ x, ψ (u * x) = ψ x) (hr : ∀ u ∈ U, ∀ x, ψ (x * u) = ψ x) (h : G) :
    ∑ i, ψ ((ε i)⁻¹ * h) = ∑ i, ψ (h * (ε i)⁻¹) := by

  set ψt : G → ℂ := fun y => ψ y⁻¹ with hψt_def
  have hψt : ∀ y : G, ∀ u ∈ U, ψt (y * u) = ψt y := fun y u hu => by
    simp only [hψt_def, mul_inv_rev]; exact hl _ (inv_mem hu) _
  have hF : ∀ x, ∑ i, ψ ((ε i)⁻¹ * x) = ∑ i, ψt (x⁻¹ * ε i) := fun x => by
    simp only [hψt_def, mul_inv_rev, inv_inv]

  have hFl : ∀ u ∈ U, ∀ x, ∑ i, ψ ((ε i)⁻¹ * (u * x)) = ∑ i, ψ ((ε i)⁻¹ * x) := by
    intro u hu x
    rw [hF, hF, mul_inv_rev]
    have := heckeCosetSum_eq_of_isHeckeCosetSystem hε (cosetSystem_const_mul hε (inv_mem hu)) hψt x⁻¹
    simpa only [mul_assoc] using this
  have hFr : ∀ u ∈ U, ∀ x, ∑ i, ψ ((ε i)⁻¹ * (x * u)) = ∑ i, ψ ((ε i)⁻¹ * x) := by
    intro u hu x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_assoc]; exact hr u hu _

  have hFτ : ∑ i, ψ ((ε i)⁻¹ * τ h) = ∑ i, ψ ((ε i)⁻¹ * h) :=
    apply_tau_of_biInvariant hτ (fun x => ∑ i, ψ ((ε i)⁻¹ * x)) hFl hFr h
  rw [← hFτ]

  have h1 : ∀ i, ψ ((ε i)⁻¹ * τ h) = ψ (h * (τ (ε i))⁻¹) := by
    intro i
    rw [← apply_tau_of_biInvariant hτ ψ hl hr ((ε i)⁻¹ * τ h), hτ.map_mul, hτ.involutive, hτ.map_inv]
  simp_rw [h1]

  exact heckeCosetSum_eq_of_isHeckeCosetSystem hε' (cosetSystem_tau_inv hτ hε) (fun y u hu => hr u hu y) h

end Abstract

section Transfer

variable {G H : Type*} [Group G] [Group H] (ι : H →* G) (loc : G →* H) (U : Subgroup G) (K : Subgroup H)

theorem isHeckeCosetSystem_of_comp (hli : ∀ h, loc (ι h) = h) (hUK : ∀ u ∈ U, loc u ∈ K)
    (hKU : ∀ k ∈ K, ι k ∈ U) {P : H} {κ : Type*} {ε : κ → H}
    (hε : IsHeckeCosetSystem U (ι P) (fun i => ι (ε i))) : IsHeckeCosetSystem K P ε := by
  refine ⟨fun i => ?_, fun y hy => ?_, fun i j hij => ?_⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := mem_doubleCoset_iff.mp (hε.mem_doubleCoset i)
    refine mem_doubleCoset_iff.mpr ⟨loc u, hUK u hu, loc v, hUK v hv, ?_⟩
    have := congrArg loc huv
    simpa only [map_mul, hli] using this
  · obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := mem_doubleCoset_iff.mp hy
    have hy' : ι (k₁ * P * k₂) ∈ doubleCoset U (ι P) := by
      rw [map_mul, map_mul]
      exact mem_doubleCoset_iff.mpr ⟨ι k₁, hKU k₁ hk₁, ι k₂, hKU k₂ hk₂, rfl⟩
    obtain ⟨i, hi⟩ := hε.covers _ hy'
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have := hUK _ hi
    rwa [← map_inv, ← map_mul, hli] at this
  · apply hε.mk_injective
    have hij' : (QuotientGroup.mk (ε i) : H ⧸ K) = QuotientGroup.mk (ε j) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    have := hKU _ hij'
    rwa [map_mul, map_inv] at this

theorem isHeckeCosetSystem_comp (hli : ∀ h, loc (ι h) = h) (hUK : ∀ u ∈ U, loc u ∈ K)
    (hKU : ∀ k ∈ K, ι k ∈ U)
    (hfac : ∀ u ∈ U, ∃ k ∈ K, ∃ u' ∈ U, u = ι k * u' ∧ ∀ h : H, ι h * u' = u' * ι h)
    {P : H} {κ : Type*} {ε : κ → H} (hε : IsHeckeCosetSystem K P ε) :
    IsHeckeCosetSystem U (ι P) (fun i => ι (ε i)) := by
  refine ⟨fun i => ?_, fun x hx => ?_, fun i j hij => ?_⟩
  · obtain ⟨u, hu, v, hv, huv⟩ := mem_doubleCoset_iff.mp (hε.mem_doubleCoset i)
    refine mem_doubleCoset_iff.mpr ⟨ι u, hKU u hu, ι v, hKU v hv, ?_⟩
    rw [← map_mul, ← map_mul, huv]
  · obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_doubleCoset_iff.mp hx
    obtain ⟨k, hk, u', hu', rfl, hcomm⟩ := hfac u₁ hu₁
    have hkP : k * P ∈ doubleCoset K P := mem_doubleCoset_iff.mpr ⟨k, hk, 1, one_mem _, by rw [mul_one]⟩
    obtain ⟨i, hi⟩ := hε.covers _ hkP
    refine ⟨i, ?_⟩
    rw [QuotientGroup.eq] at hi ⊢
    have h1 : ι k * u' * ι P * u₂ = ι (k * P) * (u' * u₂) := by
      rw [map_mul, mul_assoc (ι k) u', ← hcomm P]; simp only [mul_assoc]
    rw [h1, mul_inv_rev, mul_assoc]
    refine mul_mem (inv_mem (mul_mem hu' hu₂)) ?_
    have := hKU _ hi
    rwa [map_mul, map_inv] at this
  · apply hε.mk_injective
    have hij' : (QuotientGroup.mk (ι (ε i)) : G ⧸ U) = QuotientGroup.mk (ι (ε j)) := hij
    rw [QuotientGroup.eq] at hij' ⊢
    have := hUK _ hij'
    rwa [← map_inv, ← map_mul, hli] at this

end Transfer

section Local

open LocalGL2

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable (ϖ : R)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem transposeGL_diagPi (hϖ0 : algebraMap R K ϖ ≠ 0) : transposeGL (diagPi ϖ hϖ0 : GL (Fin 2) K) = diagPi ϖ hϖ0 := by
  refine Units.ext ?_
  rw [transposeGL_val, coe_diagPi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem transposeGL_localRepInf (hϖ0 : algebraMap R K ϖ ≠ 0) : transposeGL (localRepInf ϖ hϖ0 : GL (Fin 2) K) = localRepInf ϖ hϖ0 := by
  refine Units.ext ?_
  rw [transposeGL_val, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def transposeOp (A : Type*) [CommRing A] : GL (Fin 2) A →* (GL (Fin 2) A)ᵐᵒᵖ where
  toFun x := MulOpposite.op (transposeGL x)
  map_one' := by rw [transposeGL_one, MulOpposite.op_one]
  map_mul' x y := by rw [transposeGL_mul, MulOpposite.op_mul]

theorem transposeGL_zpow {A : Type*} [CommRing A] (x : GL (Fin 2) A) (n : ℤ) :
    transposeGL (x ^ n) = transposeGL x ^ n := by
  apply MulOpposite.op_injective
  rw [MulOpposite.op_zpow]
  exact map_zpow (transposeOp A) x n

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem commute_diagPi_localRepInf (hϖ0 : algebraMap R K ϖ ≠ 0) : Commute (diagPi ϖ hϖ0) (localRepInf ϖ hϖ0 : GL (Fin 2) K) := by
  show diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 = localRepInf ϖ hϖ0 * diagPi ϖ hϖ0
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Units.val_mul, coe_diagPi, coe_localRepInf]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem isGelfandInvolution_transposeGL (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) :
    IsGelfandInvolution (integralSubgroup R K) (transposeGL (A := K)) := by
  refine IsGelfandInvolution.of_forall_exists_fixedRep transposeGL_mul transposeGL_involutive
    (fun u hu => transposeGL_mem_integralSubgroup hu) fun g => ?_
  obtain ⟨⟨a, b⟩, ⟨-, hmem⟩, -⟩ := LocalGL2.existsUnique_mem_doubleCoset_zpow ϖ hϖ0 hϖ g
  refine ⟨diagPi ϖ hϖ0 ^ a * localRepInf ϖ hϖ0 ^ b, ?_, hmem⟩
  rw [transposeGL_mul, transposeGL_zpow, transposeGL_zpow, transposeGL_diagPi, transposeGL_localRepInf]
  exact ((commute_diagPi_localRepInf ϖ hϖ0).zpow_zpow a b).eq.symm

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem coe_diagPi_mul_localRepInf (hϖ0 : algebraMap R K ϖ ≠ 0) :
    ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      algebraMap R K ϖ • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [Units.val_mul, coe_diagPi, coe_localRepInf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem diagPi_mul_localRepInf_mem_center (hϖ0 : algebraMap R K ϖ ≠ 0) :
    diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 ∈ Subgroup.center (GL (Fin 2) K) := by
  have h := coe_diagPi_mul_localRepInf ϖ hϖ0 (K := K)
  set z : GL (Fin 2) K := diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 with hz
  clear_value z
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, h, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
theorem weylInt_mul_self : weylInt R K * weylInt R K = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [Units.val_mul, coe_weylInt]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem weylInt_conj_diagPi (hϖ0 : algebraMap R K ϖ ≠ 0) :
    weylInt R K * diagPi ϖ hϖ0 * (weylInt R K)⁻¹ =
      diagPi ϖ hϖ0 * localRepInf ϖ hϖ0 * (diagPi ϖ hϖ0)⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right (weylInt_mul_self (R := R) (K := K)),
    (commute_diagPi_localRepInf ϖ hϖ0).eq, mul_inv_cancel_right]
  rfl

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in

theorem doubleCoset_zinv_mul_diagPi_eq (hϖ0 : algebraMap R K ϖ ≠ 0) :
    doubleCoset (integralSubgroup R K) ((diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * diagPi ϖ hϖ0) =
      doubleCoset (integralSubgroup R K) (diagPi ϖ hϖ0)⁻¹ := by
  have h1 : (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0)⁻¹ * diagPi ϖ hϖ0 = (localRepInf ϖ hϖ0 : GL (Fin 2) K)⁻¹ := by
    rw [mul_inv_rev, inv_mul_cancel_right]
  rw [h1]
  apply doubleCoset_eq_of_mem

  refine mem_doubleCoset_iff.mpr ⟨weylInt R K, weylInt_mem, weylInt R K, weylInt_mem, ?_⟩
  show weylInt R K * (diagPi ϖ hϖ0)⁻¹ * weylInt R K = (weylInt R K * diagPi ϖ hϖ0 * weylInt R K)⁻¹
  rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right (weylInt_mul_self (R := R) (K := K)), mul_assoc]

end Local

section Adelic

open NumberField IsDedekindDomain AutomorphicForm AdelicDock NumberField.AdelicLevel LocalGL2

variable (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L))

noncomputable abbrev emb : GL (Fin 2) (w.adicCompletion L) →* AdelicGL2 (𝓞 L) L :=
  (finEmbed (𝓞 L) L).comp (localEmbed (𝓞 L) L w)

noncomputable abbrev loc : AdelicGL2 (𝓞 L) L →* GL (Fin 2) (w.adicCompletion L) :=
  (finComponent (𝓞 L) L w).comp (glFin (𝓞 L) L)

theorem loc_emb (h : GL (Fin 2) (w.adicCompletion L)) : loc L w (emb L w h) = h := by
  simp only [MonoidHom.comp_apply, glFin_finEmbed, finComponent_localEmbed_self]

theorem glArch_emb (h : GL (Fin 2) (w.adicCompletion L)) : glArch (𝓞 L) L (emb L w h) = 1 :=
  glArch_finEmbed _ _ _

theorem finComponent_emb_of_ne (h : GL (Fin 2) (w.adicCompletion L)) {u : HeightOneSpectrum (𝓞 L)}
    (hu : u ≠ w) : finComponent (𝓞 L) L u (glFin (𝓞 L) L (emb L w h)) = 1 := by
  simp only [MonoidHom.comp_apply, glFin_finEmbed]
  exact finComponent_localEmbed_of_ne _ _ _ _ hu

theorem ext_of_components {a b : AdelicGL2 (𝓞 L) L} (h₁ : glArch (𝓞 L) L a = glArch (𝓞 L) L b)
    (h₂ : ∀ u : HeightOneSpectrum (𝓞 L),
      finComponent (𝓞 L) L u (glFin (𝓞 L) L a) = finComponent (𝓞 L) L u (glFin (𝓞 L) L b)) :
    a = b := by
  apply Units.ext
  apply matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L
  · exact congrArg (fun x : GL (Fin 2) (InfiniteAdeleRing L) => (x : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))) h₁
  · apply matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L
    intro u
    exact congrArg (fun x : GL (Fin 2) (u.adicCompletion L) => (x : Matrix (Fin 2) (Fin 2) (u.adicCompletion L))) (h₂ u)

theorem emb_mul_eq_mul_emb_of_loc_eq_one {y : AdelicGL2 (𝓞 L) L} (hy : loc L w y = 1)
    (h : GL (Fin 2) (w.adicCompletion L)) : emb L w h * y = y * emb L w h := by
  apply ext_of_components L
  · rw [map_mul, map_mul, glArch_emb, one_mul, mul_one]
  · intro u
    rw [map_mul, map_mul, map_mul, map_mul]
    by_cases hu : u = w
    · subst hu
      have h1 : finComponent (𝓞 L) L u (glFin (𝓞 L) L (emb L u h)) = h := loc_emb L u h
      have h2 : finComponent (𝓞 L) L u (glFin (𝓞 L) L y) = 1 := hy
      rw [h1, h2, mul_one, one_mul]
    · rw [finComponent_emb_of_ne L w h hu, one_mul, mul_one]

noncomputable def cof (y : AdelicGL2 (𝓞 L) L) : AdelicGL2 (𝓞 L) L := (emb L w (loc L w y))⁻¹ * y

theorem loc_cof (y : AdelicGL2 (𝓞 L) L) : loc L w (cof L w y) = 1 := by
  rw [cof, map_mul, map_inv, loc_emb, inv_mul_cancel]

theorem emb_loc_mul_cof (y : AdelicGL2 (𝓞 L) L) : emb L w (loc L w y) * cof L w y = y := by
  rw [cof, mul_inv_cancel_left]

theorem loc_mem_integralSubgroup {M : Ideal (𝓞 L)} {u : AdelicGL2 (𝓞 L) L} (hu : u ∈ levelOne (𝓞 L) L M) :
    loc L w u ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L) := by
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) :=
    Subtype.val_injective
  have hrange : Set.range (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) =
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := Subtype.range_val
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj]
  simp only [hrange, SetLike.mem_coe]
  have h1 := mem_levelOne_iff.mp hu
  refine ⟨fun i j => h1.1.integral i j w, fun i j => ?_⟩
  have h2 : (loc L w u)⁻¹ = finComponent (𝓞 L) L w (glFin (𝓞 L) L u)⁻¹ := by
    rw [MonoidHom.comp_apply, ← map_inv]
  rw [h2]
  exact h1.2.integral i j w

theorem entries_mem_of_mem_integralSubgroup {k : GL (Fin 2) (w.adicCompletion L)}
    (hk : k ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L)) :
    (∀ i j, (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈ w.adicCompletionIntegers L) ∧
    (∀ i j, ((k⁻¹ : GL (Fin 2) (w.adicCompletion L)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) i j ∈
      w.adicCompletionIntegers L) := by
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) :=
    Subtype.val_injective
  have hrange : Set.range (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)) =
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := Subtype.range_val
  rw [FLT.SpectralSide.mem_integralSubgroup_iff_entries_mem hinj] at hk
  simpa only [hrange, SetLike.mem_coe] using hk

omit [NumberField L] in
theorem ne_bot_of_not_dvd {M : Ideal (𝓞 L)} (hwM : ¬ w.asIdeal ∣ M) : M ≠ ⊥ := by
  rintro rfl
  exact hwM ⟨⊥, by rw [Ideal.mul_bot]⟩

theorem emb_mem_levelOne_inf {M : Ideal (𝓞 L)} (hwM : ¬ w.asIdeal ∣ M)
    {k : GL (Fin 2) (w.adicCompletion L)}
    (hk : k ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L)) :
    emb L w k ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L := by
  have hM : M ≠ ⊥ := ne_bot_of_not_dvd L w hwM
  have hb : idealBound (𝓞 L) M w = 1 := idealBound_eq_one_of_not_dvd hM hwM
  have hent := entries_mem_of_mem_integralSubgroup L w hk
  have aux : ∀ m : Matrix (Fin 2) (Fin 2) (w.adicCompletion L),
      (∀ i j, m i j ∈ w.adicCompletionIntegers L) → IsLocalLevelOne (𝓞 L) L w M m := fun m hm =>
    ⟨hm, by rw [hb]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hm 1 0),
      by rw [hb]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (sub_mem (hm 1 1) (one_mem _))⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [MonoidHom.comp_apply, finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff, mem_localLevelOne_iff]
    exact ⟨aux _ hent.1, aux _ hent.2⟩
  · rw [mem_finiteAdelicGL2Subgroup_iff, MonoidHom.comp_apply, glArch_finEmbed]

theorem levelOne_factor {M : Ideal (𝓞 L)} (hwM : ¬ w.asIdeal ∣ M) (u : AdelicGL2 (𝓞 L) L)
    (hu : u ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) :
    ∃ k ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L),
      ∃ u' ∈ levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L,
        u = emb L w k * u' ∧ ∀ h : GL (Fin 2) (w.adicCompletion L), emb L w h * u' = u' * emb L w h := by
  have hk := loc_mem_integralSubgroup L w (Subgroup.mem_inf.mp hu).1
  exact ⟨loc L w u, hk, cof L w u, mul_mem (inv_mem (emb_mem_levelOne_inf L w hwM hk)) hu,
    (emb_loc_mul_cof L w u).symm, fun h => emb_mul_eq_mul_emb_of_loc_eq_one L w (loc_cof L w u) h⟩

theorem map_weylMatrix {A B : Type*} [Semiring A] [Semiring B] (f : A →+* B) :
    (!![(0 : A), 1; 1, 0] : Matrix (Fin 2) (Fin 2) A).map f = !![(0 : B), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem weylMatrix_mul_self {A : Type*} [Semiring A] :
    (!![(0 : A), 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) * !![(0 : A), 1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_mul_emb (k : GL (Fin 2) (w.adicCompletion L)) :
    weyl (𝓞 L) L * emb L w k =
      emb L w (weylInt (w.adicCompletionIntegers L) (w.adicCompletion L) * k *
        weylInt (w.adicCompletionIntegers L) (w.adicCompletion L)) * weyl (𝓞 L) L := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show _ * (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w k) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) =
    (finEmbed (𝓞 L) L (localEmbed (𝓞 L) L w
      (weylInt (w.adicCompletionIntegers L) (w.adicCompletion L) * k *
        weylInt (w.adicCompletionIntegers L) (w.adicCompletion L))) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) * _
  rw [coe_finEmbed, coe_localEmbed, coe_finEmbed, coe_localEmbed]
  have hw : ((weyl (𝓞 L) L : GL (Fin 2) (AdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))
      = !![0, 1; 1, 0] := rfl
  have hk : ((weylInt (w.adicCompletionIntegers L) (w.adicCompletion L) * k *
        weylInt (w.adicCompletionIntegers L) (w.adicCompletion L) : GL (Fin 2) (w.adicCompletion L)) :
        Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) =
        !![0, 1; 1, 0] * (k : Matrix (Fin 2) (Fin 2) (w.adicCompletion L)) * !![0, 1; 1, 0] := by
    rw [Units.val_mul, Units.val_mul, coe_weylInt]
  rw [hw, hk]
  refine matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 L) L ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, mapMatrix_arch_finMat, mul_one, one_mul]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat, mapMatrix_fin_finMat, RingHom.mapMatrix_apply, map_weylMatrix]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq (𝓞 L) L fun w' => ?_
    rw [map_mul, map_mul, RingHom.mapMatrix_apply (M := !![(0 : FiniteAdeleRing (𝓞 L) L), 1; 1, 0]),
      map_weylMatrix]
    by_cases hw' : w' = w
    · subst hw'
      rw [mapMatrix_localMat_self, mapMatrix_localMat_self, Matrix.mul_assoc, Matrix.mul_assoc,
        weylMatrix_mul_self, Matrix.mul_one]
    · rw [mapMatrix_localMat_of_ne (𝓞 L) L w _ hw', mapMatrix_localMat_of_ne (𝓞 L) L w _ hw', mul_one, one_mul]

theorem loc_mem_integralSubgroup_of_mem_principalLevel {M : Ideal (𝓞 L)} {u : AdelicGL2 (𝓞 L) L}
    (hu : u ∈ principalLevel (𝓞 L) L M) :
    loc L w u ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L) :=
  loc_mem_integralSubgroup L w (principalLevel_le_levelOne (𝓞 L) L M hu)

theorem emb_mem_principalLevel_inf {M : Ideal (𝓞 L)} (hwM : ¬ w.asIdeal ∣ M)
    {k : GL (Fin 2) (w.adicCompletion L)}
    (hk : k ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L)) :
    emb L w k ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L := by
  obtain ⟨h₁, hfin⟩ := Subgroup.mem_inf.mp (emb_mem_levelOne_inf L w hwM hk)
  refine Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 L) L M).mpr ⟨h₁, ?_⟩, hfin⟩
  set W := weylInt (w.adicCompletionIntegers L) (w.adicCompletion L) with hW
  have hWm : W ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L) := weylInt_mem
  have hk' : W * k * W ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L) :=
    mul_mem (mul_mem hWm hk) hWm
  refine Subgroup.mem_map.mpr ⟨emb L w (W * k * W), (Subgroup.mem_inf.mp (emb_mem_levelOne_inf L w hwM hk')).1, ?_⟩
  show weyl (𝓞 L) L * emb L w (W * k * W) * (weyl (𝓞 L) L)⁻¹ = emb L w k
  rw [weyl_mul_emb, mul_inv_cancel_right, hW, ← mul_assoc, ← mul_assoc, weylInt_mul_self, one_mul, mul_assoc,
    weylInt_mul_self, mul_one]

theorem principalLevel_factor {M : Ideal (𝓞 L)} (hwM : ¬ w.asIdeal ∣ M) (u : AdelicGL2 (𝓞 L) L)
    (hu : u ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) :
    ∃ k ∈ integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L),
      ∃ u' ∈ principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L,
        u = emb L w k * u' ∧ ∀ h : GL (Fin 2) (w.adicCompletion L), emb L w h * u' = u' * emb L w h := by
  have hk := loc_mem_integralSubgroup_of_mem_principalLevel L w (Subgroup.mem_inf.mp hu).1
  exact ⟨loc L w u, hk, cof L w u, mul_mem (inv_mem (emb_mem_principalLevel_inf L w hwM hk)) hu,
    (emb_loc_mul_cof L w u).symm, fun h => emb_mul_eq_mul_emb_of_loc_eq_one L w (loc_cof L w u) h⟩

theorem irreducible_of_valued_eq_exp_neg_one {ϖ : w.adicCompletionIntegers L}
    (hv : Valued.v ((ϖ : w.adicCompletionIntegers L) : w.adicCompletion L) = WithZero.exp (-1 : ℤ)) :
    Irreducible ϖ := by
  have hunit : ∀ a : w.adicCompletionIntegers L,
      IsUnit a ↔ Valued.v ((a : w.adicCompletionIntegers L) : w.adicCompletion L) = 1 := fun a =>
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [hunit, hv, WithZero.exp_eq_one] at hu
    omega
  · by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    rw [hunit] at ha hb
    have ha1 : Valued.v ((a : w.adicCompletionIntegers L) : w.adicCompletion L) < 1 := lt_of_le_of_ne a.2 ha
    have hb1 : Valued.v ((b : w.adicCompletionIntegers L) : w.adicCompletion L) < 1 := lt_of_le_of_ne b.2 hb
    have hprod : Valued.v ((a : w.adicCompletionIntegers L) : w.adicCompletion L) *
        Valued.v ((b : w.adicCompletionIntegers L) : w.adicCompletion L) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hv, hab]; rfl
    have ha0 : Valued.v ((a : w.adicCompletionIntegers L) : w.adicCompletion L) ≠ 0 := by
      intro h; rw [h, zero_mul] at hprod; exact WithZero.exp_ne_zero hprod.symm
    have hb0 : Valued.v ((b : w.adicCompletionIntegers L) : w.adicCompletion L) ≠ 0 := by
      intro h; rw [h, mul_zero] at hprod; exact WithZero.exp_ne_zero hprod.symm
    have hla : WithZero.log (Valued.v ((a : w.adicCompletionIntegers L) : w.adicCompletion L)) < 0 := by
      rwa [WithZero.log_lt_iff_lt_exp ha0, WithZero.exp_zero]
    have hlb : WithZero.log (Valued.v ((b : w.adicCompletionIntegers L) : w.adicCompletion L)) < 0 := by
      rwa [WithZero.log_lt_iff_lt_exp hb0, WithZero.exp_zero]
    have hsum := congrArg WithZero.log hprod
    rw [WithZero.log_mul ha0 hb0, WithZero.log_exp] at hsum
    omega

end Adelic

section Main

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm AdelicDock NumberField.AdelicLevel NumberField.AdelicHaar LocalGL2

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem integrable_mul_of_continuous (L : Type) [Field L] [NumberField L]
    (F φ : AdelicGL2 (𝓞 L) L → ℂ) (hF : Continuous F) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => F x * φ x) (adelicGLHaar (Fin 2) (𝓞 L) L) := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  exact (hF.mul hφ).integrable_of_hasCompactSupport hφc.mul_left

theorem mainB (L : Type) [Field L] [NumberField L]
    (N₁ N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (hw₁ : ¬ w.asIdeal ∣ N₁) (hw : ¬ w.asIdeal ∣ N)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v)
    (hvU : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L,
      v (g * u) = v g)
    (a : ℂ)
    (ha : SmoothCusp.IsHeckeCosetEigenfunctionAt L (principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w v a) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w (rightConv L v φ) a := by
  classical
  obtain ⟨r', hr', hr'eq⟩ := ha

  obtain ⟨ϖ, hϖ0, hval, hgen, sec, -, hsys⟩ := HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen L w
  have hϖ : Irreducible ϖ := irreducible_of_valued_eq_exp_neg_one L w hval
  set Kw := integralSubgroup (w.adicCompletionIntegers L) (w.adicCompletion L) with hKw
  set P : GL (Fin 2) (w.adicCompletion L) := diagPi ϖ hϖ0 with hP
  set UN := principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L with hUN
  set UN₁ := principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L with hUN₁
  set UNo := levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L with hUNo
  have ht : heckeGen (𝓞 L) L w = emb L w P := hgen.symm
  rw [ht] at hr'

  have hli := loc_emb L w
  have hUK : ∀ u ∈ UN, loc L w u ∈ Kw := fun u hu =>
    loc_mem_integralSubgroup_of_mem_principalLevel L w (Subgroup.mem_inf.mp hu).1
  have hUK₁ : ∀ u ∈ UN₁, loc L w u ∈ Kw := fun u hu =>
    loc_mem_integralSubgroup_of_mem_principalLevel L w (Subgroup.mem_inf.mp hu).1
  have hUKo : ∀ u ∈ UNo, loc L w u ∈ Kw := fun u hu => loc_mem_integralSubgroup L w (Subgroup.mem_inf.mp hu).1
  have hKU : ∀ k ∈ Kw, emb L w k ∈ UN := fun k hk => emb_mem_principalLevel_inf L w hw hk
  have hKU₁ : ∀ k ∈ Kw, emb L w k ∈ UN₁ := fun k hk => emb_mem_principalLevel_inf L w hw₁ hk
  have hKUo : ∀ k ∈ Kw, emb L w k ∈ UNo := fun k hk => emb_mem_levelOne_inf L w hw hk
  have hfac := principalLevel_factor L w hw
  have hfac₁ := principalLevel_factor L w hw₁

  set ε₀ : Option (𝓞 L ⧸ w.asIdeal) → GL (Fin 2) (w.adicCompletion L) := fun i =>
    i.elim (localRepInf ϖ hϖ0) (fun c => localRepSome ϖ hϖ0 (algebraMap (𝓞 L) (w.adicCompletionIntegers L) (sec c)))
    with hε₀
  have hε₀N : IsHeckeCosetSystem UNo (emb L w P) (fun i => emb L w (ε₀ i)) := by
    have := hsys N hw
    rw [← hgen] at this
    exact this
  have hε₀K : IsHeckeCosetSystem Kw P ε₀ := isHeckeCosetSystem_of_comp (emb L w) (loc L w) UNo Kw hli hUKo hKUo hε₀N

  haveI : Finite (𝓞 L ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Fintype (𝓞 L ⧸ w.asIdeal) := Fintype.ofFinite _
  have hcard : Fintype.card (Option (𝓞 L ⧸ w.asIdeal)) = Ideal.absNorm w.asIdeal + 1 := by
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  set e : Fin (Ideal.absNorm w.asIdeal + 1) ≃ Option (𝓞 L ⧸ w.asIdeal) := (Fintype.equivFinOfCardEq hcard).symm
    with he
  have hε₀K' : IsHeckeCosetSystem Kw P (ε₀ ∘ e) := cosetSystem_comp_equiv hε₀K e

  have hzc := diagPi_mul_localRepInf_mem_center ϖ hϖ0 (K := w.adicCompletion L)
  obtain ⟨ε, hε, -, hεz⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq hε₀K'
      (weylInt_mem (R := w.adicCompletionIntegers L) (K := w.adicCompletion L)) hzc (weylInt_conj_diagPi ϖ hϖ0)

  have hε' : IsHeckeCosetSystem Kw P⁻¹ (fun i => (ε i)⁻¹) := by
    have h1 := cosetSystem_central_mul ((Subgroup.center _).inv_mem hzc) hεz
    simp only [inv_mul_cancel_left] at h1
    exact isHeckeCosetSystem_of_doubleCoset_eq (doubleCoset_zinv_mul_diagPi_eq ϖ hϖ0) h1

  have hεN : IsHeckeCosetSystem UN (emb L w P) (fun i => emb L w (ε i)) :=
    isHeckeCosetSystem_comp (emb L w) (loc L w) UN Kw hli hUK hKU hfac hε
  have hεN₁ : IsHeckeCosetSystem UN₁ (emb L w P) (fun i => emb L w (ε i)) :=
    isHeckeCosetSystem_comp (emb L w) (loc L w) UN₁ Kw hli hUK₁ hKU₁ hfac₁ hε

  have hτ := isGelfandInvolution_transposeGL ϖ hϖ0 hϖ (K := w.adicCompletion L)
  have hΦ : ∀ x : AdelicGL2 (𝓞 L) L,
      ∑ i, φ ((emb L w (ε i))⁻¹ * x) = ∑ i, φ (x * (emb L w (ε i))⁻¹) := by
    intro x
    have hx : x = emb L w (loc L w x) * cof L w x := (emb_loc_mul_cof L w x).symm
    have hcomm : ∀ k, emb L w k * cof L w x = cof L w x * emb L w k := fun k =>
      emb_mul_eq_mul_emb_of_loc_eq_one L w (loc_cof L w x) k
    set c := cof L w x with hc
    set h := loc L w x with hh
    set ψ : GL (Fin 2) (w.adicCompletion L) → ℂ := fun k => φ (emb L w k * c) with hψ
    have hl : ∀ u ∈ Kw, ∀ y, ψ (u * y) = ψ y := fun u hu y => by
      simp only [hψ, map_mul, mul_assoc]
      exact (hbi _ (hKU u hu) _).1
    have hr : ∀ u ∈ Kw, ∀ y, ψ (y * u) = ψ y := fun u hu y => by
      simp only [hψ, map_mul, mul_assoc]
      rw [hcomm u, ← mul_assoc]
      exact (hbi _ (hKU u hu) _).2
    have key := sum_apply_inv_mul_eq_sum_apply_mul_inv hτ hε hε' ψ hl hr h
    have e1 : ∀ i, φ ((emb L w (ε i))⁻¹ * x) = ψ ((ε i)⁻¹ * h) := fun i => by
      simp only [hψ, hx, map_mul, map_inv, mul_assoc]
    have e2 : ∀ i, φ (x * (emb L w (ε i))⁻¹) = ψ (h * (ε i)⁻¹) := fun i => by
      simp only [hψ, hx, map_mul, map_inv]
      rw [mul_assoc, ← map_inv, ← hcomm, ← mul_assoc]
    simp_rw [e1, e2]
    exact key

  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L
  haveI : (adelicGLHaar (Fin 2) (𝓞 L) L).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar L
  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  have hvg : ∀ g : AdelicGL2 (𝓞 L) L, Continuous fun x => v (g * x) := fun g =>
    hv.comp (continuous_const.mul continuous_id)
  have hvgc : ∀ g c : AdelicGL2 (𝓞 L) L, Continuous fun x => v (g * x * c) := fun g c =>
    hv.comp ((continuous_const.mul continuous_id).mul continuous_const)
  have hφl : ∀ d : AdelicGL2 (𝓞 L) L, Continuous (fun x => φ (d * x)) ∧ HasCompactSupport (fun x => φ (d * x)) :=
    fun d => ⟨hφ.comp (continuous_const.mul continuous_id), hφc.comp_homeomorph (Homeomorph.mulLeft d)⟩
  have hφr : ∀ d : AdelicGL2 (𝓞 L) L, Continuous (fun x => φ (x * d)) ∧ HasCompactSupport (fun x => φ (x * d)) :=
    fun d => ⟨hφ.comp (continuous_id.mul continuous_const), hφc.comp_homeomorph (Homeomorph.mulRight d)⟩

  refine ⟨fun i => emb L w (ε i), by rw [ht]; exact hεN, fun g => ?_⟩
  show ∑ i, rightConv L v φ (g * emb L w (ε i)) = a * rightConv L v φ g
  have lhs : ∑ i, rightConv L v φ (g * emb L w (ε i)) =
      ∫ x, v (g * x) * ∑ i, φ ((emb L w (ε i))⁻¹ * x) ∂μ := by
    have h1 : ∀ i, rightConv L v φ (g * emb L w (ε i)) = ∫ x, v (g * x) * φ ((emb L w (ε i))⁻¹ * x) ∂μ :=
      fun i => by rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply, rightConv_apply]
    simp_rw [h1]
    rw [← integral_finsetSum _ (fun i _ =>
      integrable_mul_of_continuous L _ _ (hvg g) (hφl (emb L w (ε i))⁻¹).1 (hφl (emb L w (ε i))⁻¹).2)]
    congr 1
    funext x
    rw [Finset.mul_sum]
  have rhs : a * rightConv L v φ g = ∫ x, v (g * x) * ∑ i, φ (x * (emb L w (ε i))⁻¹) ∂μ := by
    rw [rightConv_apply, ← integral_const_mul]
    have h1 : ∀ x, a * (v (g * x) * φ x) = ∑ i, v (g * x * emb L w (ε i)) * φ x := fun x => by
      rw [← mul_assoc, ← Finset.sum_mul]
      congr 1
      have h2 := hr'eq (g * x)
      simp only [SmoothCusp.heckeCosetSum] at h2
      rw [← h2]
      exact heckeCosetSum_eq_of_isHeckeCosetSystem hεN₁ hr' hvU (g * x)
    simp_rw [h1]
    rw [integral_finsetSum _ (fun i _ => integrable_mul_of_continuous L _ _ (hvgc g (emb L w (ε i))) hφ hφc)]
    have h3 : ∀ i, ∫ x, v (g * x * emb L w (ε i)) * φ x ∂μ = ∫ x, v (g * x) * φ (x * (emb L w (ε i))⁻¹) ∂μ :=
      fun i => by
      rw [← integral_mul_right_eq_self (fun x => v (g * x) * φ (x * (emb L w (ε i))⁻¹)) (emb L w (ε i))]
      congr 1
      funext x
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    rw [Finset.sum_congr rfl fun i _ => h3 i]
    rw [← integral_finsetSum _ (fun i _ =>
      integrable_mul_of_continuous L _ _ (hvg g) (hφr (emb L w (ε i))⁻¹).1 (hφr (emb L w (ε i))⁻¹).2)]
    congr 1
    funext x
    rw [Finset.mul_sum]
  rw [lhs, rhs]
  congr 1
  funext x
  rw [hΦ x]

end Main

end P2mConvHecke

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open IsDedekindDomain AutomorphicForm

theorem solution
    (L : Type) [Field L] [NumberField L]
    (N₁ N : Ideal (𝓞 L)) (w : HeightOneSpectrum (𝓞 L))
    (hw₁ : ¬ w.asIdeal ∣ N₁) (hw : ¬ w.asIdeal ∣ N)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hbi : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hv : Continuous v)
    (hvU : ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L,
      v (g * u) = v g)
    (a : ℂ)
    (ha : SmoothCusp.IsHeckeCosetEigenfunctionAt L (principalLevel (𝓞 L) L N₁ ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w v a) :
    SmoothCusp.IsHeckeCosetEigenfunctionAt L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L)
      (heckeGen (𝓞 L) L w) w (rightConv L v φ) a :=
  P2mConvHecke.mainB L N₁ N w hw₁ hw φ hφ hφc hbi v hv hvU a ha

end S_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd
end P2MW
export P2MW.S_AutomorphicForm_isHeckeCosetEigenfunctionAt_rightConv_of_isBiInvariantUnder_principalLevel_of_not_dvd (solution)
