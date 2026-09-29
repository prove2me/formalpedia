-- Prove2me | solution 1 for AutomorphicForm.isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/efc1a6c2-c552-548a-90ba-14d31b929683

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LatticeTreeOrbital
import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_AutomorphicForm_exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen
import Theorems.Thm_LT_LatticeTree_unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap
import Theorems.Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant
import Theorems.Thm_LT_LatticeTree_exists_conj_eq_zpow_smul_of_not_isSquare_discr
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quot_span_eq_absNorm
import Theorems.Thm_LT_LatticeTree_unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
import Mathlib.Topology.Algebra.OpenSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
p2m_attr_erase "simp" "LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11"

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain
open scoped TensorProduct
open scoped TensorProduct.RightActions
open scoped Matrix

noncomputable section

namespace EllGermBridge

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem intEntries_mul {A B : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers K) (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers K) :
    ∀ i j, (A * B) i j ∈ v.adicCompletionIntegers K := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hB k j)

def K0 : Subgroup (GL (Fin 2) (v.adicCompletion K)) where
  carrier := localIntegralSet K v
  mul_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact intEntries_mul K v ha.1 hb.1
    · rw [mul_inv_rev, Units.val_mul]; exact intEntries_mul K v hb.2 ha.2
  one_mem' := one_mem_localIntegralSet K v
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by simpa using ha.1⟩

theorem isOpen_K0 : IsOpen ((K0 K v : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := isOpen_localIntegralSet K v

theorem scalar_mul_comm (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) c * g = g * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (Matrix.scalar_commute (n := Fin 2) (c : v.adicCompletion K) (fun r => mul_comm _ r)
    (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).eq

theorem scalar_inv_mul_comm (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g = g * (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ := by
  rw [← map_inv]; exact scalar_mul_comm K v c⁻¹ g

theorem conj_scalar_inv_mul (c : (v.adicCompletion K)ˣ) (γ x : GL (Fin 2) (v.adicCompletion K)) :
    x⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) * x =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ * x) := by
  have hz := scalar_inv_mul_comm K v c
  calc x⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) * x
      = (x⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹) * γ * x := by simp only [mul_assoc]
    _ = ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * x⁻¹) * γ * x := by rw [hz x⁻¹]
    _ = (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ * x) := by simp only [mul_assoc]

theorem centralizer_scalar_inv_mul (c : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K)) :
    localCentralizer K v ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) = localCentralizer K v γ := by
  ext t
  simp only [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
  have e1 : t * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (t * γ) := by
    rw [← mul_assoc, ← scalar_inv_mul_comm K v c t, mul_assoc]
  have e2 : (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ * t =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (γ * t) := mul_assoc _ _ _
  rw [e1, e2, mul_right_inj]

theorem coe_K0 : ((K0 K v : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v := rfl

theorem mem_K0 {g : GL (Fin 2) (v.adicCompletion K)} : g ∈ K0 K v ↔ g ∈ localIntegralSet K v := Iff.rfl

def f0 (c : (v.adicCompletion K)ˣ) : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
  (localIntegralSet K v).indicator (fun _ => (1 : ℂ)) ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)

theorem f0_conj (c : (v.adicCompletion K)ˣ) (γ x : GL (Fin 2) (v.adicCompletion K)) :
    f0 K v c (x⁻¹ * γ * x) =
      (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        (x⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) * x) := by
  rw [f0, conj_scalar_inv_mul]

theorem f0_biinv (c : (v.adicCompletion K)ˣ) (g : GL (Fin 2) (v.adicCompletion K)) :
    ∀ u₁ ∈ K0 K v, ∀ u₂ ∈ K0 K v, f0 K v c (u₁ * g * u₂) = f0 K v c g := by
  intro u₁ hu₁ u₂ hu₂
  simp only [f0]
  have hre : (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (u₁ * g * u₂) =
      u₁ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g) * u₂ := by
    calc (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (u₁ * g * u₂)
        = ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * u₁) * g * u₂ := by simp only [mul_assoc]
      _ = (u₁ * (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹) * g * u₂ := by rw [scalar_inv_mul_comm K v c u₁]
      _ = u₁ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g) * u₂ := by simp only [mul_assoc]
  rw [hre]
  by_cases h : (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g ∈ localIntegralSet K v
  · have h' : u₁ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g) * u₂ ∈ localIntegralSet K v :=
      (K0 K v).mul_mem ((K0 K v).mul_mem hu₁ h) hu₂
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
  · have h' : u₁ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g) * u₂ ∉ localIntegralSet K v := by
      intro h'
      apply h
      have := (K0 K v).mul_mem ((K0 K v).mul_mem ((K0 K v).inv_mem hu₁) h') ((K0 K v).inv_mem hu₂)
      simpa [mul_assoc, mem_K0] using this
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

theorem isLocalTestFn_f0 (c : (v.adicCompletion K)ˣ) : IsLocalTestFn K v (f0 K v c) := by
  have h0 := isLocalTestFn_indicator_localIntegralSet K v
  have hcont : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g :=
    continuous_const.mul continuous_id
  refine ⟨h0.1.comp_continuous hcont, ?_⟩
  exact h0.2.comp_homeomorph (Homeomorph.mulLeft ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹))

theorem C1 (c : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K)) (hγreg : IsRegularSemisimple γ)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ) :
    letI := localCentralizerBorel K v γ
    ∃ S : Finset (GL (Fin 2) (v.adicCompletion K)),
      (∀ s ∈ S, s⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) * s ∈ localIntegralSet K v) ∧
      (∀ s ∈ S, ∀ s' ∈ S, ∀ t ∈ localCentralizer K v γ, ∀ u ∈ localIntegralSet K v,
        s' = t * s * u → s' = s) ∧
      (∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ) * x ∈ localIntegralSet K v →
        ∃ s ∈ S, ∃ t ∈ localCentralizer K v γ, ∃ u ∈ localIntegralSet K v, x = t * s * u) ∧
      IsOrbitalIntegral K v γ τ (f0 K v c)
        (∑ s ∈ S, (((τ {t : localCentralizer K v γ |
            s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal : ℂ))⁻¹) := by
  classical
  haveI := hτ
  obtain ⟨⟨S, hP, hQ⟩, hval⟩ :=
    AutomorphicForm.exists_finset_isOrbitalIntegral_sum_mul_div_of_forall_mul_eq_of_isOpen K v γ hγreg τ
      (K0 K v) (isOpen_K0 K v) (subset_of_eq (coe_K0 K v)) (f0 K v c) (isLocalTestFn_f0 K v c)
      (fun g u₁ hu₁ u₂ hu₂ => f0_biinv K v c g u₁ hu₁ u₂ hu₂)
  obtain ⟨γ', hγ'⟩ : ∃ γ' : GL (Fin 2) (v.adicCompletion K), γ' = (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ := ⟨_, rfl⟩
  obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (GL (Fin 2) (v.adicCompletion K)), S₀ = S.filter fun s => s⁻¹ * γ' * s ∈ localIntegralSet K v :=
    ⟨_, rfl⟩
  have hP₀ : ∀ s ∈ S₀, ∀ s' ∈ S₀, ∀ t ∈ localCentralizer K v γ, ∀ u ∈ K0 K v, s' = t * s * u → s' = s :=
    fun s hs s' hs' t ht u hu =>
      hP s (Finset.mem_filter.1 (hS₀ ▸ hs)).1 s' (Finset.mem_filter.1 (hS₀ ▸ hs')).1 t ht u hu
  have hQ₀ : ∀ x : GL (Fin 2) (v.adicCompletion K), x⁻¹ * γ' * x ∈ localIntegralSet K v →
      ∃ s ∈ S₀, ∃ t ∈ localCentralizer K v γ, ∃ u ∈ K0 K v, x = t * s * u := by
    intro x hx
    have hne : f0 K v c (x⁻¹ * γ * x) ≠ 0 := by
      rw [f0_conj, ← hγ', Set.indicator_of_mem hx]; exact one_ne_zero
    obtain ⟨s, hs, t, ht, u, hu, rfl⟩ := hQ x hne
    refine ⟨s, hS₀ ▸ Finset.mem_filter.2 ⟨hs, ?_⟩, t, ht, u, hu, rfl⟩
    have htc : t * γ' = γ' * t := by
      have := (centralizer_scalar_inv_mul K v c γ).symm ▸ ht
      rw [← hγ'] at this
      exact Subgroup.mem_centralizer_singleton_iff.1 this
    have htc' : t⁻¹ * γ' * t = γ' := by rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
    have : s⁻¹ * γ' * s = u * ((t * s * u)⁻¹ * γ' * (t * s * u)) * u⁻¹ := by
      calc s⁻¹ * γ' * s = s⁻¹ * (t⁻¹ * γ' * t) * s := by rw [htc']
        _ = u * ((t * s * u)⁻¹ * γ' * (t * s * u)) * u⁻¹ := by
          simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
    rw [this]
    exact (K0 K v).mul_mem ((K0 K v).mul_mem hu hx) ((K0 K v).inv_mem hu)
  have hQ₀' : ∀ x : GL (Fin 2) (v.adicCompletion K), f0 K v c (x⁻¹ * γ * x) ≠ 0 →
      ∃ s ∈ S₀, ∃ t ∈ localCentralizer K v γ, ∃ u ∈ K0 K v, x = t * s * u := by
    intro x hx
    apply hQ₀
    by_contra h
    rw [f0_conj, ← hγ', Set.indicator_of_notMem h] at hx
    exact hx rfl
  have hmemS₀ : ∀ s ∈ S₀, s⁻¹ * γ' * s ∈ localIntegralSet K v := fun s hs => by
    rw [hS₀] at hs; exact (Finset.mem_filter.1 hs).2
  have hI := hval S₀ hP₀ hQ₀'
  subst hγ'
  refine ⟨S₀, hmemS₀, hP₀, hQ₀, ?_⟩
  have hsum : (∑ s ∈ S₀, f0 K v c (s⁻¹ * γ * s) *
        (((localHaar K v) ((K0 K v : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K)))).toReal : ℂ) /
        ((τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈
            ((K0 K v : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K)))}).toReal : ℂ)) =
      ∑ s ∈ S₀, (((τ {t : localCentralizer K v γ |
            s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal : ℂ))⁻¹ := by
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := hmemS₀ s hs
    rw [f0_conj, Set.indicator_of_mem hs', coe_K0, localHaar_localIntegralSet]
    simp
  rw [hsum] at hI
  exact hI

structure DepthData (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K) (γ : GL (Fin 2) (v.adicCompletion K)) (m : ℕ) where
  a : v.adicCompletion K
  Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)
  ha : Valued.v a ≤ 1
  hY : ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + (ϖ ^ m) • Y
  hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1
  hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
    ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ)
  hdet : Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1

def Tc (δ : GL (Fin 2) (v.adicCompletion K)) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer {δ} ⊓
    ((Units.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) :
        v.adicCompletionIntegers K →* v.adicCompletion K)).range).comap Matrix.GeneralLinearGroup.det

theorem mem_Tc (δ t : GL (Fin 2) (v.adicCompletion K)) :
    t ∈ Tc K v δ ↔ t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      ∃ w : (v.adicCompletionIntegers K)ˣ,
        Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w := by
  simp only [Tc, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_range]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have := congrArg (fun u : (v.adicCompletion K)ˣ => (u : v.adicCompletion K)) hw
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this.symm
  · rintro ⟨w, hw⟩
    refine ⟨w, Units.ext ?_⟩
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using hw.symm

def St (δ s : GL (Fin 2) (v.adicCompletion K)) : Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer {δ} ⊓ (K0 K v).comap (MulAut.conj s⁻¹).toMonoidHom

theorem mem_St (δ s t : GL (Fin 2) (v.adicCompletion K)) :
    t ∈ St K v δ s ↔ t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧ s⁻¹ * t * s ∈ localIntegralSet K v := by
  simp only [St, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
    mem_K0]

theorem exists_units_eq_of_valuation_eq_one {x : v.adicCompletion K} (hx : Valued.v x = 1) :
    ∃ w : (v.adicCompletionIntegers K)ˣ,
      x = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w := by
  have hx1 : x ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx.le
  have hx0 : x ≠ 0 := by intro h; rw [h, map_zero] at hx; exact zero_ne_one hx
  have hx2 : x⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
  refine ⟨⟨⟨x, hx1⟩, ⟨x⁻¹, hx2⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩

theorem coe_scalar_inv_mul (c : (v.adicCompletion K)ˣ) (γ : GL (Fin 2) (v.adicCompletion K)) :
    (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  rw [← map_inv, Units.val_mul]
  change (Matrix.scalar (Fin 2) ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K)) * (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = _
  rw [Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

theorem two_le_absNorm : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem exists_units_det_eq_of_mem_localIntegralSet {k : GL (Fin 2) (v.adicCompletion K)} (hk : k ∈ localIntegralSet K v) :
    ∃ w : (v.adicCompletionIntegers K)ˣ,
      Matrix.det (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w := by
  apply exists_units_eq_of_valuation_eq_one K v
  have hint : ∀ {A : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)}, (∀ i j, A i j ∈ v.adicCompletionIntegers K) → Valued.v A.det ≤ 1 := by
    intro A hA
    rw [← HeightOneSpectrum.mem_adicCompletionIntegers, Matrix.det_fin_two]
    exact sub_mem (mul_mem (hA 0 0) (hA 1 1)) (mul_mem (hA 0 1) (hA 1 0))
  have h1 := hint hk.1
  have h2 := hint hk.2
  have hmul : Matrix.det (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * Matrix.det ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  apply le_antisymm h1
  by_contra hlt
  push Not at hlt
  have heq := congrArg Valued.v hmul
  rw [map_mul, map_one] at heq
  have hlt' : Valued.v (Matrix.det (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) * Valued.v (Matrix.det ((k⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  exact absurd heq hlt'.ne

scoped instance secondCountable_localGL : SecondCountableTopology (GL (Fin 2) (v.adicCompletion K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → v.adicCompletion K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (v.adicCompletion K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isInducing.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

theorem borelSpace_localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    @BorelSpace (localCentralizer K v γ) _ (localCentralizerBorel K v γ) :=
  @BorelSpace.mk _ _ (localCentralizerBorel K v γ) rfl

theorem valuation_lt_one_iff_le {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (y : v.adicCompletion K) : Valued.v y < 1 ↔ Valued.v y ≤ Valued.v ϖ := by
  rw [hϖ]
  constructor
  · intro h
    rcases eq_or_ne (Valued.v y) 0 with h0 | h0
    · rw [h0]; exact zero_le'
    · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0
      rw [← hu] at h ⊢
      rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
      rw [WithZero.coe_le_coe]
      change Multiplicative.toAdd u ≤ -1
      have : Multiplicative.toAdd u < 0 := h
      omega
  · intro h
    refine h.trans_lt ?_
    rw [← WithZero.coe_one, WithZero.coe_lt_coe]
    change (-1 : ℤ) < 0
    norm_num

theorem mem_localIntegralSet_of_entries_of_det (g : GL (Fin 2) (v.adicCompletion K))
    (hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K)
    (hdet : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) : g ∈ localIntegralSet K v := by
  refine ⟨hint, ?_⟩
  have hinv : ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))⁻¹ • (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv']
  have hdi : (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hdet, inv_one]
  intro i j
  rw [hinv, Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_fin_two]
  refine mul_mem hdi ?_
  fin_cases i <;> fin_cases j <;> simp [hint, neg_mem]

theorem irreducible_of_valuation_eq {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (hint : ϖ ∈ v.adicCompletionIntegers K) :
    Irreducible (⟨ϖ, hint⟩ : v.adicCompletionIntegers K) := by
  have hlt : Valued.v ϖ < 1 := (valuation_lt_one_iff_le K v hϖ ϖ).2 le_rfl
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact hlt.ne
  · have h : Valued.v ϖ = Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) := by
      have := congrArg (fun x : v.adicCompletionIntegers K => Valued.v (x : v.adicCompletion K)) hab
      simpa using this
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    by_contra hne
    push Not at hne
    have ha : Valued.v (a : v.adicCompletion K) ≤ Valued.v ϖ :=
      (valuation_lt_one_iff_le K v hϖ _).1 (lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 a.2) hne.1)
    have hb : Valued.v (b : v.adicCompletion K) ≤ Valued.v ϖ :=
      (valuation_lt_one_iff_le K v hϖ _).1 (lt_of_le_of_ne ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 b.2) hne.2)
    have hϖ0 : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
    have h2 : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) ≤ Valued.v ϖ * Valued.v ϖ :=
      mul_le_mul' ha hb
    rw [← h] at h2
    have h3 : Valued.v ϖ * Valued.v ϖ < Valued.v ϖ := by
      calc Valued.v ϖ * Valued.v ϖ < Valued.v ϖ * 1 := mul_lt_mul_of_pos_left hlt hϖ0
        _ = Valued.v ϖ := mul_one _
    exact absurd (h2.trans_lt h3) (lt_irrefl _)

theorem valuation_uniformizer_zpow {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (k : ℤ) : Valued.v (ϖ ^ k) = (Multiplicative.ofAdd (-k) : Multiplicative ℤ) := by
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul]; simp

theorem normalForm {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (hϖint : ϖ ∈ v.adicCompletionIntegers K)
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (Yg : GL (Fin 2) (v.adicCompletion K)) (hYg : (Yg : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Y) :
    ∃ (x : GL (Fin 2) (v.adicCompletion K)) (μ : v.adicCompletionIntegers K) (Y₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
      ((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) μ • 1 +
          Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) ∧
      ((∀ (a : v.adicCompletionIntegers K ⧸ Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)})
          (w : Fin 2 → v.adicCompletionIntegers K ⧸ Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)}),
          Matrix.mulVec (Y₁.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)}) :
              v.adicCompletionIntegers K →+* v.adicCompletionIntegers K ⧸ Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)})) w = a • w → w = 0) ∨
       (∃ w : (v.adicCompletionIntegers K)ˣ,
          Y₁ 0 0 * Y₁ 1 1 - Y₁ 0 1 * Y₁ 1 0 = ⟨ϖ, hϖint⟩ * (w : v.adicCompletionIntegers K) ∧
          (⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K) ∣ Y₁ 0 0 + Y₁ 1 1)) := by
  classical
  have hirr := irreducible_of_valuation_eq K v hϖ hϖint
  have hv1 : Valued.v ϖ < 1 := (valuation_lt_one_iff_le K v hϖ ϖ).2 le_rfl
  have hvle : Valued.v ϖ ≤ 1 := hv1.le
  have hι : ∀ r : v.adicCompletionIntegers K,
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) ≤ 1 := fun r =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 r.2
  have hιϖ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨ϖ, hϖint⟩ = ϖ := rfl
  have hdetmap : ∀ B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K),
      (B.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) B.det := fun B => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hle1 : ∀ n : ℤ, ((Multiplicative.ofAdd n : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 ↔ n ≤ 0 := by
    intro n
    rw [← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]

  have bound : ∀ (j : ℕ) (B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
      Valued.v (ϖ ^ j • B.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det ≤ Valued.v ϖ ^ (2 * j) ∧
      Valued.v (ϖ ^ j • B.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).trace ≤ Valued.v ϖ ^ j := by
    intro j B
    constructor
    · rw [Matrix.det_smul, Fintype.card_fin, hdetmap, map_mul, map_pow, map_pow, ← pow_mul, mul_comm j 2]
      exact mul_le_of_le_one_right' (hι _)
    · rw [Matrix.trace_smul, Matrix.trace_fin_two, Matrix.map_apply, Matrix.map_apply, ← map_add, smul_eq_mul,
        map_mul, map_pow]
      exact mul_le_of_le_one_right' (hι _)

  obtain ⟨x, k, hcases⟩ := LT.LatticeTree.exists_conj_eq_zpow_smul_of_not_isSquare_discr K v ⟨ϖ, hϖint⟩ hirr Yg
    (by rw [hYg]; exact hYell)

  have hconj : ∀ b : v.adicCompletion K,
      ((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - b • 1 =
        ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * (Y - b • 1) *
          (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    intro b
    rw [Units.val_mul, Units.val_mul, hYg, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Units.inv_mul]
  have hconj_det : ∀ b : v.adicCompletion K,
      (((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - b • 1).det =
        (Y - b • 1).det := by
    intro b; rw [hconj, Matrix.det_units_conj']
  have hconj_tr : ∀ b : v.adicCompletion K,
      (((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - b • 1).trace =
        (Y - b • 1).trace := by
    intro b; rw [hconj, Matrix.trace_units_conj']
  have hYint' : Valued.v ((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det ≤ 1 := by
    have := hconj_det 0
    simp only [zero_smul, sub_zero] at this
    rw [this]; exact hYint.1
  have hYgen' : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - b • 1).det ≤ Valued.v ϖ ^ 2 ∧
         Valued.v (((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - b • 1).trace ≤ Valued.v ϖ) := by
    intro b hb; rw [hconj_det, hconj_tr]; exact hYgen b hb

  have hk_lt : ∀ (B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
      ((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨ϖ, hϖint⟩ ^ k •
          B.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) → 0 ≤ k → k = 0 := by
    intro B hB hk0
    by_contra hk
    have hk1 : 1 ≤ k := by omega
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, (Int.toNat_of_nonneg hk0).symm⟩
    have hj : 1 ≤ j := by exact_mod_cast hk1
    rw [hιϖ, zpow_natCast] at hB
    apply hYgen' 0 (by rw [map_zero]; exact zero_le')
    rw [zero_smul, sub_zero, hB]
    obtain ⟨h1, h2⟩ := bound j B
    exact ⟨h1.trans (pow_le_pow_right_of_le_one' hvle (by omega)), h2.trans (by
      calc Valued.v ϖ ^ j ≤ Valued.v ϖ ^ 1 := pow_le_pow_right_of_le_one' hvle hj
        _ = Valued.v ϖ := pow_one _)⟩

  have step : ∀ (γ' : Matrix.GeneralLinearGroup (Fin 2) (v.adicCompletionIntegers K)) (d : ℕ)
      (mu : (v.adicCompletionIntegers K)ˣ) (Y₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)),
      (∀ i j, (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j =
          (mu : v.adicCompletionIntegers K) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) i j +
            ⟨ϖ, hϖint⟩ ^ d * Y₁ i j) →
      ((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨ϖ, hϖint⟩ ^ k •
          (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) →
      ((x⁻¹ * Yg * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (mu : v.adicCompletionIntegers K) • 1 +
          Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
    intro γ' d mu Y₁ hγ' hY'
    have hdetγ' : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
        (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).det) = 1 := by
      change Valued.v (((γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).det : v.adicCompletionIntegers K) : v.adicCompletion K) = 1
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 ((Matrix.isUnit_iff_isUnit_det _).1 γ'.isUnit)
    have hk0 : 0 ≤ k := by
      have h := hYint'
      rw [hY', Matrix.det_smul, Fintype.card_fin, hdetmap, map_mul, hdetγ', mul_one, hιϖ, map_pow,
        valuation_uniformizer_zpow K v hϖ, ← WithZero.coe_pow, ← ofAdd_nsmul, hle1] at h
      try simp only [nsmul_eq_mul, smul_eq_mul] at h
      omega
    have hk := hk_lt _ hY' hk0
    rw [hk, zpow_zero, one_smul] at hY'
    have hexp : (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)).map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (mu : v.adicCompletionIntegers K) • 1 +
          ϖ ^ d • Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
      ext i j
      rw [Matrix.map_apply, hγ' i j, map_add, map_mul, map_mul, map_pow, hιϖ, Matrix.add_apply, Matrix.smul_apply,
        Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply, smul_eq_mul, smul_eq_mul]
      split_ifs <;> simp
    rw [hexp] at hY'
    have hd : d = 0 := by
      by_contra hd
      have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.2 hd
      apply hYgen' (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (mu : v.adicCompletionIntegers K)) (hι _)
      rw [hY', add_sub_cancel_left]
      obtain ⟨h1, h2⟩ := bound d Y₁
      exact ⟨h1.trans (pow_le_pow_right_of_le_one' hvle (by omega)), h2.trans (by
        calc Valued.v ϖ ^ d ≤ Valued.v ϖ ^ 1 := pow_le_pow_right_of_le_one' hvle hd1
          _ = Valued.v ϖ := pow_one _)⟩
    rw [hY', hd, pow_zero, one_smul]
  rcases hcases with ⟨γ', d, mu, Y₁, hγ', haniso, hY'⟩ | ⟨γ', d, mu, Y₁, w, hγ', hdetY₁, htrY₁, hY'⟩ |
    ⟨Y₁, w, hdetY₁, htrY₁, hY'⟩
  · exact ⟨x, mu, Y₁, step γ' d mu Y₁ hγ' hY', Or.inl haniso⟩
  · exact ⟨x, mu, Y₁, step γ' d mu Y₁ hγ' hY', Or.inr ⟨w, hdetY₁, htrY₁⟩⟩
  · have hdet1 : Y₁.det = ⟨ϖ, hϖint⟩ * (w : v.adicCompletionIntegers K) := by rw [Matrix.det_fin_two]; exact hdetY₁
    have hw1 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (w : v.adicCompletionIntegers K)) = 1 := by
      change Valued.v (((w : v.adicCompletionIntegers K)) : v.adicCompletion K) = 1
      exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 w.isUnit
    have hk0 : 0 ≤ k := by
      have h := hYint'
      rw [hY', Matrix.det_smul, Fintype.card_fin, hdetmap, hdet1, map_mul, map_mul, map_mul, hw1, mul_one,
        hιϖ, map_pow, valuation_uniformizer_zpow K v hϖ, hϖ, ← WithZero.coe_pow, ← WithZero.coe_mul, ← ofAdd_nsmul,
        ← ofAdd_add, hle1] at h
      try simp only [nsmul_eq_mul, smul_eq_mul] at h
      omega
    have hk := hk_lt _ hY' hk0
    rw [hk, zpow_zero, one_smul] at hY'
    refine ⟨x, 0, Y₁, ?_, Or.inr ⟨w, hdetY₁, htrY₁⟩⟩
    rw [hY', map_zero, zero_smul, zero_add]

section General

variable {F : Type*} [Field F]

theorem mat2_eq_smul_one_add_smul_iff (g A : Matrix (Fin 2) (Fin 2) F) (α β : F) :
    g = α • 1 + β • A ↔
      g 0 0 = α + β * A 0 0 ∧ g 0 1 = β * A 0 1 ∧ g 1 0 = β * A 1 0 ∧ g 1 1 = α + β * A 1 1 := by
  rw [← Matrix.ext_iff]
  simp [Fin.forall_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, and_assoc]

theorem mat2_eq_smul_one_iff (A : Matrix (Fin 2) (Fin 2) F) (a : F) :
    A = a • 1 ↔ A 0 0 = a ∧ A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = a := by
  rw [← Matrix.ext_iff]
  simp [Fin.forall_fin_two, Matrix.smul_apply, Matrix.one_apply, and_assoc]

theorem mat2_mul_eq_mul_iff (g A : Matrix (Fin 2) (Fin 2) F) :
    g * A = A * g ↔
      g 0 0 * A 0 0 + g 0 1 * A 1 0 = A 0 0 * g 0 0 + A 0 1 * g 1 0 ∧
      g 0 0 * A 0 1 + g 0 1 * A 1 1 = A 0 0 * g 0 1 + A 0 1 * g 1 1 ∧
      g 1 0 * A 0 0 + g 1 1 * A 1 0 = A 1 0 * g 0 0 + A 1 1 * g 1 0 ∧
      g 1 0 * A 0 1 + g 1 1 * A 1 1 = A 1 0 * g 0 1 + A 1 1 * g 1 1 := by
  rw [← Matrix.ext_iff]
  simp [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, and_assoc]

theorem mul_eq_mul_iff_exists_eq_smul_one_add_smul (A g : Matrix (Fin 2) (Fin 2) F)
    (hA : ¬ ∃ a : F, A = a • 1) :
    g * A = A * g ↔ ∃ α β : F, g = α • 1 + β • A := by
  constructor
  · intro h
    rw [mat2_mul_eq_mul_iff] at h
    obtain ⟨h00, h01, h10, h11⟩ := h
    by_cases hb : A 0 1 = 0
    · by_cases hc : A 1 0 = 0
      · have had : A 0 0 - A 1 1 ≠ 0 := by
          intro had
          exact hA ⟨A 0 0, (mat2_eq_smul_one_iff A (A 0 0)).2 ⟨rfl, hb, hc, by linear_combination (-1 : F) * had⟩⟩
        refine ⟨g 0 0 - (g 0 0 - g 1 1) / (A 0 0 - A 1 1) * A 0 0, (g 0 0 - g 1 1) / (A 0 0 - A 1 1), ?_⟩
        rw [mat2_eq_smul_one_add_smul_iff]
        simp only [hb, hc, mul_zero, zero_mul, add_zero, zero_add] at h00 h01 h10 h11
        have hq : g 0 1 = 0 := by
          have : g 0 1 * (A 0 0 - A 1 1) = 0 := by linear_combination (-1 : F) * h01
          exact (mul_eq_zero.1 this).resolve_right had
        have hr : g 1 0 = 0 := by
          have : g 1 0 * (A 0 0 - A 1 1) = 0 := by linear_combination h10
          exact (mul_eq_zero.1 this).resolve_right had
        refine ⟨by ring, by rw [hq, hb, mul_zero], by rw [hr, hc, mul_zero], ?_⟩
        field_simp
        ring
      ·
        refine ⟨g 0 0 - g 1 0 / A 1 0 * A 0 0, g 1 0 / A 1 0, ?_⟩
        rw [mat2_eq_smul_one_add_smul_iff]
        simp only [hb, mul_zero, zero_mul, add_zero, zero_add] at h00 h01 h10 h11
        have hq : g 0 1 = 0 := by
          have : g 0 1 * A 1 0 = 0 := by linear_combination h00
          exact (mul_eq_zero.1 this).resolve_right hc
        refine ⟨by ring, by rw [hq, hb, mul_zero], by field_simp, ?_⟩
        field_simp
        linear_combination h10
    ·
      refine ⟨g 0 0 - g 0 1 / A 0 1 * A 0 0, g 0 1 / A 0 1, ?_⟩
      rw [mat2_eq_smul_one_add_smul_iff]
      refine ⟨by ring, by field_simp, ?_, ?_⟩
      · field_simp
        linear_combination (-1 : F) * h00
      · field_simp
        linear_combination (-1 : F) * h01
  · rintro ⟨α, β, rfl⟩
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem centralizer_eq_centralizer_of_mem (γ₀ γ : GL (Fin 2) F)
    (h₀ : ¬ ∃ a : F, (γ₀ : Matrix (Fin 2) (Fin 2) F) = a • 1)
    (h : ¬ ∃ a : F, (γ : Matrix (Fin 2) (Fin 2) F) = a • 1)
    (hmem : γ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F))) :
    Subgroup.centralizer ({γ} : Set (GL (Fin 2) F)) = Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F)) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hmem
  have hmat : (γ : Matrix (Fin 2) (Fin 2) F) * γ₀ = γ₀ * γ := by
    rw [← Units.val_mul, ← Units.val_mul, hmem]
  obtain ⟨α, β, hαβ⟩ := (mul_eq_mul_iff_exists_eq_smul_one_add_smul _ _ h₀).1 hmat
  have hβ : β ≠ 0 := by
    rintro rfl
    exact h ⟨α, by rw [hαβ, zero_smul, add_zero]⟩
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hg
    apply Units.ext
    have hg' : (g : Matrix (Fin 2) (Fin 2) F) * γ = γ * g := by
      rw [← Units.val_mul, ← Units.val_mul, hg]
    rw [hαβ] at hg'
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      add_right_inj] at hg'
    rw [Units.val_mul, Units.val_mul]
    exact smul_right_injective _ hβ hg'
  · intro hg
    apply Units.ext
    have hg' : (g : Matrix (Fin 2) (Fin 2) F) * γ₀ = γ₀ * g := by
      rw [← Units.val_mul, ← Units.val_mul, hg]
    rw [Units.val_mul, Units.val_mul, hαβ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, hg']

theorem discr_smul_one_add_smul (a b : F) (A : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • A) ^ 2 - 4 * Matrix.det (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • A) =
      b ^ 2 * (Matrix.trace A ^ 2 - 4 * Matrix.det A) := by
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul]
  ring

theorem isSquare_mul_sq_iff {b x : F} (hb : b ≠ 0) : IsSquare (b ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r / b, by field_simp; linear_combination hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨b * r, by rw [hr]; ring⟩

theorem not_exists_eq_smul_one_of_discr_ne_zero (γ : GL (Fin 2) F)
    (hreg : Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) ≠ 0) :
    ¬ ∃ a : F, (γ : Matrix (Fin 2) (Fin 2) F) = a • 1 := by
  rintro ⟨a, ha⟩
  apply hreg
  rw [ha, Matrix.trace_smul, Matrix.det_smul, Matrix.trace_one, Matrix.det_one, Fintype.card_fin]
  simp
  ring

theorem not_exists_eq_smul_one_of_forall_not_diagonal (γ₀ : GL (Fin 2) F)
    (hns : ∀ g : GL (Fin 2) F,
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)) :
    ¬ ∃ a : F, (γ₀ : Matrix (Fin 2) (Fin 2) F) = a • 1 := by
  rintro ⟨a, ha⟩
  apply hns 1
  rw [inv_one, one_mul, mul_one, ha]
  simp

theorem det_smul_one_add_smul (a b : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Y).det = a ^ 2 + a * b * Y.trace + b ^ 2 * Y.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), smul_eq_mul]
  ring

theorem trace_smul_one_add_smul (a b : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • Y).trace = 2 * a + b * Y.trace := by
  simp only [Matrix.trace_fin_two, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul]
  ring

theorem smul_one_add_smul_eq_smul_sub (α β : F) (hβ : β ≠ 0) (Y : Matrix (Fin 2) (Fin 2) F) :
    α • (1 : Matrix (Fin 2) (Fin 2) F) + β • Y = β • (Y - (-α / β) • 1) := by
  rw [smul_sub, smul_smul, show β * (-α / β) = -α by field_simp, neg_smul, sub_neg_eq_add, add_comm]

theorem discr_sub_smul_one (b : F) (Y : Matrix (Fin 2) (Fin 2) F) :
    (Y - b • 1).trace ^ 2 - 4 * (Y - b • 1).det = Y.trace ^ 2 - 4 * Y.det := by
  have : Y - b • 1 = (-b) • (1 : Matrix (Fin 2) (Fin 2) F) + (1 : F) • Y := by
    rw [neg_smul, one_smul, neg_add_eq_sub]
  rw [this, discr_smul_one_add_smul, one_pow, one_mul]

theorem charpoly_root_of_sq {t d s i2 : F} (hs : s * s = t ^ 2 - 4 * d) (hi2 : 2 * i2 = 1) :
    ((t + s) * i2) ^ 2 - t * ((t + s) * i2) + d = 0 := by
  linear_combination (i2 - i2 ^ 2) * hs + ((t * s + s ^ 2 + 2 * d) * i2 - d) * hi2

theorem not_isSquare_discr_of_forall_not_diagonal' (h2 : (2 : F) ≠ 0) (γ₀ : GL (Fin 2) F)
    (hreg : Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F) ≠ 0)
    (hns : ∀ g : GL (Fin 2) F,
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)) :
    ¬ IsSquare (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F)) := by
  rintro ⟨s, hs⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (Fin 2) (Fin 2) F, (γ₀ : Matrix (Fin 2) (Fin 2) F) = A := ⟨_, rfl⟩
  obtain ⟨i2, hi2⟩ : ∃ i2 : F, 2 * i2 = 1 := ⟨2⁻¹, mul_inv_cancel₀ h2⟩
  rw [hA, Matrix.trace_fin_two, Matrix.det_fin_two] at hs hreg
  have hs0 : s ≠ 0 := by rintro rfl; exact hreg (by rw [hs, mul_zero])
  have hs' : s * s = (A 0 0 + A 1 1) ^ 2 - 4 * (A 0 0 * A 1 1 - A 0 1 * A 1 0) := hs.symm
  obtain ⟨lp, hlp⟩ : ∃ lp : F, lp = (A 0 0 + A 1 1 + s) * i2 := ⟨_, rfl⟩
  obtain ⟨lm, hlm⟩ : ∃ lm : F, lm = (A 0 0 + A 1 1 - s) * i2 := ⟨_, rfl⟩
  have hrp : lp ^ 2 - (A 0 0 + A 1 1) * lp + (A 0 0 * A 1 1 - A 0 1 * A 1 0) = 0 := by
    rw [hlp]; exact charpoly_root_of_sq hs' hi2
  have hrm : lm ^ 2 - (A 0 0 + A 1 1) * lm + (A 0 0 * A 1 1 - A 0 1 * A 1 0) = 0 := by
    rw [hlm, show A 0 0 + A 1 1 - s = A 0 0 + A 1 1 + -s from sub_eq_add_neg _ _]
    exact charpoly_root_of_sq (s := -s) (by rw [neg_mul_neg]; exact hs') hi2

  have key : ∀ (g D : Matrix (Fin 2) (Fin 2) F) (hg : g.det ≠ 0), A * g = g * D → D 0 1 = 0 → D 1 0 = 0 → False := by
    intro g D hg hAg hD01 hD10
    obtain ⟨u, hu⟩ : ∃ u : GL (Fin 2) F, u = Matrix.GeneralLinearGroup.mkOfDetNeZero g hg := ⟨_, rfl⟩
    have hval : (u : Matrix (Fin 2) (Fin 2) F) = g := by rw [hu]; rfl
    have hinv : ((u⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
      have := Units.inv_mul u
      rwa [hval] at this
    apply hns u
    have hC : ((u⁻¹ * γ₀ * u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = D := by
      rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hA, hval, hAg, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    rw [hC]
    exact ⟨hD01, hD10⟩
  by_cases hc : A 1 0 = 0
  · by_cases hb : A 0 1 = 0
    · exact key 1 A (by rw [Matrix.det_one]; exact one_ne_zero) (by rw [Matrix.mul_one, Matrix.one_mul]) hb hc
    ·
      refine key !![A 0 1, A 0 1; lp - A 0 0, lm - A 0 0] !![lp, 0; 0, lm] ?_ ?_ rfl rfl
      · rw [Matrix.det_fin_two_of]
        have : A 0 1 * (lm - A 0 0) - A 0 1 * (lp - A 0 0) = -(A 0 1 * s) := by
          rw [hlp, hlm]; linear_combination (-(A 0 1) * s) * hi2
        rw [this, neg_ne_zero]
        exact mul_ne_zero hb hs0
      · rw [← Matrix.ext_iff]
        simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        exact ⟨⟨by ring, by ring⟩, by linear_combination (-1 : F) * hrp, by linear_combination (-1 : F) * hrm⟩
  ·
    refine key !![lp - A 1 1, lm - A 1 1; A 1 0, A 1 0] !![lp, 0; 0, lm] ?_ ?_ rfl rfl
    · rw [Matrix.det_fin_two_of]
      have : (lp - A 1 1) * A 1 0 - (lm - A 1 1) * A 1 0 = A 1 0 * s := by
        rw [hlp, hlm]; linear_combination (A 1 0 * s) * hi2
      rw [this]
      exact mul_ne_zero hc hs0
    · rw [← Matrix.ext_iff]
      simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      exact ⟨⟨by linear_combination (-1 : F) * hrp, by linear_combination (-1 : F) * hrm⟩, by ring, by ring⟩

end General

section Bridge

variable {F : Type*} [Field F]

theorem not_isSquare_discr_of_smul_eq_smul_one_add_smul' (h2 : (2 : F) ≠ 0) (γ₀ : GL (Fin 2) F)
    (hreg : Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F) ≠ 0)
    (hns : ∀ g : GL (Fin 2) F,
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0))
    (γ : GL (Fin 2) F) (hγ : γ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) F)))
    (hγreg : Matrix.trace (γ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ : Matrix (Fin 2) (Fin 2) F) ≠ 0)
    (c a b : F) (hc : c ≠ 0) (hb : b ≠ 0) (Y : Matrix (Fin 2) (Fin 2) F)
    (h : c • (γ : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • Y) :
    ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det) := by
  intro hsq
  apply not_isSquare_discr_of_forall_not_diagonal' h2 γ₀ hreg hns
  have h₀ := not_exists_eq_smul_one_of_forall_not_diagonal γ₀ hns
  have h₁ := not_exists_eq_smul_one_of_discr_ne_zero γ hγreg
  have hmat : (γ : Matrix (Fin 2) (Fin 2) F) * γ₀ = γ₀ * γ := by
    rw [← Units.val_mul, ← Units.val_mul, Subgroup.mem_centralizer_singleton_iff.1 hγ]
  obtain ⟨α, β, hαβ⟩ := (mul_eq_mul_iff_exists_eq_smul_one_add_smul _ _ h₀).1 hmat
  have hβ : β ≠ 0 := by
    rintro rfl
    exact h₁ ⟨α, by rw [hαβ, zero_smul, add_zero]⟩
  have hbY : b • Y = (c * α - a) • (1 : Matrix (Fin 2) (Fin 2) F) + (c * β) • (γ₀ : Matrix (Fin 2) (Fin 2) F) := by
    calc b • Y = (a • 1 + b • Y) - a • 1 := by rw [add_sub_cancel_left]
      _ = c • (α • 1 + β • (γ₀ : Matrix (Fin 2) (Fin 2) F)) - a • 1 := by rw [← h, hαβ]
      _ = (c * α - a) • 1 + (c * β) • (γ₀ : Matrix (Fin 2) (Fin 2) F) := by
        rw [smul_add, smul_smul, smul_smul, sub_smul]; abel
  have hdisc : b ^ 2 * (Y.trace ^ 2 - 4 * Y.det) =
      (c * β) ^ 2 * (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F)) := by
    rw [← discr_smul_one_add_smul (c * α - a) (c * β), ← hbY, Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin,
      smul_eq_mul]
    ring
  have hcb : c * β ≠ 0 := mul_ne_zero hc hβ
  have key : Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F) =
      ((c * β)⁻¹ * b) ^ 2 * (Y.trace ^ 2 - 4 * Y.det) := by
    calc Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F)
        = (c * β)⁻¹ ^ 2 * ((c * β) ^ 2 *
            (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) F))) := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hcb, one_pow, one_mul]
      _ = (c * β)⁻¹ ^ 2 * (b ^ 2 * (Y.trace ^ 2 - 4 * Y.det)) := by rw [hdisc]
      _ = ((c * β)⁻¹ * b) ^ 2 * (Y.trace ^ 2 - 4 * Y.det) := by ring
  rw [key]
  exact (isSquare_mul_sq_iff (mul_ne_zero (inv_ne_zero hcb) hb)).2 hsq

end Bridge

section Index

theorem v_algebraMap_units (w : (v.adicCompletionIntegers K)ˣ) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) w) = 1 :=
  HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 w.isUnit

theorem mem_Tc_iff_v_det_eq_one (δ t : GL (Fin 2) (v.adicCompletion K)) :
    t ∈ Tc K v δ ↔ t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
  rw [mem_Tc]
  refine and_congr_right fun _ => ⟨?_, fun h => exists_units_eq_of_valuation_eq_one K v h⟩
  rintro ⟨w, hw⟩
  rw [hw]
  exact v_algebraMap_units K v w

theorem v_det_ne_zero (t : GL (Fin 2) (v.adicCompletion K)) :
    Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≠ 0 := by
  rw [Valuation.ne_zero_iff, ← Matrix.GeneralLinearGroup.val_det_apply]
  exact (Matrix.GeneralLinearGroup.det t).ne_zero

def evenDet : Subgroup (GL (Fin 2) (v.adicCompletion K)) where
  carrier := {t | ∃ k : ℤ, Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = WithZero.exp (2 * k)}
  mul_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, map_mul, hk, hl, ← WithZero.exp_add]
    congr 1; ring
  one_mem' := ⟨0, by simp⟩
  inv_mem' := by
    rintro a ⟨k, hk⟩
    have h1 : Matrix.det ((a⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        Matrix.det (a : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 := congrArg Valued.v h1
    rw [map_mul, map_one, hk] at h2
    refine ⟨-k, ?_⟩
    rw [eq_inv_of_mul_eq_one_left h2, ← WithZero.exp_neg]
    congr 1; ring

theorem Tc_le_evenDet (δ : GL (Fin 2) (v.adicCompletion K)) : Tc K v δ ≤ evenDet K v := fun t ht =>
  ⟨0, by rw [((mem_Tc_iff_v_det_eq_one K v δ t).1 ht).2]; simp⟩

theorem v_coe_scalar_det (u : (v.adicCompletion K)ˣ) :
    Valued.v (Matrix.det ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Valued.v (u : v.adicCompletion K) ^ 2 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
    Units.val_pow_eq_pow_val, map_pow]

theorem center_le_evenDet : Subgroup.center (GL (Fin 2) (v.adicCompletion K)) ≤ evenDet K v := by
  intro z hz
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, rfl⟩ := hz
  refine ⟨WithZero.log (Valued.v (c : v.adicCompletion K)), ?_⟩
  have hc : Valued.v (c : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).2 c.ne_zero
  rw [v_coe_scalar_det, two_mul, WithZero.exp_add, WithZero.exp_log hc, pow_two]

theorem Tc_sup_center_le_evenDet (δ : GL (Fin 2) (v.adicCompletion K)) :
    Tc K v δ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K)) ≤ evenDet K v :=
  sup_le (Tc_le_evenDet K v δ) (center_le_evenDet K v)

theorem scalar_mem_centralizer (u : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (v.adicCompletion K)) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have hz : Matrix.GeneralLinearGroup.scalar (Fin 2) u ∈ Subgroup.center (GL (Fin 2) (v.adicCompletion K)) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩
  exact Subgroup.center_le_centralizer _ hz

theorem v_det_scalar_zpow_mul (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (hϖ0 : ϖ ≠ 0) (k : ℤ) (t : GL (Fin 2) (v.adicCompletion K)) :
    Valued.v (Matrix.det ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ϖ hϖ0 ^ k) * t :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      WithZero.exp (-(2 * k)) * Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, v_coe_scalar_det, Units.val_zpow_eq_zpow_val, Units.val_mk0,
    map_zpow₀, hϖ, ← WithZero.exp_eq_coe_ofAdd, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul]
  congr 2; ring

theorem mem_Tc_sup_center_of_v_det (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (δ t : GL (Fin 2) (v.adicCompletion K))
    (ht : t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K)))) (k : ℤ)
    (hk : Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = WithZero.exp (2 * k)) :
    t ∈ Tc K v δ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K)) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
  obtain ⟨s, hs⟩ : ∃ s : GL (Fin 2) (v.adicCompletion K),
      s = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ϖ hϖ0 ^ k) := ⟨_, rfl⟩
  have hz : s ∈ Subgroup.center (GL (Fin 2) (v.adicCompletion K)) := by
    rw [hs, Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact ⟨_, rfl⟩
  have hsT : s * t ∈ Tc K v δ := by
    rw [mem_Tc_iff_v_det_eq_one]
    refine ⟨Subgroup.mul_mem _ (hs ▸ scalar_mem_centralizer K v _ δ) ht, ?_⟩
    rw [hs, v_det_scalar_zpow_mul K v ϖ hϖ hϖ0 k t, hk, ← WithZero.exp_add]
    simp
  have hcomm : s * t * s⁻¹ = t := by
    rw [Subgroup.mem_center_iff] at hz
    rw [← hz t, mul_inv_cancel_right]
  rw [← hcomm]
  exact Subgroup.mul_mem_sup hsT (Subgroup.inv_mem _ hz)

theorem v_det_eq_exp_log (t : GL (Fin 2) (v.adicCompletion K)) :
    Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      WithZero.exp (WithZero.log (Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))) :=
  (WithZero.exp_log (v_det_ne_zero K v t)).symm

theorem relIndex_Tc_sup_center_eq_one
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (δ : GL (Fin 2) (v.adicCompletion K))
    (hnr : ¬ ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ)) :
    (Tc K v δ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K)))) = 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm
  rw [Subgroup.relIndex_eq_one]
  intro t ht
  have hn := v_det_eq_exp_log K v t
  rcases Int.even_or_odd' (WithZero.log (Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))) with ⟨k, hk | hk⟩
  · exact mem_Tc_sup_center_of_v_det K v ϖ hϖ δ t ht k (by rw [hn, hk])
  · exfalso
    apply hnr
    refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ϖ hϖ0 ^ (k + 1)) * t,
      Subgroup.mul_mem _ (scalar_mem_centralizer K v _ δ) ht, ?_⟩
    rw [v_det_scalar_zpow_mul K v ϖ hϖ hϖ0 (k + 1) t, hn, hk, ← WithZero.exp_add, ← WithZero.exp_eq_coe_ofAdd]
    congr 1; ring

theorem relIndex_Tc_sup_center_eq_two
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (δ : GL (Fin 2) (v.adicCompletion K))
    (hram : ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
      Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ)) :
    (Tc K v δ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K)))) = 2 := by
  obtain ⟨t₀, ht₀, hv₀⟩ := hram
  rw [← WithZero.exp_eq_coe_ofAdd] at hv₀
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨t₀, ht₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  have hn := v_det_eq_exp_log K v (b : GL (Fin 2) (v.adicCompletion K))
  have hprod : Valued.v (Matrix.det (((b : GL (Fin 2) (v.adicCompletion K)) * t₀ : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      WithZero.exp (WithZero.log (Valued.v (Matrix.det ((b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))) - 1) := by
    rw [Units.val_mul, Matrix.det_mul, map_mul, hv₀]
    conv_lhs => rw [hn]
    rw [← WithZero.exp_add, ← sub_eq_add_neg]
  rcases Int.even_or_odd' (WithZero.log (Valued.v (Matrix.det ((b : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))))) with ⟨k, hk | hk⟩
  ·
    refine Or.inr ⟨mem_Tc_sup_center_of_v_det K v ϖ hϖ δ _ b.2 k (by rw [hn, hk]), fun hmem => ?_⟩
    obtain ⟨l, hl⟩ := Tc_sup_center_le_evenDet K v δ hmem
    rw [hprod, hk, WithZero.exp_inj] at hl
    omega
  ·
    refine Or.inl ⟨mem_Tc_sup_center_of_v_det K v ϖ hϖ δ _ (Subgroup.mul_mem _ b.2 ht₀) k (by rw [hprod, hk]; congr 1; ring),
      fun hmem => ?_⟩
    obtain ⟨l, hl⟩ := Tc_sup_center_le_evenDet K v δ hmem
    rw [hn, hk, WithZero.exp_inj] at hl
    omega

open Classical in

theorem relIndex_Tc_sup_center
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (δ : GL (Fin 2) (v.adicCompletion K)) :
    (Tc K v δ ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K)))) =
      if (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
        Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ))
      then 2 else 1 := by
  split_ifs with h
  · exact relIndex_Tc_sup_center_eq_two K v ϖ hϖ δ h
  · exact relIndex_Tc_sup_center_eq_one K v ϖ hϖ δ h

end Index

section Integrality

theorem two_ne_zero_adicCompletion : (2 : v.adicCompletion K) ≠ 0 := by
  intro h
  apply (two_ne_zero : (2 : K) ≠ 0)
  apply (algebraMap K (v.adicCompletion K)).injective
  rw [map_ofNat, map_zero, h]

theorem not_isSquare_discr_of_forall_not_diagonal (γ₀ : GL (Fin 2) (v.adicCompletion K))
    (hreg : IsRegularSemisimple γ₀)
    (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0)) :
    ¬ IsSquare (Matrix.trace (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ^ 2 -
      4 * Matrix.det (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :=
  not_isSquare_discr_of_forall_not_diagonal' (two_ne_zero_adicCompletion K v) γ₀
    ((isRegularSemisimple_iff_ne_zero γ₀).1 hreg) hns

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne x 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    omega

theorem v_ne_zero_of_v_eq_ofAdd (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ)) : ϖ ≠ 0 := by
  intro h; rw [h, map_zero] at hϖ; exact WithZero.coe_ne_zero hϖ.symm

theorem inv_le_v_of_one_lt (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    {x : WithZero (Multiplicative ℤ)} (hx : 1 < x) : x⁻¹ ≤ Valued.v ϖ := by
  rw [hϖ, ← WithZero.exp_eq_coe_ofAdd]
  have hx0 : x ≠ 0 := (zero_lt_one.trans hx).ne'
  rw [← WithZero.exp_log hx0, ← WithZero.exp_neg, WithZero.exp_le_exp]
  rw [← WithZero.exp_log hx0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
  omega

theorem v_det_eq_sq_of_v_lt (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1) (α β : v.adicCompletion K)
    (hβα : Valued.v β < Valued.v α) :
    Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det = Valued.v α ^ 2 := by
  have hα0 : α ≠ 0 := by rintro rfl; rw [map_zero] at hβα; exact not_lt_zero hβα
  have hvα0 : Valued.v α ≠ 0 := (Valuation.ne_zero_iff _).2 hα0
  have hc : Valued.v (β / α) < 1 := by
    rw [map_div₀]; exact (div_lt_one₀ (zero_lt_iff.2 hvα0)).2 hβα
  have hX : (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det =
      α ^ 2 * (1 + ((β / α) * Y.trace + (β / α) ^ 2 * Y.det)) := by
    rw [det_smul_one_add_smul]; field_simp; ring
  have hsmall : Valued.v ((β / α) * Y.trace + (β / α) ^ 2 * Y.det) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact mul_lt_one_of_lt_of_le hc hYint.2
    · rw [map_mul, map_pow, pow_two]; exact mul_lt_one_of_lt_of_le (mul_lt_one_of_lt_of_le hc hc.le) hYint.1
  rw [hX, map_mul, map_pow, Valuation.map_one_add_of_lt _ hsmall, mul_one]

theorem v_sub_smul_one_of_v_le (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (α β : v.adicCompletion K)
    (hβ0 : β ≠ 0) (hαβ : Valued.v α ≤ Valued.v β) :
    Valued.v (-α / β) ≤ 1 ∧
      Valued.v (Y - (-α / β) • 1).det =
        (Valued.v β)⁻¹ ^ 2 * Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det ∧
      Valued.v (Y - (-α / β) • 1).trace =
        (Valued.v β)⁻¹ * Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).trace := by
  have hvβ0 : Valued.v β ≠ 0 := (Valuation.ne_zero_iff _).2 hβ0
  refine ⟨?_, ?_, ?_⟩
  · rw [map_div₀, Valuation.map_neg]; exact div_le_one_of_le₀ hαβ zero_le'
  · rw [smul_one_add_smul_eq_smul_sub α β hβ0 Y, Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, ← mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hvβ0, one_pow, one_mul]
  · rw [smul_one_add_smul_eq_smul_sub α β hβ0 Y, Matrix.trace_smul, smul_eq_mul, map_mul, ← mul_assoc,
      inv_mul_cancel₀ hvβ0, one_mul]

theorem v_le_one_of_v_det_le_one_of_v_trace_le_one
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (α β : v.adicCompletion K)
    (h : Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det ≤ 1 ∧
      Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).trace ≤ 1) :
    Valued.v α ≤ 1 ∧ Valued.v β ≤ 1 := by
  by_contra hcon
  rcases le_or_gt (Valued.v α) (Valued.v β) with hαβ | hβα
  · have hβ1 : 1 < Valued.v β := by
      by_contra h'; exact hcon ⟨hαβ.trans (not_lt.1 h'), not_lt.1 h'⟩
    have hβ0 : β ≠ 0 := by rintro rfl; rw [map_zero] at hβ1; exact not_lt_zero hβ1
    obtain ⟨hb, hdet, htr⟩ := v_sub_smul_one_of_v_le K v Y α β hβ0 hαβ
    have hβinv := inv_le_v_of_one_lt K v ϖ hϖ hβ1
    refine hYgen (-α / β) hb ⟨?_, ?_⟩
    · rw [hdet]
      calc (Valued.v β)⁻¹ ^ 2 * Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det
          ≤ Valued.v ϖ ^ 2 * 1 := mul_le_mul' (pow_le_pow_left' hβinv 2) h.1
        _ = Valued.v ϖ ^ 2 := mul_one _
    · rw [htr]
      calc (Valued.v β)⁻¹ * Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).trace
          ≤ Valued.v ϖ * 1 := mul_le_mul' hβinv h.2
        _ = Valued.v ϖ := mul_one _
  · have hα1 : 1 < Valued.v α := by
      by_contra h'; exact hcon ⟨not_lt.1 h', hβα.le.trans (not_lt.1 h')⟩
    have e := v_det_eq_sq_of_v_lt K v Y hYint α β hβα
    have : 1 < Valued.v α ^ 2 := by
      rw [pow_two]; exact one_lt_mul'' hα1 hα1
    exact absurd h.1 (by rw [e]; exact not_le.2 this)

theorem v_coe_le_one (r : v.adicCompletionIntegers K) : Valued.v (r : v.adicCompletion K) ≤ 1 := by
  have h := r.2
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  exact h

theorem exists_irreducible_coe_eq (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ)) :
    ∃ p : v.adicCompletionIntegers K, Irreducible p ∧ (p : v.adicCompletion K) = ϖ := by
  rw [← WithZero.exp_eq_coe_ofAdd] at hϖ
  have hle : Valued.v ϖ ≤ 1 := by
    rw [hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have hmem : ϖ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact hle
  refine ⟨⟨ϖ, hmem⟩, ⟨?_, fun a b hab => ?_⟩, rfl⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v ϖ ≠ 1
    rw [hϖ, ← WithZero.exp_zero, Ne, WithZero.exp_inj]; norm_num
  · have hv : Valued.v (a : v.adicCompletion K) * Valued.v (b : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul, ← hϖ]; exact congrArg Valued.v (congrArg Subtype.val hab).symm
    have ha : Valued.v (a : v.adicCompletion K) ≤ 1 := v_coe_le_one K v a
    have hb : Valued.v (b : v.adicCompletion K) ≤ 1 := v_coe_le_one K v b
    by_cases ha1 : Valued.v (a : v.adicCompletion K) = 1
    · exact Or.inl (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 ha1)
    · right
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      by_contra hb1
      have ha' := le_exp_neg_one_of_lt_one (lt_of_le_of_ne ha ha1)
      have hb' := le_exp_neg_one_of_lt_one (lt_of_le_of_ne hb hb1)
      have := mul_le_mul' ha' hb'
      rw [hv, ← WithZero.exp_add, WithZero.exp_le_exp] at this
      omega

theorem v_algebraMap_le_one (r : v.adicCompletionIntegers K) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) ≤ 1 :=
  v_coe_le_one K v r

theorem trace_map_algebraMap (M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) :
    (M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).trace =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) M.trace := by
  simp [Matrix.trace_fin_two]

theorem det_map_algebraMap (M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) :
    (M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) M.det :=
  (RingHom.map_det _ M).symm

theorem v_trace_le_of_normal_form (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (trW detW c trM detM : v.adicCompletion K) (k : ℤ) (hc : Valued.v c = WithZero.exp (-k))
    (htr : trW = c * trM) (hdet : detW = c ^ 2 * detM) (htrM : Valued.v trM ≤ 1)
    (hdetM : Valued.v detM = 1 ∨ Valued.v detM = Valued.v ϖ)
    (hle : Valued.v detW ≤ Valued.v ϖ ^ 2) : Valued.v trW ≤ Valued.v ϖ := by
  rw [hϖ, ← WithZero.exp_eq_coe_ofAdd] at hdetM hle ⊢
  have hk : 1 ≤ k := by
    rw [hdet, map_mul, map_pow, hc, pow_two, pow_two, ← WithZero.exp_add, ← WithZero.exp_add] at hle
    rcases hdetM with h1 | h1
    · rw [h1, mul_one, WithZero.exp_le_exp] at hle
      omega
    · rw [h1, ← WithZero.exp_add, WithZero.exp_le_exp] at hle
      omega
  rw [htr, map_mul, hc]
  calc WithZero.exp (-k) * Valued.v trM ≤ WithZero.exp (-1) * 1 :=
        mul_le_mul' (WithZero.exp_le_exp.2 (by omega)) htrM
    _ = WithZero.exp (-1) := mul_one _

theorem v_trace_le_of_v_det_le_of_not_isSquare
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (W : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (hW : ¬ IsSquare (W.trace ^ 2 - 4 * W.det))
    (hdet : Valued.v W.det ≤ Valued.v ϖ ^ 2) :
    Valued.v W.trace ≤ Valued.v ϖ := by
  obtain ⟨p, hp, hpϖ⟩ := exists_irreducible_coe_eq K v ϖ hϖ
  have hdet0 : W.det ≠ 0 := by
    intro h0; apply hW; rw [h0, mul_zero, sub_zero, pow_two]; exact ⟨W.trace, rfl⟩
  obtain ⟨Wu, hWu⟩ : ∃ Wu : GL (Fin 2) (v.adicCompletion K), Wu = Matrix.GeneralLinearGroup.mkOfDetNeZero W hdet0 :=
    ⟨_, rfl⟩
  have hcoe : (Wu : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = W := by rw [hWu]; rfl
  obtain ⟨x, k, hcases⟩ :=
    LT.LatticeTree.exists_conj_eq_zpow_smul_of_not_isSquare_discr K v p hp Wu (by rw [hcoe]; exact hW)

  have htrc : Matrix.trace ((x⁻¹ * Wu * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      W.trace := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, hcoe]
  have hdetc : Matrix.det ((x⁻¹ * Wu * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      W.det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul, hcoe]
  have hvc : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) p ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) p = (p : v.adicCompletion K) from rfl,
      hpϖ, hϖ, ← WithZero.exp_eq_coe_ofAdd, ← WithZero.exp_zsmul]
    congr 1; ring

  have read : ∀ M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K),
      ((x⁻¹ * Wu * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) p ^ k •
          M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) →
      W.trace = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) p ^ k *
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) M.trace ∧
      W.det = (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) p ^ k) ^ 2 *
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) M.det := by
    intro M hM
    refine ⟨?_, ?_⟩
    · rw [← htrc, hM, Matrix.trace_smul, smul_eq_mul, trace_map_algebraMap]
    · rw [← hdetc, hM, Matrix.det_smul, Fintype.card_fin, det_map_algebraMap]
  rcases hcases with ⟨γ', -, -, -, -, -, hconj⟩ | ⟨γ', -, -, -, -, -, -, -, hconj⟩ | ⟨Y', w, hdetY', -, hconj⟩
  · obtain ⟨h1, h2⟩ := read _ hconj
    have hu : IsUnit (Matrix.det (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ'.isUnit
    exact v_trace_le_of_normal_form K v ϖ hϖ _ _ _ _ _ k hvc h1 h2 (v_algebraMap_le_one K v _)
      (Or.inl (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu)) hdet
  · obtain ⟨h1, h2⟩ := read _ hconj
    have hu : IsUnit (Matrix.det (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))) :=
      (Matrix.isUnit_iff_isUnit_det _).1 γ'.isUnit
    exact v_trace_le_of_normal_form K v ϖ hϖ _ _ _ _ _ k hvc h1 h2 (v_algebraMap_le_one K v _)
      (Or.inl (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.1 hu)) hdet
  · obtain ⟨h1, h2⟩ := read _ hconj
    have hdY : Matrix.det Y' = p * w := by rw [Matrix.det_fin_two]; exact hdetY'
    refine v_trace_le_of_normal_form K v ϖ hϖ _ _ _ _ _ k hvc h1 h2 (v_algebraMap_le_one K v _) (Or.inr ?_) hdet
    rw [hdY, map_mul, map_mul, v_algebraMap_units, mul_one,
      show algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) p = (p : v.adicCompletion K) from rfl, hpϖ]

theorem v_le_one_of_v_det_eq_one
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (α β : v.adicCompletion K)
    (h : Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • Y).det = 1) :
    Valued.v α ≤ 1 ∧ Valued.v β ≤ 1 := by
  rcases le_or_gt (Valued.v α) (Valued.v β) with hαβ | hβα
  · by_cases hβ1 : Valued.v β ≤ 1
    · exact ⟨hαβ.trans hβ1, hβ1⟩
    · exfalso
      rw [not_le] at hβ1
      have hβ0 : β ≠ 0 := by rintro rfl; rw [map_zero] at hβ1; exact not_lt_zero hβ1
      obtain ⟨hb, hdet, htr⟩ := v_sub_smul_one_of_v_le K v Y α β hβ0 hαβ
      have hβinv := inv_le_v_of_one_lt K v ϖ hϖ hβ1
      have hdetW : Valued.v (Y - (-α / β) • 1).det ≤ Valued.v ϖ ^ 2 := by
        rw [hdet, h, mul_one]; exact pow_le_pow_left' hβinv 2
      have hW : ¬ IsSquare ((Y - (-α / β) • 1).trace ^ 2 - 4 * (Y - (-α / β) • 1).det) := by
        rwa [discr_sub_smul_one]
      exact hYgen (-α / β) hb ⟨hdetW, v_trace_le_of_v_det_le_of_not_isSquare K v ϖ hϖ _ hW hdetW⟩
  · have e := v_det_eq_sq_of_v_lt K v Y hYint α β hβα
    rw [h] at e
    have hα : Valued.v α = 1 := by
      rcases lt_trichotomy (Valued.v α) 1 with h1 | h1 | h1
      · exfalso
        have : Valued.v α ^ 2 < 1 := by rw [pow_two]; exact mul_lt_one_of_lt_of_le h1 h1.le
        exact absurd e.symm this.ne
      · exact h1
      · exfalso
        have : 1 < Valued.v α ^ 2 := by rw [pow_two]; exact one_lt_mul'' h1 h1
        exact absurd e.symm this.ne'
    exact ⟨hα.le, (hβα.trans_eq hα).le⟩

theorem exists_integral_coords_of_mem_centralizer_of_v_det_eq_one
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (δ : GL (Fin 2) (v.adicCompletion K)) (a b : v.adicCompletion K) (hb : b ≠ 0)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + b • Y)
    (t : GL (Fin 2) (v.adicCompletion K))
    (ht : t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))))
    (hdet : Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    ∃ α β : v.adicCompletion K, Valued.v α ≤ 1 ∧ Valued.v β ≤ 1 ∧
      (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = α • 1 + β • Y := by

  have hYns : ¬ ∃ y : v.adicCompletion K, Y = y • 1 := by
    rintro ⟨y, rfl⟩
    have hy : Valued.v y ≤ 1 := by
      have h2 := hYint.1
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, map_pow] at h2
      by_contra hy; rw [not_le] at hy
      exact absurd h2 (not_le.2 (by rw [pow_two]; exact one_lt_mul'' hy hy))
    exact hYgen y hy ⟨by rw [sub_self, Matrix.det_zero, map_zero]; exact zero_le',
      by rw [sub_self, Matrix.trace_zero, map_zero]; exact zero_le'⟩
  have ht' : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * Y = Y * t := by
    have h1 : (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * δ = δ * t := by
      rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_singleton_iff.1 ht)]
    rw [hδ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, add_right_inj] at h1
    exact smul_right_injective _ hb h1
  obtain ⟨α, β, hαβ⟩ := (mul_eq_mul_iff_exists_eq_smul_one_add_smul Y _ hYns).1 ht'
  refine ⟨α, β, ?_⟩
  have hint := v_le_one_of_v_det_eq_one K v ϖ hϖ Y hYint hYgen hYell α β (by rw [← hαβ]; exact hdet)
  exact ⟨hint.1, hint.2, hαβ⟩

theorem v_trace_le_one_of_mem_centralizer_of_v_det_eq_one
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (δ : GL (Fin 2) (v.adicCompletion K)) (a b : v.adicCompletion K) (hb : b ≠ 0)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + b • Y)
    (t : GL (Fin 2) (v.adicCompletion K))
    (ht : t ∈ Subgroup.centralizer ({δ} : Set (GL (Fin 2) (v.adicCompletion K))))
    (hdet : Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    Valued.v (Matrix.trace (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≤ 1 := by
  obtain ⟨α, β, hα, hβ, ht⟩ :=
    exists_integral_coords_of_mem_centralizer_of_v_det_eq_one K v ϖ hϖ Y hYint hYgen hYell δ a b hb hδ t ht hdet
  rw [ht, trace_smul_one_add_smul]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [two_mul]
    exact (Valuation.map_add _ _ _).trans (by rw [max_self]; exact hα)
  · rw [map_mul]; exact mul_le_one' hβ hYint.2

end Integrality

section Compact

theorem v_det_eq_one_iff_le_and_inv_le (t : GL (Fin 2) (v.adicCompletion K)) :
    Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 ↔
      Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≤ 1 ∧
        Valued.v (Matrix.det ((t⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≤ 1 := by
  have hmul : Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) *
      Valued.v (Matrix.det ((t⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    rw [h, one_mul] at hmul
    exact hmul.le
  · rintro ⟨h1, h2⟩
    apply le_antisymm h1
    by_contra hlt
    rw [not_le] at hlt
    exact absurd hmul (mul_lt_one_of_lt_of_le hlt h2).ne

theorem isClosed_Tc (δ : GL (Fin 2) (v.adicCompletion K)) :
    IsClosed ((Tc K v δ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := by
  have hball : IsClosed {x : v.adicCompletion K | Valued.v x ≤ 1} := by
    have : {x : v.adicCompletion K | Valued.v x ≤ 1} = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      ext x; simp [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)).isClosed
  have e : ((Tc K v δ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) =
      {t | t * δ = δ * t} ∩
        ((fun t : GL (Fin 2) (v.adicCompletion K) => Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
            {x | Valued.v x ≤ 1} ∩
          (fun t : GL (Fin 2) (v.adicCompletion K) =>
              Matrix.det ((t⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
            {x | Valued.v x ≤ 1}) := by
    ext t
    simp only [SetLike.mem_coe, mem_Tc_iff_v_det_eq_one, Subgroup.mem_centralizer_singleton_iff, Set.mem_inter_iff,
      Set.mem_setOf_eq, Set.mem_preimage, v_det_eq_one_iff_le_and_inv_le]
  rw [e]
  refine (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)).inter
    ((hball.preimage ?_).inter (hball.preimage ?_))
  · exact Units.continuous_val.matrix_det
  · exact (Units.continuous_val.comp continuous_inv).matrix_det

theorem isCompact_Tc
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (δ : GL (Fin 2) (v.adicCompletion K)) (a b : v.adicCompletion K) (hb : b ≠ 0)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + b • Y) :
    IsCompact ((Tc K v δ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : v.adicCompletion K × v.adicCompletion K → Matrix (Fin 2) (Fin 2) (v.adicCompletion K),
      φ = fun p => p.1 • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + p.2 • Y := ⟨_, rfl⟩
  have hφc : Continuous φ := by
    rw [hφ]
    exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hO : IsCompact {x : v.adicCompletion K | Valued.v x ≤ 1} := by
    have : {x : v.adicCompletion K | Valued.v x ≤ 1} = (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
      ext x; simp [HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [this]
    exact isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v)
  have hC : IsCompact (φ '' ({x : v.adicCompletion K | Valued.v x ≤ 1} ×ˢ {x : v.adicCompletion K | Valued.v x ≤ 1})) :=
    (hO.prod hO).image hφc
  have mem : ∀ t ∈ Tc K v δ, (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ∈
      φ '' ({x : v.adicCompletion K | Valued.v x ≤ 1} ×ˢ {x : v.adicCompletion K | Valued.v x ≤ 1}) := by
    intro t ht
    rw [mem_Tc_iff_v_det_eq_one] at ht
    obtain ⟨α, β, hα, hβ, heq⟩ := exists_integral_coords_of_mem_centralizer_of_v_det_eq_one K v ϖ hϖ Y hYint hYgen hYell
      δ a b hb hδ t ht.1 ht.2
    exact ⟨(α, β), ⟨hα, hβ⟩, by rw [hφ, heq]⟩
  have hsub : ((Tc K v δ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) ⊆
      Units.embedProduct (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ⁻¹'
        ((φ '' ({x : v.adicCompletion K | Valued.v x ≤ 1} ×ˢ {x : v.adicCompletion K | Valued.v x ≤ 1})) ×ˢ
          (MulOpposite.op '' (φ '' ({x : v.adicCompletion K | Valued.v x ≤ 1} ×ˢ {x : v.adicCompletion K | Valued.v x ≤ 1})))) := by
    intro t ht
    simp only [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
    exact ⟨mem t ht, ⟨_, mem t⁻¹ ((Tc K v δ).inv_mem ht), rfl⟩⟩
  exact (Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))).of_isClosed_subset
    (isClosed_Tc K v δ) hsub

end Compact

section BridgeKv

theorem not_isSquare_discr_of_smul_eq_smul_one_add_smul
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
    (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγ : γ ∈ Subgroup.centralizer ({γ₀} : Set (GL (Fin 2) (v.adicCompletion K))))
    (hγreg : IsRegularSemisimple γ)
    (c a b : v.adicCompletion K) (hc : c ≠ 0) (hb : b ≠ 0) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (h : c • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + b • Y) :
    ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det) :=
  not_isSquare_discr_of_smul_eq_smul_one_add_smul' (two_ne_zero_adicCompletion K v) γ₀
    ((isRegularSemisimple_iff_ne_zero γ₀).1 hreg) hns γ hγ ((isRegularSemisimple_iff_ne_zero γ).1 hγreg) c a b hc hb Y h

theorem v_trace_le_one_of_mem_Tc
    (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (δ : GL (Fin 2) (v.adicCompletion K)) (a b : v.adicCompletion K) (hb : b ≠ 0)
    (hδ : (δ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + b • Y)
    (t : GL (Fin 2) (v.adicCompletion K)) (ht : t ∈ Tc K v δ) :
    Valued.v (Matrix.trace (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≤ 1 :=
  v_trace_le_one_of_mem_centralizer_of_v_det_eq_one K v ϖ hϖ Y hYint hYgen hYell δ a b hb hδ t
    ((mem_Tc_iff_v_det_eq_one K v δ t).1 ht).1 ((mem_Tc_iff_v_det_eq_one K v δ t).1 ht).2

end BridgeKv

section A8a

theorem isUnit_det_smul_one_add_of_anisotropic {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) (Y : Matrix (Fin 2) (Fin 2) R)
    (hanis : ∀ (a : R ⧸ Ideal.span {ϖ}) (w : Fin 2 → R ⧸ Ideal.span {ϖ}),
      Matrix.mulVec (Y.map (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) w = a • w → w = 0)
    (b : R) : IsUnit (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det := by
  haveI : (Ideal.span {ϖ}).IsMaximal := by rw [← hϖ.maximalIdeal_eq]; exact IsLocalRing.maximalIdeal.isMaximal R
  by_contra hnu
  have hmem : (b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).det ∈ Ideal.span {ϖ} := by
    rw [← hϖ.maximalIdeal_eq]; exact hnu
  have hz : ((b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).map
      (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  letI : Field (R ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field (Ideal.span {ϖ})
  have hnotinj : ¬ Function.Injective (((b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).map
      (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})).mulVec) := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, hz]
    exact not_isUnit_zero
  obtain ⟨w₁, w₂, hw12, hne⟩ := Function.not_injective_iff.mp hnotinj
  apply hne
  rw [← sub_eq_zero]
  apply hanis (-(Ideal.Quotient.mk (Ideal.span {ϖ}) b)) (w₁ - w₂)
  have hw : Matrix.mulVec ((b • (1 : Matrix (Fin 2) (Fin 2) R) + Y).map
      (Ideal.Quotient.mk (Ideal.span {ϖ}) : R →+* R ⧸ Ideal.span {ϖ})) (w₁ - w₂) = 0 := by
    rw [Matrix.mulVec_sub, hw12, sub_self]
  rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec, Matrix.map_smul' _ _ _ (map_mul _),
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.smul_mulVec, Matrix.one_mulVec] at hw
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_right hw

theorem torus_A8a {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (hϖint : ϖ ∈ v.adicCompletionIntegers K)
    (γ' x : GL (Fin 2) (v.adicCompletion K)) (m : ℕ) (a₁ : v.adicCompletionIntegers K)
    (Y₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))
    (hg : ((x⁻¹ * γ' * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) a₁ • 1 +
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨ϖ, hϖint⟩ ^ m •
          Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))
    (hanis : ∀ (a : v.adicCompletionIntegers K ⧸ Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)})
        (w : Fin 2 → v.adicCompletionIntegers K ⧸ Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)}),
        Matrix.mulVec (Y₁.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)}) :
            v.adicCompletionIntegers K →+* v.adicCompletionIntegers K ⧸ Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)})) w = a • w → w = 0) :
    ∀ t ∈ Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))),
      Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ≠ Multiplicative.ofAdd (-1 : ℤ) := by
  intro t ht hvt

  set φ := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) with hφ
  set ϖR : v.adicCompletionIntegers K := ⟨ϖ, hϖint⟩ with hϖR
  set YK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) := Y₁.map φ with hYK
  have hϖirr : Irreducible ϖR :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖR).mpr
      (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hϖ)
  have hϖ0 : ϖ ≠ 0 := v_ne_zero_of_v_eq_ofAdd K v ϖ hϖ
  have hc0 : φ ϖR ^ m ≠ 0 := pow_ne_zero _ (by rw [hφ, ValuationSubring.algebraMap_apply]; exact hϖ0)
  have hφinj : Function.Injective φ := fun a b h => Subtype.ext h

  have hYKint : Valued.v YK.det ≤ 1 ∧ Valued.v YK.trace ≤ 1 := by
    rw [hYK, det_map_algebraMap, trace_map_algebraMap]
    exact ⟨v_algebraMap_le_one K v _, v_algebraMap_le_one K v _⟩

  have hns : ¬ ∃ a : v.adicCompletion K, YK = a • 1 := by
    rintro ⟨a, ha⟩
    have h01 : Y₁ 0 1 = 0 := hφinj (by
      have := congrFun (congrFun ha 0) 1
      rw [hYK, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero] at this
      rw [this, map_zero])
    have h10 : Y₁ 1 0 = 0 := hφinj (by
      have := congrFun (congrFun ha 1) 0
      rw [hYK, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero] at this
      rw [this, map_zero])
    have key := hanis (Ideal.Quotient.mk _ (Y₁ 0 0)) (Pi.single 0 1) (by
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, h10, Pi.single_apply])
    have h1 : (1 : v.adicCompletionIntegers K ⧸ Ideal.span {ϖR}) = 0 := by
      have := congrFun key 0
      simpa using this
    exact hϖirr.not_isUnit (Ideal.span_singleton_eq_top.mp
      ((Ideal.Quotient.zero_eq_one_iff).mp h1.symm))

  set t' : GL (Fin 2) (v.adicCompletion K) := x⁻¹ * t * x with ht'
  have hcommG : t' * (x⁻¹ * γ' * x) = (x⁻¹ * γ' * x) * t' := by
    have h := (Subgroup.mem_centralizer_singleton_iff.mp ht)
    rw [ht']
    calc x⁻¹ * t * x * (x⁻¹ * γ' * x) = x⁻¹ * (t * γ') * x := by group
      _ = x⁻¹ * (γ' * t) * x := by rw [h]
      _ = x⁻¹ * γ' * x * (x⁻¹ * t * x) := by group
  have hcomm : ((t' : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * YK =
      YK * (t' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    have h2 : ((t' : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        ((x⁻¹ * γ' * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        ((x⁻¹ * γ' * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        (t' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      rw [← Units.val_mul, ← Units.val_mul, hcommG]
    rw [hg] at h2
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, add_right_inj] at h2
    exact smul_right_injective _ hc0 h2
  obtain ⟨α, β, hαβ⟩ := (mul_eq_mul_iff_exists_eq_smul_one_add_smul YK _ hns).mp hcomm

  have hdet' : Matrix.det ((t' : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    rw [ht', Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, one_mul]
  rw [← hdet', hαβ] at hvt

  have hsq : ∃ z : v.adicCompletion K, z ≠ 0 ∧
      Valued.v (α • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + β • YK).det = Valued.v z ^ 2 := by
    rcases eq_or_ne β 0 with hβ | hβ
    · refine ⟨α, ?_, ?_⟩
      · rintro rfl
        have : ((t' : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det = 0 := by
          rw [hαβ, hβ, zero_smul, zero_smul, add_zero, Matrix.det_zero]
        exact (Matrix.GeneralLinearGroup.det_ne_zero t') this
      · rw [hβ, zero_smul, add_zero, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, map_pow]
    · rcases lt_or_ge (Valued.v β) (Valued.v α) with hlt | hle
      · refine ⟨α, ?_, v_det_eq_sq_of_v_lt K v YK hYKint α β hlt⟩
        rintro rfl; rw [map_zero] at hlt; exact not_lt_zero hlt
      · obtain ⟨hbint, hdetb, -⟩ := v_sub_smul_one_of_v_le K v YK α β hβ hle

        set bR : v.adicCompletionIntegers K := ⟨-α / β, hbint⟩ with hbR
        have hφb : φ bR = -α / β := rfl
        have hunit : Valued.v (YK - (-α / β) • 1).det = 1 := by
          have hmat : YK - (-α / β) • 1 = ((-bR) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) + Y₁).map φ := by
            rw [Matrix.map_add _ (map_add _), Matrix.map_smul' _ _ _ (map_mul _),
              Matrix.map_one _ (map_zero _) (map_one _), map_neg, hφb, ← hYK, neg_smul, sub_eq_add_neg, add_comm]
          rw [hmat, det_map_algebraMap]
          exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
            (isUnit_det_smul_one_add_of_anisotropic ϖR hϖirr Y₁ hanis (-bR))
        have hvβ0 : Valued.v β ≠ 0 := (Valuation.ne_zero_iff _).2 hβ
        refine ⟨β, hβ, ?_⟩
        rw [hunit] at hdetb

        have := hdetb.symm
        rw [inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hvβ0)] at this
        exact this.symm
  obtain ⟨z, hz0, hz⟩ := hsq
  rw [hz] at hvt
  have hvz0 : Valued.v z ≠ 0 := (Valuation.ne_zero_iff _).2 hz0
  rw [← WithZero.exp_log hvz0, ← WithZero.exp_nsmul, ← WithZero.exp_eq_coe_ofAdd, WithZero.exp_inj, two_nsmul] at hvt
  omega

end A8a

theorem torus_A8b {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (hϖint : ϖ ∈ v.adicCompletionIntegers K)
    (γ' x : GL (Fin 2) (v.adicCompletion K)) (m : ℕ) (a₁ : v.adicCompletionIntegers K)
    (Y₁ : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K))
    (hg : ((x⁻¹ * γ' * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) a₁ • 1 +
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨ϖ, hϖint⟩ ^ m •
          Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)))
    (w : (v.adicCompletionIntegers K)ˣ)
    (hYdet : Y₁ 0 0 * Y₁ 1 1 - Y₁ 0 1 * Y₁ 1 0 = ⟨ϖ, hϖint⟩ * (w : v.adicCompletionIntegers K)) :
    ∃ t ∈ Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))),
      Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ) := by

  have hdetR : Y₁.det = ⟨ϖ, hϖint⟩ * (w : v.adicCompletionIntegers K) := by rw [Matrix.det_fin_two]; exact hYdet
  have hdetK : (Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det =
      ϖ * ((w : v.adicCompletionIntegers K) : v.adicCompletion K) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hdetR, map_mul]; rfl
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hw1 : Valued.v ((w : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp w.isUnit
  have hdet0 : (Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det ≠ 0 := by
    rw [hdetK]; refine mul_ne_zero hϖ0 ?_
    intro h; rw [h, map_zero] at hw1; exact zero_ne_one hw1
  set Yg := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet0 with hYg
  refine ⟨x * Yg * x⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]

    have hcomm : Yg * (x⁻¹ * γ' * x) = (x⁻¹ * γ' * x) * Yg := by
      apply Units.ext
      rw [Units.val_mul Yg (x⁻¹ * γ' * x), Units.val_mul (x⁻¹ * γ' * x) Yg, hg]
      show Y₁.map _ * _ = _ * Y₁.map _
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    calc x * Yg * x⁻¹ * γ' = x * (Yg * (x⁻¹ * γ' * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * γ' * x) * Yg) * x⁻¹ := by rw [hcomm]
      _ = γ' * (x * Yg * x⁻¹) := by group
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul]
    have hx : Valued.v (Matrix.det (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) *
        Valued.v (Matrix.det ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
      rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
    rw [mul_right_comm, hx, one_mul]
    show Valued.v (Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).det = _
    rw [hdetK, map_mul, hϖ, hw1, mul_one]

open Classical in

theorem count_SD
    {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ)) (hϖint : ϖ ∈ v.adicCompletionIntegers K)
    (γ' : GL (Fin 2) (v.adicCompletion K)) (m : ℕ) (a : v.adicCompletion K) (ha : Valued.v a ≤ 1)
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (hγ' : (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + ϖ ^ m • Y)
    (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 → ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det))
    (hdet : Valued.v (Matrix.det (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    (Ideal.absNorm v.asIdeal - 1) * LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ' + 2 =
      if (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
            Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ))
      then 2 * Ideal.absNorm v.asIdeal ^ (m + 1) else (Ideal.absNorm v.asIdeal + 1) * Ideal.absNorm v.asIdeal ^ m := by

  set ϖR : v.adicCompletionIntegers K := ⟨ϖ, hϖint⟩ with hϖR
  have hϖirr : Irreducible ϖR :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖR).mpr
      (HeightOneSpectrum.adicCompletion.maximalIdeal_eq_span_uniformizer K v hϖ)

  have hq : Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span ({ϖR} : Set (v.adicCompletionIntegers K))) =
      Ideal.absNorm v.asIdeal :=
    IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_quot_span_eq_absNorm K v ϖR hϖ
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  haveI : Finite (v.adicCompletionIntegers K ⧸ Ideal.span ({ϖR} : Set (v.adicCompletionIntegers K))) :=
    Nat.finite_of_card_ne_zero (by rw [hq]; exact hN0)

  have hYdet : Y.det ≠ 0 := by
    intro h; exact hYell ⟨Y.trace, by rw [h, mul_zero, sub_zero, sq]⟩

  obtain ⟨x, μ, Y₁, hconj, hkind⟩ :=
    normalForm K v hϖ hϖint Y hYint hYgen hYell (Matrix.GeneralLinearGroup.mkOfDetNeZero Y hYdet) rfl

  have haint : a + ϖ ^ m * (μ : v.adicCompletion K) ∈ v.adicCompletionIntegers K :=
    add_mem ha (mul_mem (pow_mem hϖint m) μ.2)
  set a₁ : v.adicCompletionIntegers K := ⟨a + ϖ ^ m * (μ : v.adicCompletion K), haint⟩ with ha₁
  have hconj' : ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * Y *
      (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) μ • 1 +
        Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
    rw [← hconj, Units.val_mul, Units.val_mul]; rfl
  have hg : ((x⁻¹ * γ' * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) a₁ • 1 +
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖR ^ m •
          Y₁.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) := by
    rw [Units.val_mul, Units.val_mul, hγ', Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Units.inv_mul, Matrix.mul_smul, Matrix.smul_mul, hconj', smul_add, smul_smul, ← add_assoc,
      ← add_smul]
    rfl

  have hdetR : IsUnit ((a₁ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) + ϖR ^ m • Y₁).det) := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h1 : ((a₁ • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) + ϖR ^ m • Y₁).det).1 =
        Matrix.det ((x⁻¹ * γ' * x : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      have hφ : ∀ z : v.adicCompletionIntegers K,
          z.1 = algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) z := fun z => rfl
      rw [hg, hφ, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add _),
        Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_smul' _ _ _ (map_mul _),
        Matrix.map_one _ (map_zero _) (map_one _), map_pow]
    rw [h1, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul, mul_right_comm,
      ← map_mul, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, map_one, one_mul,
      hdet]

  have hcount : LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ' =
      LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) (x⁻¹ * γ' * x) := by
    conv_lhs => rw [show γ' = x * (x⁻¹ * γ' * x) * x⁻¹ by group]
    exact LT.LatticeTree.unitOrbitalCount_conj _ _

  have hTC := LT.LatticeTree.unitOrbitalCount_eq_of_anisotropic_and_eq_of_eisenstein_of_depth
    (v.adicCompletionIntegers K) (v.adicCompletion K) ϖR hϖirr
  rcases hkind with hanis | ⟨w, hYdet1, hYtr1⟩
  ·
    have hb2 := hTC.1 Y₁ hanis m a₁ (x⁻¹ * γ' * x) hg hdetR
    have hnot : ¬ (∃ t : GL (Fin 2) (v.adicCompletion K),
        t ∈ Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
          Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ)) := by
      rintro ⟨t, ht, hvt⟩
      exact torus_A8a K v hϖ hϖint γ' x m a₁ Y₁ hg hanis t ht hvt
    rw [if_neg hnot, hcount, ← hq]
    exact hb2
  ·
    have hb3 := hTC.2 Y₁ w (by rw [Matrix.det_fin_two]; exact hYdet1) (by rw [Matrix.trace_fin_two]; exact hYtr1)
      m a₁ (x⁻¹ * γ' * x) hg hdetR
    have hram : ∃ t : GL (Fin 2) (v.adicCompletion K),
        t ∈ Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))) ∧
          Valued.v (Matrix.det (t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = Multiplicative.ofAdd (-1 : ℤ) := by
      obtain ⟨t, ht, hvt⟩ := torus_A8b K v hϖ hϖint γ' x m a₁ Y₁ hg w hYdet1
      exact ⟨t, ht, hvt⟩
    rw [if_pos hram, hcount, ← hq]
    exact hb3

theorem isUnit_det_one_add_of_aniso {R : Type*} [CommRing R] (I : Ideal R) [hI : I.IsMaximal]
    (hlocal : ∀ r : R, ¬ IsUnit r → r ∈ I) (Y₁ : Matrix (Fin 2) (Fin 2) R)
    (haniso : ∀ (a : R ⧸ I) (w : Fin 2 → R ⧸ I),
      Matrix.mulVec (Y₁.map (Ideal.Quotient.mk I : R →+* R ⧸ I)) w = a • w → w = 0) :
    IsUnit (1 + Y₁).det := by
  classical
  by_contra hnu
  have hmem := hlocal _ hnu
  have h1Y' : ((1 : Matrix (Fin 2) (Fin 2) R) + Y₁).map (Ideal.Quotient.mk I : R →+* R ⧸ I) =
      1 + Y₁.map (Ideal.Quotient.mk I : R →+* R ⧸ I) := by
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, map_add, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs <;> simp
  have hdet0' : (1 + Y₁.map (Ideal.Quotient.mk I : R →+* R ⧸ I)).det = 0 := by
    rw [← h1Y', ← RingHom.mapMatrix_apply, ← RingHom.map_det, Ideal.Quotient.eq_zero_iff_mem]; exact hmem
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0'
  apply hw0
  refine haniso (-1) w ?_
  rw [Matrix.add_mulVec, Matrix.one_mulVec] at hw
  rw [neg_one_smul]
  exact eq_neg_of_add_eq_zero_right hw

theorem det_one_add_of_eisenstein {R : Type*} [CommRing R] (p : R) (Y₁ : Matrix (Fin 2) (Fin 2) R) (w : R)
    (hdet : Y₁ 0 0 * Y₁ 1 1 - Y₁ 0 1 * Y₁ 1 0 = p * w) (t : R) (ht : Y₁ 0 0 + Y₁ 1 1 = p * t) :
    (1 + Y₁).det = 1 + p * (t + w) := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
  linear_combination ht + hdet

theorem exists_shift_det_unit {ϖ : v.adicCompletion K} (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (hϖint : ϖ ∈ v.adicCompletionIntegers K)
    (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))
    (hYell : ¬ IsSquare (Y.trace ^ 2 - 4 * Y.det)) (n : ℕ) :
    ∃ a' : v.adicCompletion K, Valued.v a' ≤ 1 ∧
      Valued.v (a' • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + ϖ ^ n • Y).det = 1 := by
  classical
  have hv1 : Valued.v ϖ < 1 := (valuation_lt_one_iff_le K v hϖ ϖ).2 le_rfl
  have hvle : Valued.v ϖ ≤ 1 := hv1.le
  have hι : ∀ r : v.adicCompletionIntegers K,
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) ≤ 1 := fun r =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 r.2
  rcases Nat.eq_zero_or_pos n with hn | hn
  swap
  ·
    refine ⟨1, by rw [map_one], ?_⟩
    rw [det_smul_one_add_smul, one_pow, one_mul, add_assoc]
    apply Valuation.map_one_add_of_lt
    have hϖn : Valued.v (ϖ ^ n) < 1 := by
      rw [map_pow]; exact pow_lt_one' hv1 hn.ne'
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul]
      calc Valued.v (ϖ ^ n) * Valued.v Y.trace ≤ Valued.v (ϖ ^ n) * 1 := mul_le_mul_right hYint.2 _
        _ = Valued.v (ϖ ^ n) := mul_one _
        _ < 1 := hϖn
    · rw [map_mul, map_pow]
      calc Valued.v (ϖ ^ n) ^ 2 * Valued.v Y.det ≤ Valued.v (ϖ ^ n) ^ 2 * 1 := mul_le_mul_right hYint.1 _
        _ = Valued.v (ϖ ^ n) ^ 2 := mul_one _
        _ < 1 := pow_lt_one' hϖn two_ne_zero
  ·
    subst hn
    rw [pow_zero]
    have hdet0 : Y.det ≠ 0 := by
      intro h0; apply hYell; rw [h0, mul_zero, sub_zero]; exact ⟨Y.trace, sq Y.trace⟩
    obtain ⟨x, μ, Y₁, hY', hkind⟩ := normalForm K v hϖ hϖint Y hYint hYgen hYell
      (Matrix.GeneralLinearGroup.mkOfDetNeZero Y hdet0) rfl
    set ι := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) with hιdef
    have hdetmap : ∀ B : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K), (B.map ι).det = ι B.det := fun B => by
      rw [hιdef, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    refine ⟨1 - ι μ, ?_, ?_⟩
    · have : (1 : v.adicCompletion K) - ι μ = ι (1 - μ) := by rw [map_sub, map_one]
      rw [this]; exact hι _
    have h1Y : ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K)) + Y₁).map ι = 1 + Y₁.map ι := by
      ext i j
      rw [Matrix.map_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, map_add, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp

    have hconj : ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        ((1 - ι μ) • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + (1 : v.adicCompletion K) • Y) *
          (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ((1 + Y₁).map ι) := by
      have hx : ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * Y *
          (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ι μ • 1 + Y₁.map ι := by
        rw [← hY', Units.val_mul, Units.val_mul]; rfl
      rw [one_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Units.inv_mul, hx,
        h1Y, sub_smul, one_smul]
      abel
    rw [← Matrix.det_units_conj' x, hconj, hdetmap]
    change Valued.v (((1 + Y₁).det : v.adicCompletionIntegers K) : v.adicCompletion K) = 1
    rw [← HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    rcases hkind with haniso | ⟨w, hdetY₁, htrY₁⟩
    ·
      have hirr := irreducible_of_valuation_eq K v hϖ hϖint
      haveI hmaxI : (Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)}).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible hirr
      have hmax : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) = Ideal.span {(⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K)} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirr
      exact isUnit_det_one_add_of_aniso _ (fun r hr => by rw [← hmax]; exact (IsLocalRing.mem_maximalIdeal _).2 hr) Y₁ haniso
    ·
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      obtain ⟨t, ht⟩ := htrY₁
      have hdet1 : (1 + Y₁).det = 1 + (⟨ϖ, hϖint⟩ : v.adicCompletionIntegers K) * (t + w) :=
        det_one_add_of_eisenstein _ Y₁ _ hdetY₁ t ht
      rw [hdet1]
      show Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (1 + ⟨ϖ, hϖint⟩ * (t + ↑w))) = 1
      rw [map_add, map_one, map_mul]
      apply Valuation.map_one_add_of_lt
      rw [map_mul]
      calc Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ⟨ϖ, hϖint⟩) * Valued.v _ ≤ Valued.v ϖ * 1 :=
            mul_le_mul' le_rfl (hι _)
        _ = Valued.v ϖ := mul_one _
        _ < 1 := hv1

theorem relIndex_ne_zero_of_isOpen_of_isCompact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H H' : Subgroup G) (hle : H ≤ H') (hH : IsOpen (H : Set G))
    (hH' : IsCompact (H' : Set G)) : H.relIndex H' ≠ 0 := by
  haveI : CompactSpace H' := isCompact_iff_compactSpace.mp hH'
  have hopen : IsOpen ((H.subgroupOf H' : Subgroup H') : Set H') := by
    have : ((H.subgroupOf H' : Subgroup H') : Set H') = Subtype.val ⁻¹' (H : Set G) := by
      ext x; simp [Subgroup.mem_subgroupOf]
    rw [this]
    exact hH.preimage continuous_subtype_val
  haveI : DiscreteTopology (H' ⧸ H.subgroupOf H') := QuotientGroup.discreteTopology hopen
  haveI : CompactSpace (H' ⧸ H.subgroupOf H') := Quotient.compactSpace
  haveI : Finite (H' ⧸ H.subgroupOf H') := finite_of_compact_of_discrete
  have hfi : (H.subgroupOf H').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact hfi.index_ne_zero

theorem arith_ram (q uoc sidx m : ℕ) (hq : 2 ≤ q) (hc : uoc = 2 * sidx)
    (hd : (q - 1) * uoc + 2 = 2 * q ^ (m + 1)) (θ : ℝ) :
    ((sidx : ℂ) / (θ : ℂ)) = ((q : ℂ) ^ (m + 1) - 1) / (((q : ℂ) - 1) * (θ : ℂ)) := by
  have h1 : (q - 1) * sidx + 1 = q ^ (m + 1) := by
    subst hc
    have : 2 * ((q - 1) * sidx + 1) = 2 * q ^ (m + 1) := by rw [← hd]; ring
    omega
  have hq1 : ((q - 1 : ℕ) : ℂ) = (q : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h2 : ((q : ℂ) - 1) * (sidx : ℂ) = (q : ℂ) ^ (m + 1) - 1 := by
    have := congrArg (fun n : ℕ => (n : ℂ)) h1
    push_cast at this
    rw [hq1] at this
    linear_combination this
  have hq0 : (q : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((q : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by rw [sub_eq_zero] at h; simpa using h
    exact absurd (Nat.cast_inj.1 h') (by omega)
  rw [← h2, mul_comm ((q : ℂ) - 1) (sidx : ℂ), mul_comm ((q : ℂ) - 1) (θ : ℂ)]
  by_cases hθ : (θ : ℂ) = 0
  · rw [hθ]; simp
  · field_simp

theorem arith_unr (q uoc sidx m : ℕ) (hq : 2 ≤ q) (hc : uoc = 1 * sidx)
    (hd : (q - 1) * uoc + 2 = (q + 1) * q ^ m) (θ : ℝ) :
    ((sidx : ℂ) / (θ : ℂ)) = (((q : ℂ) + 1) * (q : ℂ) ^ m - 2) / (((q : ℂ) - 1) * (θ : ℂ)) := by
  have h1 : (q - 1) * sidx + 2 = (q + 1) * q ^ m := by
    subst hc; simpa using hd
  have hq1 : ((q - 1 : ℕ) : ℂ) = (q : ℂ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h2 : ((q : ℂ) - 1) * (sidx : ℂ) = ((q : ℂ) + 1) * (q : ℂ) ^ m - 2 := by
    have := congrArg (fun n : ℕ => (n : ℂ)) h1
    push_cast at this
    rw [hq1] at this
    linear_combination this
  have hq0 : (q : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : ((q : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by rw [sub_eq_zero] at h; simpa using h
    exact absurd (Nat.cast_inj.1 h') (by omega)
  rw [← h2, mul_comm ((q : ℂ) - 1) (sidx : ℂ), mul_comm ((q : ℂ) - 1) (θ : ℂ)]
  by_cases hθ : (θ : ℂ) = 0
  · rw [hθ]; simp
  · field_simp

theorem core
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
    (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧ ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγT : γ ∈ localCentralizer K v γ₀) (hγreg : IsRegularSemisimple γ)
    (m : ℕ) (D : DepthData K v c ϖ γ m)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (hτν : @Measure.map _ _ (localCentralizerBorel K v γ) (localGLBorel K v) Subtype.val τ = νT) :
    letI := localGLBorel K v
    let q : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
    let θ : ℝ := (νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal
    let Ram : Prop := ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)
    (Ram → IsOrbitalIntegral K v γ τ (f0 K v c) ((q ^ (m + 1) - 1) / ((q - 1) * (θ : ℂ)))) ∧
    (¬ Ram → IsOrbitalIntegral K v γ τ (f0 K v c) (((q + 1) * q ^ m - 2) / ((q - 1) * (θ : ℂ)))) := by
  classical
  letI : MeasurableSpace (localCentralizer K v γ) := localCentralizerBorel K v γ

  obtain ⟨S, hSsupp, hP, hQ, hI⟩ := C1 K v c γ hγreg τ hτ
  obtain ⟨γ', hγ'⟩ : ∃ γ' : GL (Fin 2) (v.adicCompletion K), γ' = (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * γ := ⟨_, rfl⟩
  rw [← hγ'] at hSsupp hQ
  have hcen : localCentralizer K v γ' = localCentralizer K v γ := hγ' ▸ centralizer_scalar_inv_mul K v c γ
  have hA2main : localCentralizer K v γ = localCentralizer K v γ₀ :=
    centralizer_eq_centralizer_of_mem γ₀ γ (not_exists_eq_smul_one_of_forall_not_diagonal γ₀ hns)
      (not_exists_eq_smul_one_of_discr_ne_zero γ ((isRegularSemisimple_iff_ne_zero γ).1 hγreg)) hγT

  have hdetγ' : Valued.v (Matrix.det (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
    rw [hγ', coe_scalar_inv_mul]; exact D.hdet
  obtain ⟨u, hu⟩ := exists_units_eq_of_valuation_eq_one K v hdetγ'
  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hϖ; exact WithZero.coe_ne_zero.symm hϖ
  have hγ'mat0 : (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = D.a • 1 + ϖ ^ m • D.Y := by rw [hγ', coe_scalar_inv_mul, D.hY]
  have hYell0 : ¬ IsSquare (D.Y.trace ^ 2 - 4 * D.Y.det) :=
    not_isSquare_discr_of_smul_eq_smul_one_add_smul K v γ₀ hreg hns γ hγT hγreg
      ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) D.a (ϖ ^ m) (Units.ne_zero _) (pow_ne_zero m hϖ0) D.Y D.hY

  have hcount := LT.LatticeTree.unitOrbitalCount_eq_relIndex_mul_sum_relIndex_of_det_eq_algebraMap K v γ' u hu
    (Tc K v γ') (mem_Tc K v γ') (St K v γ') (mem_St K v γ') S hSsupp
    (fun s hs s' hs' t ht w hw h => hP s hs s' hs' t (hcen ▸ ht) w hw h)
    (fun x hx => by
      obtain ⟨s, hs, t, ht, w, hw, h⟩ := hQ x hx
      exact ⟨s, hs, t, by rw [show Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))) = localCentralizer K v γ from hcen]; exact ht,
        w, hw, h⟩)

  obtain ⟨BT, hBT⟩ : ∃ BT : Set (localCentralizer K v γ),
      BT = {t : ↥(localCentralizer K v γ) | (t : GL (Fin 2) (v.adicCompletion K)) ∈ Tc K v γ'} := ⟨_, rfl⟩

  have hSB : ∀ s ∈ S,
      τ BT = ((St K v γ' s).relIndex (Tc K v γ') : ENNReal) *
        τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v} ∧
      τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v} ≠ 0 ∧
      τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v} ≠ ⊤ ∧
      (St K v γ' s).relIndex (Tc K v γ') ≠ 0 := by
    haveI := hτ
    haveI := borelSpace_localCentralizer K v γ
    have hTc_cpt : IsCompact ((Tc K v γ' : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) :=
      isCompact_Tc K v ϖ hϖ D.Y D.hYint D.hYgen hYell0 γ' D.a (ϖ ^ m) (pow_ne_zero m hϖ0) hγ'mat0
    have hTcle : Tc K v γ' ≤ localCentralizer K v γ := fun t ht => hcen ▸ ((mem_Tc K v γ' t).1 ht).1
    intro s hs

    obtain ⟨HT, hHT⟩ : ∃ HT : Subgroup (localCentralizer K v γ),
        HT = (Tc K v γ').comap (localCentralizer K v γ).subtype := ⟨_, rfl⟩
    obtain ⟨Hs, hHs⟩ : ∃ Hs : Subgroup (localCentralizer K v γ),
        Hs = (St K v γ' s).comap (localCentralizer K v γ).subtype := ⟨_, rfl⟩
    have hHT_coe : (HT : Set (localCentralizer K v γ)) = BT := by
      rw [hHT, hBT]; ext t; simp [Subgroup.mem_subgroupOf]
    have hHs_coe : (Hs : Set (localCentralizer K v γ)) =
        {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v} := by
      rw [hHs]; ext t
      simp only [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype, mem_St, Set.mem_setOf_eq,
        and_iff_right_iff_imp]
      intro _
      show (t : GL (Fin 2) (v.adicCompletion K)) ∈ localCentralizer K v γ'
      rw [hcen]; exact t.2
    have hle : Hs ≤ HT := by
      rw [hHs, hHT]
      intro t ht
      rw [Subgroup.mem_comap, mem_St] at ht
      rw [Subgroup.mem_comap, mem_Tc]
      refine ⟨ht.1, ?_⟩
      obtain ⟨w, hw⟩ := exists_units_det_eq_of_mem_localIntegralSet K v ht.2
      refine ⟨w, ?_⟩
      rw [← hw, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) _,
        mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]

    have hcont : Continuous fun t : localCentralizer K v γ => s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s :=
      (continuous_const.mul continuous_subtype_val).mul continuous_const
    have hopen : IsOpen (Hs : Set (localCentralizer K v γ)) := by
      rw [hHs_coe]; exact (isOpen_localIntegralSet K v).preimage hcont
    have hclosedT : IsClosed ((localCentralizer K v γ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := by
      have h : IsClosed {t : GL (Fin 2) (v.adicCompletion K) | t * γ = γ * t} :=
        isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
      convert h using 1
      ext t; simp [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
    have hcpt : IsCompact (HT : Set (localCentralizer K v γ)) := by
      rw [hHT]
      have : ((Tc K v γ').comap (localCentralizer K v γ).subtype : Set (localCentralizer K v γ)) =
          Subtype.val ⁻¹' (Tc K v γ' : Set (GL (Fin 2) (v.adicCompletion K))) := by ext; simp [Subgroup.mem_subgroupOf]
      rw [this]
      exact hclosedT.isClosedEmbedding_subtypeVal.isCompact_preimage hTc_cpt
    have hidx : Hs.relIndex HT ≠ 0 :=
      relIndex_ne_zero_of_isOpen_of_isCompact Hs HT hle hopen hcpt
    have hidx' : Hs.relIndex HT = (St K v γ' s).relIndex (Tc K v γ') := by
      rw [hHs, hHT, Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_of_le_right hTcle]
    have hmeas : MeasurableSet (Hs : Set (localCentralizer K v γ)) := hopen.measurableSet
    have hmain := MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isMulLeftInvariant τ Hs HT hle hmeas hidx
    rw [hHT_coe, hHs_coe, hidx'] at hmain
    refine ⟨hmain, ?_, ?_, hidx' ▸ hidx⟩
    · rw [← hHs_coe]
      exact (hopen.measure_pos τ ⟨1, Hs.one_mem⟩).ne'
    · rw [← hHs_coe]
      have hsub : (Hs : Set (localCentralizer K v γ)) ⊆ (HT : Set (localCentralizer K v γ)) := fun t ht => hle ht
      exact ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne

  have hSC : (Tc K v γ' ⊔ Subgroup.center (GL (Fin 2) (v.adicCompletion K))).relIndex
      (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K)))) =
      if (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)) then 2 else 1 := by
    have h := relIndex_Tc_sup_center K v ϖ hϖ γ'
    have hset : Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))) = localCentralizer K v γ₀ := hcen.trans hA2main
    rw [h]
    simp only [hset]

  have hSD : (Ideal.absNorm v.asIdeal - 1) * LT.LatticeTree.unitOrbitalCount (v.adicCompletionIntegers K) γ' + 2 =
      if (∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ))
      then 2 * Ideal.absNorm v.asIdeal ^ (m + 1) else (Ideal.absNorm v.asIdeal + 1) * Ideal.absNorm v.asIdeal ^ m := by
    have hϖint : ϖ ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact ((valuation_lt_one_iff_le K v hϖ ϖ).2 le_rfl).le
    have hYell : ¬ IsSquare (D.Y.trace ^ 2 - 4 * D.Y.det) := hYell0
    have hγ'mat : (γ' : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = D.a • 1 + ϖ ^ m • D.Y := hγ'mat0
    have h := count_SD K v hϖ hϖint γ' m D.a D.ha D.Y hγ'mat D.hYint D.hYgen hYell hdetγ'
    have hset : Subgroup.centralizer ({γ'} : Set (GL (Fin 2) (v.adicCompletion K))) = localCentralizer K v γ₀ := hcen.trans hA2main
    rw [h]
    simp only [hset]

  have hSE : (νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal = (τ BT).toReal := by

    have hA2 : localCentralizer K v γ = localCentralizer K v γ₀ := hA2main
    have hA5c : ∀ t : GL (Fin 2) (v.adicCompletion K), t ∈ Tc K v γ' → Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1 := fun t ht =>
      v_trace_le_one_of_mem_Tc K v ϖ hϖ D.Y D.hYint D.hYgen hYell0 γ' D.a (ϖ ^ m) (pow_ne_zero m hϖ0) hγ'mat0 t ht
    letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
    haveI := borelSpace_localGLBorel K v
    haveI := borelSpace_localCentralizer K v γ
    congr 1
    rw [← hτν, Measure.map_apply continuous_subtype_val.measurable]
    · congr 1
      rw [hBT]
      ext t
      simp only [Set.mem_preimage, Set.mem_setOf_eq, mem_Tc]
      constructor
      · rintro ⟨-, h1, -⟩
        refine ⟨?_, exists_units_eq_of_valuation_eq_one K v h1⟩
        show (t : GL (Fin 2) (v.adicCompletion K)) ∈ localCentralizer K v γ'
        rw [hcen]; exact t.2
      · rintro ⟨-, w, hw⟩
        have hv : Valued.v (Matrix.det ((t : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
          rw [hw]; exact (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one).1 (Units.isUnit w)
        refine ⟨hA2 ▸ t.2, hv, hA5c _ ((mem_Tc K v γ' _).2 ⟨?_, w, hw⟩)⟩
        show (t : GL (Fin 2) (v.adicCompletion K)) ∈ localCentralizer K v γ'
        rw [hcen]; exact t.2
    ·
      have hc1 : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        Units.continuous_val.matrix_det
      have hc1' : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => Matrix.det ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        hc1.comp continuous_inv
      have hc2 : Continuous fun g : GL (Fin 2) (v.adicCompletion K) => Matrix.trace (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
        Units.continuous_val.matrix_trace
      have hZ : IsClosed ((localCentralizer K v γ₀ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) := by
        have h : IsClosed {t : GL (Fin 2) (v.adicCompletion K) | t * γ₀ = γ₀ * t} :=
          isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
        convert h using 1
        ext t; simp [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
      have hO : IsClosed ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
        Valued.isClosed_valuationSubring _
      have hdetmul : ∀ g : GL (Fin 2) (v.adicCompletion K), Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * Matrix.det ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := fun g => by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      have heq : {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
            Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1} =
          ((localCentralizer K v γ₀ : Subgroup (GL (Fin 2) (v.adicCompletion K))) : Set (GL (Fin 2) (v.adicCompletion K))) ∩
            ((fun g : GL (Fin 2) (v.adicCompletion K) => Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩
            ((fun g : GL (Fin 2) (v.adicCompletion K) => Matrix.det ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹'
                (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩
            (fun g : GL (Fin 2) (v.adicCompletion K) => Matrix.trace (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) ⁻¹' (v.adicCompletionIntegers K : Set (v.adicCompletion K)))) := by
        ext g
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
          HeightOneSpectrum.mem_adicCompletionIntegers]
        constructor
        · rintro ⟨hg, h1, h2⟩
          refine ⟨hg, h1.le, ?_, h2⟩
          have := congrArg Valued.v (hdetmul g)
          rw [map_mul, map_one, h1, one_mul] at this
          exact this.le
        · rintro ⟨hg, h1, h1', h2⟩
          refine ⟨hg, le_antisymm h1 ?_, h2⟩
          have := congrArg Valued.v (hdetmul g)
          rw [map_mul, map_one] at this
          calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) * Valued.v (Matrix.det ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := this.symm
            _ ≤ Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) * 1 := mul_le_mul_right h1' _
            _ = _ := mul_one _
      rw [heq]
      exact (hZ.inter ((hO.preimage hc1).inter ((hO.preimage hc1').inter (hO.preimage hc2)))).measurableSet
  have hq : 2 ≤ Ideal.absNorm v.asIdeal := two_le_absNorm K v

  have hterm : ∀ s ∈ S,
      (((τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal : ℂ))⁻¹ =
        (((St K v γ' s).relIndex (Tc K v γ') : ℕ) : ℂ) / ((τ BT).toReal : ℂ) := by
    intro s hs
    obtain ⟨h1, h2, h3, h4⟩ := hSB s hs
    have h5 : (τ BT).toReal = ((St K v γ' s).relIndex (Tc K v γ') : ℝ) *
        (τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal := by
      rw [h1, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    have h6 : (τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal ≠ 0 :=
      (ENNReal.toReal_pos h2 h3).ne'
    rw [h5]
    push_cast
    have h7 : (((St K v γ' s).relIndex (Tc K v γ') : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h4
    have h8 : ((τ {t : localCentralizer K v γ | s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 h6
    field_simp
  have hsum : (∑ s ∈ S, (((τ {t : localCentralizer K v γ |
        s⁻¹ * (t : GL (Fin 2) (v.adicCompletion K)) * s ∈ localIntegralSet K v}).toReal : ℂ))⁻¹) =
      ((∑ s ∈ S, (St K v γ' s).relIndex (Tc K v γ') : ℕ) : ℂ) / ((τ BT).toReal : ℂ) := by
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
    push_cast
    rfl
  rw [hsum] at hI
  rw [hSE]
  refine ⟨fun hram => ?_, fun hur => ?_⟩
  · rw [if_pos hram] at hSC hSD
    rw [hSC] at hcount
    rwa [arith_ram (Ideal.absNorm v.asIdeal) _ _ m hq hcount hSD] at hI
  · rw [if_neg hur] at hSC hSD
    rw [hSC] at hcount
    rwa [arith_unr (Ideal.absNorm v.asIdeal) _ _ m hq hcount hSD] at hI

def f1 (c : (v.adicCompletion K)ˣ) : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
  {k : GL (Fin 2) (v.adicCompletion K) | k ∈ localIntegralSet K v ∧
      ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
    ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)

theorem trace_smul_one_add_smul_Kv (a b : v.adicCompletion K) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + b • Y).trace = 2 * a + b * Y.trace := by
  simp [Matrix.trace_fin_two]; ring

theorem det_smul_one_add_smul_Kv (a b : v.adicCompletion K) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + b • Y).det = a ^ 2 + a * b * Y.trace + b ^ 2 * Y.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring

theorem discr_smul_one_add_smul_Kv (a b : v.adicCompletion K) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :
    (a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + b • Y).trace ^ 2 - 4 * (a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + b • Y).det =
      b ^ 2 * (Y.trace ^ 2 - 4 * Y.det) := by
  rw [trace_smul_one_add_smul_Kv, det_smul_one_add_smul_Kv]; ring

theorem DepthData.commute_Y {c : (v.adicCompletion K)ˣ} {ϖ : v.adicCompletion K} {γ : GL (Fin 2) (v.adicCompletion K)} {m : ℕ}
    (D : DepthData K v c ϖ γ m) (hϖ0 : ϖ ≠ 0) (B : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) (hB : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * B = B * (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :
    D.Y * B = B * D.Y := by
  have h1 : (ϖ ^ m • D.Y) = ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - D.a • 1 := by
    rw [D.hY]; abel
  have h2 : (ϖ ^ m • D.Y) * B = B * (ϖ ^ m • D.Y) := by
    rw [h1, sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul, hB, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.smul_mul, Matrix.mul_smul] at h2
  exact smul_right_injective _ (pow_ne_zero m hϖ0) h2

theorem isOrbitalIntegral_transfer (γ γ₂ : GL (Fin 2) (v.adicCompletion K))
    (h : localCentralizer K v γ = localCentralizer K v γ₂)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (f f₂ : GL (Fin 2) (v.adicCompletion K) → ℂ) (hpt : ∀ x : GL (Fin 2) (v.adicCompletion K), f (x⁻¹ * γ * x) = f₂ (x⁻¹ * γ₂ * x)) (I : ℂ) :
    IsOrbitalIntegral K v γ₂
        (@Measure.map _ _ (localCentralizerBorel K v γ) (localCentralizerBorel K v γ₂)
          (MulEquiv.subgroupCongr h) τ) f₂ I →
      IsOrbitalIntegral K v γ τ f I := by
  letI := localCentralizerBorel K v γ
  letI := localCentralizerBorel K v γ₂
  haveI := borelSpace_localCentralizer K v γ
  haveI := borelSpace_localCentralizer K v γ₂
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  rintro ⟨w, ⟨h0, hmeas, hcs, hsec⟩, hI⟩
  have hcont : Continuous (MulEquiv.subgroupCongr h : localCentralizer K v γ → localCentralizer K v γ₂) :=
    Continuous.subtype_mk continuous_subtype_val _
  refine ⟨w, ⟨h0, hmeas, hcs, fun x hx => ?_⟩, ?_⟩
  · have hx' : f₂ (x⁻¹ * γ₂ * x) ≠ 0 := by rwa [← hpt]
    have := hsec x hx'
    rw [MeasureTheory.integral_map hcont.measurable.aemeasurable] at this
    · exact this
    · exact (hmeas.comp ((continuous_subtype_val.mul continuous_const).measurable)).aestronglyMeasurable
  · rw [hI]
    congr 1
    ext x
    rw [hpt]

theorem kp_clause
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K) (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (hreg : IsRegularSemisimple γ₀)
    (hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧ ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v))
    (γ : GL (Fin 2) (v.adicCompletion K)) (hγT : γ ∈ localCentralizer K v γ₀) (hγreg : IsRegularSemisimple γ)
    (m : ℕ) (D : DepthData K v c ϖ γ m) (hm : 1 ≤ m) (hnear : Valued.v (D.a - 1) < 1)
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (localCentralizerBorel K v γ) τ)
    (hτν : @Measure.map _ _ (localCentralizerBorel K v γ) (localGLBorel K v) Subtype.val τ = νT) :
    letI := localGLBorel K v
    let q : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
    let θ : ℝ := (νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧ Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal
    let Ram : Prop := ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)
    (Ram → IsOrbitalIntegral K v γ τ (f1 K v c) ((q ^ m - 1) / ((q - 1) * (θ : ℂ)))) ∧
    (¬ Ram → IsOrbitalIntegral K v γ τ (f1 K v c) (((q + 1) * q ^ (m - 1) - 2) / ((q - 1) * (θ : ℂ)))) := by
  classical
  letI : MeasurableSpace (localCentralizer K v γ) := localCentralizerBorel K v γ
  letI : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := localGLBorel K v
  haveI := borelSpace_localGLBorel K v

  have hKP1 : ∃ a' : v.adicCompletion K, Valued.v a' ≤ 1 ∧
      Valued.v (a' • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + ϖ ^ (m - 1) • D.Y).det = 1 := by
    have hϖ0' : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hϖ; exact WithZero.coe_ne_zero.symm hϖ
    have hϖint : ϖ ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact ((valuation_lt_one_iff_le K v hϖ ϖ).2 le_rfl).le
    have hYell : ¬ IsSquare (D.Y.trace ^ 2 - 4 * D.Y.det) :=
      not_isSquare_discr_of_smul_eq_smul_one_add_smul K v γ₀ hreg hns γ hγT hγreg
        ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) D.a (ϖ ^ m) (Units.ne_zero _) (pow_ne_zero m hϖ0') D.Y D.hY
    exact exists_shift_det_unit K v hϖ hϖint D.Y D.hYint D.hYgen hYell (m - 1)
  obtain ⟨a', ha', hdet'⟩ := hKP1
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), M = a' • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + ϖ ^ (m - 1) • D.Y := ⟨_, rfl⟩
  have hMdet : M.det ≠ 0 := by
    intro h0; rw [← hM] at hdet'; rw [h0, map_zero] at hdet'; exact zero_ne_one hdet'
  obtain ⟨g4, hg4⟩ : ∃ g4 : GL (Fin 2) (v.adicCompletion K), (g4 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = M := ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hMdet, rfl⟩
  obtain ⟨γ₂, hγ₂⟩ : ∃ γ₂ : GL (Fin 2) (v.adicCompletion K), γ₂ = Matrix.GeneralLinearGroup.scalar (Fin 2) c * g4 := ⟨_, rfl⟩
  have hcg : ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = M := by
    rw [← hg4, ← coe_scalar_inv_mul, hγ₂, ← mul_assoc, inv_mul_cancel, one_mul]
  have D2 : DepthData K v c ϖ γ₂ (m - 1) :=
    ⟨a', D.Y, ha', by rw [hcg, hM], D.hYint, D.hYgen, by rw [hcg, hM]; exact hdet'⟩

  have hϖ0 : ϖ ≠ 0 := by intro h; rw [h, map_zero] at hϖ; exact WithZero.coe_ne_zero.symm hϖ
  have hγ₂T : γ₂ ∈ localCentralizer K v γ₀ := by
    have hγc : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      have h := congrArg (fun g : GL (Fin 2) (v.adicCompletion K) => (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) (Subgroup.mem_centralizer_singleton_iff.1 hγT)
      simp only [Units.val_mul] at h
      exact h
    have hY := D.commute_Y K v hϖ0 (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) hγc
    have hM' : M * (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (γ₀ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * M := by
      rw [hM, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, hY,
        Matrix.one_mul, Matrix.mul_one]
    rw [hγ₂]
    refine (localCentralizer K v γ₀).mul_mem ?_ ?_
    · rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]; exact scalar_mul_comm K v c γ₀
    · rw [localCentralizer, Subgroup.mem_centralizer_singleton_iff]
      apply Units.ext; rw [Units.val_mul, Units.val_mul, hg4]; exact hM'
  have hγ₂reg : IsRegularSemisimple γ₂ := by
    rw [isRegularSemisimple_iff_ne_zero] at hγreg ⊢
    have e1 : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (c : v.adicCompletion K) • (D.a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + ϖ ^ m • D.Y) := by
      rw [← D.hY, smul_smul, Units.mul_inv, one_smul]
    have e2 : (γ₂ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = (c : v.adicCompletion K) • (a' • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + ϖ ^ (m - 1) • D.Y) := by
      rw [← hM, ← hcg, smul_smul, Units.mul_inv, one_smul]
    have key : ∀ (s : v.adicCompletion K) (N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)),
        (s • N).trace ^ 2 - 4 * (s • N).det = s ^ 2 * (N.trace ^ 2 - 4 * N.det) := by
      intro s N; simp [Matrix.det_fin_two, Matrix.trace_fin_two]; ring
    rw [e1, key, discr_smul_one_add_smul_Kv] at hγreg
    rw [e2, key, discr_smul_one_add_smul_Kv]
    have hdisc : D.Y.trace ^ 2 - 4 * D.Y.det ≠ 0 := fun h => hγreg (by rw [h]; ring)
    exact mul_ne_zero (pow_ne_zero 2 (Units.ne_zero c))
      (mul_ne_zero (pow_ne_zero 2 (pow_ne_zero _ hϖ0)) hdisc)
  have hcen2 : localCentralizer K v γ = localCentralizer K v γ₂ := by
    have h0 := not_exists_eq_smul_one_of_forall_not_diagonal γ₀ hns
    have e1 : localCentralizer K v γ = localCentralizer K v γ₀ :=
      centralizer_eq_centralizer_of_mem γ₀ γ h0
        (not_exists_eq_smul_one_of_discr_ne_zero γ ((isRegularSemisimple_iff_ne_zero γ).1 hγreg)) hγT
    have e2 : localCentralizer K v γ₂ = localCentralizer K v γ₀ :=
      centralizer_eq_centralizer_of_mem γ₀ γ₂ h0
        (not_exists_eq_smul_one_of_discr_ne_zero γ₂ ((isRegularSemisimple_iff_ne_zero γ₂).1 hγ₂reg)) hγ₂T
    exact e1.trans e2.symm

  have hpt : ∀ x : GL (Fin 2) (v.adicCompletion K), f1 K v c (x⁻¹ * γ * x) = f0 K v c (x⁻¹ * γ₂ * x) := by
    intro x
    have hm1 : ϖ ^ m = ϖ * ϖ ^ (m - 1) := by rw [← pow_succ', Nat.sub_add_cancel hm]
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K), X = ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * D.Y * (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := ⟨_, rfl⟩
    have hconj : ∀ (s t : v.adicCompletion K) (N : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)),
        ((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * (s • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) + t • N) * (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          s • 1 + t • (((x⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * N * (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) := by
      intro s t N
      rw [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

    have e1 : (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ * x) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        D.a • 1 + ϖ ^ m • X := by
      rw [← conj_scalar_inv_mul, Units.val_mul, Units.val_mul, coe_scalar_inv_mul, D.hY, hconj, ← hX]
    have e2 : (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ₂ * x) : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
        a' • 1 + ϖ ^ (m - 1) • X := by
      rw [← conj_scalar_inv_mul, Units.val_mul, Units.val_mul, coe_scalar_inv_mul, hcg, hM, hconj, ← hX]
    have d1 : Valued.v (Matrix.det (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ * x) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
      rw [← conj_scalar_inv_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
        mul_comm (Matrix.det _) _, mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.det_one, mul_one, coe_scalar_inv_mul]
      exact D.hdet
    have d2 : Valued.v (Matrix.det (((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ₂ * x) : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
      rw [← conj_scalar_inv_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
        mul_comm (Matrix.det _) _, mul_assoc, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.det_one, mul_one, coe_scalar_inv_mul, hcg, hM]
      exact hdet'
    have hint_a : D.a ∈ v.adicCompletionIntegers K := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 D.ha
    have hint_a' : a' ∈ v.adicCompletionIntegers K := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ha'
    have hint_ϖ : ϖ ∈ v.adicCompletionIntegers K := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]; exact ((valuation_lt_one_iff_le K v hϖ ϖ).2 le_rfl).le
    have hint_one : ∀ i j : Fin 2, (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
      intro i j; rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]

    have key : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ₂ * x) ∈ localIntegralSet K v) ↔
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ * x) ∈
          {k : GL (Fin 2) (v.adicCompletion K) | k ∈ localIntegralSet K v ∧ ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}) := by
      constructor
      · intro h
        have hXint : ∀ i j, (ϖ ^ (m - 1) • X) i j ∈ v.adicCompletionIntegers K := by
          intro i j
          have := h.1 i j
          rw [e2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at this
          have h2 : (ϖ ^ (m - 1) • X) i j = (D.a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) - (D.a • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) + (ϖ ^ (m - 1) • X) i j := by ring
          have := sub_mem this (mul_mem hint_a' (hint_one i j))
          rwa [add_sub_cancel_left] at this
        refine ⟨mem_localIntegralSet_of_entries_of_det K v _ ?_ d1, ?_⟩
        · intro i j
          rw [e1, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hm1, ← smul_smul, Matrix.smul_apply, smul_eq_mul]
          exact add_mem (mul_mem hint_a (hint_one i j)) (mul_mem hint_ϖ (hXint i j))
        · intro i j
          rw [e1, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hm1, ← smul_smul,
            Matrix.smul_apply, smul_eq_mul]
          have hre : D.a * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j + ϖ * (ϖ ^ (m - 1) • X) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
              (D.a - 1) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j + ϖ * (ϖ ^ (m - 1) • X) i j := by ring
          rw [hre]
          refine (Valued.v.map_add _ _).trans_lt (max_lt ?_ ?_)
          · rw [map_mul]
            calc Valued.v (D.a - 1) * Valued.v ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ Valued.v (D.a - 1) * 1 :=
                  mul_le_mul_right ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint_one i j)) _
              _ < 1 := by rw [mul_one]; exact hnear
          · rw [valuation_lt_one_iff_le K v hϖ, map_mul]
            calc Valued.v ϖ * Valued.v ((ϖ ^ (m - 1) • X) i j) ≤ Valued.v ϖ * 1 :=
                  mul_le_mul_right ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hXint i j)) _
              _ = Valued.v ϖ := mul_one _
      · rintro ⟨h, hsmall⟩
        have hXint : ∀ i j, (ϖ ^ (m - 1) • X) i j ∈ v.adicCompletionIntegers K := by
          intro i j
          have h1 := hsmall i j
          rw [e1, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, hm1, ← smul_smul,
            Matrix.smul_apply, smul_eq_mul] at h1
          have hre : ϖ * (ϖ ^ (m - 1) • X) i j =
              (D.a * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j + ϖ * (ϖ ^ (m - 1) • X) i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) - (D.a - 1) * (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
            ring
          have h2 : Valued.v (ϖ * (ϖ ^ (m - 1) • X) i j) < 1 := by
            rw [hre]
            refine (Valued.v.map_sub _ _).trans_lt (max_lt h1 ?_)
            rw [map_mul]
            calc Valued.v (D.a - 1) * Valued.v ((1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) ≤ Valued.v (D.a - 1) * 1 :=
                  mul_le_mul_right ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint_one i j)) _
              _ < 1 := by rw [mul_one]; exact hnear
          rw [valuation_lt_one_iff_le K v hϖ, map_mul] at h2
          rw [HeightOneSpectrum.mem_adicCompletionIntegers]
          have hϖpos : 0 < Valued.v ϖ := by rw [hϖ]; exact WithZero.zero_lt_coe _
          calc Valued.v ((ϖ ^ (m - 1) • X) i j) = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v ((ϖ ^ (m - 1) • X) i j)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hϖpos.ne', one_mul]
            _ ≤ (Valued.v ϖ)⁻¹ * Valued.v ϖ := mul_le_mul_right h2 _
            _ = 1 := inv_mul_cancel₀ hϖpos.ne'
        refine mem_localIntegralSet_of_entries_of_det K v _ ?_ d2
        intro i j
        rw [e2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        exact add_mem (mul_mem hint_a' (hint_one i j)) (hXint i j)
    simp only [f1, f0]
    by_cases h : (Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * (x⁻¹ * γ₂ * x) ∈ localIntegralSet K v
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (key.1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (key.2 h'))]

  letI : MeasurableSpace (localCentralizer K v γ₂) := localCentralizerBorel K v γ₂
  haveI := borelSpace_localCentralizer K v γ
  haveI := borelSpace_localCentralizer K v γ₂
  haveI := hτ
  obtain ⟨e, he⟩ : ∃ e : localCentralizer K v γ ≃* localCentralizer K v γ₂, e = MulEquiv.subgroupCongr hcen2 :=
    ⟨_, rfl⟩
  have hecont : Continuous e := he ▸ Continuous.subtype_mk continuous_subtype_val _
  have hesymm : Continuous e.symm := he ▸ Continuous.subtype_mk continuous_subtype_val _
  obtain ⟨τ₂, hτ₂def⟩ : ∃ τ₂ : Measure (localCentralizer K v γ₂), τ₂ = Measure.map e τ := ⟨_, rfl⟩
  have hτ₂ : τ₂.IsHaarMeasure := by
    rw [hτ₂def]; exact MulEquiv.isHaarMeasure_map τ e hecont hesymm
  have hτν₂ : Measure.map Subtype.val τ₂ = νT := by
    rw [hτ₂def, Measure.map_map continuous_subtype_val.measurable hecont.measurable]
    have : (Subtype.val ∘ (e : localCentralizer K v γ → localCentralizer K v γ₂)) = Subtype.val := by
      funext t; rw [he]; rfl
    rw [this]; exact hτν
  have hC2 := core K v c ϖ hϖ γ₀ hreg hns νT γ₂ hγ₂T hγ₂reg (m - 1) D2 τ₂ hτ₂ hτν₂
  obtain ⟨hC2a, hC2b⟩ := hC2
  rw [Nat.sub_add_cancel hm] at hC2a
  have htr := fun I => isOrbitalIntegral_transfer K v γ γ₂ hcen2 τ (f1 K v c) (f0 K v c) hpt I
  rw [← he, ← hτ₂def] at htr
  exact ⟨fun hram => htr _ (hC2a hram), fun hur => htr _ (hC2b hur)⟩

end EllGermBridge
p2m_reactivate "P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal.EllGermBridge"

end
p2m_reactivate "P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal.EllGermBridge"

open EllGermBridge in
theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (c : (v.adicCompletion K)ˣ) (ϖ : v.adicCompletion K)
    (hϖ : Valued.v ϖ = Multiplicative.ofAdd (-1 : ℤ))
    (γ₀ : GL (Fin 2) (v.adicCompletion K)) (_hreg : AutomorphicForm.IsRegularSemisimple γ₀)
    (_hns : ∀ g : GL (Fin 2) (v.adicCompletion K),
      ¬ (((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
         ((g⁻¹ * γ₀ * g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0))
    (νT : @Measure (GL (Fin 2) (v.adicCompletion K)) (AutomorphicForm.localGLBorel K v))

    (γ : GL (Fin 2) (v.adicCompletion K)) (_hγT : γ ∈ AutomorphicForm.localCentralizer K v γ₀)
    (_hγreg : AutomorphicForm.IsRegularSemisimple γ)
    (_hdet : Valued.v ((((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))).det) = 1)

    (m : ℕ) (a : v.adicCompletion K) (_ha : Valued.v a ≤ 1) (Y : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))
    (_hY : ((c⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) • (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a • 1 + (ϖ ^ m) • Y)
    (_hYint : Valued.v Y.det ≤ 1 ∧ Valued.v Y.trace ≤ 1)
    (_hYgen : ∀ b : v.adicCompletion K, Valued.v b ≤ 1 →
      ¬ (Valued.v (Y - b • 1).det ≤ Valued.v ϖ ^ 2 ∧ Valued.v (Y - b • 1).trace ≤ Valued.v ϖ))

    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (_hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (_hτν : @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ) (AutomorphicForm.localGLBorel K v)
        Subtype.val τ = νT) :
    letI := AutomorphicForm.localGLBorel K v

    let q : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
    let f₀ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)
    let f₁ : GL (Fin 2) (v.adicCompletion K) → ℂ := fun g =>
      {k : GL (Fin 2) (v.adicCompletion K) | k ∈ AutomorphicForm.localIntegralSet K v ∧
          ∀ i j, Valued.v (((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) - 1) i j) < 1}.indicator (fun _ => (1 : ℂ))
        ((Matrix.GeneralLinearGroup.scalar (Fin 2) c)⁻¹ * g)
    let θ : ℝ := (νT {g : GL (Fin 2) (v.adicCompletion K) | g ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = 1 ∧
          Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).trace) ≤ 1}).toReal
    let Ram : Prop := ∃ t : GL (Fin 2) (v.adicCompletion K), t ∈ AutomorphicForm.localCentralizer K v γ₀ ∧
        Valued.v ((t : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det) = Multiplicative.ofAdd (-1 : ℤ)
    let Near : Prop := 1 ≤ m ∧ Valued.v (a - 1) < 1
    (Ram →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f₀ ((q ^ (m + 1) - 1) / ((q - 1) * (θ : ℂ))) ∧
      (Near → AutomorphicForm.IsOrbitalIntegral K v γ τ f₁ ((q ^ m - 1) / ((q - 1) * (θ : ℂ))))) ∧
    (¬ Ram →
      AutomorphicForm.IsOrbitalIntegral K v γ τ f₀ (((q + 1) * q ^ m - 2) / ((q - 1) * (θ : ℂ))) ∧
      (Near → AutomorphicForm.IsOrbitalIntegral K v γ τ f₁ (((q + 1) * q ^ (m - 1) - 2) / ((q - 1) * (θ : ℂ))))) := by
  have hC := EllGermBridge.core K v c ϖ hϖ γ₀ _hreg _hns νT γ _hγT _hγreg m
    ⟨a, Y, _ha, _hY, _hYint, _hYgen, _hdet⟩ τ _hτ _hτν
  have hP := EllGermBridge.kp_clause K v c ϖ hϖ γ₀ _hreg _hns νT γ _hγT _hγreg m
    ⟨a, Y, _ha, _hY, _hYint, _hYgen, _hdet⟩
  exact ⟨fun hram => ⟨hC.1 hram, fun hnear => (hP hnear.1 hnear.2 τ _hτ _hτν).1 hram⟩,
    fun hur => ⟨hC.2 hur, fun hnear => (hP hnear.1 hnear.2 τ _hτ _hτν).2 hur⟩⟩

end S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal
end P2MW
export P2MW.S_AutomorphicForm_isOrbitalIntegral_indicator_scalar_localIntegralSet_and_principalCongruence_of_depth_of_forall_not_diagonal (solution)
