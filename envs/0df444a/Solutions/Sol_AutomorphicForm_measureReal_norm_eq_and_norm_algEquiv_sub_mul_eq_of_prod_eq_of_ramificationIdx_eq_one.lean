-- Prove2me | solution 1 for AutomorphicForm.measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/05e641fa-3c44-529f-8d0a-6df5c56c37bc

import Definitions.Def_DedekindDomain_Completion_BaseChange
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_Extension_relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
import Theorems.Thm_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow
import Theorems.Thm_MeasureTheory_Measure_measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

noncomputable section

namespace Ws31S3

section NormVal

variable (F : Type) [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem one_lt_q : (1 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm u

theorem q_pos : (0 : ℝ) < (Ideal.absNorm u.asIdeal : ℝ) := lt_trans zero_lt_one (one_lt_q F u)

private theorem _root_.Ws31S3.exists_norm_eq_zpow_and_v_eq {x : u.adicCompletion F} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ k ∧
      (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

p2m_export "Ws31S3" "exists_norm_eq_zpow_and_v_eq"

theorem v_eq_exp_of_norm_eq_zpow {x : u.adicCompletion F} {k : ℤ}
    (h : ‖x‖ = (Ideal.absNorm u.asIdeal : ℝ) ^ k) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (zpow_pos (q_pos F u) k).ne h
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq F u hx
  rw [hk'] at h
  have hk : k' = k := zpow_right_injective₀ (q_pos F u) (one_lt_q F u).ne' h
  rw [hv, hk]

theorem v_eq_one_of_norm_eq_one {x : u.adicCompletion F} (h : ‖x‖ = 1) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  have := v_eq_exp_of_norm_eq_zpow F u (k := 0) (by rw [h, zpow_zero])
  rwa [WithZero.exp_zero] at this

theorem v_le_one_of_norm_le_one {x : u.adicCompletion F} (h : ‖x‖ ≤ 1) :
    (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 :=
  Valued.toNormedField.norm_le_one_iff.1 h

theorem mem_integers_iff_v (x : u.adicCompletion F) :
    x ∈ u.adicCompletionIntegers F ↔ (Valued.v x : WithZero (Multiplicative ℤ)) ≤ 1 :=
  HeightOneSpectrum.mem_adicCompletionIntegers _ _ _

end NormVal

section Unramified

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_int_coe (x : v.adicCompletionIntegers K) :
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x :
        w.1.adicCompletionIntegers L) : w.1.adicCompletion L) =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (x : v.adicCompletion K) := rfl

theorem algebraMap_int_field (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletion L) x =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (x : v.adicCompletion K) := rfl

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_algebraMap (x : v.adicCompletion K) :
    (Valued.v (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x) : WithZero (Multiplicative ℤ)) =
      Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom K L x) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hw, pow_one]

theorem algebraMap_mem_integers_iff (x : v.adicCompletion K) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x ∈ w.1.adicCompletionIntegers L ↔
      x ∈ v.adicCompletionIntegers K := by
  rw [mem_integers_iff_v, mem_integers_iff_v, v_algebraMap K L v w hw]

theorem exists_eq_algebraMap_mul_unit {y : w.1.adicCompletion L} (hy : y ≠ 0) :
    ∃ x : v.adicCompletion K, x ≠ 0 ∧
      (Valued.v (y * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x)⁻¹) :
        WithZero (Multiplicative ℤ)) = 1 := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v y : WithZero (Multiplicative ℤ))
  have hy0 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hy0 hx.symm
  refine ⟨x, hx0, ?_⟩
  rw [map_mul, map_inv₀, v_algebraMap K L v w hw, hx, mul_inv_cancel₀ hy0]

end Unramified

section Theta

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)

theorem isIntegral_of_mem {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

theorem mem_of_isIntegral {y : w.1.adicCompletion L} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

theorem theta_mem {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) :
    θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  have h := isIntegral_of_mem K L v w hy
  exact h.map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

theorem theta_pow_mem (i : ℕ) {y : w.1.adicCompletion L} (hy : y ∈ w.1.adicCompletionIntegers L) :
    (θ ^ i) y ∈ w.1.adicCompletionIntegers L := by
  induction i with
  | zero => simpa using hy
  | succ i ih => rw [pow_succ', AlgEquiv.mul_apply]; exact theta_mem K L v w θ ih

theorem v_theta_eq_one {y : w.1.adicCompletion L} (hy : (Valued.v y : WithZero (Multiplicative ℤ)) = 1) (i : ℕ) :
    (Valued.v ((θ ^ i) y) : WithZero (Multiplicative ℤ)) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have h1 : (θ ^ i) y ∈ w.1.adicCompletionIntegers L :=
    theta_pow_mem K L v w θ i ((mem_integers_iff_v L w.1 y).2 hy.le)
  have h2 : (θ ^ i) y⁻¹ ∈ w.1.adicCompletionIntegers L :=
    theta_pow_mem K L v w θ i ((mem_integers_iff_v L w.1 y⁻¹).2 (by rw [map_inv₀, hy, inv_one]))
  rw [map_inv₀] at h2
  rw [mem_integers_iff_v] at h1 h2
  rw [map_inv₀] at h2
  have h3 : (Valued.v ((θ ^ i) y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (θ ^ i).injective).2 hy0)
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.2 h3)] at h2)

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_c_eq_one {f : ℕ} (hf : 0 < f) (c : w.1.adicCompletion L) (n : v.adicCompletion K)
    (hn : (Valued.v n : WithZero (Multiplicative ℤ)) = 1)
    (hc : ∏ i ∈ Finset.range f, (θ ^ i) c = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n) :
    (Valued.v c : WithZero (Multiplicative ℤ)) = 1 := by
  have hn0 : n ≠ 0 := by intro h; rw [h, map_zero] at hn; exact zero_ne_one hn
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    have : (∏ i ∈ Finset.range f, (θ ^ i) (0 : w.1.adicCompletion L)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hf) (map_zero _)
    rw [this, eq_comm, map_eq_zero] at hc
    exact hn0 hc
  obtain ⟨x, hx0, hu⟩ := exists_eq_algebraMap_mul_unit K L v w hw hc0
  set a := algebraMap (v.adicCompletion K) (w.1.adicCompletion L) x with ha
  have ha0 : a ≠ 0 := (map_ne_zero _).2 hx0
  set uu := c * a⁻¹ with huu
  have hcu : c = a * uu := by rw [huu, mul_left_comm, mul_inv_cancel₀ ha0, mul_one]

  have hprod : ∏ i ∈ Finset.range f, (θ ^ i) c = a ^ f * ∏ i ∈ Finset.range f, (θ ^ i) uu := by
    rw [← Finset.card_range f, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hcu, map_mul, ha, AlgEquiv.commutes]
  have hval := congrArg (fun z => (Valued.v z : WithZero (Multiplicative ℤ))) hc
  rw [hprod, map_mul, map_pow, map_prod, v_algebraMap K L v w hw, v_algebraMap K L v w hw, hn,
    Finset.prod_eq_one (fun i _ => v_theta_eq_one K L v w θ hu i), mul_one] at hval
  have hx1 : (Valued.v x : WithZero (Multiplicative ℤ)) = 1 :=
    le_antisymm ((pow_le_one_iff hf.ne').1 hval.le) ((one_le_pow_iff hf.ne').1 hval.ge)
  rw [hcu, map_mul, v_algebraMap K L v w hw, hx1, one_mul, hu]

end Theta

section ModuleSetup

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

theorem algebraMap_int_injective :
    Function.Injective (algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)) := by
  intro x y hxy
  have h := congrArg (fun z : w.1.adicCompletionIntegers L => (z : w.1.adicCompletion L)) hxy
  simp only [algebraMap_int_coe] at h
  exact Subtype.ext ((algebraMap (v.adicCompletion K) (w.1.adicCompletion L)).injective h)

scoped instance isTorsionFree_int : Module.IsTorsionFree (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  Module.isTorsionFree_iff_algebraMap_injective.2 (algebraMap_int_injective K L v w)

scoped instance free_int : Module.Free (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  Module.free_of_finite_type_torsion_free'

scoped instance isIntegralClosure_int :
    IsIntegralClosure (w.1.adicCompletionIntegers L) (v.adicCompletionIntegers K) (w.1.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := fun {y} =>
    ⟨fun h => ⟨⟨y, mem_of_isIntegral K L v w h⟩, rfl⟩, fun ⟨z, hz⟩ => hz ▸ isIntegral_of_mem K L v w z.2⟩

theorem isLocalization_int :
    IsLocalization (Algebra.algebraMapSubmonoid (w.1.adicCompletionIntegers L)
      (nonZeroDivisors (v.adicCompletionIntegers K))) (w.1.adicCompletion L) :=
  IsIntegralClosure.isLocalization (v.adicCompletionIntegers K) (v.adicCompletion K)
    (w.1.adicCompletion L) (w.1.adicCompletionIntegers L)

end ModuleSetup

section Uniformizer

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

theorem exp_neg_one_pow (m : ℕ) : (WithZero.exp (-1 : ℤ)) ^ m = WithZero.exp (-(m : ℤ)) := by
  rw [← WithZero.exp_nsmul, smul_neg, nsmul_one]

theorem isUnit_int_iff (x : v.adicCompletionIntegers K) :
    IsUnit x ↔ (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = 1 :=
  Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)

theorem associated_of_v_eq {x y : v.adicCompletionIntegers K} (hy : y ≠ 0)
    (h : (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) = Valued.v (y : v.adicCompletion K)) :
    Associated x y := by
  have hy' : (y : v.adicCompletion K) ≠ 0 := fun h' => hy (Subtype.ext h')
  have hvy : (Valued.v (y : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy'
  have hx' : (x : v.adicCompletion K) ≠ 0 := by
    intro h'
    rw [h', map_zero] at h
    exact hvy h.symm
  set t : v.adicCompletion K := (y : v.adicCompletion K) * (x : v.adicCompletion K)⁻¹ with ht
  have hvt : (Valued.v t : WithZero (Multiplicative ℤ)) = 1 := by
    rw [ht, map_mul, map_inv₀, h, mul_inv_cancel₀ hvy]
  have htO : t ∈ v.adicCompletionIntegers K := (mem_integers_iff_v K v t).2 hvt.le
  obtain ⟨u, hu⟩ := (isUnit_int_iff K v ⟨t, htO⟩).2 hvt
  refine ⟨u, Subtype.ext ?_⟩
  change (x : v.adicCompletion K) * ((u : v.adicCompletionIntegers K) : v.adicCompletion K) = y
  rw [hu]
  change (x : v.adicCompletion K) * t = y
  rw [ht, mul_comm, inv_mul_cancel_right₀ hx']

variable (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
include hϖ

theorem v_pi : (Valued.v ϖ : WithZero (Multiplicative ℤ)) = WithZero.exp (-1) :=
  v_eq_exp_of_norm_eq_zpow K v (k := -1) (by rw [hϖ, zpow_neg_one])

theorem pi_ne_zero : ϖ ≠ 0 := by
  intro h
  have := v_pi K v ϖ hϖ
  rw [h, map_zero] at this
  exact WithZero.coe_ne_zero this.symm

theorem pi_mem : ϖ ∈ v.adicCompletionIntegers K := by
  rw [mem_integers_iff_v, v_pi K v ϖ hϖ, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

def piO : v.adicCompletionIntegers K := ⟨ϖ, pi_mem K v ϖ hϖ⟩

theorem coe_piO : ((piO K v ϖ hϖ : v.adicCompletionIntegers K) : v.adicCompletion K) = ϖ := rfl

theorem irreducible_piO : Irreducible (piO K v ϖ hϖ) := by
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [isUnit_int_iff, coe_piO, v_pi K v ϖ hϖ, ← WithZero.exp_zero]
    intro h
    have := WithZero.exp_injective h
    omega
  · have hv : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) * Valued.v (b : v.adicCompletion K) =
        WithZero.exp (-1) := by
      rw [← map_mul, ← v_pi K v ϖ hϖ, ← coe_piO K v ϖ hϖ, hab]; rfl
    by_cases ha : IsUnit a
    · exact Or.inl ha
    · right
      have ha' : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) < 1 :=
        (Valuation.Integer.not_isUnit_iff_valuation_lt_one (x := a)).1 ha
      have ha'' := le_exp_neg_one_of_lt_one ha'
      have hb1 : (Valued.v (b : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≤ 1 := b.2
      rw [isUnit_int_iff]
      refine le_antisymm hb1 ?_
      by_contra hlt
      push Not at hlt
      have hlt' : (Valued.v (a : v.adicCompletion K) : WithZero (Multiplicative ℤ)) * Valued.v (b : v.adicCompletion K) <
          WithZero.exp (-1) * 1 := mul_lt_mul_of_le_of_lt_of_nonneg_of_pos ha'' hlt zero_le' WithZero.exp_pos
      rw [mul_one, hv] at hlt'
      exact lt_irrefl _ hlt'

theorem v_piO_pow (m : ℕ) :
    (Valued.v (((piO K v ϖ hϖ) ^ m : v.adicCompletionIntegers K) : v.adicCompletion K) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-(m : ℤ)) := by
  rw [SubmonoidClass.coe_pow, map_pow, coe_piO, v_pi K v ϖ hϖ, exp_neg_one_pow]

end Uniformizer

section Rank

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

theorem finrank_int : Module.finrank (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) =
    Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := by
  classical
  haveI := isLocalization_int K L v w
  let b := Module.Free.chooseBasis (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis
    (b.localizationLocalization (v.adicCompletion K) (nonZeroDivisors (v.adicCompletionIntegers K))
      (w.1.adicCompletion L))]

end Rank

section Transport

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)
  (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ)

theorem finite_residueField : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  exact Finite.of_equiv _ (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv

theorem card_residueField : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField K v).toEquiv,
    Ideal.absNorm_apply, Submodule.cardQuot_apply]

abbrev pis : w.1.adicCompletion L := algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s)

theorem pis_eq : pis K L v w ϖ s =
    ((algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) ((piO K v ϖ hϖ) ^ s) :
      w.1.adicCompletionIntegers L) : w.1.adicCompletion L) := by
  rw [algebraMap_int_coe, SubmonoidClass.coe_pow, coe_piO]

include hϖ in
theorem pis_ne_zero : pis K L v w ϖ s ≠ 0 :=
  (map_ne_zero _).2 (pow_ne_zero _ (pi_ne_zero K v ϖ hϖ))

theorem theta_pis : θ (pis K L v w ϖ s) = pis K L v w ϖ s := θ.commutes _

include hϖ in
theorem mulLeft_pis_injective : Function.Injective (AddMonoidHom.mulLeft (pis K L v w ϖ s)) := by
  intro x y hxy
  exact mul_left_cancel₀ (pis_ne_zero K L v w ϖ hϖ s) hxy

abbrev iota : w.1.adicCompletionIntegers L →+ w.1.adicCompletion L :=
  (w.1.adicCompletionIntegers L).subtype.toAddMonoidHom

theorem iota_apply (y : w.1.adicCompletionIntegers L) : iota K L v w y = (y : w.1.adicCompletion L) := rfl

theorem iota_injective : Function.Injective (iota K L v w) := fun _ _ h => Subtype.ext h

theorem map_iota_smul_top :
    ((Ideal.span {(piO K v ϖ hϖ) ^ s} • ⊤ :
        Submodule (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)).toAddSubgroup).map (iota K L v w) =
    (w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (pis K L v w ϖ s)) := by
  ext x
  rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hy
    obtain ⟨z, -, rfl⟩ := hy
    refine ⟨(z : w.1.adicCompletion L), z.2, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, iota_apply, pis_eq K L v w ϖ hϖ s]
    rfl
  · rintro ⟨t, ht, rfl⟩
    refine ⟨(piO K v ϖ hϖ ^ s) • (⟨t, ht⟩ : w.1.adicCompletionIntegers L), ?_, ?_⟩
    · rw [Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨⟨t, ht⟩, Submodule.mem_top, rfl⟩
    · rw [AddMonoidHom.coe_mulLeft, iota_apply, pis_eq K L v w ϖ hϖ s]
      rfl

end Transport

section ShellIndex

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

theorem relIndex_comap_comap_of_surjective {G G' : Type*} [AddCommGroup G] [AddCommGroup G']
    (f : G' →+ G) (hf : Function.Surjective f) (H H' : AddSubgroup G) :
    (H.comap f).relIndex (H'.comap f) = H.relIndex H' := by
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hf]

theorem mulLeft_algebraMap_surjective (t : v.adicCompletion K) (ht : t ≠ 0) :
    Function.Surjective (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t)) := by
  intro y
  refine ⟨algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t⁻¹ * y, ?_⟩
  rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]

theorem P_comp_mulLeft (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))
    (c : w.1.adicCompletion L) (t : v.adicCompletion K) :
    (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c).comp
        (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t)) =
      (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t)).comp
        (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c) := by
  ext y
  show θ.toAlgHom.toRingHom (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * y) -
      c * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * y) =
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * (θ.toAlgHom.toRingHom y - c * y)
  rw [map_mul, mul_sub, mul_left_comm]
  congr 1
  show θ (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t) * θ y = _
  rw [AlgEquiv.commutes]
  rfl

theorem mulLeft_comp_mulLeft (a b : w.1.adicCompletion L) :
    (AddMonoidHom.mulLeft a).comp (AddMonoidHom.mulLeft b) = AddMonoidHom.mulLeft (a * b) := by
  ext y
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, mul_assoc]

include hϖ in

theorem relIndex_map_mulLeft_pis (s : ℕ) :
    ((w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (pis K L v w ϖ s))).relIndex
        (w.1.adicCompletionIntegers L).toAddSubgroup =
      Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * s) := by
  haveI := finite_residueField K v
  set c₀ : v.adicCompletionIntegers K := (piO K v ϖ hϖ) ^ s with hc₀
  let f : (w.1.adicCompletionIntegers L) →ₗ[v.adicCompletionIntegers K] (w.1.adicCompletionIntegers L) :=
    c₀ • LinearMap.id
  have hf_apply : ∀ y : w.1.adicCompletionIntegers L,
      f y = algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) c₀ * y := fun y => by
    show c₀ • y = _
    rw [Algebra.smul_def]
  have hc0 : c₀ ≠ 0 := pow_ne_zero _ (irreducible_piO K v ϖ hϖ).ne_zero
  have hac0 : algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) c₀ ≠ 0 := by
    intro h0
    exact hc0 (algebraMap_int_injective K L v w (by rw [h0, map_zero]))
  have hf : Function.Injective f := by
    intro x y hxy
    rw [hf_apply, hf_apply] at hxy
    exact mul_left_cancel₀ hac0 hxy
  have hdet : Associated (LinearMap.det f)
      ((piO K v ϖ hϖ) ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * s)) := by
    have h1 : LinearMap.det f = c₀ ^ Module.finrank (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) := by
      show LinearMap.det (c₀ • (LinearMap.id : (w.1.adicCompletionIntegers L) →ₗ[v.adicCompletionIntegers K]
        (w.1.adicCompletionIntegers L))) = _
      rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
    rw [h1, hc₀, ← pow_mul, finrank_int K L v w, mul_comm]
  have hidx := LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow
    (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) f hf (piO K v ϖ hϖ) (irreducible_piO K v ϖ hϖ)
    (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * s) hdet
  rw [card_residueField] at hidx
  have hmap_range : (LinearMap.range f).toAddSubgroup.map (iota K L v w) =
      (w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (pis K L v w ϖ s)) := by
    ext x
    rw [AddSubgroup.mem_map, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨(z : w.1.adicCompletion L), z.2, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, iota_apply, hf_apply, pis_eq K L v w ϖ hϖ s]
      rfl
    · rintro ⟨t, ht, rfl⟩
      refine ⟨f ⟨t, ht⟩, ?_, ?_⟩
      · rw [Submodule.mem_toAddSubgroup, LinearMap.mem_range]
        exact ⟨⟨t, ht⟩, rfl⟩
      · rw [AddMonoidHom.coe_mulLeft, iota_apply, hf_apply, pis_eq K L v w ϖ hϖ s]
        rfl
  have hmap_top : (⊤ : AddSubgroup (w.1.adicCompletionIntegers L)).map (iota K L v w) =
      (w.1.adicCompletionIntegers L).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, AddSubgroup.mem_top _, rfl⟩
  rw [← hmap_range, ← hmap_top, AddSubgroup.relIndex_map_map_of_injective _ _ (iota_injective K L v w),
    AddSubgroup.relIndex_top_right]
  exact hidx

end ShellIndex

namespace U5

section Norms

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev qv : ℝ := (Ideal.absNorm v.asIdeal : ℝ)

theorem one_lt_qv : 1 < qv K v := by
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  unfold qv
  exact_mod_cast this

theorem qv_pos : 0 < qv K v := lt_trans zero_lt_one (one_lt_qv K v)

theorem qv_ne_zero : qv K v ≠ 0 := (qv_pos K v).ne'

theorem mem_integers_iff_norm (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem exists_norm_eq_zpow_and_v_eq {x : v.adicCompletion K} (hx : x ≠ 0) :
    ∃ k : ℤ, ‖x‖ = qv K v ^ k ∧ (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hv0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨Multiplicative.toAdd (WithZero.unzero hv0), ?_, ?_⟩
  · rw [NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv0]
    push_cast
    rfl
  · conv_lhs => rw [← WithZero.coe_unzero hv0]
    rfl

theorem norm_eq_zero_or_zpow (x : v.adicCompletion K) : ‖x‖ = 0 ∨ ∃ n : ℤ, ‖x‖ = qv K v ^ n := by
  by_cases hx : x = 0
  · exact Or.inl (by rw [hx, norm_zero])
  · obtain ⟨k, hk, -⟩ := exists_norm_eq_zpow_and_v_eq K v hx
    exact Or.inr ⟨k, hk⟩

theorem v_eq_exp_of_norm_eq_zpow {x : v.adicCompletion K} {k : ℤ} (h : ‖x‖ = qv K v ^ k) :
    (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at h
    exact (zpow_pos (qv_pos K v) k).ne h
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hk'] at h
  have hk : k' = k := zpow_right_injective₀ (qv_pos K v) (one_lt_qv K v).ne' h
  rw [hv, hk]

theorem norm_eq_zpow_of_v_eq_exp {x : v.adicCompletion K} {k : ℤ}
    (h : (Valued.v x : WithZero (Multiplicative ℤ)) = WithZero.exp k) : ‖x‖ = qv K v ^ k := by
  have hx : x ≠ 0 := by
    intro hx
    rw [hx, map_zero] at h
    exact WithZero.coe_ne_zero h.symm
  obtain ⟨k', hk', hv⟩ := exists_norm_eq_zpow_and_v_eq K v hx
  rw [hv] at h
  have : k' = k := WithZero.exp_injective h
  rw [hk', this]

theorem norm_eq_one_iff_v (x : v.adicCompletion K) :
    ‖x‖ = 1 ↔ (Valued.v x : WithZero (Multiplicative ℤ)) = 1 := by
  constructor
  · intro h
    have := v_eq_exp_of_norm_eq_zpow K v (k := 0) (by rw [h, zpow_zero])
    rwa [WithZero.exp_zero] at this
  · intro h
    have := norm_eq_zpow_of_v_eq_exp K v (k := 0) (by rw [h, WithZero.exp_zero])
    rwa [zpow_zero] at this

theorem zpow_add_one_le_norm_of_lt {x : v.adicCompletion K} {n : ℤ} (h : qv K v ^ n < ‖x‖) :
    qv K v ^ (n + 1) ≤ ‖x‖ := by
  rcases norm_eq_zero_or_zpow K v x with h0 | ⟨k, hk⟩
  · rw [h0] at h; exact absurd h (not_lt.2 (zpow_nonneg (qv_pos K v).le _))
  · rw [hk] at h ⊢
    have hlt : n < k := (zpow_lt_zpow_iff_right₀ (one_lt_qv K v)).1 h
    exact zpow_le_zpow_right₀ (one_lt_qv K v).le (by omega)

theorem exists_norm_eq_inv : ∃ ϖ : v.adicCompletion K, ‖ϖ‖ = (qv K v)⁻¹ := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1))
  exact ⟨x, by rw [norm_eq_zpow_of_v_eq_exp K v hx, zpow_neg, zpow_one]⟩

end Norms

section Unramified

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

local notation "Kv" => HeightOneSpectrum.adicCompletion K v
local notation "Lw" => HeightOneSpectrum.adicCompletion L (Subtype.val w)

scoped instance isScalarTower_int : IsScalarTower (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem liesOver : w.1.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal w.2).symm⟩

variable (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
include hw

theorem v_algebraMap (x : Kv) :
    (Valued.v (algebraMap Kv Lw x) : WithZero (Multiplicative ℤ)) = Valued.v x := by
  change Valued.v (w.adicCompletionSemialgHom K L x) = _
  rw [HeightOneSpectrum.Extension.valued_adicCompletionSemialgHom K L w x, hw, pow_one]

theorem norm_algebraMap_eq_one_iff (x : Kv) : ‖algebraMap Kv Lw x‖ = 1 ↔ ‖x‖ = 1 := by
  rw [norm_eq_one_iff_v, norm_eq_one_iff_v, v_algebraMap K L v w hw]

theorem norm_algebraMap_uniformizer {ϖ : Kv} (hϖ : ‖ϖ‖ = (qv K v)⁻¹) :
    ‖algebraMap Kv Lw ϖ‖ = (qv L w.1)⁻¹ := by
  have h1 := v_eq_exp_of_norm_eq_zpow K v (k := -1) (by rw [hϖ, zpow_neg, zpow_one])
  rw [← v_algebraMap K L v w hw] at h1
  rw [norm_eq_zpow_of_v_eq_exp L w.1 h1, zpow_neg, zpow_one]

theorem exists_eq_algebraMap_mul_unit {y : Lw} (hy : y ≠ 0) :
    ∃ x : Kv, x ≠ 0 ∧ (Valued.v (y * (algebraMap Kv Lw x)⁻¹) : WithZero (Multiplicative ℤ)) = 1 := by
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v
    (Valued.v y : WithZero (Multiplicative ℤ))
  have hy0 : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact hy0 hx.symm
  refine ⟨x, hx0, ?_⟩
  rw [map_mul, map_inv₀, v_algebraMap K L v w hw, hx, mul_inv_cancel₀ hy0]

theorem qv_w_eq_pow : qv L w.1 = qv K v ^ Module.finrank Kv Lw := by
  have hef := HeightOneSpectrum.adicCompletion.ramificationIdx_mul_inertiaDeg_eq_finrank K L w
  have hw' : v.asIdeal.ramificationIdx' w.1.asIdeal = 1 := by
    have h2 : HeightOneSpectrum.under (𝓞 K) w.1 = v := w.2
    have h3 := hw
    rw [h2] at h3
    exact h3
  rw [hw', one_mul] at hef
  haveI := liesOver K L v w
  unfold qv
  rw [Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver w.1.asIdeal v.asIdeal v.isPrime v.ne_bot, hef]
  push_cast
  rfl

omit hw in

theorem isIntegral_of_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) :
    IsIntegral (v.adicCompletionIntegers K) y := by
  haveI : Algebra.IsIntegral (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.of_finite _ _
  have h : IsIntegral (v.adicCompletionIntegers K) (⟨y, hy⟩ : w.1.adicCompletionIntegers L) :=
    Algebra.IsIntegral.isIntegral _
  exact h.map (IsScalarTower.toAlgHom (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L)
    (w.1.adicCompletion L))

omit hw in

theorem mem_of_isIntegral {y : Lw} (hy : IsIntegral (v.adicCompletionIntegers K) y) :
    y ∈ w.1.adicCompletionIntegers L := by
  have h2 : IsIntegral (w.1.adicCompletionIntegers L) y := hy.tower_top
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := w.1.adicCompletionIntegers L)
    (K := w.1.adicCompletion L)).1 h2
  rw [← hz]
  exact z.2

variable (θ : (w.1.adicCompletion L) ≃ₐ[v.adicCompletion K] (w.1.adicCompletion L))

omit hw in

theorem theta_mem {y : Lw} (hy : y ∈ w.1.adicCompletionIntegers L) : θ y ∈ w.1.adicCompletionIntegers L := by
  apply mem_of_isIntegral K L v w
  exact (isIntegral_of_mem K L v w hy).map (θ.restrictScalars (v.adicCompletionIntegers K)).toAlgHom

omit hw in

theorem v_theta_eq_one {y : Lw} (hy : (Valued.v y : WithZero (Multiplicative ℤ)) = 1) :
    (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, map_zero] at hy; exact zero_ne_one hy
  have h1 : θ y ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hy.le)
  have h2 : θ y⁻¹ ∈ w.1.adicCompletionIntegers L :=
    theta_mem K L v w θ ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (by rw [map_inv₀, hy, inv_one]))
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [map_inv₀, map_inv₀] at h2
  have h3 : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ θ.injective).2 hy0)
  exact le_antisymm h1 (by rwa [inv_le_one₀ (zero_lt_iff.2 h3)] at h2)

theorem v_theta (y : Lw) : (Valued.v (θ y) : WithZero (Multiplicative ℤ)) = Valued.v y := by
  by_cases hy : y = 0
  · rw [hy, map_zero]
  obtain ⟨x, hx0, hu⟩ := exists_eq_algebraMap_mul_unit K L v w hw hy
  have ha0 : algebraMap Kv Lw x ≠ 0 := (map_ne_zero _).2 hx0
  have hy' : y = (y * (algebraMap Kv Lw x)⁻¹) * algebraMap Kv Lw x := by
    rw [mul_assoc, inv_mul_cancel₀ ha0, mul_one]
  conv_lhs => rw [hy', map_mul, AlgEquiv.commutes, map_mul, v_theta_eq_one K L v w θ hu]
  conv_rhs => rw [hy', map_mul, hu]

theorem norm_theta (y : Lw) : ‖θ y‖ = ‖y‖ := by
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def, v_theta K L v w hw θ]

end Unramified

end U5
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section Law

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (ϖ : v.adicCompletion K)

def Alat (s : ℕ) : AddSubgroup (w.1.adicCompletion L) :=
  ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
      (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)) ⊓
    ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
      (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))

def Lam (a u : ℕ) : AddSubgroup (w.1.adicCompletion L) :=
  ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
      (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a)))) ⊓
    ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
      ((AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u))).comp
        (θ.toAlgHom.toRingHom.toAddMonoidHom - AddMonoidHom.mulLeft c)))

theorem mem_Alat (s : ℕ) (y : w.1.adicCompletion L) :
    y ∈ Alat K L v w θ c ϖ s ↔
      θ y - c * y ∈ w.1.adicCompletionIntegers L ∧ algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s) * y ∈ w.1.adicCompletionIntegers L :=
  Iff.rfl

theorem mem_Lam (a u : ℕ) (y : w.1.adicCompletion L) :
    y ∈ Lam K L v w θ c ϖ a u ↔
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a) * y ∈ w.1.adicCompletionIntegers L ∧
        algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u) * (θ y - c * y) ∈ w.1.adicCompletionIntegers L :=
  Iff.rfl

theorem P_mul (t : v.adicCompletion K) (y : w.1.adicCompletion L) :
    θ (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * y) - c * (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * y) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * (θ y - c * y) := by
  rw [map_mul, AlgEquiv.commutes, mul_sub, mul_left_comm]

variable (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

include hϖ in
theorem algebraMap_pow_mem (t : ℕ) : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ t) ∈ w.1.adicCompletionIntegers L := by
  have h := pis_eq K L v w ϖ hϖ t
  dsimp only [pis] at h
  rw [h]
  exact SetLike.coe_mem _

include hϖ in
theorem algebraMap_pow_ne_zero (t : ℕ) : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ t) ≠ 0 := pis_ne_zero K L v w ϖ hϖ t

include hϖ in

theorem Lam_eq_comap (s u : ℕ) :
    Lam K L v w θ c ϖ (s + u) u = (Alat K L v w θ c ϖ s).comap (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u))) := by
  ext y
  rw [AddSubgroup.mem_comap, mem_Lam, mem_Alat, AddMonoidHom.coe_mulLeft, P_mul, ← mul_assoc, ← map_mul,
    ← pow_add, and_comm]

theorem O_le_Alat (hcO : c ∈ w.1.adicCompletionIntegers L) (hϖ' : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹) (s : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup ≤ Alat K L v w θ c ϖ s := by
  intro y hy
  rw [mem_Alat]
  exact ⟨sub_mem (theta_mem K L v w θ hy) (mul_mem hcO hy), mul_mem (algebraMap_pow_mem K L v w ϖ hϖ' s) hy⟩

include hϖ in

theorem map_mulLeft_le (u : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u))) ≤
      (w.1.adicCompletionIntegers L).toAddSubgroup := by
  rintro x ⟨y, hy, rfl⟩
  show algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u) * y ∈ w.1.adicCompletionIntegers L
  exact mul_mem (algebraMap_pow_mem K L v w ϖ hϖ u) (show y ∈ w.1.adicCompletionIntegers L from hy)

include hϖ in

theorem Lam_eq_of_le (hcO : c ∈ w.1.adicCompletionIntegers L) {a u : ℕ} (h : a ≤ u) :
    Lam K L v w θ c ϖ a u =
      (w.1.adicCompletionIntegers L).toAddSubgroup.comap (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a))) := by
  refine le_antisymm inf_le_left fun y hy => ⟨hy, ?_⟩
  rw [AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft] at hy
  show algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u) * (θ y - c * y) ∈ w.1.adicCompletionIntegers L
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, map_mul, mul_comm (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a)), mul_assoc, ← P_mul]
  exact mul_mem (algebraMap_pow_mem K L v w ϖ hϖ k)
    (sub_mem (theta_mem K L v w θ hy) (mul_mem hcO hy))

end Law
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section Index

theorem index_Lam_add
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    (s u : ℕ) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ (s + u) u) =
      Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * u + min s m) := by
  have hn1 : (Valued.v n : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one K v hn
  have hcunit := v_c_eq_one K L v w θ hw hprime.pos c n hn1 hc
  have hcO : c ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 c).2 hcunit.le
  have hsurj := mulLeft_algebraMap_surjective K L v w (ϖ ^ u) (pow_ne_zero _ (pi_ne_zero K v ϖ hϖ))
  have hinj := mulLeft_pis_injective K L v w ϖ hϖ u
  have hA : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Alat K L v w θ c ϖ s) =
      Ideal.absNorm v.asIdeal ^ min s m :=
    IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
      K L v w hw hprime θ hθ hres c n hn m hm hc ϖ hϖ s
  have key : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ (s + u) u) =
      ((w.1.adicCompletionIntegers L).toAddSubgroup.map
        (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u)))).relIndex (Alat K L v w θ c ϖ s) := by
    rw [Lam_eq_comap K L v w θ c ϖ hϖ,
      ← relIndex_comap_comap_of_surjective (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u))) hsurj
        ((w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ u))))
        (Alat K L v w θ c ϖ s),
      AddSubgroup.comap_map_eq_self_of_injective hinj]
  rw [key, ← AddSubgroup.relIndex_mul_relIndex _ _ _ (map_mulLeft_le K L v w ϖ hϖ u)
      (O_le_Alat K L v w θ c ϖ hcO hϖ s),
    relIndex_map_mulLeft_pis K L v w ϖ hϖ u, hA, pow_add]

theorem index_Lam_of_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    {a u : ℕ} (h : a ≤ u) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) =
      Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * a) := by
  have hn1 : (Valued.v n : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one K v hn
  have hcunit := v_c_eq_one K L v w θ hw hprime.pos c n hn1 hc
  have hcO : c ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 c).2 hcunit.le
  have hsurj := mulLeft_algebraMap_surjective K L v w (ϖ ^ a) (pow_ne_zero _ (pi_ne_zero K v ϖ hϖ))
  have hinj := mulLeft_pis_injective K L v w ϖ hϖ a
  rw [Lam_eq_of_le K L v w θ c ϖ hϖ hcO h]
  have key : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
      ((w.1.adicCompletionIntegers L).toAddSubgroup.comap (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a)))) =
      ((w.1.adicCompletionIntegers L).toAddSubgroup.map
        (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a)))).relIndex (w.1.adicCompletionIntegers L).toAddSubgroup := by
    rw [← relIndex_comap_comap_of_surjective (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a))) hsurj
        ((w.1.adicCompletionIntegers L).toAddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ a))))
        (w.1.adicCompletionIntegers L).toAddSubgroup,
      AddSubgroup.comap_map_eq_self_of_injective hinj]
  rw [key, relIndex_map_mulLeft_pis K L v w ϖ hϖ a]

end Index
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section MeasureLaw

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
  (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
  (c : w.1.adicCompletion L) (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)

include hw hϖ in

theorem mul_mem_iff_norm_le (t : ℕ) (z : w.1.adicCompletion L) :
    algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ t) * z ∈ w.1.adicCompletionIntegers L ↔ ‖z‖ ≤ U5.qv L w.1 ^ t := by
  have hπ : ‖algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ϖ‖ = (U5.qv L w.1)⁻¹ := U5.norm_algebraMap_uniformizer K L v w hw hϖ
  rw [U5.mem_integers_iff_norm, norm_mul, map_pow, norm_pow, hπ, inv_pow,
    inv_mul_le_iff₀ (pow_pos (U5.qv_pos L w.1) t), mul_one]

include hw hϖ in
theorem coe_Lam (a u : ℕ) :
    (Lam K L v w θ c ϖ a u : Set (w.1.adicCompletion L)) =
      {y | ‖y‖ ≤ U5.qv L w.1 ^ a ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ u} := by
  ext y
  rw [SetLike.mem_coe, mem_Lam, Set.mem_setOf_eq, mul_mem_iff_norm_le K L v w hw ϖ hϖ,
    mul_mem_iff_norm_le K L v w hw ϖ hϖ]

omit hϖ in
theorem continuous_P : Continuous fun y : w.1.adicCompletion L => θ y - c * y := by
  have hθ : Continuous θ := IsModuleTopology.continuous_of_linearMap θ.toLinearMap
  exact hθ.sub (continuous_const.mul continuous_id)

include hw hϖ in
theorem isClosed_Lam (a u : ℕ) : IsClosed (Lam K L v w θ c ϖ a u : Set (w.1.adicCompletion L)) := by
  rw [coe_Lam K L v w hw θ c ϖ hϖ]
  exact (isClosed_le continuous_norm continuous_const).inter
    (isClosed_le (continuous_norm.comp (continuous_P K L v w θ c)) continuous_const)

theorem coe_integers_eq_closedBall :
    (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = Metric.closedBall 0 1 := by
  ext y
  rw [SetLike.mem_coe, U5.mem_integers_iff_norm, Metric.mem_closedBall, dist_zero_right]

theorem isClosed_integers : IsClosed (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) := by
  rw [coe_integers_eq_closedBall]
  exact Metric.isClosed_closedBall

theorem norm_eq_pow_iff {t : ℕ} (ht : 1 ≤ t) (z : w.1.adicCompletion L) :
    ‖z‖ = U5.qv L w.1 ^ t ↔ ‖z‖ ≤ U5.qv L w.1 ^ t ∧ ¬ ‖z‖ ≤ U5.qv L w.1 ^ (t - 1) := by
  constructor
  · intro h
    refine ⟨h.le, ?_⟩
    rw [h, not_le]
    exact pow_lt_pow_right₀ (U5.one_lt_qv L w.1) (by omega)
  · rintro ⟨h1, h2⟩
    rw [not_le] at h2
    have h3 := U5.zpow_add_one_le_norm_of_lt L w.1 (n := ((t - 1 : ℕ) : ℤ)) (by rwa [zpow_natCast])
    have h4 : ((t - 1 : ℕ) : ℤ) + 1 = ((t : ℕ) : ℤ) := by omega
    rw [h4, zpow_natCast] at h3
    exact le_antisymm h1 h3

end MeasureLaw
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section MeasureIndex

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))

theorem index_Lam_of_ge
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    {a u : ℕ} (h : u ≤ a) :
    (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) =
      Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * u + min (a - u) m) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, add_comm u s]
  exact index_Lam_add K L v w hw hprime θ hθ hres c n hn m hm hc ϖ hϖ s u

variable [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
  (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
  (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1)

include hμE in

theorem measure_eq_of_relIndex
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (c : w.1.adicCompletion L) (hcO : c ∈ w.1.adicCompletionIntegers L)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    (a u e : ℕ)
    (hidx : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) =
      Ideal.absNorm v.asIdeal ^ e) :
    μE (Lam K L v w θ c ϖ a u : Set (w.1.adicCompletion L)) = ((Ideal.absNorm v.asIdeal ^ e : ℕ) : ENNReal) := by
  have hle : (w.1.adicCompletionIntegers L).toAddSubgroup ≤ Lam K L v w θ c ϖ a u := by
    intro y hy
    have hy' : y ∈ w.1.adicCompletionIntegers L := hy
    rw [mem_Lam]
    exact ⟨mul_mem (algebraMap_pow_mem K L v w ϖ hϖ a) hy',
      mul_mem (algebraMap_pow_mem K L v w ϖ hϖ u) (sub_mem (theta_mem K L v w θ hy') (mul_mem hcO hy'))⟩
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  have hfin : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) ≠ 0 := by
    rw [hidx]; exact pow_ne_zero _ hq0
  have hO : MeasurableSet (((w.1.adicCompletionIntegers L).toAddSubgroup : AddSubgroup (w.1.adicCompletion L)) :
      Set (w.1.adicCompletion L)) :=
    (isClosed_integers K L v w).measurableSet
  rw [MeasureTheory.Measure.measure_coe_eq_relIndex_mul_of_le_of_isAddLeftInvariant μE _ _ hle hO hfin, hidx]
  have : μE (((w.1.adicCompletionIntegers L).toAddSubgroup : AddSubgroup (w.1.adicCompletion L)) :
      Set (w.1.adicCompletion L)) = 1 := hμE
  rw [this, mul_one]

end MeasureIndex
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section Cumulative

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
  [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
  (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
  (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1)

theorem shellSet_eq_diff
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (c : w.1.adicCompletion L) (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    {a : ℕ} (ha : 1 ≤ a) (u : ℕ) :
    {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ a ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ u} =
      (Lam K L v w θ c ϖ a u : Set (w.1.adicCompletion L)) \ (Lam K L v w θ c ϖ (a - 1) u : Set (w.1.adicCompletion L)) := by
  ext y
  rw [Set.mem_diff, coe_Lam K L v w hw θ c ϖ hϖ, coe_Lam K L v w hw θ c ϖ hϖ, Set.mem_setOf_eq, Set.mem_setOf_eq,
    Set.mem_setOf_eq, norm_eq_pow_iff K L v w ha]
  tauto

include hμE in

theorem measureReal_shellSet
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (m : ℕ)
    (hm : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(m : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)
    (ϖ : v.adicCompletion K) (hϖ : ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹)
    {a : ℕ} (ha : 1 ≤ a) (u e₁ e₂ : ℕ)
    (h₁ : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) = Ideal.absNorm v.asIdeal ^ e₁)
    (h₂ : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ (a - 1) u) = Ideal.absNorm v.asIdeal ^ e₂)
    (h12 : e₂ ≤ e₁) :
    (μE {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ a ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ u}).toReal =
      U5.qv K v ^ e₁ - U5.qv K v ^ e₂ := by
  have hn1 : (Valued.v n : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one K v hn
  have hcunit := v_c_eq_one K L v w θ hw hprime.pos c n hn1 hc
  have hcO : c ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 c).2 hcunit.le
  have hμ1 := measure_eq_of_relIndex K L v w μE hμE θ c hcO ϖ hϖ a u e₁ h₁
  have hμ2 := measure_eq_of_relIndex K L v w μE hμE θ c hcO ϖ hϖ (a - 1) u e₂ h₂
  have hsub : (Lam K L v w θ c ϖ (a - 1) u : Set (w.1.adicCompletion L)) ⊆ Lam K L v w θ c ϖ a u := by
    intro y hy
    rw [coe_Lam K L v w hw θ c ϖ hϖ, Set.mem_setOf_eq] at hy ⊢
    exact ⟨hy.1.trans (pow_le_pow_right₀ (U5.one_lt_qv L w.1).le (Nat.sub_le a 1)), hy.2⟩
  rw [shellSet_eq_diff K L v w hw θ c ϖ hϖ ha u,
    measure_diff hsub (isClosed_Lam K L v w hw θ c ϖ hϖ (a - 1) u).measurableSet.nullMeasurableSet
      (by rw [hμ2]; exact ENNReal.natCast_ne_top _),
    hμ1, hμ2, ENNReal.toReal_sub_of_le (by exact_mod_cast pow_le_pow_right₀ (NumberField.HeightOneSpectrum.one_lt_absNorm v).le h12)
      (ENNReal.natCast_ne_top _),
    ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  push_cast
  rfl

end Cumulative
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section Arith

theorem geomSum_pos {q : ℝ} (hq : 1 < q) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : 0 < ∑ t ∈ Finset.range ℓ, q ^ t := by
  apply Finset.sum_pos (fun t _ => pow_pos (lt_trans zero_lt_one hq) t)
  exact ⟨0, Finset.mem_range.2 (by omega)⟩

theorem arith_mid (q : ℝ) (hq : 1 < q) (ℓ' k j : ℕ) (S : ℝ) (hS : S * (q - 1) = q ^ (ℓ' + 1) - 1)
    (hS0 : S ≠ 0) :
    q ^ ((ℓ' + 1) * k + j + 1) - q ^ ((ℓ' + 1) * k + j) =
      ((q ^ (ℓ' + 1)) ^ (j + 1 + k) - (q ^ (ℓ' + 1)) ^ (j + k)) * (q ^ (ℓ' * j) * S)⁻¹ := by
  have hq0 : q ≠ 0 := (lt_trans zero_lt_one hq).ne'
  rw [eq_mul_inv_iff_mul_eq₀ (mul_ne_zero (pow_ne_zero _ hq0) hS0), ← pow_mul, ← pow_mul]
  linear_combination (q ^ ((ℓ' + 1) * k + j + ℓ' * j)) * hS

end Arith
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

section MainMeasure

set_option maxHeartbeats 6400000 in
theorem mainM
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (d : ℕ)
    (hd : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)

    (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((Ideal.absNorm v.asIdeal : ℝ) ^
          ((Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (i - 1)) *
        ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
          (Ideal.absNorm v.asIdeal : ℝ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)

    [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
    (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
    (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1)
    (m : ℕ) (hm : 1 ≤ m) :

    (∀ y : w.1.adicCompletion L, ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m →
        ∃ t : ℕ, t ≤ d ∧ ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ ((m : ℤ) - t)) ∧
    (∀ i : ℕ, i ≤ d → i < m →
        (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧
            ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - i)}).toReal =
          ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) *
            (P i - P (i + 1))) ∧
    (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧ ‖θ y - c * y‖ ≤ 1}).toReal =
      ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) * P m  := by

  obtain ⟨ϖ, hϖ⟩ := U5.exists_norm_eq_inv K v
  have hn1 : (Valued.v n : WithZero (Multiplicative ℤ)) = 1 := v_eq_one_of_norm_eq_one K v hn
  have hcunit := v_c_eq_one K L v w θ hw hprime.pos c n hn1 hc
  have hcO : c ∈ w.1.adicCompletionIntegers L := (mem_integers_iff_v L w.1 c).2 hcunit.le
  have hc1 : ‖c‖ = 1 := (U5.norm_eq_one_iff_v L w.1 c).2 hcunit
  have hN : U5.qv L w.1 = U5.qv K v ^ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := U5.qv_w_eq_pow K L v w hw
  have hq1 : 1 < U5.qv K v := U5.one_lt_qv K v
  have hq0 : U5.qv K v ≠ 0 := U5.qv_ne_zero K v
  have hNw1 : 1 < U5.qv L w.1 := U5.one_lt_qv L w.1
  have hℓ2 : 2 ≤ Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) := hprime.two_le
  obtain ⟨ℓ', hℓ'⟩ : ∃ ℓ' : ℕ, Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = ℓ' + 1 := ⟨Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1, by omega⟩
  set S : ℝ := ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), U5.qv K v ^ t with hSdef
  have hS : S * (U5.qv K v - 1) = U5.qv K v ^ (ℓ' + 1) - 1 := by rw [hSdef, geom_sum_mul, hℓ']
  have hS0 : S ≠ 0 := (geomSum_pos hq1 _ (by omega)).ne'

  have hidx_ge : ∀ a u : ℕ, u ≤ a →
      (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) =
        Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * u + min (a - u) d) := fun a u h =>
    index_Lam_of_ge K L v w hw hprime θ hθ hres c n hn d hd hc ϖ hϖ h
  have hidx_le : ∀ a u : ℕ, a ≤ u →
      (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Lam K L v w θ c ϖ a u) =
        Ideal.absNorm v.asIdeal ^ (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) * a) := fun a u h =>
    index_Lam_of_le K L v w hw hprime θ hθ hres c n hn d hd hc ϖ hϖ h

  have cumul : ∀ i : ℕ, i ≤ m →
      (μE {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ (m - i)}).toReal =
        (U5.qv L w.1 ^ m - U5.qv L w.1 ^ (m - 1)) * P i := by
    intro i him
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    ·
      have h₁ := hidx_ge m (m - 0) (Nat.sub_le m 0)
      have h₂ := hidx_le (m - 1) (m - 0) (by omega)
      rw [show m - (m - 0) = 0 by omega, Nat.zero_min, add_zero] at h₁
      rw [measureReal_shellSet K L v w μE hμE hw hprime θ hθ hres c n hn d hd hc ϖ hϖ hm (m - 0) _ _ h₁ h₂
          (Nat.mul_le_mul_left _ (Nat.sub_le m 1)),
        hP0, mul_one, hN, ← pow_mul, ← pow_mul, Nat.sub_zero]
    · rcases le_or_gt i d with hid | hid
      ·
        have h₁ := hidx_ge m (m - i) (Nat.sub_le m i)
        have h₂ := hidx_ge (m - 1) (m - i) (by omega)
        rw [show m - (m - i) = i by omega, Nat.min_eq_left hid] at h₁
        rw [show m - 1 - (m - i) = i - 1 by omega, Nat.min_eq_left (by omega : i - 1 ≤ d)] at h₂
        rw [measureReal_shellSet K L v w μE hμE hw hprime θ hθ hres c n hn d hd hc ϖ hϖ hm (m - i) _ _ h₁ h₂ (by omega),
          hP i hi1 hid, hN]
        obtain ⟨k, hk⟩ : ∃ k : ℕ, m = i + k := ⟨m - i, by omega⟩
        obtain ⟨j, hj⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
        subst hk
        subst hj
        rw [show j + 1 + k - (j + 1) = k by omega, show j + 1 + k - 1 = j + k by omega,
          show j + 1 - 1 = j by omega, hℓ', show ℓ' + 1 - 1 = ℓ' by omega,
          show (ℓ' + 1) * k + (j + 1) = (ℓ' + 1) * k + j + 1 by ring]
        exact arith_mid _ hq1 ℓ' k j S hS hS0
      ·
        have h₁ := hidx_ge m (m - i) (Nat.sub_le m i)
        have h₂ := hidx_ge (m - 1) (m - i) (by omega)
        rw [show m - (m - i) = i by omega, Nat.min_eq_right hid.le] at h₁
        rw [show m - 1 - (m - i) = i - 1 by omega, Nat.min_eq_right (by omega : d ≤ i - 1)] at h₂
        rw [measureReal_shellSet K L v w μE hμE hw hprime θ hθ hres c n hn d hd hc ϖ hϖ hm (m - i) _ _ h₁ h₂ le_rfl,
          hPd i hid, mul_zero, sub_self]

  have hmeasT : ∀ u : ℕ, MeasurableSet {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ u} := by
    intro u
    rw [shellSet_eq_diff K L v w hw θ c ϖ hϖ hm u]
    exact (isClosed_Lam K L v w hw θ c ϖ hϖ m u).measurableSet.diff (isClosed_Lam K L v w hw θ c ϖ hϖ (m - 1) u).measurableSet
  have hfinT : ∀ u : ℕ, μE {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ u} ≠ ⊤ := by
    intro u
    refine ((measure_mono ?_).trans_lt (isCompact_closedBall (0 : w.1.adicCompletion L) (U5.qv L w.1 ^ m)).measure_lt_top).ne
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hy.1.le
  refine ⟨?_, ?_, ?_⟩
  ·
    intro y hy
    change ‖y‖ = U5.qv L w.1 ^ m at hy
    have hy0 : y ≠ 0 := by
      intro h; rw [h, norm_zero] at hy; exact (pow_pos (lt_trans zero_lt_one hNw1) m).ne hy

    have hA : ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ m := by
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, U5.norm_theta K L v w hw θ, norm_mul, hc1, one_mul, max_self, hy]

    have hsat : Alat K L v w θ c ϖ (d + 1) ≤ Alat K L v w θ c ϖ d := by
      have hle : Alat K L v w θ c ϖ d ≤ Alat K L v w θ c ϖ (d + 1) := by
        intro z hz
        rw [mem_Alat] at hz ⊢
        refine ⟨hz.1, ?_⟩
        rw [pow_succ, map_mul, mul_comm (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ d)), mul_assoc]
        exact mul_mem (by simpa using algebraMap_pow_mem K L v w ϖ hϖ 1) hz.2
      have hOd := O_le_Alat K L v w θ c ϖ hcO hϖ d
      have hId : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Alat K L v w θ c ϖ d) =
          Ideal.absNorm v.asIdeal ^ min d d :=
        IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
          K L v w hw hprime θ hθ hres c n hn d hd hc ϖ hϖ d
      have hId1 : (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex (Alat K L v w θ c ϖ (d + 1)) =
          Ideal.absNorm v.asIdeal ^ min (d + 1) d :=
        IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one
          K L v w hw hprime θ hθ hres c n hn d hd hc ϖ hϖ (d + 1)
      rw [min_self] at hId
      rw [Nat.min_eq_right (Nat.le_succ d)] at hId1
      have hmul := AddSubgroup.relIndex_mul_relIndex _ _ _ hOd hle
      rw [hId, hId1] at hmul
      have hq0' : Ideal.absNorm v.asIdeal ^ d ≠ 0 := pow_ne_zero _ (by
        have := NumberField.HeightOneSpectrum.one_lt_absNorm v; omega)
      have h1 : (Alat K L v w θ c ϖ d).relIndex (Alat K L v w θ c ϖ (d + 1)) = 1 := by
        have := hmul
        nth_rewrite 2 [← mul_one (Ideal.absNorm v.asIdeal ^ d)] at this
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq0') this
      exact AddSubgroup.relIndex_eq_one.1 h1

    have hB : ¬ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ ((m : ℤ) - d - 1) := by
      intro hle
      have hϖ0 : ϖ ≠ 0 := pi_ne_zero K v ϖ hϖ
      set t : v.adicCompletion K := ϖ ^ ((m : ℤ) - d - 1) with ht
      have hπ : ‖algebraMap (v.adicCompletion K) (w.1.adicCompletion L) ϖ‖ = (U5.qv L w.1)⁻¹ := U5.norm_algebraMap_uniformizer K L v w hw hϖ
      have hnt : ‖algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t‖ = U5.qv L w.1 ^ (-((m : ℤ) - d - 1)) := by
        rw [ht, map_zpow₀, norm_zpow, hπ, inv_zpow']
      set y' : w.1.adicCompletion L := algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * y with hy'
      have hy'n : ‖y'‖ = U5.qv L w.1 ^ (d + 1) := by
        rw [hy', norm_mul, hnt, hy, ← zpow_natCast, ← zpow_add₀ (U5.qv_ne_zero L w.1), ← zpow_natCast]
        congr 1; push_cast; ring
      have hPy' : θ y' - c * y' = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) t * (θ y - c * y) := P_mul K L v w θ c t y
      have h1 : θ y' - c * y' ∈ w.1.adicCompletionIntegers L := by
        rw [U5.mem_integers_iff_norm, hPy', norm_mul, hnt]
        calc U5.qv L w.1 ^ (-((m : ℤ) - d - 1)) * ‖θ y - c * y‖
            ≤ U5.qv L w.1 ^ (-((m : ℤ) - d - 1)) * U5.qv L w.1 ^ ((m : ℤ) - d - 1) :=
              mul_le_mul_of_nonneg_left hle (zpow_nonneg (U5.qv_pos L w.1).le _)
          _ = 1 := by rw [← zpow_add₀ (U5.qv_ne_zero L w.1), neg_add_cancel, zpow_zero]
      have h2 : algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ (d + 1)) * y' ∈ w.1.adicCompletionIntegers L := by
        rw [mul_mem_iff_norm_le K L v w hw ϖ hϖ, hy'n]
      have hmem : y' ∈ Alat K L v w θ c ϖ (d + 1) := (mem_Alat K L v w θ c ϖ (d + 1) y').2 ⟨h1, h2⟩
      have hmem' := ((mem_Alat K L v w θ c ϖ d y').1 (hsat hmem)).2
      rw [mul_mem_iff_norm_le K L v w hw ϖ hϖ, hy'n] at hmem'
      exact absurd hmem' (not_le.2 (pow_lt_pow_right₀ hNw1 (Nat.lt_succ_self d)))

    have hP0' : θ y - c * y ≠ 0 := by
      intro h; apply hB; rw [h, norm_zero]; exact zpow_nonneg (U5.qv_pos L w.1).le _
    obtain ⟨k, hk, -⟩ := U5.exists_norm_eq_zpow_and_v_eq L w.1 hP0'
    have hkm : k ≤ (m : ℤ) := by
      rw [hk, ← zpow_natCast] at hA
      exact (zpow_le_zpow_iff_right₀ hNw1).1 hA
    have hkd : (m : ℤ) - d ≤ k := by
      rw [hk, not_le] at hB
      have := (zpow_lt_zpow_iff_right₀ hNw1).1 hB
      omega
    refine ⟨((m : ℤ) - k).toNat, by omega, ?_⟩
    change ‖θ y - c * y‖ = U5.qv L w.1 ^ ((m : ℤ) - (((m : ℤ) - k).toNat : ℕ))
    rw [hk]; congr 1; omega
  ·
    intro i hid him
    change (μE {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ = U5.qv L w.1 ^ (m - i)}).toReal =
      (U5.qv L w.1 ^ m - U5.qv L w.1 ^ (m - 1)) * (P i - P (i + 1))
    have hset : {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ = U5.qv L w.1 ^ (m - i)} =
        {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ (m - i)} \
          {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ (m - (i + 1))} := by
      ext y
      simp only [Set.mem_diff, Set.mem_setOf_eq]
      rw [norm_eq_pow_iff K L v w (by omega : 1 ≤ m - i) (θ y - c * y), show m - (i + 1) = m - i - 1 by omega]
      tauto
    have hsub : {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ (m - (i + 1))} ⊆
        {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ U5.qv L w.1 ^ (m - i)} := by
      intro y hy
      exact ⟨hy.1, hy.2.trans (pow_le_pow_right₀ hNw1.le (by omega))⟩
    rw [hset, measure_diff hsub (hmeasT _).nullMeasurableSet (hfinT _),
      ENNReal.toReal_sub_of_le (measure_mono hsub) (hfinT _), cumul i him.le, cumul (i + 1) (by omega)]
    ring
  ·
    change (μE {y : w.1.adicCompletion L | ‖y‖ = U5.qv L w.1 ^ m ∧ ‖θ y - c * y‖ ≤ 1}).toReal =
      (U5.qv L w.1 ^ m - U5.qv L w.1 ^ (m - 1)) * P m
    have := cumul m le_rfl
    rwa [Nat.sub_self, pow_zero] at this

end MainMeasure
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5"

end Ws31S3
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5 P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3"

end
p2m_reactivate "P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3.U5 P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one.Ws31S3"

open Ws31S3 in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (hprime : (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)).Prime)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (hres : ∃ y : w.1.adicCompletion L, ‖y‖ ≤ 1 ∧ ‖θ y - y‖ = 1)
    (c : w.1.adicCompletion L) (n : v.adicCompletion K) (hn : ‖n‖ = 1) (d : ℕ)
    (hd : ‖1 - n‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(d : ℤ)))
    (hc : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)), (θ ^ i) c =
      algebraMap (v.adicCompletion K) (w.1.adicCompletion L) n)

    (P : ℕ → ℝ) (hP0 : P 0 = 1)
    (hP : ∀ i : ℕ, 1 ≤ i → i ≤ d →
      P i = ((Ideal.absNorm v.asIdeal : ℝ) ^
          ((Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) - 1) * (i - 1)) *
        ∑ t ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
          (Ideal.absNorm v.asIdeal : ℝ) ^ t)⁻¹)
    (hPd : ∀ i : ℕ, d < i → P i = 0)

    [MeasurableSpace (w.1.adicCompletion L)] [BorelSpace (w.1.adicCompletion L)]
    (μE : Measure (w.1.adicCompletion L)) [μE.IsAddHaarMeasure]
    (hμE : μE (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) = 1)
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ y : w.1.adicCompletion L, ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m →
        ∃ t : ℕ, t ≤ d ∧ ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ ((m : ℤ) - t)) ∧
    (∀ i : ℕ, i ≤ d → i < m →
        (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧
            ‖θ y - c * y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - i)}).toReal =
          ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) *
            (P i - P (i + 1))) ∧
    (μE {y : w.1.adicCompletion L | ‖y‖ = (Ideal.absNorm w.1.asIdeal : ℝ) ^ m ∧ ‖θ y - c * y‖ ≤ 1}).toReal =
      ((Ideal.absNorm w.1.asIdeal : ℝ) ^ m - (Ideal.absNorm w.1.asIdeal : ℝ) ^ (m - 1)) * P m :=
  Ws31S3.mainM K L v w hw hprime θ hθ hres c n hn d hd hc P hP0 hP hPd μE hμE m hm

end S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_AutomorphicForm_measureReal_norm_eq_and_norm_algEquiv_sub_mul_eq_of_prod_eq_of_ramificationIdx_eq_one (solution)
