-- Prove2me | solution 1 for AutomorphicForm.exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a69ed23b-14a1-5fcc-a707-e77bf7b4cccb

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_AdelicHeight_adelicHeight_globalPoints_mul_of_mem_borelSubgroup
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_apply_unitsAct_eq_of_forall_mem_normOneIdeles
import Theorems.Thm_AutomorphicForm_integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

open MeasureTheory NumberField
open scoped NNReal ENNReal Pointwise

noncomputable section

open NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel NumberField.AdelicHeight

namespace R1S9Vanish

section Height

variable {K : Type*} [NormedField K]

theorem rowMaxNorm_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowMaxNorm ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowMaxNorm
  rw [Matrix.GeneralLinearGroup.coe_mul, hbot 0, hbot 1, norm_mul, norm_mul,
    mul_max_of_nonneg _ _ (norm_nonneg z)]

theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  unfold finLocalHeight
  rw [hdet, rowMaxNorm_scalar_entries_mul h10 h11 g, mul_pow,
    mul_div_mul_left _ _ hz2.ne']

variable (F : Type) [Field F] [NumberField F]

theorem adelicHeight_centralScalar_mul (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    adelicHeight F (centralScalar (𝓞 F) F z * g) = adelicHeight F g := by
  have hcoe : ∀ i j : Fin 2, ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j = if i = j then (z : AdeleRing (𝓞 F) F) else 0 := by
    intro i j
    show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  unfold adelicHeight
  rw [map_mul, map_mul]
  congr 1
  · refine archHeight_scalar_entries_mul F (z := (z : AdeleRing (𝓞 F) F).1) (fun v => ?_) ?_ ?_ ?_ ?_ _
    · exact (Units.map ((archEval F v).comp (adeleArch (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [glArch_apply, hcoe]; rfl
  · unfold finHeight
    refine finprod_congr fun v => ?_
    rw [map_mul]
    refine finLocalHeight_scalar_entries_mul (z := ((z : AdeleRing (𝓞 F) F).2) v) ?_ ?_ ?_ ?_ ?_ _
    · exact (Units.map ((finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)).toMonoidHom z).ne_zero
    all_goals rw [finComponent_apply, glFin_apply, hcoe]; rfl

end Height

end R1S9Vanish

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped NNReal ENNReal Pointwise

namespace R1S9Vanish

section AdelicAlgebra

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

theorem sigmaAdelicAct_centralScalar (z : (AdeleRing (𝓞 L) L)ˣ) :
    sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z) = centralScalar (𝓞 L) L (D.unitsAct σ z) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((D.act σ : RingAut (AdeleRing (𝓞 L) L)).toRingHom) (Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 L) L) i j) =
    Matrix.scalar (Fin 2) ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) (z : AdeleRing (𝓞 L) L)) i j
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem sigmaAdelicAct_globalPoints' (g : GL (Fin 2) L) :
    sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L g) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.map (σ : L →+* L) g) :=
  sigmaAdelicAct_globalPoints K L D σ g

theorem conj_identity (h δ : GL (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L) :
    (globalPoints (𝓞 L) L h * x)⁻¹ * globalPoints (𝓞 L) L δ * sigmaAdelicAct K L D σ y =
      x⁻¹ * globalPoints (𝓞 L) L (h⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h) *
        sigmaAdelicAct K L D σ ((globalPoints (𝓞 L) L h)⁻¹ * y) := by
  rw [map_mul (sigmaAdelicAct K L D σ), map_inv (sigmaAdelicAct K L D σ), sigmaAdelicAct_globalPoints',
    map_mul (globalPoints (𝓞 L) L), map_mul (globalPoints (𝓞 L) L), map_inv (globalPoints (𝓞 L) L), mul_inv_rev]
  simp only [mul_assoc, mul_inv_cancel_left]

theorem centralScalar_comm (w : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    centralScalar (𝓞 L) L w * y = y * centralScalar (𝓞 L) L w := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  exact congrFun (congrFun (Matrix.scalar_commute (w : AdeleRing (𝓞 L) L) (fun r' => mul_comm _ r')
    (y : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L))).eq i) j

theorem mul_cs_left (g y : AdelicGL2 (𝓞 L) L) (w : (AdeleRing (𝓞 L) L)ˣ) :
    g * (centralScalar (𝓞 L) L w * y) = centralScalar (𝓞 L) L w * (g * y) := by
  rw [← mul_assoc, ← centralScalar_comm, mul_assoc]

theorem centralScalar_principal (q : Lˣ) :
    centralScalar (𝓞 L) L (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      globalPoints (𝓞 L) L (Matrix.GeneralLinearGroup.scalar (Fin 2) q) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  show Matrix.scalar (Fin 2) (algebraMap L (AdeleRing (𝓞 L) L) (q : L)) i j =
    algebraMap L (AdeleRing (𝓞 L) L) (Matrix.scalar (Fin 2) (q : L) i j)
  rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem unitsAct_principal (q : Lˣ) :
    D.unitsAct σ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) =
      Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) (Units.map (σ : L →* L) q) :=
  Units.ext (D.compat σ (q : L))

end AdelicAlgebra

section Stabiliser

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mul_diag_apply {γ δ₀ : GL (Fin 2) L}
    (hu : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hl : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (i j : Fin 2) :
    ((γ * δ₀ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      (γ : Matrix (Fin 2) (Fin 2) L) i j * (δ₀ : Matrix (Fin 2) (Fin 2) L) j j := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases j <;> simp [hu, hl]

theorem diag_mul_scalar_mul_map_apply (σ : L →+* L) {γ δ₀ : GL (Fin 2) L} (t : Lˣ)
    (hu : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hl : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) (i j : Fin 2) :
    ((δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) t * Matrix.GeneralLinearGroup.map σ γ : GL (Fin 2) L) :
        Matrix (Fin 2) (Fin 2) L) i j =
      (δ₀ : Matrix (Fin 2) (Fin 2) L) i i * (t : L) * σ ((γ : Matrix (Fin 2) (Fin 2) L) i j) := by
  have hsc : ∀ i j, ((Matrix.GeneralLinearGroup.scalar (Fin 2) t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      if i = j then (t : L) else 0 := fun i j => by
    show Matrix.scalar (Fin 2) (t : L) i j = _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hmap : ∀ i j, ((Matrix.GeneralLinearGroup.map σ γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j =
      σ ((γ : Matrix (Fin 2) (Fin 2) L) i j) := fun i j => rfl
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hsc, hmap]
  fin_cases i <;> fin_cases j <;> simp [hu, hl] <;> ring

theorem norm_inv' {x : L} (hx : x ≠ 0) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])

theorem norm_eq_one_of_two_entries [FiniteDimensional K L] (σ : L ≃ₐ[K] L) {p q t di dj di' dj' : L}
    (hp : p ≠ 0) (hq : q ≠ 0) (ht : t ≠ 0) (hdi : di ≠ 0) (hdj : dj ≠ 0) (hdi' : di' ≠ 0) (hdj' : dj' ≠ 0)
    (h1 : p * dj = di * t * σ p) (h2 : q * dj' = di' * t * σ q) :
    Algebra.norm K (di * dj' / (dj * di')) = 1 := by
  have hσp : σ p ≠ 0 := (map_ne_zero σ).mpr hp
  have hσq : σ q ≠ 0 := (map_ne_zero σ).mpr hq

  set m : L := p / q with hm
  have hm0 : m ≠ 0 := div_ne_zero hp hq
  have hσm : σ m = m * (dj * di' / (di * dj')) := by
    rw [hm, map_div₀]
    have e1 : σ p = p * dj / (di * t) := by
      rw [eq_div_iff (mul_ne_zero hdi ht), h1]; ring
    have e2 : σ q = q * dj' / (di' * t) := by
      rw [eq_div_iff (mul_ne_zero hdi' ht), h2]; ring
    rw [e1, e2]
    first | (field_simp; ring) | field_simp
  have hN : Algebra.norm K (σ m) = Algebra.norm K m := Algebra.norm_eq_of_algEquiv σ m
  rw [hσm, map_mul] at hN
  have hNm : Algebra.norm K m ≠ 0 := Algebra.norm_ne_zero_iff.mpr hm0
  have hc : Algebra.norm K (dj * di' / (di * dj')) = 1 := by
    have := hN
    rwa [mul_right_eq_self₀, or_iff_left hNm] at this
  have hinv : di * dj' / (dj * di') = (dj * di' / (di * dj'))⁻¹ := by
    rw [inv_div]
  have hc0 : dj * di' / (di * dj') ≠ 0 := div_ne_zero (mul_ne_zero hdj hdi') (mul_ne_zero hdi hdj')
  rw [hinv, norm_inv' (K := K) hc0, hc, inv_one]

theorem diag_or_antidiag_of_mem_stabiliser [FiniteDimensional K L] (σ : L ≃ₐ[K] L) (δ₀ : GL (Fin 2) L)
    (hu : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hl : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (γ : GL (Fin 2) L)
    (hγ : δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L)) :
    ((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) := by

  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hγ
  obtain ⟨t, ht⟩ := hγ
  have hmat : γ * δ₀ = δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) t * Matrix.GeneralLinearGroup.map (σ : L →+* L) γ := by
    have h := ht
    rw [eq_comm, inv_mul_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul] at h
    exact h

  have hent : ∀ i j : Fin 2, (γ : Matrix (Fin 2) (Fin 2) L) i j * (δ₀ : Matrix (Fin 2) (Fin 2) L) j j =
      (δ₀ : Matrix (Fin 2) (Fin 2) L) i i * (t : L) * σ ((γ : Matrix (Fin 2) (Fin 2) L) i j) := by
    intro i j
    have h := congrArg (fun M : GL (Fin 2) L => (M : Matrix (Fin 2) (Fin 2) L) i j) hmat
    rw [mul_diag_apply hu hl, diag_mul_scalar_mul_map_apply (σ : L →+* L) t hu hl] at h
    exact h

  have hdet : (δ₀ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := (Matrix.isUnits_det_units δ₀).ne_zero
  rw [Matrix.det_fin_two, hu, hl] at hdet
  have ha : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 := by
    intro h0; apply hdet; rw [h0]; ring
  have hd : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 := by
    intro h0; apply hdet; rw [h0]; ring
  have ht0 : (t : L) ≠ 0 := t.ne_zero
  set a := (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 with ha_def
  set d := (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1 with hd_def
  have hreg' : Algebra.norm K (d / a) ≠ 1 := by
    intro h1
    apply hreg
    have : a / d = (d / a)⁻¹ := by rw [inv_div]
    rw [this, norm_inv' (K := K) (div_ne_zero hd ha), h1, inv_one]

  have hσe : ∀ i j, ((σ : L →+* L) ((γ : Matrix (Fin 2) (Fin 2) L) i j)) = σ ((γ : Matrix (Fin 2) (Fin 2) L) i j) :=
    fun i j => rfl
  have ex1 : ¬ ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0) := by
    rintro ⟨hp, hq⟩
    have h := norm_eq_one_of_two_entries σ hp hq ht0 ha ha ha hd (hent 0 0) (hent 0 1)

    apply hreg'
    have : d / a = a * d / (a * a) := by field_simp
    rw [this, h]
  have ex2 : ¬ ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0) := by
    rintro ⟨hp, hq⟩
    have h := norm_eq_one_of_two_entries σ hp hq ht0 ha ha hd ha (hent 0 0) (hent 1 0)
    apply hreg
    have : a / d = a * a / (a * d) := by field_simp
    rw [this, h]
  have ex3 : ¬ ((γ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0) := by
    rintro ⟨hp, hq⟩
    have h := norm_eq_one_of_two_entries σ hp hq ht0 hd hd ha hd (hent 1 1) (hent 0 1)
    apply hreg'
    have : d / a = d * d / (d * a) := by field_simp
    rw [this, h]
  have ex4 : ¬ ((γ : Matrix (Fin 2) (Fin 2) L) 1 1 ≠ 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 ≠ 0) := by
    rintro ⟨hp, hq⟩
    have h := norm_eq_one_of_two_entries σ hp hq ht0 hd hd hd ha (hent 1 1) (hent 1 0)
    apply hreg
    have : a / d = d * a / (d * d) := by field_simp
    rw [this, h]

  have hdetγ : (γ : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  rw [Matrix.det_fin_two] at hdetγ
  by_cases h00 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0
  · right
    refine ⟨h00, ?_⟩
    by_contra h11
    have h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 ≠ 0 := by
      intro h01; apply hdetγ; rw [h00, h01]; ring
    exact ex3 ⟨h11, h01⟩
  · left
    have h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by
      by_contra h01; exact ex1 ⟨h00, h01⟩
    have h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
      by_contra h10; exact ex2 ⟨h00, h10⟩
    exact ⟨h10, h01⟩

theorem weyl_mul_mem_borel_of_antidiag {γ : GL (Fin 2) L}
    (h00 : (γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0) :
    gl2Weyl * γ ∈ borelSubgroup L := by
  show ((gl2Weyl * γ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
  rw [Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two, h00]

theorem mul_weyl_inv_mem_borel_of_antidiag {γ : GL (Fin 2) L}
    (h11 : (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) :
    γ * gl2Weyl⁻¹ ∈ borelSubgroup L := by
  show ((γ * gl2Weyl⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0
  rw [gl2Weyl_inv, Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two, h11]

theorem weyl_conj_mem_borel_of_diag {γ : GL (Fin 2) L}
    (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (h01 : (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) :
    gl2Weyl * γ * gl2Weyl⁻¹ ∈ borelSubgroup L := by
  apply mul_weyl_inv_mem_borel_of_antidiag
  rw [Matrix.GeneralLinearGroup.coe_mul, gl2Weyl_val]
  simp [Matrix.mul_apply, Fin.sum_univ_two, h01]

theorem mem_borel_of_diag {γ : GL (Fin 2) L} (h10 : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    γ ∈ borelSubgroup L := h10

end Stabiliser

section Weight

variable (L : Type) [Field L] [NumberField L]

def jump (R : ℝ) (h : ℝ) : ℂ := if Real.exp R < h then 1 else 0

def wt (R : ℝ) (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < adelicHeight L y} (fun _ => (1 : ℂ)) y
    - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < adelicHeight L (adelicWeyl (𝓞 L) L * y)}
        (fun _ => (1 : ℂ)) y

theorem wt_eq (R : ℝ) (y : AdelicGL2 (𝓞 L) L) :
    wt L R y = 1 - jump R (adelicHeight L y) - jump R (adelicHeight L (adelicWeyl (𝓞 L) L * y)) := by
  unfold wt jump
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

theorem adelicWeyl_eq : adelicWeyl (𝓞 L) L = globalPoints (𝓞 L) L gl2Weyl := rfl

theorem wt_globalPoints_mul_of_diag_or_antidiag (R : ℝ) {γ : GL (Fin 2) L}
    (h : ((γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∨
      ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 1 1 = 0))
    (y : AdelicGL2 (𝓞 L) L) :
    wt L R (globalPoints (𝓞 L) L γ * y) = wt L R y := by
  rw [wt_eq, wt_eq, adelicWeyl_eq]
  rcases h with ⟨h10, h01⟩ | ⟨h00, h11⟩
  ·
    have e1 : adelicHeight L (globalPoints (𝓞 L) L γ * y) = adelicHeight L y :=
      adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (mem_borel_of_diag h10) y
    have e2 : adelicHeight L (globalPoints (𝓞 L) L gl2Weyl * (globalPoints (𝓞 L) L γ * y)) =
        adelicHeight L (globalPoints (𝓞 L) L gl2Weyl * y) := by
      have : globalPoints (𝓞 L) L gl2Weyl * (globalPoints (𝓞 L) L γ * y) =
          globalPoints (𝓞 L) L (gl2Weyl * γ * gl2Weyl⁻¹) * (globalPoints (𝓞 L) L gl2Weyl * y) := by
        simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (weyl_conj_mem_borel_of_diag h10 h01) _
    rw [e1, e2]
  ·
    have e1 : adelicHeight L (globalPoints (𝓞 L) L γ * y) = adelicHeight L (globalPoints (𝓞 L) L gl2Weyl * y) := by
      have : globalPoints (𝓞 L) L γ * y =
          globalPoints (𝓞 L) L (γ * gl2Weyl⁻¹) * (globalPoints (𝓞 L) L gl2Weyl * y) := by
        simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
      rw [this]
      exact adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (mul_weyl_inv_mem_borel_of_antidiag h11) _
    have e2 : adelicHeight L (globalPoints (𝓞 L) L gl2Weyl * (globalPoints (𝓞 L) L γ * y)) = adelicHeight L y := by
      rw [← mul_assoc, ← map_mul]
      exact adelicHeight_globalPoints_mul_of_mem_borelSubgroup L (weyl_mul_mem_borel_of_antidiag h00) _
    rw [e1, e2]
    ring

theorem wt_centralScalar_mul (R : ℝ) (a : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    wt L R (centralScalar (𝓞 L) L a * y) = wt L R y := by
  rw [wt_eq, wt_eq, mul_cs_left, adelicHeight_centralScalar_mul, adelicHeight_centralScalar_mul]

end Weight

section Reindex

variable {Γ G M : Type*} [Group Γ] [Group G] [AddCommMonoid M] [TopologicalSpace M]

theorem exists_equiv_of_cosetReps (Λ : Subgroup Γ) {ι : Type*} (r : ι → Γ)
    (hr : ∀ γ : Γ, ∃! i, (r i)⁻¹ * γ ∈ Λ) (g : Γ) :
    ∃ e : ι ≃ ι, ∀ i, (r i)⁻¹ * g * r (e i) ∈ Λ := by
  classical

  let P : Γ → ι → ι := fun g i => (hr (g * r i)).exists.choose
  have hP : ∀ g i, (r (P g i))⁻¹ * (g * r i) ∈ Λ := fun g i => (hr (g * r i)).exists.choose_spec
  have hPu : ∀ g i j, (r j)⁻¹ * (g * r i) ∈ Λ → j = P g i := fun g i j hj =>
    (hr (g * r i)).unique hj (hP g i)
  have hinv : ∀ g i, P g⁻¹ (P g i) = i := by
    intro g i
    symm
    apply hPu
    have h := Λ.inv_mem (hP g i)
    rw [mul_inv_rev, mul_inv_rev, inv_inv] at h
    simpa only [mul_assoc] using h
  have hleft : ∀ i, P g (P g⁻¹ i) = i := fun i => by
    have h := hinv g⁻¹ i
    rwa [inv_inv] at h
  refine ⟨⟨P g⁻¹, P g, hleft, hinv g⟩, fun i => ?_⟩
  have h := Λ.inv_mem (hP g⁻¹ i)
  rw [mul_inv_rev, mul_inv_rev, inv_inv, inv_inv] at h
  show (r i)⁻¹ * g * r (P g⁻¹ i) ∈ Λ
  exact h

theorem tsum_comp_inv_mul_eq (Λ : Subgroup Γ) {ι : Type*} (r : ι → Γ)
    (hr : ∀ γ : Γ, ∃! i, (r i)⁻¹ * γ ∈ Λ) (θ : Γ →* G) (F : G → M)
    (hF : ∀ l ∈ Λ, ∀ y : G, F (θ l * y) = F y) (g : Γ) (x : G) :
    ∑' i, F ((θ (r i))⁻¹ * (θ g * x)) = ∑' i, F ((θ (r i))⁻¹ * x) := by
  obtain ⟨e, he⟩ := exists_equiv_of_cosetReps Λ r hr g
  have hterm : ∀ i, F ((θ (r i))⁻¹ * (θ g * x)) = F ((θ (r (e i)))⁻¹ * x) := by
    intro i
    have h1 : (θ (r i))⁻¹ * (θ g * x) = θ ((r i)⁻¹ * g * r (e i)) * ((θ (r (e i)))⁻¹ * x) := by
      simp only [map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
    rw [h1, hF _ (he i)]
  simp_rw [hterm]
  exact e.tsum_eq (fun j => F ((θ (r j))⁻¹ * x))

end Reindex

end R1S9Vanish

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicHeight NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm
open scoped NNReal ENNReal Pointwise

namespace R1S9Vanish

section Slab

variable (L : Type) [Field L] [NumberField L]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

theorem borelSpace_adele : BorelSpace (AdeleRing (𝓞 L) L) := borelSpace_adeleBorel (𝓞 L) L

attribute [local instance] borelSpace_adele

theorem borelSpace_GL2 : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_glBorel (Fin 2) (𝓞 L) L

attribute [local instance] borelSpace_GL2

scoped instance isHaarMeasure_adelicGLHaar' : (adelicGLHaar (Fin 2) (𝓞 L) L).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 L) L

theorem countable_numberField : Countable L :=
  (Module.Free.chooseBasis ℚ L).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_GL2 : Countable (GL (Fin 2) L) := by
  haveI : Countable L := countable_numberField L
  haveI : Countable (Matrix (Fin 2) (Fin 2) L) := inferInstanceAs (Countable (Fin 2 → Fin 2 → L))
  exact Function.Injective.countable (f := (Units.val : GL (Fin 2) L → _)) Units.val_injective

def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 L) L) :=
  {g | ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

theorem measurableSet_slab (α β : ℝ) : MeasurableSet (slab L α β) :=
  measurableSet_preimage (NumberField.TateGlobal.continuous_ideleNorm_det L).measurable measurableSet_Icc

theorem ideleNorm_inv (z : (AdeleRing (𝓞 L) L)ˣ) :
    ideleNorm L z⁻¹ = (ideleNorm L z)⁻¹ := by
  unfold ideleNorm; rw [map_inv, NNReal.coe_inv]

theorem ideleNorm_det_globalPoints_mul (γ : GL (Fin 2) L) (g : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ * g)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem det_centralScalar (w : (AdeleRing (𝓞 L) L)ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L w) = w * w := by
  refine Units.ext ?_
  show Matrix.det (Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 L) L)) = (w : AdeleRing (𝓞 L) L) * w
  rw [Matrix.det_fin_two]
  simp [Matrix.scalar_apply]

theorem ideleNorm_det_centralScalar_mul {w : (AdeleRing (𝓞 L) L)ˣ} (hw : ideleNorm L w = 1) (g : AdelicGL2 (𝓞 L) L) :
    ideleNorm L (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L w * g)) =
      ideleNorm L (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, ideleNorm_mul, det_centralScalar, ideleNorm_mul, hw, one_mul, one_mul]

theorem smulInvariantMeasure_restrict (H : Subgroup (AdelicGL2 (𝓞 L) L)) (S : Set (AdelicGL2 (𝓞 L) L))
    (hinv : ∀ h ∈ H, ∀ x, h * x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure H (AdelicGL2 (𝓞 L) L) ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict S) := by
  refine ⟨fun h A hA => ?_⟩
  obtain ⟨h, hh⟩ := h
  show (adelicGLHaar (Fin 2) (𝓞 L) L).restrict S ((fun x => h * x) ⁻¹' A) =
    (adelicGLHaar (Fin 2) (𝓞 L) L).restrict S A
  rw [Measure.restrict_apply (measurableSet_preimage (measurable_const_mul h) hA), Measure.restrict_apply hA]
  have hset : (fun x => h * x) ⁻¹' A ∩ S = (fun x => h * x) ⁻¹' (A ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hinv h hh]
  rw [hset, measure_preimage_mul]

theorem smulInvariantMeasure_restrict_slab (α β : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine smulInvariantMeasure_restrict L _ _ fun h hh x => ?_
  obtain ⟨γ, rfl⟩ := hh
  show ideleNorm L (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 L) L γ * x)) ∈ Set.Icc α β ↔
    ideleNorm L (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
  rw [ideleNorm_det_globalPoints_mul]

def normOneCentre : Subgroup (AdelicGL2 (𝓞 L) L) := (normOneIdeles L).map (centralScalar (𝓞 L) L)

theorem smulInvariantMeasure_restrict_slab_centre (α β : ℝ) :
    SMulInvariantMeasure (normOneCentre L) (AdelicGL2 (𝓞 L) L)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict (slab L α β)) := by
  refine smulInvariantMeasure_restrict L _ _ fun h hh x => ?_
  obtain ⟨w, hw, rfl⟩ := hh
  show ideleNorm L (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L w * x)) ∈ Set.Icc α β ↔
    ideleNorm L (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β
  rw [ideleNorm_det_centralScalar_mul L ((mem_normOneIdeles_iff w).mp hw)]

scoped instance smulCommClass_centre :
    SMulCommClass (normOneCentre L) (globalPoints (𝓞 L) L).range (AdelicGL2 (𝓞 L) L) := by
  refine ⟨fun a b x => ?_⟩
  obtain ⟨_, ⟨w, -, rfl⟩⟩ := a
  obtain ⟨b, hb⟩ := b
  show centralScalar (𝓞 L) L w * (b * x) = b * (centralScalar (𝓞 L) L w * x)
  rw [mul_cs_left]

theorem countable_range_globalPoints : Countable (globalPoints (𝓞 L) L).range := by
  haveI := countable_GL2 L
  exact (MonoidHom.rangeRestrict_surjective (globalPoints (𝓞 L) L)).countable

end Slab

section Orbital

variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)

def Psi {mZ : MeasurableSpace (AdeleRing (𝓞 L) L)ˣ} (ν : Measure (AdeleRing (𝓞 L) L)ˣ)
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (δ₀ : GL (Fin 2) L)
    (y : AdelicGL2 (𝓞 L) L) : ℂ :=
  ∫ z, ((ξ z : ℂˣ) : ℂ) *
    φ (y⁻¹ * globalPoints (𝓞 L) L δ₀ * sigmaAdelicAct K L D σ (centralScalar (𝓞 L) L z * y)) ∂ν

variable {K L D σ}

theorem Psi_centralScalar_mul [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsMulLeftInvariant]
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (φ : AdelicGL2 (𝓞 L) L → ℂ) (δ₀ : GL (Fin 2) L)
    (a : (AdeleRing (𝓞 L) L)ˣ) (y : AdelicGL2 (𝓞 L) L) :
    Psi K L D σ ν ξ φ δ₀ (centralScalar (𝓞 L) L a * y) =
      ((ξ (D.unitsAct σ⁻¹ (a⁻¹ * D.unitsAct σ a)))⁻¹ : ℂˣ) * Psi K L D σ ν ξ φ δ₀ y := by
  unfold Psi
  refine AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
    K L D σ ν ξ φ (globalPoints (𝓞 L) L δ₀) (centralScalar (𝓞 L) L a) y (a⁻¹ * D.unitsAct σ a) ?_
  rw [sigmaAdelicAct_centralScalar, map_mul, ← map_inv,
    centralScalar_comm L a⁻¹ (globalPoints (𝓞 L) L δ₀), mul_assoc]

theorem Psi_globalPoints_mul_of_mem [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsMulLeftInvariant]
    (ξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hξt : ∀ q : Lˣ, ξ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (δ₀ : GL (Fin 2) L)
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {l : GL (Fin 2) L} (hl : l ∈ Λ) (y : AdelicGL2 (𝓞 L) L) :
    Psi K L D σ ν ξ φ δ₀ (globalPoints (𝓞 L) L l * y) = Psi K L D σ ν ξ φ δ₀ y := by

  have hl' := (hΛ l⁻¹).mp (Λ.inv_mem hl)
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hl'
  obtain ⟨t, ht⟩ := hl'
  have hmat : l⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) l =
      δ₀ * Matrix.GeneralLinearGroup.scalar (Fin 2) t := by
    have h := ht
    rw [map_inv, inv_inv, eq_comm, inv_mul_eq_iff_eq_mul] at h
    exact h
  set m : (AdeleRing (𝓞 L) L)ˣ := Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) t
    with hm
  have hg : (globalPoints (𝓞 L) L l)⁻¹ * globalPoints (𝓞 L) L δ₀ *
      sigmaAdelicAct K L D σ (globalPoints (𝓞 L) L l) =
      globalPoints (𝓞 L) L δ₀ * centralScalar (𝓞 L) L m := by
    rw [sigmaAdelicAct_globalPoints', ← map_inv, ← map_mul, ← map_mul, hmat, map_mul, hm,
      centralScalar_principal]
  have h := AutomorphicForm.integral_mul_apply_inv_mul_mul_sigmaAdelicAct_centralScalar_mul_eq_of_inv_mul_mul_sigmaAdelicAct_eq_mul_centralScalar
    K L D σ ν ξ φ (globalPoints (𝓞 L) L δ₀) (globalPoints (𝓞 L) L l) y m hg
  unfold Psi
  rw [h, hm, unitsAct_principal, hξt, inv_one, Units.val_one, one_mul]

end Orbital

end R1S9Vanish
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn.R1S9Vanish"

open R1S9Vanish
open NumberField.AdelicLevel
open scoped TensorProduct ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ¬ ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : AutomorphicForm.IsFactorizableTestFn L φ) :
    ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
      ∫ x in Φ₀, ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0 := by
  haveI : BorelSpace (AdelicGL2 (𝓞 L) L) := borelSpace_GL2 L
  haveI : FiniteDimensional K L := Module.Finite.of_restrictScalars_finite ℚ K L
  refine ⟨0, fun R _ => ?_⟩

  let ξ' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξL.comp (Subgroup.topEquiv (G := (AdeleRing (𝓞 L) L)ˣ)).symm.toMonoidHom
  have hξ' : ∀ z, ξ' z = ξL ⟨z, Subgroup.mem_top z⟩ := fun z => rfl
  have hξt' : ∀ q : Lˣ, ξ' (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L) q) = 1 :=
    fun q => hξt _ ⟨q, rfl⟩
  obtain ⟨a, ha1, hane⟩ : ∃ a : (AdeleRing (𝓞 L) L)ˣ, a ∈ normOneIdeles L ∧ ξ' (D.unitsAct σ⁻¹ a) ≠ ξ' a := by
    by_contra hcon
    push Not at hcon
    apply hξσ
    intro z
    have h := M4aHerbrand.IdeleGaloisDescent.apply_unitsAct_eq_of_forall_mem_normOneIdeles K L D σ⁻¹ ξ' hcon
      (D.unitsAct σ z)
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply] at h
    show ξ' (D.unitsAct σ z) = ξ' z
    exact h.symm
  have ha1' : ideleNorm L a = 1 := (mem_normOneIdeles_iff a).mp ha1
  set χ : ℂ := (((ξ' (D.unitsAct σ⁻¹ (a⁻¹ * D.unitsAct σ a)))⁻¹ : ℂˣ) : ℂ) with hχ
  have hχ1 : χ ≠ 1 := by
    intro h1
    apply hane
    have h2 : D.unitsAct σ⁻¹ (a⁻¹ * D.unitsAct σ a) = (D.unitsAct σ⁻¹ a)⁻¹ * a := by
      rw [map_mul, map_inv, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [hχ, h2, Units.val_eq_one, inv_eq_one, map_mul, map_inv, inv_mul_eq_one] at h1
    exact h1

  set μ := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set F : AdelicGL2 (𝓞 L) L → ℂ := fun y => wt L R y * Psi K L D σ νZL ξ' φ δ₀ y with hF
  set G : AdelicGL2 (𝓞 L) L → ℂ := fun x => ∑' i, F ((globalPoints (𝓞 L) L (r i))⁻¹ * x) with hG
  show ∫ x in Φ₀, G x ∂μ = 0

  have hFc : ∀ y, F (centralScalar (𝓞 L) L a * y) = χ * F y := by
    intro y
    simp only [hF, wt_centralScalar_mul, Psi_centralScalar_mul, hχ]
    ring
  have hFΛ : ∀ l ∈ Λ, ∀ y, F (globalPoints (𝓞 L) L l * y) = F y := by
    intro l hl y
    simp only [hF]
    rw [wt_globalPoints_mul_of_diag_or_antidiag L R
        (diag_or_antidiag_of_mem_stabiliser σ δ₀ hδ₀u hδ₀l hreg l ((hΛ l).mp hl)) y,
      Psi_globalPoints_mul_of_mem νZL ξ' hξt' φ δ₀ Λ hΛ hl y]
  have hGc : ∀ x, G (centralScalar (𝓞 L) L a * x) = χ * G x := by
    intro x
    simp only [hG]
    rw [← tsum_mul_left]
    refine tsum_congr fun i => ?_
    rw [mul_cs_left, hFc]
  have hGinv : ∀ (γ : GL (Fin 2) L) (x : AdelicGL2 (𝓞 L) L), G (globalPoints (𝓞 L) L γ * x) = G x := by
    intro γ x
    simp only [hG]
    exact tsum_comp_inv_mul_eq Λ r hr (globalPoints (𝓞 L) L) F hFΛ γ x

  have hJ1 : ∫ x in Φ₀, G x ∂μ = χ * ∫ x in (centralScalar (𝓞 L) L a)⁻¹ • Φ₀, G x ∂μ := by
    have h := (measurePreserving_mul_left μ (centralScalar (𝓞 L) L a)).setIntegral_preimage_emb
      (MeasurableEquiv.mulLeft (centralScalar (𝓞 L) L a)).measurableEmbedding G Φ₀
    have hpre : (fun x => centralScalar (𝓞 L) L a * x) ⁻¹' Φ₀ = (centralScalar (𝓞 L) L a)⁻¹ • Φ₀ :=
      Set.preimage_smul (centralScalar (𝓞 L) L a) Φ₀
    rw [← h, hpre]
    simp_rw [hGc]
    exact integral_const_mul _ _

  have hsub : (centralScalar (𝓞 L) L a)⁻¹ • Φ₀ ⊆ slab L α β := by
    rintro _ ⟨y, hy, rfl⟩
    show ideleNorm L (Matrix.GeneralLinearGroup.det ((centralScalar (𝓞 L) L a)⁻¹ * y)) ∈ Set.Icc α β
    rw [← map_inv, ideleNorm_det_centralScalar_mul L (by rw [ideleNorm_inv, ha1', inv_one])]
    exact hΦ₀s hy
  have hJ2 : ∫ x in (centralScalar (𝓞 L) L a)⁻¹ • Φ₀, G x ∂μ = ∫ x in Φ₀, G x ∂μ := by
    rw [← Measure.restrict_restrict_of_subset hsub, ← Measure.restrict_restrict_of_subset (μ := μ) hΦ₀s]
    change ∫ x in (centralScalar (𝓞 L) L a)⁻¹ • Φ₀, G x ∂(μ.restrict (slab L α β)) =
      ∫ x in Φ₀, G x ∂(μ.restrict (slab L α β))
    haveI := smulInvariantMeasure_restrict_slab L α β
    haveI := smulInvariantMeasure_restrict_slab_centre L α β
    haveI := countable_range_globalPoints L
    have hs : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀ (μ.restrict (slab L α β)) := hΦ₀
    have hmem : (centralScalar (𝓞 L) L a)⁻¹ ∈ normOneCentre L :=
      ⟨a⁻¹, (mem_normOneIdeles_iff _).mpr (by rw [ideleNorm_inv, ha1', inv_one]), map_inv _ _⟩
    have ht : IsFundamentalDomain (globalPoints (𝓞 L) L).range ((centralScalar (𝓞 L) L a)⁻¹ • Φ₀)
        (μ.restrict (slab L α β)) :=
      hs.smul_of_comm (G' := normOneCentre L) ⟨(centralScalar (𝓞 L) L a)⁻¹, hmem⟩
    symm
    refine hs.setIntegral_eq ht fun g x => ?_
    obtain ⟨_, ⟨γ, rfl⟩⟩ := g
    show G (globalPoints (𝓞 L) L γ * x) = G x
    exact hGinv γ x

  rw [hJ2] at hJ1
  have hzero : (1 - χ) * ∫ x in Φ₀, G x ∂μ = 0 := by rw [sub_mul, one_mul, ← hJ1, sub_self]
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd (sub_eq_zero.mp h).symm hχ1
  · exact h

end
end S_AutomorphicForm_exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_setIntegral_tsum_weight_mul_integral_eq_zero_of_not_sigmaInvariant_of_isFactorizableTestFn (solution)
