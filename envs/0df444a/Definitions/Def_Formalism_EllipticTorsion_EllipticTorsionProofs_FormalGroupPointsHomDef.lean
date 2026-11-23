-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
-- name    : Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:28.003822+00:00
-- url     : https://prove2.me/theorems/fb9256f4-4a9e-4059-94e2-80d7eddbee01
-- title:
--   Formal Group Points Hom Def
-- statement:
--   Definitions and structural lemmas for Formal Group Points Hom Def, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/FormalGroupPointsHomDef.lean

import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsParametrisation
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL.FormalGroupPointsHom
open Formalism.ELL Formalism.G
section Analysis
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
theorem summable_of_bound {ι : Type*} {f : ι → K} (deg : ι → ℕ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < 1) (hfin : ∀ N : ℕ, {i | f i ≠ 0 ∧ deg i < N}.Finite)
    (h : ∀ i, ‖f i‖ ≤ r ^ deg i) : Summable f := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr
  refine Filter.eventually_cofinite.2 ((hfin N).subset ?_)
  intro i hi
  simp only [Set.mem_ofPred_eq, dist_zero_right, not_lt] at hi ⊢
  refine ⟨fun h0 => by rw [h0, norm_zero] at hi; linarith, ?_⟩
  by_contra hge
  push Not at hge
  have h1 := h i
  have h2 : r ^ deg i ≤ r ^ N := pow_le_pow_of_le_one hr0 hr.le hge
  linarith
theorem degree_fin_two_eq_add_of_ne (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
theorem finite_degree_lt (N : ℕ) : {d : Fin 2 →₀ ℕ | d.degree < N}.Finite := by
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun _ => N)).subset ?_
  intro d hd
  simp only [Set.mem_ofPred_eq, degree_fin_two_eq_add_of_ne] at hd
  simp only [Set.mem_Iic, Finsupp.le_def]
  intro i; fin_cases i <;> simp <;> omega
theorem norm_mono_le {a b : K} {r : ℝ} (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (d : Fin 2 →₀ ℕ) :
    ‖a ^ (d 0) * b ^ (d 1)‖ ≤ r ^ d.degree := by
  rw [degree_fin_two_eq_add_of_ne, pow_add, norm_mul, norm_pow, norm_pow]
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha _) (pow_le_pow_left₀ (norm_nonneg _) hb _)
    (pow_nonneg (norm_nonneg _) _) (pow_nonneg hr _)
def term (F : MvPowerSeries (Fin 2) K) (a b : K) (d : Fin 2 →₀ ℕ) : K :=
  MvPowerSeries.coeff d F * (a ^ (d 0) * b ^ (d 1))
theorem evalMv2_eq (F : MvPowerSeries (Fin 2) K) (a b : K) :
    evalMv2 F a b = ∑' d, term F a b d := by
  unfold evalMv2 term; congr 1; funext d; ring
theorem norm_term_le {F : MvPowerSeries (Fin 2) K} (hF : IntegralMv F) {a b : K} {r : ℝ}
    (ha : ‖a‖ ≤ r) (hb : ‖b‖ ≤ r) (d : Fin 2 →₀ ℕ) : ‖term F a b d‖ ≤ r ^ d.degree := by
  unfold term
  rw [norm_mul]
  have hr : 0 ≤ r := (norm_nonneg a).trans ha
  calc ‖MvPowerSeries.coeff d F‖ * ‖a ^ (d 0) * b ^ (d 1)‖ ≤ 1 * r ^ d.degree :=
        mul_le_mul (hF d) (norm_mono_le ha hb d) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _
theorem summable_term {F : MvPowerSeries (Fin 2) K} (hF : IntegralMv F) {a b : K}
    (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : Summable (term F a b) :=
  summable_of_bound Finsupp.degree (le_trans (norm_nonneg a) (le_max_left _ _))
    (max_lt ha hb) (fun N => (finite_degree_lt N).subset fun d hd => hd.2)
    (norm_term_le hF (le_max_left _ _) (le_max_right _ _))
def IL (K : Type u) [NormedField K] [IsUltrametricDist K] : Subring (MvPowerSeries (Fin 2) K) where
  carrier := {F | IntegralMv F}
  mul_mem' hF hG := SubstitutionCoefficientCongruence.integral_mul hF hG
  one_mem' := SubstitutionCoefficientCongruence.integral_one
  add_mem' {F G} hF hG := fun d => by
    rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hF d) (hG d))
  zero_mem' := fun d => by simp
  neg_mem' {F} hF := fun d => by rw [map_neg, norm_neg]; exact hF d
theorem summable_prod_term {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    Summable fun x : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) => term F a b x.1 * term G a b x.2 := by
  have hr0 : 0 ≤ max ‖a‖ ‖b‖ := le_trans (norm_nonneg a) (le_max_left _ _)
  refine summable_of_bound (fun x => x.1.degree + x.2.degree) hr0 (max_lt ha hb) ?_ ?_
  · intro N
    refine ((finite_degree_lt N).prod (finite_degree_lt N)).subset ?_
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_prod, Set.mem_ofPred_eq]
    omega
  · intro x
    rw [norm_mul, pow_add]
    exact mul_le_mul (norm_term_le hF (le_max_left _ _) (le_max_right _ _) _)
      (norm_term_le hG (le_max_left _ _) (le_max_right _ _) _) (norm_nonneg _)
      (pow_nonneg hr0 _)
theorem evalMv2_one (a b : K) : evalMv2 (1 : MvPowerSeries (Fin 2) K) a b = 1 := by
  classical
  rw [evalMv2_eq, tsum_eq_single 0]
  · simp [term]
  · intro d hd
    simp [term, MvPowerSeries.coeff_one, hd]
theorem evalMv2_mul {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (F * G) a b = evalMv2 F a b * evalMv2 G a b := by
  classical
  rw [evalMv2_eq, evalMv2_eq, evalMv2_eq,
    (summable_term hF ha hb).tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_term hG ha hb)
      (summable_prod_term hF hG ha hb)]
  congr 1; funext n
  unfold term
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← hkl]
  simp only [Finsupp.add_apply, pow_add]
  ring
theorem evalMv2_add {F G : MvPowerSeries (Fin 2) K} (hF : IntegralMv F)
    (hG : IntegralMv G) {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) :
    evalMv2 (F + G) a b = evalMv2 F a b + evalMv2 G a b := by
  rw [evalMv2_eq, evalMv2_eq, evalMv2_eq,
    ← (summable_term hF ha hb).tsum_add (summable_term hG ha hb)]
  congr 1; funext d
  simp [term, add_mul]
def ev (a b : K) (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : IL K →+* K where
  toFun F := evalMv2 F.1 a b
  map_one' := evalMv2_one a b
  map_mul' F G := evalMv2_mul F.2 G.2 ha hb
  map_zero' := by simp [evalMv2]
  map_add' F G := evalMv2_add F.2 G.2 ha hb
end Analysis
def chordPX {R : Type*} [CommRing R] (a1 a2 z1 z2 w1 w2 c v : R) : R :=
  c * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2 - v * ((w1 - w2) ^ 2 * w1 * w2
    + a1 * (w1 - w2) * (z1 * w2 - z2 * w1) * w1 * w2 - a2 * (z1 * w2 - z2 * w1) ^ 2 * w1 * w2
    - z1 * (z1 * w2 - z2 * w1) ^ 2 * w2 - z2 * (z1 * w2 - z2 * w1) ^ 2 * w1)
def chordPY {R : Type*} [CommRing R] (a1 a3 z1 z2 w1 w2 c v : R) : R :=
  (z1 * w2 - z2 * w1) * w1 - (w1 - w2) * (c * w1 - z1 * v) + (z1 * w2 - z2 * w1) * v
    - a1 * c * (z1 * w2 - z2 * w1) * w1 - a3 * v * (z1 * w2 - z2 * w1) * w1
def tanPX {R : Type*} [CommRing R] (a1 a2 a3 a4 z w c v : R) : R :=
  c * w ^ 2 * (-2 + a1 * z + a3 * w) ^ 2 - v * ((3 * z ^ 2 + 2 * a2 * z * w + a4 * w ^ 2 + a1 * w) ^ 2
    + a1 * (3 * z ^ 2 + 2 * a2 * z * w + a4 * w ^ 2 + a1 * w) * w * (-2 + a1 * z + a3 * w)
    - a2 * w ^ 2 * (-2 + a1 * z + a3 * w) ^ 2 - 2 * z * w * (-2 + a1 * z + a3 * w) ^ 2)
def tanPY {R : Type*} [CommRing R] (a1 a2 a3 a4 z w c v : R) : R :=
  w ^ 2 * (-2 + a1 * z + a3 * w) - (3 * z ^ 2 + 2 * a2 * z * w + a4 * w ^ 2 + a1 * w) * (c * w - z * v)
    + v * w * (-2 + a1 * z + a3 * w) - a1 * c * w ^ 2 * (-2 + a1 * z + a3 * w)
    - a3 * v * w ^ 2 * (-2 + a1 * z + a3 * w)
section Field
variable {E : Type*} [Field E] (W : WeierstrassCurve.Affine E)
end Field
def mP {R : Type*} [CommRing R] (a1 a3 z w : R) : R := -2 + a1 * z + a3 * w
def weqP {R : Type*} [CommRing R] (a1 a2 a3 a4 a6 s v : R) : R :=
  v - (s ^ 3 + a1 * (s * v) + a2 * (s ^ 2 * v) + a3 * v ^ 2 + a4 * (s * v ^ 2) + a6 * v ^ 3)
section Maps
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
end Maps
section Formal
variable {K : Type u} [Field K]
end Formal
section Main
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
end Main
section Cases
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
end Cases
section MainLemma
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
end MainLemma
end Formalism.ELL.FormalGroupPointsHom


