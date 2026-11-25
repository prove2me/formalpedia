-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T16:07:35.26415+00:00
-- url     : https://prove2.me/theorems/977c0dbd-d45f-425f-8a4d-93ba84b78699
-- title:
--   Haar Density Ne Zero
-- statement:
--   Definitions and structural lemmas for Haar Density Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/HaarDensityNeZero.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsOmegaLeb
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormLeSum
import Theorems.Thm_Formalism_UG_P_indefinite_unitary_compact
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_Chart_exists_density__3bdf3fbd8cf6
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ballU_lt_top_1e0ba7e20666
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_ballU_pos_9cb43a7a02ab
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_exists_omegaLeb_bcdf9b3adbe0
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_isOpen_ballU_9cf18b3e43f2
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_logA_exp_60d72a73aded
import Theorems.Thm_UpperTheory_Reformulated_B_Qk34_norm_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set Matrix Formalism.UG.P
open scoped ENNReal NNReal Matrix.Norms.Operator
variable (P Q : ℕ)
local notation "J" => Formalism.UG.Jpq P Q
instance : CompleteSpace (MM P Q) := FiniteDimensional.complete ℝ _
def matHom : UpqT P Q →* MM P Q where
  toFun := UpqT.mat
  map_one' := rfl
  map_mul' _ _ := rfl
theorem mat_mem (g : UpqT P Q) : (UpqT.mat g)ᴴ * J * UpqT.mat g = J := g.2
theorem mat_inducing : IsInducing (UpqT.mat : UpqT P Q → MM P Q) := by
  exact Units.isOpenEmbedding_val.toIsEmbedding.toIsInducing.comp Topology.IsInducing.subtypeVal
theorem mat_injective : Function.Injective (UpqT.mat : UpqT P Q → MM P Q) := fun a b h => Subtype.ext (Units.ext h)
theorem mat_embedding : IsEmbedding (UpqT.mat : UpqT P Q → MM P Q) := ⟨mat_inducing P Q, mat_injective P Q⟩
theorem exists_of_mem (h : MM P Q) (hh : hᴴ * J * h = J) : ∃ g : UpqT P Q, UpqT.mat g = h := by
  have hl : J * hᴴ * J * h = 1 := by
    calc J * hᴴ * J * h = J * (hᴴ * J * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh, J_sq]
  have hr : h * (J * hᴴ * J) = 1 := mul_eq_one_comm.mp hl
  exact ⟨⟨⟨h, J * hᴴ * J, hr, hl⟩, hh⟩, rfl⟩
theorem mat_range : Set.range (UpqT.mat : UpqT P Q → MM P Q) = {h | hᴴ * J * h = J} := by
  ext h
  constructor
  · rintro ⟨g, rfl⟩
    exact mat_mem P Q g
  · intro hh
    exact exists_of_mem P Q h hh
theorem mat_closedEmbedding : IsClosedEmbedding (UpqT.mat : UpqT P Q → MM P Q) := by
  refine ⟨mat_embedding P Q, ?_⟩
  rw [mat_range]
  exact isClosed_eq
    ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const
instance : LocallyCompactSpace (UpqT P Q) :=
  haveI : LocallyCompactSpace (MM P Q) :=
    inferInstanceAs (LocallyCompactSpace (Fin P ⊕ Fin Q → Fin P ⊕ Fin Q → ℂ))
  (mat_closedEmbedding P Q).locallyCompactSpace
instance (N : ℕ) : CompactSpace (UpqT N 0) :=
  isCompact_iff_compactSpace.mp (indefinite_unitary_compact N)
theorem exp_neg_mul' (X : MM P Q) : exp (-X) * exp X = 1 := by
  have h := NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl X))
  rw [neg_add_cancel, NormedSpace.exp_zero] at h
  exact h.symm
theorem exp_conjJ (A : MM P Q) : exp (J * A * J) = J * exp A * J := by
  let u : (MM P Q)ˣ := ⟨J, J, J_sq P Q, J_sq P Q⟩
  exact NormedSpace.exp_units_conj u A
theorem exp_mem (X : MM P Q) (hX : X ∈ lieU P Q) : (exp X)ᴴ * J * exp X = J := by
  have h1 : J * (-Xᴴ) * J = X := (mem_lieU_iff P Q X).1 hX
  have e : J * (J * (-Xᴴ) * J) * J = -Xᴴ := by
    rw [mul_assoc, mul_assoc (J * (-Xᴴ)), J_sq, mul_one, ← mul_assoc, J_sq, one_mul]
  have h2 : Xᴴ = J * (-X) * J := by
    rw [h1] at e
    rw [mul_neg, neg_mul, e, neg_neg]
  rw [← Matrix.exp_conjTranspose, h2, exp_conjJ]
  calc J * exp (-X) * J * J * exp X = J * (exp (-X) * (J * J) * exp X) := by
        simp only [mul_assoc]
    _ = J := by rw [J_sq, mul_one, exp_neg_mul', mul_one]
theorem exp_theta (Z : MM P Q) (hZ : (exp Z)ᴴ * J * exp Z = J) : exp (J * (-Zᴴ) * J) = exp Z := by
  have hc : (exp Z)ᴴ = exp Zᴴ := (Matrix.exp_conjTranspose Z).symm
  rw [hc] at hZ
  have h1 : J * exp Z = exp (-Zᴴ) * J := by
    calc J * exp Z = exp (-Zᴴ) * exp Zᴴ * J * exp Z := by rw [exp_neg_mul', one_mul]
      _ = exp (-Zᴴ) * (exp Zᴴ * J * exp Z) := by simp only [mul_assoc]
      _ = exp (-Zᴴ) * J := by rw [hZ]
  rw [exp_conjJ]
  calc J * exp (-Zᴴ) * J = J * (exp (-Zᴴ) * J) := by rw [mul_assoc]
    _ = J * (J * exp Z) := by rw [h1]
    _ = exp Z := by rw [← mul_assoc, J_sq, one_mul]
def chart : Chart (lieU P Q) (UpqT P Q) where
  mat := matHom P Q
  emb := mat_embedding P Q
  H1 := fun X => exists_of_mem P Q _ (exp_mem P Q X X.2)
  H2 := by
    have hθ : Continuous (fun Z : MM P Q => J * (-Zᴴ) * J) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
    have h0 : Tendsto (fun Z : MM P Q => J * (-Zᴴ) * J) (𝓝 0) (𝓝 0) := by
      have := hθ.tendsto 0
      simpa using this
    filter_upwards [logA_exp (𝔸 := MM P Q), h0.eventually (logA_exp (𝔸 := MM P Q))] with Z h1 h2
    rintro ⟨g, hg⟩
    have hm : (exp Z)ᴴ * J * exp Z = J := by
      have := mat_mem P Q g
      rw [show UpqT.mat g = exp Z from hg] at this
      exact this
    rw [mem_lieU_iff]
    calc J * (-Zᴴ) * J = logA (MM P Q) (exp (J * (-Zᴴ) * J)) := h2.symm
      _ = logA (MM P Q) (exp Z) := congrArg (logA (MM P Q)) (exp_theta P Q Z hm)
      _ = Z := h1
theorem norm_le_sum (X : MM P Q) : ‖X‖ ≤ ∑ i, ∑ j, ‖X i j‖ := by
  have hs : (Finset.univ.sup fun i => ∑ j, ‖X i j‖₊) ≤ ∑ i, ∑ j, ‖X i j‖₊ :=
    Finset.sup_le fun i _ =>
      Finset.single_le_sum (f := fun i => ∑ j, ‖X i j‖₊) (fun _ _ => zero_le) (Finset.mem_univ i)
  rw [Matrix.linfty_opNorm_def]
  refine (NNReal.coe_le_coe.mpr hs).trans (le_of_eq ?_)
  simp [NNReal.coe_sum]
theorem omegaDensity_haar (μ : Measure (UpqT P Q)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ OmegaDensity μ c := by
  obtain ⟨lam, hlam⟩ := exists_omegaLeb P Q
  have := hlam.1
  obtain ⟨c, hc0, hct, h⟩ := (chart P Q).exists_density' (finDimLie P Q) _ (instBorelLie P Q) _
    (instBorelU P Q) (instTopGroupU P Q) μ inferInstance lam hlam.1
  refine ⟨c, hc0, hct, lam, hlam, ?_⟩
  exact h (ballU P Q) (fun r => (isOpen_ballU P Q r).measurableSet)
    (fun δ hδ => by
      filter_upwards [Ioo_mem_nhdsGT hδ] with r hr X hX
      exact lt_of_le_of_lt (norm_le_sum P Q X) (lt_trans hX hr.2))
    (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ⟨(ballU_pos P Q lam hr).ne', (ballU_lt_top P Q lam r).ne⟩)
theorem omegaDensity_smul {μ : Measure (UpqT P Q)} {c : ℝ≥0∞} (h : OmegaDensity μ c) (t : ℝ≥0∞)
    (ht : t ≠ ⊤) : OmegaDensity (t • μ) (t * c) := by
  obtain ⟨lam, hl, hc⟩ := h
  refine ⟨lam, hl, ?_⟩
  refine (ENNReal.Tendsto.const_mul hc (Or.inr ht)).congr (fun r => ?_)
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
def mu0 : Measure (UpqT P Q) := Measure.haar
instance : (mu0 P Q).IsHaarMeasure := inferInstanceAs (Measure.haar.IsHaarMeasure)
def c0 : ℝ≥0∞ := (omegaDensity_haar P Q (mu0 P Q)).choose
theorem haar_density_ne_zero : c0 P Q ≠ 0 := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.1
theorem haar_density_ne_top : c0 P Q ≠ ⊤ := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.1
theorem haar_density_spec : OmegaDensity (mu0 P Q) (c0 P Q) := (omegaDensity_haar P Q (mu0 P Q)).choose_spec.2.2
def mass (N : ℕ) : ℝ≥0∞ := mu0 N 0 Set.univ
theorem mass_ne_zero (N : ℕ) : mass N ≠ 0 := isOpen_univ.measure_ne_zero (mu0 N 0) ⟨1, trivial⟩
theorem mass_ne_top (N : ℕ) : mass N ≠ ⊤ := (isCompact_univ.measure_lt_top (μ := mu0 N 0)).ne
def scale : ℝ≥0∞ := c0 (P + Q) 0 / (mass (P + Q) * c0 P Q)
theorem scale_ne_zero : scale P Q ≠ 0 := ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, ENNReal.mul_ne_top (mass_ne_top _) (haar_density_ne_top _ _)⟩
theorem scale_ne_top : scale P Q ≠ ⊤ := ENNReal.div_ne_top (haar_density_ne_top _ _) (mul_ne_zero (mass_ne_zero _) (haar_density_ne_zero _ _))
theorem scale_mul : scale P Q * c0 P Q = c0 (P + Q) 0 / mass (P + Q) := by
  unfold scale
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (haar_density_ne_top _ _)) (Or.inr (haar_density_ne_zero _ _)), mul_assoc, mul_assoc,
    ENNReal.inv_mul_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), mul_one]
theorem scale_mass (N : ℕ) : scale N 0 * mass N = 1 := by
  unfold scale
  rw [Nat.add_zero, div_eq_mul_inv, ENNReal.mul_inv (Or.inl (mass_ne_zero _)) (Or.inl (mass_ne_top _)),
    mul_comm (mass N)⁻¹, ← mul_assoc, ENNReal.mul_inv_cancel (haar_density_ne_zero _ _) (haar_density_ne_top _ _), one_mul,
    ENNReal.inv_mul_cancel (mass_ne_zero _) (mass_ne_top _)]
def cdHaar : CDHaar where
  cd := fun P Q => scale P Q • mu0 P Q
  haar := fun P Q => Measure.IsHaarMeasure.smul (mu0 P Q) (scale_ne_zero P Q) (scale_ne_top P Q)
  prob := fun N => ⟨by
    rw [Measure.smul_apply, smul_eq_mul]
    exact scale_mass N⟩
  trick := fun P Q => ⟨c0 (P + Q) 0 / mass (P + Q),
    ENNReal.div_ne_zero.mpr ⟨haar_density_ne_zero _ _, mass_ne_top _⟩,
    ENNReal.div_ne_top (haar_density_ne_top _ _) (mass_ne_zero _),
    by
      rw [← scale_mul P Q]
      exact omegaDensity_smul P Q (haar_density_spec P Q) _ (scale_ne_top P Q),
    by
      have h := omegaDensity_smul (P + Q) 0 (haar_density_spec (P + Q) 0) _ (scale_ne_top (P + Q) 0)
      rw [scale_mul (P + Q) 0] at h
      exact h⟩
end Formalism.BasicNotions.Examples₂.CD


