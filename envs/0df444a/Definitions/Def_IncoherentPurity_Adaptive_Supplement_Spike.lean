-- Prove2me | Definitions.Def_IncoherentPurity_Adaptive_Supplement_Spike
-- name    : IncoherentPurity_Adaptive_Supplement_Spike
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:04:56.921195+00:00
-- url     : https://prove2.me/theorems/e135dba7-578d-46ef-97b8-4a0f757c59ad
-- title:
--   Haar-spiked states, Born outcome laws and extended KL expectation
-- statement:
--   For a positive integer dimension $d$, a direction $v\in\mathbb C^d$ is a unit vector, represented by $\operatorname{tr}(|v\rangle\langle v|)=1$. The published Haar law on unitaries induces a probability measure on such directions through the first column; forgetting the normalization witness gives exactly the published pure-vector Haar law. For $0\le\theta\le1$, construct the density matrix
--
--   $$\rho_{\theta,v}=\frac{1-\theta}{d}I+\theta|v\rangle\langle v|.$$
--
--   Its positive semidefiniteness and unit trace are proved in the constructor. For a fixed POVM $M$ on any measurable outcome space, $p_{\theta,v}$ is its actual Born probability measure at this state. Define the Haar information as
--
--   $$\mathbb E_v\,D(p_{t,v}\Vert p_{s,v}).$$
--
--   Here $D$ is Mathlib's natural-log measure-theoretic KL divergence, valued in $[0,+\infty]$, and the expectation is a nonnegative extended Lebesgue integral. Failure of absolute continuity or integrability gives infinite divergence. This interface supplies the state family and information quantity used in Lemma 5.3 without imposing finite outcomes or full rank.
--
--   **Formalization Note** The constructor also permits the pure endpoint $\theta=1$; the information theorem retains the source's strict $s,t<1$. Structural helpers certify measurable maps and probability laws.
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), preprint, pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce; Section 5, PDF p.16 = printed p.16, Eqs. (5.4)–(5.10); Definition 2.1, PDF p.8 = printed p.8

import Definitions.Def_IncoherentPurity_Adaptive_Estimators

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive.Supplement

/-- Unit vectors: the trace of the rank-one outer product is the squared Euclidean norm. -/
abbrev Direction (d : ℕ) := {v : Fin d → ℂ // (outer v).trace = 1}

/-- The same first-column map used in the published `pureHaar`, with its unit-vector witness. -/
def haarDirection {d : ℕ} (hd : 0 < d) (U : Unitary d) : Direction d := by
  refine ⟨fun i => U.val i ⟨0, hd⟩, ?_⟩
  have h := congrArg (fun A : Op d => A ⟨0, hd⟩ ⟨0, hd⟩)
    (Matrix.UnitaryGroup.star_mul_self U)
  simpa [outer, Matrix.trace, Matrix.diag, Matrix.mul_apply, mul_comm] using h

lemma measurable_haarDirection {d : ℕ} (hd : 0 < d) : Measurable (haarDirection hd) := by
  apply Continuous.measurable
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply _).comp
    ((continuous_apply i).comp continuous_subtype_val))

/-- Normalized complex Haar law on unit vectors; its underlying vector law is `pureHaar H`. -/
def directionHaar {d : ℕ} (hd : 0 < d) (H : HaarBasis d) : Measure (Direction d) :=
  H.law.map (haarDirection hd)

instance directionHaar_probability {d : ℕ} (hd : 0 < d) (H : HaarBasis d) :
    IsProbabilityMeasure (directionHaar hd H) := by
  let := H.probability
  exact Measure.isProbabilityMeasure_map (measurable_haarDirection hd).aemeasurable

lemma directionHaar_map_val {d : ℕ} (hd : 0 < d) (H : HaarBasis d) :
    (directionHaar hd H).map Subtype.val = pureHaar H := by
  rw [directionHaar, Measure.map_map measurable_subtype_coe (measurable_haarDirection hd)]
  simp [pureHaar, hd, Function.comp_def, haarDirection]

/-- The actual spiked density matrix (5.4), including positivity and trace-one witnesses.
The closed parameter interval also permits the pure endpoint without any full-rank assumption. -/
def spikeState {d : ℕ} (hd : 0 < d) (θ : Set.Icc (0 : ℝ) 1) (v : Direction d) : State d := by
  refine ⟨((1 - θ.val) / (d : ℝ)) • (1 : Op d) + θ.val • outer v.val, ?_, ?_⟩
  · exact (Matrix.PosSemidef.one.smul (div_nonneg (sub_nonneg.mpr θ.property.2)
      (Nat.cast_nonneg d))).add
      ((Matrix.posSemidef_vecMulVec_self_star v.val).smul θ.property.1)
  · have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      v.property]
    simp only [Algebra.smul_def]
    push_cast
    field_simp
    ring

lemma continuous_spikeState {d : ℕ} (hd : 0 < d) (θ : Set.Icc (0 : ℝ) 1) :
    Continuous (spikeState hd θ) := by
  apply Continuous.subtype_mk
  change Continuous (fun v : Direction d =>
    ((1 - θ.val) / (d : ℝ)) • (1 : Op d) + θ.val • outer v.val)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun v : Direction d =>
    ((1 - θ.val) / (d : ℝ)) • (1 : Op d) i j + θ.val • (v.val i * star (v.val j)))
  exact continuous_const.add
    ((((continuous_apply i).comp continuous_subtype_val).mul
      (((continuous_apply j).comp continuous_subtype_val).star)).const_smul θ.val)

/-- Actual Born outcome law of a fixed POVM on the constructed spike state. -/
def spikeOutcome {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω]
    (M : POVM d Ω) (θ : Set.Icc (0 : ℝ) 1) (v : Direction d) : Measure Ω :=
  M.born (spikeState hd θ v)

lemma measurable_spikeOutcome {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω]
    (M : POVM d Ω) (θ : Set.Icc (0 : ℝ) 1) : Measurable (spikeOutcome hd M θ) :=
  M.born.measurable.comp (continuous_spikeState hd θ).measurable

instance spikeOutcome_probability {d : ℕ} (hd : 0 < d) {Ω : Type*} [MeasurableSpace Ω]
    (M : POVM d Ω) (θ : Set.Icc (0 : ℝ) 1) (v : Direction d) :
    IsProbabilityMeasure (spikeOutcome hd M θ v) := by
  let := M.markov
  exact inferInstanceAs (IsProbabilityMeasure (M.born (spikeState hd θ v)))

/-- Natural-log KL, with value infinity on failure of absolute continuity or integrability,
and its extended nonnegative Haar expectation. No real totalized expectation is used. -/
def haarInformation {d : ℕ} (hd : 0 < d) (H : HaarBasis d)
    {Ω : Type*} [MeasurableSpace Ω] (M : POVM d Ω)
    (s t : Set.Icc (0 : ℝ) 1) : ℝ≥0∞ :=
  ∫⁻ v, InformationTheory.klDiv (spikeOutcome hd M t v) (spikeOutcome hd M s v)
    ∂directionHaar hd H

end IncoherentPurity.Adaptive.Supplement


