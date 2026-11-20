-- Prove2me | Definitions.Def_Kyprianou_Ch10_Core05
-- name    : Kyprianou_Ch10_Core05
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:38:37.102805+00:00
-- url     : https://prove2.me/theorems/e19f1675-aa04-499b-ba69-5ba2d5535066
-- title:
--   Kyprianou Ch10 original model source, bounded segment 5/7
-- statement:
--   Dependency-closed Chapter 10 original Lean source segment 5 of 7. Theorem 10.10 is represented by its source-faithful canonical independent product-exponential-clock conditional limit, replacing the former extra existential tilted-law construction. Other helper declarations and source-parent theorem obligations are preserved and remain Open.

import Definitions.Def_Kyprianou_Ch10_Core04
open Filter Set ProbabilityTheory MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch10.StageD1Certificates
def certExercise10_1 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (c : Time) (rate : Time) (F : Measure Time),
      Kyprianou.Ch10.StageDExercises.exercise10_1_source_type Y T c rate F

def certExercise10_2 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDExercises.exercise10_2_source_type X T

def certExercise10_3 : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDExercises.exercise10_3_source_type Y T rho

/-- Full chapter parent assertion with all sixteen source obligations.
This is an UNPROVED source Prop, not a theorem certificate. -/
def chapterTenMainResults : Prop :=
  certTheorem10_1 ∧
  certTheorem10_2 ∧
  certTheorem10_3 ∧
  certTheorem10_5 ∧
  certCorollary10_6 ∧
  certTheorem10_7 ∧
  certCorollary10_8 ∧
  certCorollary10_9 ∧
  certTheorem10_10 ∧
  certLemma10_11 ∧
  certTheorem10_12 ∧
  certLemma10_13 ∧
  certLemma10_14 ∧
  certExercise10_1 ∧
  certExercise10_2 ∧
  certExercise10_3

theorem chapterTenMain_implies_certTheorem10_1 (h : chapterTenMainResults) :
    certTheorem10_1 := by
  exact h.1

theorem chapterTenMain_implies_certTheorem10_2 (h : chapterTenMainResults) :
    certTheorem10_2 := by
  exact h.2.1

theorem chapterTenMain_implies_certTheorem10_3 (h : chapterTenMainResults) :
    certTheorem10_3 := by
  exact h.2.2.1

theorem chapterTenMain_implies_certTheorem10_5 (h : chapterTenMainResults) :
    certTheorem10_5 := by
  exact h.2.2.2.1

theorem chapterTenMain_implies_certCorollary10_6 (h : chapterTenMainResults) :
    certCorollary10_6 := by
  exact h.2.2.2.2.1

theorem chapterTenMain_implies_certTheorem10_7 (h : chapterTenMainResults) :
    certTheorem10_7 := by
  exact h.2.2.2.2.2.1

theorem chapterTenMain_implies_certCorollary10_8 (h : chapterTenMainResults) :
    certCorollary10_8 := by
  exact h.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certCorollary10_9 (h : chapterTenMainResults) :
    certCorollary10_9 := by
  exact h.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certTheorem10_10 (h : chapterTenMainResults) :
    certTheorem10_10 := by
  exact h.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certLemma10_11 (h : chapterTenMainResults) :
    certLemma10_11 := by
  exact h.2.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certTheorem10_12 (h : chapterTenMainResults) :
    certTheorem10_12 := by
  exact h.2.2.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certLemma10_13 (h : chapterTenMainResults) :
    certLemma10_13 := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certLemma10_14 (h : chapterTenMainResults) :
    certLemma10_14 := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certExercise10_1 (h : chapterTenMainResults) :
    certExercise10_1 := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certExercise10_2 (h : chapterTenMainResults) :
    certExercise10_2 := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem chapterTenMain_implies_certExercise10_3 (h : chapterTenMainResults) :
    certExercise10_3 := by
  exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

def certExercise10_1_i : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (c : Time) (rate : Time) (F : Measure Time),
      Kyprianou.Ch10.StageDExercises.exercise10_1_part_i Y T c rate F

def certExercise10_1_ii : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (c : Time) (rate : Time) (F : Measure Time),
      Kyprianou.Ch10.StageDExercises.exercise10_1_part_ii Y T c rate F

def certExercise10_2_i : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDExercises.exercise10_2_part_i X T

def certExercise10_2_ii : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDExercises.exercise10_2_part_ii X T

def certExercise10_2_iii : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Kyprianou.Ch10.StageDExercises.exercise10_2_part_iii X T

def certExercise10_3_i : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDExercises.exercise10_3_part_i Y T rho

def certExercise10_3_ii : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDExercises.exercise10_3_part_ii Y T rho

def certExercise10_3_iii : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDExercises.exercise10_3_part_iii Y T rho

def certExercise10_3_iv : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (Y : CSBPRaw Ω) (T : Mechanism.Parameters) (rho : ℝ),
      Kyprianou.Ch10.StageDExercises.exercise10_3_part_iv Y T rho

end Kyprianou.Ch10.StageD1Certificates

/- Stage E source-semantic bridge: zero-parameter progeny is a finite-event
indicator. All antecedents are definitional; no book result is assumed. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageD

theorem zeroLaplace_one_iff_finite (m : Mass) :
    extendedProgenyLaplace 0 m = 1 ↔ m ≠ ⊤ := by
  by_cases h : m = ⊤
  · simp [extendedProgenyLaplace, h]
  · simp [extendedProgenyLaplace, h]

theorem zeroLaplace_zero_iff_infinite (m : Mass) :
    extendedProgenyLaplace 0 m = 0 ↔ m = ⊤ := by
  by_cases h : m = ⊤
  · simp [extendedProgenyLaplace, h]
  · simp [extendedProgenyLaplace, h]

theorem zeroDiscount_one_iff_finite {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (ω : Ω) (τ : Mass) :
    discountedUntil Y 0 ω τ = 1 ↔ progenyUntil Y ω τ ≠ ⊤ := by
  simpa only [discountedUntil] using
    (zeroLaplace_one_iff_finite (progenyUntil Y ω τ))

end Kyprianou.Ch10.StageD

/- The zero-discount transform integrates to the finite-progeny probability.
This is a measure-level result, conditional only on event measurability. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageD

theorem zeroDiscount_lintegral_eq_finite_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : CSBPRaw Ω) (x : Time) (τ : Mass)
    (hMeas : MeasurableSet {ω : Ω | progenyUntil Y ω τ ≠ ⊤}) :
    (∫⁻ ω, discountedUntil Y 0 ω τ ∂ Y.law x) =
      Y.law x {ω | progenyUntil Y ω τ ≠ ⊤} := by
  let S : Set Ω := {ω | progenyUntil Y ω τ ≠ ⊤}
  have hS : MeasurableSet S := hMeas
  have heq (ω : Ω) :
      discountedUntil Y 0 ω τ = S.indicator (fun _ => (1 : Mass)) ω := by
    by_cases h : ω ∈ S
    · have hfinite : progenyUntil Y ω τ ≠ ⊤ := h
      rw [discountedUntil_zero_finite Y ω τ hfinite]
      simp [Set.indicator, h]
    · have hinf : progenyUntil Y ω τ = ⊤ := not_ne_iff.mp h
      rw [discountedUntil_zero_infinite Y ω τ hinf]
      simp [Set.indicator, h]
  calc
    (∫⁻ ω, discountedUntil Y 0 ω τ ∂ Y.law x) =
        ∫⁻ ω, S.indicator (fun _ => (1 : Mass)) ω ∂ Y.law x :=
          lintegral_congr heq
    _ = Y.law x S := by
      rw [lintegral_indicator hS]
      simp

end Kyprianou.Ch10.StageD


/- Stage E1 isolated noncanonical conditioning correction.
The product marginal is proved; the full limit is an OPEN proposition. -/
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch10.StageE1

abbrev Time := Kyprianou.Ch10.Time
abbrev Mass := Kyprianou.Ch10.Mass

/-- An independent exponential coordinate can be added while exactly
preserving the original probability law on the first coordinate. -/
theorem exponential_product_law_preserves_original
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ P : Measure (Ω × ℝ),
      IsProbabilityMeasure P ∧
      P.map (Prod.fst : Ω × ℝ → Ω) = μ := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  refine ⟨μ.prod (ProbabilityTheory.expMeasure 1), inferInstance, ?_⟩
  simp

/-- The source numerator requires t < e_q; its conditioning denominator
contains only tau_0^- > e_q, with positive survival probability. -/
noncomputable def correctedConditional {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (μ : Measure Ω)
    (kill : Ω → Mass) (t : Time) (A : Set Ω) : Mass :=
  StageDConditioning.conditional μ
    (A ∩ {ω | (t : Mass) < kill ω})
    {ω | Levy.firstStrictNegative X.path ω > kill ω}


/-- A clock constructed measurably from the new exponential coordinate
is independent of the entire source process path under the product law. -/
theorem coordinate_clock_independent_of_full_path
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (clock : ℝ → Mass) (hclock : Measurable clock) :
    Indep
      (MeasurableSpace.comap
        (fun p : Ω × ℝ => clock p.2) inferInstance)
      (MeasurableSpace.comap
        (fun p : Ω × ℝ => fun t : Time => X.path t p.1) inferInstance)
      (μ.prod ν) := by
  have hpath : Measurable (fun ω : Ω => fun t : Time => X.path t ω) :=
    measurable_pi_lambda _ (fun t => X.coordinate_measurable t)
  exact (indepFun_prod hpath hclock).symm

/-- An explicit probability-space extension preserving the source law
and making any measurable coordinate clock independent of the full path. -/
theorem exponential_coordinate_extension_with_independence
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (clock : ℝ → Mass) (hclock : Measurable clock) :
    ∃ P : Measure (Ω × ℝ),
      IsProbabilityMeasure P ∧
      P.map (Prod.fst : Ω × ℝ → Ω) = μ ∧
      Indep
        (MeasurableSpace.comap
          (fun p : Ω × ℝ => clock p.2) inferInstance)
        (MeasurableSpace.comap
          (fun p : Ω × ℝ => fun t : Time => X.path t p.1) inferInstance)
        P := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  refine ⟨μ.prod (ProbabilityTheory.expMeasure 1), inferInstance, ?_, ?_⟩
  · simp
  · exact coordinate_clock_independent_of_full_path X μ
      (ProbabilityTheory.expMeasure 1) clock hclock

end Kyprianou.Ch10.StageE1


/- A single law-preserving lifted process family, rather than just
pointwise existence of a product marginal measure. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

noncomputable def liftPositiveJumpPaths {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) :
    Levy.PositiveJumpPaths (Ω × ℝ) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  refine {
    path := fun t p => X.path t p.1
    leftLimit := fun t p => X.leftLimit t p.1
    law := fun x => (X.law x).prod (ProbabilityTheory.expMeasure 1)
    probability := ?_
    coordinate_measurable := ?_
    initial := ?_
    left_limit_correct := ?_
    no_negative_jump := ?_
  }
  · intro x
    letI : IsProbabilityMeasure (X.law x) := X.probability x
    infer_instance
  · intro t
    exact (X.coordinate_measurable t).comp measurable_fst
  · intro x
    letI : IsProbabilityMeasure (X.law x) := X.probability x
    let S : Set Ω := {ω | X.path 0 ω = x}
    have hS : MeasurableSet S :=
      (measurableSet_singleton x).preimage (X.coordinate_measurable 0)
    change ((X.law x).prod (ProbabilityTheory.expMeasure 1))
      ((Prod.fst : Ω × ℝ → Ω) ⁻¹' S) = 1
    rw [← Measure.map_apply measurable_fst hS]
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    exact X.initial x
  · intro p t ht
    exact X.left_limit_correct p.1 t ht
  · intro p t ht
    exact X.no_negative_jump p.1 t ht

/-- The SAME lifted process preserves each original starting-mass law. -/
theorem liftPositiveJumpPaths_law_preserving
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (y : ℝ) :
    (liftPositiveJumpPaths X).law y =
      (X.law y).prod (ProbabilityTheory.expMeasure 1) ∧
    ((liftPositiveJumpPaths X).law y).map
      (Prod.fst : Ω × ℝ → Ω) = X.law y := by
  constructor
  · rfl
  · letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
    change ((X.law y).prod (ProbabilityTheory.expMeasure 1)).map
      (Prod.fst : Ω × ℝ → Ω) = X.law y
    simp

/-- The path and left-limit coordinates of the lifted process are exact copies. -/
theorem liftPositiveJumpPaths_path_preserving
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω)
    (p : Ω × ℝ) (t : Kyprianou.Ch10.Time) :
    (liftPositiveJumpPaths X).path t p = X.path t p.1 ∧
    (liftPositiveJumpPaths X).leftLimit t p = X.leftLimit t p.1 := by
  exact ⟨rfl, rfl⟩

end Kyprianou.Ch10.StageE1


/- Rate-one exponential survival on the new coordinate. This step
does not establish the q-dependent family. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem rateOneExp_measure_survival (t : Kyprianou.Ch10.Time) :
    ProbabilityTheory.expMeasure 1 (Set.Ioi (t : ℝ)) =
      ENNReal.ofReal (Real.exp (-(t : ℝ))) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have ht : (0 : ℝ) ≤ (t : ℝ) := t.property
  have he : 0 ≤ Real.exp (-(t : ℝ)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(t : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have hCDF : ProbabilityTheory.expMeasure 1 (Set.Iic (t : ℝ)) =
      ENNReal.ofReal (1 - Real.exp (-(t : ℝ))) := by
    rw [← ProbabilityTheory.ofReal_cdf (ProbabilityTheory.expMeasure 1) (t : ℝ)]
    rw [ProbabilityTheory.cdf_expMeasure_eq (by norm_num)]
    simp [ht]
  calc
    ProbabilityTheory.expMeasure 1 (Set.Ioi (t : ℝ)) =
        1 - ProbabilityTheory.expMeasure 1 (Set.Iic (t : ℝ)) := by
          rw [← Set.compl_Iic]
          rw [measure_compl (μ := ProbabilityTheory.expMeasure 1)
            measurableSet_Iic (measure_ne_top _ _)]
          simp
    _ = 1 - ENNReal.ofReal (1 - Real.exp (-(t : ℝ))) := by rw [hCDF]
    _ = ENNReal.ofReal (Real.exp (-(t : ℝ))) := by
      calc
        (1 : ENNReal) - ENNReal.ofReal (1 - Real.exp (-(t : ℝ))) =
            ENNReal.ofReal ((1 : ℝ) - (1 - Real.exp (-(t : ℝ)))) := by
              rw [ENNReal.ofReal_sub (1 : ℝ) (sub_nonneg.mpr he1)]
              simp
        _ = ENNReal.ofReal (Real.exp (-(t : ℝ))) := by ring

end Kyprianou.Ch10.StageE1


/- A single Exp(1) coordinate is sufficient for a measurable family of
Exp(q) killing times on the same enlarged probability space for q>0. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

noncomputable def expClockReal (q : Time) (r : ℝ) : Mass :=
  if q = 0 then ⊤ else ENNReal.ofReal (r / (q : ℝ))

noncomputable def expClock {Ω : Type*} (q : Time) (p : Ω × ℝ) : Mass :=
  expClockReal q p.2

theorem expClockReal_measurable (q : Time) :
    Measurable (expClockReal q) := by
  classical
  unfold expClockReal
  split_ifs with hq
  · exact measurable_const
  · exact (measurable_id.div_const (q : ℝ)).ennreal_ofReal

theorem expClock_event_iff {Ω : Type*}
    (q t : Time) (hq : 0 < q) (p : Ω × ℝ) :
    (t : Mass) < expClock q p ↔
      (t : ℝ) * (q : ℝ) < p.2 := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  simp only [expClock, expClockReal, if_neg (ne_of_gt hq)]
  rw [ENNReal.coe_lt_ofReal]
  exact lt_div_iff₀ hqr

end Kyprianou.Ch10.StageE1

namespace Kyprianou.Ch10.StageE1

noncomputable def theorem10_10_corrected_coupled_source_type : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω),
    letI : MeasurableSpace Ω := m
    ∀ (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters),
      Levy.HasLevyLaw X →
      HasKilledLaplaceExponent X (fun _ : Ω => (⊤ : Mass)) T →
      T.killing = 0 →
      (∃ slope : EReal,
        HasRightSlope (Mechanism.psi T) slope ∧ 0 ≤ slope) →
      ∀ x : Time, 0 < x →
        ∀ t : Time, 0 < t →
          ∀ A : Set Ω,
            @MeasurableSet Ω
              (MeasurableSpace.comap
                (fun ω : Ω =>
                  fun s : {s : Time // s ≤ t} => X.path s.1 ω)
                inferInstance) A →
            Tendsto
              (fun q : Time =>
                correctedConditional (liftPositiveJumpPaths X)
                  ((liftPositiveJumpPaths X).law (x : ℝ))
                  (expClock q) t ((Prod.fst : Ω × ℝ → Ω) ⁻¹' A))
              (nhdsWithin (0 : Time) (Set.Ioi 0))
              (nhds (∫⁻ ω in A, StageDConditioning.levyDensity X x t ω
                ∂ X.law (x : ℝ)))


end Kyprianou.Ch10.StageE1


