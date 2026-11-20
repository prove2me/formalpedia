-- Prove2me | Definitions.Def_Kyprianou_Ch10_Core06
-- name    : Kyprianou_Ch10_Core06
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:39:24.381184+00:00
-- url     : https://prove2.me/theorems/9069e208-e57c-4b6f-9c83-2ce55bedf44a
-- title:
--   Kyprianou Ch10 original model source, bounded segment 6/7
-- statement:
--   Dependency-closed original Chapter 10 Lean source, ordered segment 6 of 7; immutable source lines 2409 to 2879. Historical original declaration names and proof bodies preserved; no theorem is being asserted Proved.

import Definitions.Def_Kyprianou_Ch10_Core05
open Filter Set ProbabilityTheory MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1
theorem liftedLevy_expClock_rate_law
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (y : ℝ)
    (q : Time) (hq : 0 < q) :
    Killing.HasExponentialKilling
      ((liftPositiveJumpPaths X).law y)
      (fun p : Ω × ℝ => expClock q p) q := by
  intro t
  letI : IsProbabilityMeasure (X.law y) := X.probability y
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hset :
      {p : Ω × ℝ | (t : Mass) < expClock q p} =
        (Prod.snd : Ω × ℝ → ℝ) ⁻¹'
          Set.Ioi ((t : ℝ) * (q : ℝ)) := by
    ext p
    exact expClock_event_iff q t hq p
  change ((X.law y).prod (ProbabilityTheory.expMeasure 1))
    {p : Ω × ℝ | (t : Mass) < expClock q p} =
    ENNReal.ofReal (Real.exp (-((q : ℝ) * (t : ℝ))))
  rw [hset]
  calc
    ((X.law y).prod (ProbabilityTheory.expMeasure 1))
       ((Prod.snd : Ω × ℝ → ℝ) ⁻¹'
         Set.Ioi ((t : ℝ) * (q : ℝ))) =
       (((X.law y).prod (ProbabilityTheory.expMeasure 1)).map
         (Prod.snd : Ω × ℝ → ℝ))
           (Set.Ioi ((t : ℝ) * (q : ℝ))) := by
             rw [Measure.map_apply measurable_snd measurableSet_Ioi]
    _ = ProbabilityTheory.expMeasure 1
          (Set.Ioi ((t : ℝ) * (q : ℝ))) := by
            rw [Measure.map_snd_prod]
            simp
    _ = ENNReal.ofReal (Real.exp (-((q : ℝ) * (t : ℝ)))) := by
          simpa [mul_comm] using rateOneExp_measure_survival (t * q)

theorem liftedLevy_expClock_independent
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (q : Time) :
    IndependentKilling (liftPositiveJumpPaths X)
      (fun p : Ω × ℝ => expClock q p) := by
  intro y
  letI : IsProbabilityMeasure (X.law y) := X.probability y
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  change Indep
    (MeasurableSpace.comap
      (fun p : Ω × ℝ => expClockReal q p.2) inferInstance)
    (MeasurableSpace.comap
      (fun p : Ω × ℝ => fun t : Time => X.path t p.1) inferInstance)
    ((X.law y).prod (ProbabilityTheory.expMeasure 1))
  exact coordinate_clock_independent_of_full_path X
    (X.law y) (ProbabilityTheory.expMeasure 1)
    (expClockReal q) (expClockReal_measurable q)

/-- A law-preserving process and a coupled q-indexed exponential family exist
on one fixed product space; each killing clock is independent of the full path
under EVERY positive-start law. No path-level Levy equivalence is assumed. -/
theorem liftedLevy_exponential_family
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) :
    ∃ kill : Time → Ω × ℝ → Mass,
      ∀ q : Time, 0 < q →
        (∀ y : ℝ,
          Killing.HasExponentialKilling
            ((liftPositiveJumpPaths X).law y) (kill q) q) ∧
        IndependentKilling (liftPositiveJumpPaths X) (kill q) := by
  refine ⟨fun q p => expClock q p, ?_⟩
  intro q hq
  constructor
  · intro y
    exact liftedLevy_expClock_rate_law X y q hq
  · exact liftedLevy_expClock_independent X q

end Kyprianou.Ch10.StageE1


/- Exact Lévy law of the law-preserving independent-coordinate process lift. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem liftPositiveJumpPaths_hasLevyLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω)
    (h : Levy.HasLevyLaw X) :
    Levy.HasLevyLaw (liftPositiveJumpPaths X) := by
  rcases h with ⟨hRight, hStationary, hIndependent⟩
  refine ⟨?_, ?_, ?_⟩
  · intro p t
    exact hRight p.1 t
  · intro x s t
    letI : IsProbabilityMeasure (X.law x) := X.probability x
    letI : IsProbabilityMeasure (X.law 0) := X.probability 0
    change
      ((X.law x).prod (ProbabilityTheory.expMeasure 1)).map
        (fun p : Ω × ℝ => X.path (s + t) p.1 - X.path s p.1) =
      ((X.law 0).prod (ProbabilityTheory.expMeasure 1)).map
        (fun p : Ω × ℝ => X.path t p.1)
    have hLeft : Measurable (fun ω : Ω =>
          X.path (s+t) ω - X.path s ω) :=
      (X.coordinate_measurable (s+t)).sub (X.coordinate_measurable s)
    have hRight' : Measurable (X.path t) := X.coordinate_measurable t
    letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
    have hMap (μ : Measure Ω) [IsProbabilityMeasure μ]
        (f : Ω → ℝ) (hf : Measurable f) :
        ((μ.prod (ProbabilityTheory.expMeasure 1)).map
          (fun p : Ω × ℝ => f p.1)) = μ.map f := by
      calc
        (μ.prod (ProbabilityTheory.expMeasure 1)).map
          (fun p : Ω × ℝ => f p.1) =
          ((μ.prod (ProbabilityTheory.expMeasure 1)).map
            (Prod.fst : Ω × ℝ → Ω)).map f := by
              rw [Measure.map_map hf measurable_fst]
              rfl
        _ = μ.map f := by simp
    rw [hMap (X.law x) _ hLeft, hMap (X.law 0) _ hRight']
    exact hStationary x s t
  · intro x s t
    letI : IsProbabilityMeasure (X.law x) := X.probability x
    letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
      ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
    let past : Ω → ({r : Time // r ≤ s} → ℝ) :=
      fun ω r => X.path r.1 ω
    let incr : Ω → ℝ := fun ω => X.path (s + t) ω - X.path s ω
    have hpast : Measurable past :=
      measurable_pi_lambda _ (fun r => X.coordinate_measurable r.1)
    have hincr : Measurable incr :=
      (X.coordinate_measurable (s + t)).sub (X.coordinate_measurable s)
    have hSourceFun : past ⟂ᵢ[X.law x] incr :=
      (ProbabilityTheory.IndepFun_iff_Indep past incr (X.law x)).mpr
        (hIndependent x s t)
    have hIdent :
        ProbabilityTheory.IdentDistrib
          (fun ω : Ω => (past ω, incr ω))
          (fun p : Ω × ℝ => (past p.1, incr p.1))
          (X.law x) ((X.law x).prod (ProbabilityTheory.expMeasure 1)) := by
      refine ⟨(hpast.prodMk hincr).aemeasurable,
        ((hpast.prodMk hincr).comp measurable_fst).aemeasurable, ?_⟩
      calc
        (X.law x).map (fun ω : Ω => (past ω, incr ω)) =
          (((X.law x).prod (ProbabilityTheory.expMeasure 1)).map
            (Prod.fst : Ω × ℝ → Ω)).map
              (fun ω : Ω => (past ω, incr ω)) := by simp
        _ = ((X.law x).prod (ProbabilityTheory.expMeasure 1)).map
            (fun p : Ω × ℝ => (past p.1, incr p.1)) := by
              rw [Measure.map_map (hpast.prodMk hincr) measurable_fst]
              rfl
    have hNewFun :=
      ProbabilityTheory.indepFun_of_identDistrib_pair hSourceFun hIdent
    have hNewIndep :=
      (ProbabilityTheory.IndepFun_iff_Indep
        (fun p : Ω × ℝ => past p.1)
        (fun p : Ω × ℝ => incr p.1)
        ((X.law x).prod (ProbabilityTheory.expMeasure 1))).mp hNewFun
    change Indep
      (MeasurableSpace.comap
        (fun p : Ω × ℝ => past p.1) inferInstance)
      (MeasurableSpace.comap
        (fun p : Ω × ℝ => incr p.1) inferInstance)
      ((X.law x).prod (ProbabilityTheory.expMeasure 1))
    exact hNewIndep

end Kyprianou.Ch10.StageE1
/- The source's un-killed Laplace exponent is preserved exactly under
the law-preserving product lift; no independent-clock assumption is used. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem liftPositiveJumpPaths_uncut_laplaceExponent
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters)
    (h : HasKilledLaplaceExponent X
      (fun _ : Ω => (⊤ : Mass)) T) :
    HasKilledLaplaceExponent (liftPositiveJumpPaths X)
      (fun _ : Ω × ℝ => (⊤ : Mass)) T := by
  intro x t theta
  letI : IsProbabilityMeasure (X.law x) := X.probability x
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  let f : Ω → Mass :=
    fun ω => ENNReal.ofReal
      (Real.exp (-((theta : ℝ) * (X.path t ω - x))))
  have hinput : Measurable
      (fun ω : Ω => -((theta : ℝ) * (X.path t ω - x))) :=
    (measurable_const.mul
      ((X.coordinate_measurable t).sub_const x)).neg
  have hf : Measurable f :=
    (Real.measurable_exp.comp hinput).ennreal_ofReal
  have hfinite : (t : Mass) < ⊤ := ENNReal.coe_lt_top
  have hsource := h x t theta
  simp only [hfinite, ite_true] at hsource ⊢
  change (∫⁻ p : Ω × ℝ, f p.1 ∂
      (X.law x).prod (ProbabilityTheory.expMeasure 1)) =
    ENNReal.ofReal (Real.exp ((t : ℝ) * Mechanism.psi T theta))
  calc
    (∫⁻ p : Ω × ℝ, f p.1 ∂
       (X.law x).prod (ProbabilityTheory.expMeasure 1)) =
       ∫⁻ ω : Ω, f ω ∂
          (((X.law x).prod (ProbabilityTheory.expMeasure 1)).map
            (Prod.fst : Ω × ℝ → Ω)) := by
              rw [lintegral_map hf measurable_fst]
    _ = ∫⁻ ω : Ω, f ω ∂ X.law x := by
          rw [Measure.map_fst_prod]
          simp
    _ = ENNReal.ofReal
          (Real.exp ((t : ℝ) * Mechanism.psi T theta)) := hsource

end Kyprianou.Ch10.StageE1


/- One fixed enlarged probability space carries BOTH an exact Lévy-law copy
and a family of independent Exp(q) clocks for all q>0. The survival denominator
and the h-transform limit remain separate original-source obligations. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem coupledLevyFamily_exists_of_sourceLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω) (T : Mechanism.Parameters)
    (hLaw : Levy.HasLevyLaw X)
    (hLaplace : HasKilledLaplaceExponent X
      (fun _ : Ω => (⊤ : Mass)) T) :
    ∃ (X' : Levy.PositiveJumpPaths (Ω × ℝ))
      (kill : Time → Ω × ℝ → Mass),
      (∀ y : ℝ,
        X'.law y = (X.law y).prod (ProbabilityTheory.expMeasure 1) ∧
        (X'.law y).map (Prod.fst : Ω × ℝ → Ω) = X.law y) ∧
      (∀ (t : Time) (p : Ω × ℝ),
        X'.path t p = X.path t p.1 ∧
        X'.leftLimit t p = X.leftLimit t p.1) ∧
      Levy.HasLevyLaw X' ∧
      HasKilledLaplaceExponent X'
        (fun _ : Ω × ℝ => (⊤ : Mass)) T ∧
      (∀ q : Time, 0 < q →
        (∀ y : ℝ,
          Killing.HasExponentialKilling (X'.law y) (kill q) q) ∧
        IndependentKilling X' (kill q)) := by
  refine ⟨liftPositiveJumpPaths X, (fun q p => expClock q p), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    exact liftPositiveJumpPaths_law_preserving X y
  · intro t p
    exact liftPositiveJumpPaths_path_preserving X p t
  · exact liftPositiveJumpPaths_hasLevyLaw X hLaw
  · exact liftPositiveJumpPaths_uncut_laplaceExponent X T hLaplace
  · intro q hq
    constructor
    · intro y
      exact liftedLevy_expClock_rate_law X y q hq
    · exact liftedLevy_expClock_independent X q

end Kyprianou.Ch10.StageE1


/- Strict positivity of the actual conditioning denominator follows
from a positive deterministic-horizon survival event and an independent
clock that has positive probability to ring before that horizon. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem positive_killed_survival_of_positive_rectangle
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ν : Measure ℝ) [SFinite ν]
    (τ : Ω → Mass) (kill : ℝ → Mass) (c : Mass)
    (hSurvive : 0 < μ {ω | c < τ ω})
    (hClock : 0 < ν {r | kill r < c}) :
    0 < (μ.prod ν) {p : Ω × ℝ | kill p.2 < τ p.1} := by
  have hrectangle :
      ({ω : Ω | c < τ ω} ×ˢ {r : ℝ | kill r < c}) ⊆
        {p : Ω × ℝ | kill p.2 < τ p.1} := by
    rintro ⟨ω, r⟩ ⟨hω, hr⟩
    change c < τ ω at hω
    change kill r < c at hr
    exact lt_trans hr hω
  have hproduct :
      0 < (μ.prod ν) ({ω : Ω | c < τ ω} ×ˢ
          {r : ℝ | kill r < c}) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos (ne_of_gt hSurvive) (ne_of_gt hClock)
  exact hproduct.trans_le (measure_mono hrectangle)

end Kyprianou.Ch10.StageE1


/- Exp(1) has positive probability to generate an Exp(q) killing time
no later than ANY positive c, q>0. This is an actual distribution
calculation rather than an assumption of nonzero conditioning mass. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem expClock_le_horizon_positive
    (q c : Time) (hq : 0 < q) (hc : 0 < c) :
    0 < ProbabilityTheory.expMeasure 1
      {r : ℝ | expClockReal q r ≤ (c : Mass)} := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hcr : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
  have hmul : (0 : ℝ) < (c : ℝ) * (q : ℝ) := mul_pos hcr hqr
  have hCDF :
      ProbabilityTheory.expMeasure 1
          (Set.Iic ((c : ℝ) * (q : ℝ))) =
      ENNReal.ofReal (1 - Real.exp (-((c : ℝ) * (q : ℝ)))) := by
    rw [← ProbabilityTheory.ofReal_cdf
      (ProbabilityTheory.expMeasure 1) ((c : ℝ) * (q : ℝ))]
    rw [ProbabilityTheory.cdf_expMeasure_eq (by norm_num)]
    simp [hmul.le]
  have hleft :
      0 < ProbabilityTheory.expMeasure 1
          (Set.Iic ((c : ℝ) * (q : ℝ))) := by
    rw [hCDF, ENNReal.ofReal_pos]
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hmul))
  have hsubset :
      Set.Iic ((c : ℝ) * (q : ℝ)) ⊆
      {r : ℝ | expClockReal q r ≤ (c : Mass)} := by
    intro r hr
    change r ≤ ((c : ℝ) * (q : ℝ)) at hr
    change expClockReal q r ≤ (c : Mass)
    apply le_of_not_gt
    intro hbad
    have hbad' :
        (c : ℝ) * (q : ℝ) < r :=
      (expClock_event_iff (Ω := Unit) q c hq ((), r)).mp hbad
    exact (not_lt_of_ge hr) hbad'
  exact hleft.trans_le (measure_mono hsubset)

/-- Positive numerator-free conditioning denominator using a positively
likely deterministic survival horizon and the real Exp(q) clock law. -/
theorem coupled_clock_survival_positive_of_horizon
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → Mass) (q c : Time)
    (hq : 0 < q) (hc : 0 < c)
    (hSurvive : 0 < μ {ω | (c : Mass) < τ ω}) :
    0 < (μ.prod (ProbabilityTheory.expMeasure 1))
      {p : Ω × ℝ | expClockReal q p.2 < τ p.1} := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hrect :
      ({ω : Ω | (c : Mass) < τ ω} ×ˢ
        {r : ℝ | expClockReal q r ≤ (c : Mass)}) ⊆
        {p : Ω × ℝ | expClockReal q p.2 < τ p.1} := by
    rintro ⟨ω, r⟩ ⟨hω, hr⟩
    change (c : Mass) < τ ω at hω
    change expClockReal q r ≤ (c : Mass) at hr
    exact lt_of_le_of_lt hr hω
  have hleft :
      0 < (μ.prod (ProbabilityTheory.expMeasure 1))
        ({ω : Ω | (c : Mass) < τ ω} ×ˢ
          {r : ℝ | expClockReal q r ≤ (c : Mass)}) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos
      (ne_of_gt hSurvive)
      (ne_of_gt (expClock_le_horizon_positive q c hq hc))
  exact hleft.trans_le (measure_mono hrect)

end Kyprianou.Ch10.StageE1


/- Countable positive deterministic survival horizon from
a positive-probability positive lifetime. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem positive_deterministic_survival_of_positive_lifetime
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (τ : Ω → Mass)
    (hPositive : 0 < μ {ω : Ω | 0 < τ ω}) :
    ∃ δ : Time, 0 < δ ∧
      0 < μ {ω : Ω | (δ : Mass) < τ ω} := by
  let δ : ℕ → Time := fun n => 1 / (n + 1)
  have hδpos (n : ℕ) : 0 < δ n := by
    simp [δ]
  have hcofinal (m : Mass) (hm : 0 < m) :
      ∃ n : ℕ, (δ n : Mass) < m := by
    by_cases htop : m = ⊤
    · exact ⟨0, by simp [htop, δ]⟩
    · have hm' : 0 < m.toNNReal := by
        apply (ENNReal.coe_pos).mp
        simpa only [ENNReal.coe_toNNReal htop] using hm
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hm'
      refine ⟨n, ?_⟩
      have hcast : ((1 / (n + 1) : Time) : Mass) <
          (m.toNNReal : Mass) :=
        ENNReal.coe_lt_coe.mpr hn
      simpa [δ, ENNReal.coe_toNNReal htop] using hcast
  have hcover :
      {ω : Ω | 0 < τ ω} ⊆
        ⋃ n : ℕ, {ω : Ω | (δ n : Mass) < τ ω} := by
    intro ω hω
    obtain ⟨n, hn⟩ := hcofinal (τ ω) hω
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hPositiveUnion :
      0 < μ (⋃ n : ℕ, {ω : Ω | (δ n : Mass) < τ ω}) :=
    lt_of_lt_of_le hPositive (measure_mono hcover)
  obtain ⟨n, hn⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null
      (ne_of_gt hPositiveUnion)
  exact ⟨δ n, hδpos n, hn⟩

theorem coupled_clock_survival_positive_of_lifetime
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (τ : Ω → Mass) (q : Time) (hq : 0 < q)
    (hPositive : 0 < μ {ω : Ω | 0 < τ ω}) :
    0 < (μ.prod (ProbabilityTheory.expMeasure 1))
      {p : Ω × ℝ | expClockReal q p.2 < τ p.1} := by
  obtain ⟨c, hc, hSurvive⟩ :=
    positive_deterministic_survival_of_positive_lifetime μ τ hPositive
  exact coupled_clock_survival_positive_of_horizon μ τ q c
    hq hc hSurvive

end Kyprianou.Ch10.StageE1


/- A nonnegative trajectory throughout [0, delta) has first strict
negative passage no earlier than delta, even for non-attained sInf. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem strict_negative_passage_ge_of_nonnegative_interval
    {Ω : Type*}
    (X : Time → Ω → ℝ) (ω : Ω) (δ : Time)
    (hpositive : ∀ s : Time, s < δ → 0 ≤ X s ω) :
    (δ : Mass) ≤ Levy.firstStrictNegative X ω := by
  unfold Levy.firstStrictNegative
  apply le_sInf
  intro r hr
  rcases hr with ⟨hrFin, hrNeg⟩
  by_contra hlt
  have hltReal : r < (δ : Mass) := lt_of_not_ge hlt
  have hδ : r.toNNReal < δ := by
    apply (ENNReal.coe_lt_coe).mp
    simpa [ENNReal.coe_toNNReal hrFin] using hltReal
  exact (not_lt_of_ge (hpositive r.toNNReal hδ)) hrNeg

end Kyprianou.Ch10.StageE1

/- Source positivity: under right continuity and a strictly positive
initial law, every path starting at x has positive first-negative time. -/
set_option autoImplicit false
namespace Kyprianou.Ch10.StageE1

theorem firstNegative_strictPositive_of_rightContinuous
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Levy.PositiveJumpPaths Ω)
    (hLaw : Levy.HasLevyLaw X)
    (ω : Ω) (x : Time)
    (hx : 0 < x) (hinit : X.path 0 ω = (x : ℝ)) :
    0 < Levy.firstStrictNegative X.path ω := by
  have hIci : (Set.Ici (0 : Time)) = Set.univ := by
    ext s
    simp
  have hRight : Tendsto (fun s : Time => X.path s ω)
      (nhds (0 : Time)) (nhds (X.path 0 ω)) := by
    simpa [hIci] using hLaw.1 ω 0
  have hGood : {s : Time | 0 < X.path s ω} ∈ nhds (0 : Time) := by
    change (fun s : Time => X.path s ω) ⁻¹' Set.Ioi (0 : ℝ) ∈ nhds _
    have hxr : (0 : ℝ) < X.path 0 ω := by
      simpa [hinit] using hx
    exact hRight (isOpen_Ioi.mem_nhds hxr)
  obtain ⟨δ, hδ, hsmall⟩ := (NNReal.nhds_zero_basis.mem_iff).mp hGood
  have hNonneg : ∀ s : Time, s < δ → 0 ≤ X.path s ω := by
    intro s hs
    exact le_of_lt (hsmall hs)
  have hτ : (δ : Mass) ≤ Levy.firstStrictNegative X.path ω :=
    strict_negative_passage_ge_of_nonnegative_interval X.path ω δ hNonneg
  have hδpos : 0 < (δ : Mass) := by exact_mod_cast hδ
  exact lt_of_lt_of_le hδpos hτ

end Kyprianou.Ch10.StageE1


