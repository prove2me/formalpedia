-- Prove2me | Definitions.Def_MPBSelect_Supplement_Sequential
-- name    : MPBSelect_Supplement_Sequential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:47:17.471908+00:00
-- url     : https://prove2.me/theorems/ec446222-e61d-5f47-bf0f-23e5c0beaaa2
-- title:
--   Complete stochastic run relations for Algorithms 1-4
-- statement:
--   This bundle formalizes the complete adaptive experiments of Algorithms 1-4. A run includes the warm start, normal prior precision (with zero precision for the noninformative prior), independent Gaussian simulation outputs, posterior updates (5), plug-in conditional optima and MPB, the paper's outer tie-breaking rule, empirical $G$ and $W$ matrices, sampling decisions, count updates and an information filtration. The next selected output has its Gaussian law conditionally on the past.
--
--   Algorithm 2 additionally draws and discards fresh posterior samples for the current estimated MPB outside its estimated favorable set. Algorithms 3 and 4 replace the weights and use the full global-balance sum exactly as specified below (30). Unbounded sampling is expressed as: for every threshold, some later count reaches it.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, Algorithms 0-2 and surrounding conventions, pp.21-24, and Algorithms 3-4 below (30), pp.26-27

import Mathlib
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_W
import Definitions.Def_MPBSelect_Supplement_ExactRates
import Definitions.Def_MPBSelect_Supplement_Favorable

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MPBSelect.Supplement

/-- Prior and warm-start data for Algorithms 0--4. `priorPrec = 1/σ²_{i,0}`; zero precision is
the noninformative prior. -/
structure SequentialData {k B : ℕ} (P : MPBSelect.Problem k B) where
  n0 : ℕ
  n0_pos : 0 < n0
  priorMean : Fin k → Fin B → ℝ
  priorPrec : Fin k → Fin B → ℝ
  priorPrec_nonneg : ∀ i b, 0 ≤ priorPrec i b

/-- Public bundle name for the sequential-algorithm data and run relations. -/
abbrev Sequential {k B : ℕ} (P : MPBSelect.Problem k B) := SequentialData P

/-- Total number of simulation replications after `t` post-warm-start decisions. -/
def SequentialData.total {k B : ℕ} {P : MPBSelect.Problem k B}
    (D : SequentialData P) (t : ℕ) : ℕ := D.n0 * k * B + t

/-- Posterior mean (5), using the first `N_i^n(θ_b)` independent outputs at each pair. -/
def posteriorMean {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B) (D : SequentialData P)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (t : ℕ) (ω : Ω) (i : Fin k) (b : Fin B) : ℝ :=
  let c := N t ω i b
  (D.priorPrec i b * D.priorMean i b +
      (∑ r ∈ Finset.range c, Y i b r ω) / P.lam i b ^ 2) /
    (D.priorPrec i b + (c : ℝ) / P.lam i b ^ 2)

/-- Posterior variance in (5). -/
def posteriorVariance {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B) (D : SequentialData P)
    (N : ℕ → Ω → Fin k → Fin B → ℕ) (t : ℕ) (ω : Ω)
    (i : Fin k) (b : Fin B) : ℝ :=
  (D.priorPrec i b + (N t ω i b : ℝ) / P.lam i b ^ 2)⁻¹

/-- Empirical allocation fraction after `t` adaptive decisions. -/
def allocationFraction {k B : ℕ} {P : MPBSelect.Problem k B} {Ω : Type*} (D : SequentialData P)
    (N : ℕ → Ω → Fin k → Fin B → ℕ) (t : ℕ) (ω : Ω)
    (i : Fin k) (b : Fin B) : ℝ :=
  (N t ω i b : ℝ) / (D.total t : ℝ)

/-- Plug-in conditional-optimum mapping from a table of estimated means. -/
def plugInMapping {k B : ℕ} (P : MPBSelect.Problem k B)
    (m : Fin k → Fin B → ℝ) : Mapping k B :=
  fun b => argminFin (lt_of_lt_of_le (by decide : 0 < 2) P.two_le_k) (fun i => m i b)

/-- Plug-in `Ξ`. -/
def empiricalXi {k B : ℕ} (istar : Fin k) (ib : Mapping k B) :
    Finset (Fin k × Fin B) :=
  Finset.univ.filter fun x => x.1 ≠ istar ∧ x.1 ≠ ib x.2

/-- Plug-in preference gap. -/
def empiricalGap {k B : ℕ} (p : Fin B → ℝ) (ib : Mapping k B)
    (istar j : Fin k) : ℝ :=
  MPBSelect.prefProb p ib istar - MPBSelect.prefProb p ib j

/-- Plug-in balance weight (17). -/
def empiricalW {k B : ℕ} (p : Fin B → ℝ) (ib : Mapping k B)
    (istar i : Fin k) (b : Fin B) : ℝ :=
  let md := sInf {z : ℝ | ∃ j : Fin k, j ≠ istar ∧ z = empiricalGap p ib istar j}
  if ib b = istar then max (min md (empiricalGap p ib istar i / 2) / p b) 1
  else max (empiricalGap p ib istar i / p b) 1

/-- Empirical Gaussian comparison rate, expressed in counts as used by the algorithms. -/
def empiricalG {k B : ℕ} (P : MPBSelect.Problem k B)
    (m : Fin k → Fin B → ℝ) (N : Fin k → Fin B → ℕ)
    (ib : Mapping k B) (i : Fin k) (b : Fin B) : ℝ :=
  if 0 < N i b ∧ 0 < N (ib b) b then
    (m i b - m (ib b) b) ^ 2 /
      (2 * (P.lam i b ^ 2 / (N i b : ℝ) +
        P.lam (ib b) b ^ 2 / (N (ib b) b : ℝ)))
  else 0

/-- The tie-breaking score prescribed below Algorithm 0: the least empirical rate on the
estimated adversarial set of a tied MPB candidate. Empty adversarial sets have value `+∞`. -/
def tieScore {k B : ℕ} (P : MPBSelect.Problem k B) (m : Fin k → Fin B → ℝ)
    (N : Fin k → Fin B → ℕ) (ib : Mapping k B) (j : Fin k) : EReal :=
  sInf {z : EReal | ∃ b : Fin B, ib b ≠ j ∧
    z = (empiricalG P m N ib j b : EReal)}

/-- A selected empirical MPB obeys both the outer argmax and the paper's adversarial-rate
tie-breaking rule. -/
def IsTieBrokenMPB {k B : ℕ} (P : MPBSelect.Problem k B)
    (m : Fin k → Fin B → ℝ) (N : Fin k → Fin B → ℕ)
    (ib : Mapping k B) (istar : Fin k) : Prop :=
  istar ∈ mpbSet P.p ib ∧
    ∀ j ∈ mpbSet P.p ib, tieScore P m N ib j ≤ tieScore P m N ib istar

/-- The pair chosen by Line 4 of Algorithm 1. -/
def IsMinPair {k B : ℕ} (P : MPBSelect.Problem k B)
    (m : Fin k → Fin B → ℝ) (N : Fin k → Fin B → ℕ)
    (ib : Mapping k B) (istar : Fin k) (x : Fin k × Fin B) : Prop :=
  x ∈ empiricalXi istar ib ∧ ∀ y ∈ empiricalXi istar ib,
    empiricalW P.p ib istar x.1 x.2 * empiricalG P m N ib x.1 x.2 ≤
      empiricalW P.p ib istar y.1 y.2 * empiricalG P m N ib y.1 y.2

/-- The next pair in Algorithms 1--2 after the global-balance comparison. -/
def nextPair {k B : ℕ} (P : MPBSelect.Problem k B) (N : Fin k → Fin B → ℕ)
    (ib : Mapping k B) (istar : Fin k) (x : Fin k × Fin B) : Fin k × Fin B :=
  if (N (ib x.2) x.2 : ℝ) ^ 2 / P.lam (ib x.2) x.2 ^ 2 <
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ ib x.2 ∧ j ≠ istar),
        (N j x.2 : ℝ) ^ 2 / P.lam j x.2 ^ 2
  then (ib x.2, x.2) else x

/-- The empirical active set `Ξ ∪ Ξ^adv` for Algorithms 3--4. -/
def empiricalFavorablePairs {k B : ℕ} (ib : Mapping k B) (istar : Fin k) :
    Finset (Fin k × Fin B) :=
  empiricalXi istar ib ∪
    Finset.univ.filter (fun x : Fin k × Fin B => x.1 = istar ∧ ib x.2 ≠ istar)

inductive FavorableMode
  | acc
  | fn
  deriving DecidableEq

/-- The true weight family selected by Algorithm 3 (`acc`) or Algorithm 4 (`fn`). -/
def favorableWeight {k B : ℕ} (mode : FavorableMode) (P : MPBSelect.Problem k B)
    (i : Fin k) (b : Fin B) : ℝ :=
  match mode with
  | .acc => wAcc P i b
  | .fn => wFN P i b

/-- Plug-in versions of the two weights in (30). -/
def empiricalFavorableW {k B : ℕ} (mode : FavorableMode) (P : MPBSelect.Problem k B)
    (ib : Mapping k B) (istar i : Fin k) (b : Fin B) : ℝ :=
  match mode with
  | .acc => if ib b = istar ∨ (i = istar ∧ ib b ≠ istar) then 1
      else empiricalW P.p ib istar i b
  | .fn => if (i, b) ∈ empiricalXi istar ib then empiricalW P.p ib istar i b else 1

/-- The pair selected by Algorithms 3--4. -/
def IsMinFavorablePair {k B : ℕ} (mode : FavorableMode) (P : MPBSelect.Problem k B)
    (m : Fin k → Fin B → ℝ) (N : Fin k → Fin B → ℕ)
    (ib : Mapping k B) (istar : Fin k) (x : Fin k × Fin B) : Prop :=
  x ∈ empiricalFavorablePairs ib istar ∧ ∀ y ∈ empiricalFavorablePairs ib istar,
    empiricalFavorableW mode P ib istar x.1 x.2 * empiricalG P m N ib x.1 x.2 ≤
      empiricalFavorableW mode P ib istar y.1 y.2 * empiricalG P m N ib y.1 y.2

/-- The global-balance decision of Algorithms 3--4, whose sum includes every `j ≠ i^b`. -/
def nextFavorablePair {k B : ℕ} (P : MPBSelect.Problem k B)
    (N : Fin k → Fin B → ℕ) (ib : Mapping k B) (x : Fin k × Fin B) : Fin k × Fin B :=
  if (N (ib x.2) x.2 : ℝ) ^ 2 / P.lam (ib x.2) x.2 ^ 2 <
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => j ≠ ib x.2),
        (N j x.2 : ℝ) ^ 2 / P.lam j x.2 ^ 2
  then (ib x.2, x.2) else x

/-- Common probability and filtration clauses for an adaptive run: all primitive outputs have
the independent Gaussian law of Model (4); decisions and counts are known before a step; the
chosen fresh output is revealed at the next step and has its Gaussian law conditionally on the
past. -/
structure IsAdaptiveExperiment {k B : ℕ} (P : MPBSelect.Problem k B)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (decision : ℕ → Ω → Fin k × Fin B) : Prop where
  gaussian : IsGaussianSamples P μ Y
  count_meas : ∀ t i b c, MeasurableSet[F t] {ω | N t ω i b = c}
  decision_meas : ∀ t x, MeasurableSet[F t] {ω | decision t ω = x}
  next_output_meas : ∀ t,
    Measurable[F (t + 1)] (fun ω => Y (decision t ω).1 (decision t ω).2
      (N t ω (decision t ω).1 (decision t ω).2) ω)
  next_output_law : ∀ t, ∀ A : Set ℝ, MeasurableSet A →
    μ[Set.indicator {ω | Y (decision t ω).1 (decision t ω).2
        (N t ω (decision t ω).1 (decision t ω).2) ω ∈ A} (fun _ => (1 : ℝ)) | F t]
      =ᵐ[μ] fun ω =>
        (gaussianReal (P.y (decision t ω).1 (decision t ω).2)
          ⟨P.lam (decision t ω).1 (decision t ω).2 ^ 2, sq_nonneg _⟩ A).toReal

/-- A complete stochastic run relation for Algorithm 1: warm start, posterior update, plug-in
inner and outer optima with the stated tie-break, minimum weighted rate, global-balance branch,
count update, Gaussian samples and filtration are all included. -/
structure IsAlgorithm1Run {k B : ℕ} (P : MPBSelect.Problem k B) (D : SequentialData P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (istar : ℕ → Ω → Fin k) (selected decision : ℕ → Ω → Fin k × Fin B) : Prop where
  experiment : IsAdaptiveExperiment P μ F Y N decision
  init : ∀ ω i b, N 0 ω i b = D.n0
  outer : ∀ t ω,
    IsTieBrokenMPB P (fun i b => posteriorMean P D Y N t ω i b) (N t ω)
      (plugInMapping P (fun i b => posteriorMean P D Y N t ω i b)) (istar t ω)
  select : ∀ t ω,
    IsMinPair P (fun i b => posteriorMean P D Y N t ω i b) (N t ω)
      (plugInMapping P (fun i b => posteriorMean P D Y N t ω i b))
      (istar t ω) (selected t ω)
  decide : ∀ t ω, decision t ω = nextPair P (N t ω)
    (plugInMapping P (fun i b => posteriorMean P D Y N t ω i b))
    (istar t ω) (selected t ω)
  update : ∀ t ω i b, N (t + 1) ω i b =
    N t ω i b + if decision t ω = (i, b) then 1 else 0

/-- Posterior-sampled means in Line 4 of Algorithm 2. Only the current estimated MPB on the
complement of its estimated favorable set is replaced, and samples are discarded each round. -/
def hybridMeans {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B) (D : SequentialData P)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (Z : ℕ → Fin B → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ) (t : ℕ) (ω : Ω)
    (baseIb : Mapping k B) (istar : Fin k) : Fin k → Fin B → ℝ :=
  fun i b => if i = istar ∧ baseIb b ≠ istar then
    posteriorMean P D Y N t ω i b +
      Real.sqrt (posteriorVariance P D N t ω i b) * Z t b ω
  else posteriorMean P D Y N t ω i b

/-- A complete stochastic run relation for Algorithm 2, including its fresh independent standard
normal posterior draws. -/
structure IsAlgorithm2Run {k B : ℕ} (P : MPBSelect.Problem k B) (D : SequentialData P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (Z : ℕ → Fin B → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (istar : ℕ → Ω → Fin k) (selected decision : ℕ → Ω → Fin k × Fin B) : Prop where
  experiment : IsAdaptiveExperiment P μ F Y N decision
  posterior_noise : (∀ t b, Measurable (Z t b) ∧
      Measure.map (Z t b) μ = gaussianReal 0 1)
  all_noise_indep : iIndepFun
    (fun q : Sum ((Fin k × Fin B) × ℕ) (ℕ × Fin B) =>
      (match q with
      | .inl r => Y r.1.1 r.1.2 r.2
      | .inr r => Z r.1 r.2 : Ω → ℝ)) μ
  init : ∀ ω i b, N 0 ω i b = D.n0
  outer : ∀ t ω,
    let m := fun i b => posteriorMean P D Y N t ω i b
    let ib := plugInMapping P m
    IsTieBrokenMPB P m (N t ω) ib (istar t ω)
  select : ∀ t ω,
    let m := fun i b => posteriorMean P D Y N t ω i b
    let ib0 := plugInMapping P m
    let mh := hybridMeans P D Y Z N t ω ib0 (istar t ω)
    let ib := plugInMapping P mh
    IsMinPair P mh (N t ω) ib (istar t ω) (selected t ω)
  decide : ∀ t ω,
    let m := fun i b => posteriorMean P D Y N t ω i b
    let ib0 := plugInMapping P m
    let mh := hybridMeans P D Y Z N t ω ib0 (istar t ω)
    let ib := plugInMapping P mh
    decision t ω = nextPair P (N t ω) ib (istar t ω) (selected t ω)
  update : ∀ t ω i b, N (t + 1) ω i b =
    N t ω i b + if decision t ω = (i, b) then 1 else 0

/-- A complete run relation for Algorithm 3 (`acc`) or Algorithm 4 (`fn`). -/
structure IsFavorableAlgorithmRun {k B : ℕ} (mode : FavorableMode)
    (P : MPBSelect.Problem k B) (D : SequentialData P)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F : Filtration ℕ ‹MeasurableSpace Ω›)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (istar : ℕ → Ω → Fin k) (selected decision : ℕ → Ω → Fin k × Fin B) : Prop where
  experiment : IsAdaptiveExperiment P μ F Y N decision
  init : ∀ ω i b, N 0 ω i b = D.n0
  outer : ∀ t ω,
    IsTieBrokenMPB P (fun i b => posteriorMean P D Y N t ω i b) (N t ω)
      (plugInMapping P (fun i b => posteriorMean P D Y N t ω i b)) (istar t ω)
  select : ∀ t ω,
    IsMinFavorablePair mode P (fun i b => posteriorMean P D Y N t ω i b) (N t ω)
      (plugInMapping P (fun i b => posteriorMean P D Y N t ω i b))
      (istar t ω) (selected t ω)
  decide : ∀ t ω, decision t ω = nextFavorablePair P (N t ω)
    (plugInMapping P (fun i b => posteriorMean P D Y N t ω i b)) (selected t ω)
  update : ∀ t ω i b, N (t + 1) ω i b =
    N t ω i b + if decision t ω = (i, b) then 1 else 0

/-- `G_{i,n}` in Theorems 5 and 7, using the true conditional optimum but the current posterior
means and counts. -/
def empiricalTrueG {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B) (D : SequentialData P)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (t : ℕ) (ω : Ω) (i : Fin k) (b : Fin B) : ℝ :=
  empiricalG P (fun j c => posteriorMean P D Y N t ω j c) (N t ω) P.ib i b

/-- Unbounded sampling, the well-typed meaning of `limsup N_i^n(θ_b)=∞`. -/
def UnboundedSampling {k B : ℕ} {Ω : Type*} (N : ℕ → Ω → Fin k → Fin B → ℕ)
    (ω : Ω) (i : Fin k) (b : Fin B) : Prop :=
  ∀ C : ℕ, ∃ t : ℕ, C ≤ N t ω i b

end MPBSelect.Supplement


