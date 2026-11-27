-- Prove2me | Definitions.Def_MPBSelect_Supplement_ExactRates
-- name    : MPBSelect_Supplement_ExactRates
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:45:10.105082+00:00
-- url     : https://prove2.me/theorems/ec74f554-0ae0-5a32-ba45-af0da0289f8d
-- title:
--   Exact false-selection mappings, events and large-deviations rates
-- statement:
--   For the finite MPB problem, a **conditional-optimum mapping** assigns one solution to each parameter. The true mapping assigns $i^b$ to $\theta_b$; its misspecification set contains exactly the pairs at which another solution is selected. For each competitor $j$, $\mathcal A_j$ is the finite set of mappings under which $j$ ties or exceeds $i^*$ in preference probability.
--
--   The exact inner rate is
--
--   $$
--   \widetilde G_i(\theta_b)=\min_{x\in[y_{i^b}(\theta_b),y_i(\theta_b)]}\left\{
--   \frac{\alpha_{i^b}(\theta_b)}{2\lambda_{i^b}^2(\theta_b)}(x-y_{i^b}(\theta_b))^2+
--   \frac{\alpha_i(\theta_b)}{2\lambda_i^2(\theta_b)}(x-y_i(\theta_b))^2+
--   \sum_{\ell\ne i^b:\,y_\ell(\theta_b)<y_i(\theta_b)}
--   \frac{\alpha_\ell(\theta_b)}{2\lambda_\ell^2(\theta_b)}[(x-y_\ell(\theta_b))^+]^2
--   \right\}.
--   $$
--
--   The bundle also defines the summed outer-comparison rate, the minimum false-selection rate, independent Gaussian simulation arrays, the normal prior of Model (4) and the posterior means (5) under the static rule (zero prior precision gives the sample means), and the set-valued false-selection event used by Theorems 1 and EC.1. Extended-real negative logarithms give probability-zero events rate $+\infty$.
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, conditional-optimum mappings (10)-(13), pp.11-12, and Theorem 1, (14), p.13

import Mathlib
import Definitions.Def_MPBSelect_Problem
import Definitions.Def_MPBSelect_Problem_Xi
import Definitions.Def_MPBSelect_Problem_W

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MPBSelect.Supplement

/-- A conditional-optimum mapping, represented directly rather than as the paper's one-hot
`k × B` matrix. -/
abbrev Mapping (k B : ℕ) := Fin B → Fin k

/-- Public bundle name for the exact-rate definitions used by Theorems 1--2. -/
abbrev ExactRates (k B : ℕ) := Mapping k B

/-- The preference-probability gap `d_j(M)` in (11). -/
def mappingGap {k B : ℕ} (P : MPBSelect.Problem k B) (M : Mapping k B) (j : Fin k) : ℝ :=
  MPBSelect.prefProb P.p M P.istar - MPBSelect.prefProb P.p M j

/-- The misspecified pairs `I(M)` in (11). -/
def misspecified {k B : ℕ} (P : MPBSelect.Problem k B) (M : Mapping k B) :
    Finset (Fin k × Fin B) :=
  Finset.univ.filter fun x => M x.2 = x.1 ∧ x.1 ≠ P.ib x.2

/-- The collection `A_j` in (12). -/
def badMappings {k B : ℕ} (P : MPBSelect.Problem k B) (j : Fin k) :
    Finset (Mapping k B) :=
  Finset.univ.filter fun M => mappingGap P M j ≤ 0

/-- The quadratic expression inside the braces of (14). -/
def exactInnerIntegrand {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B) (x : ℝ) : ℝ :=
  α (P.ib b) b / (2 * P.lam (P.ib b) b ^ 2) * (x - P.y (P.ib b) b) ^ 2 +
    α i b / (2 * P.lam i b ^ 2) * (x - P.y i b) ^ 2 +
    ∑ l ∈ Finset.univ.filter (fun l : Fin k => l ≠ P.ib b ∧ P.y l b < P.y i b),
      α l b / (2 * P.lam l b ^ 2) * (max (x - P.y l b) 0) ^ 2

/-- The exact inner false-selection rate `G̃_i(θ_b)` in (14).

The defining interval is always nonempty (`y_{i^b} ≤ y_i`; it is a singleton when `i=i^b`),
and the continuous quadratic integrand is bounded below on it. Thus this real `sInf` is the
minimum printed in the paper, not the default value of an empty or unbounded infimum. -/
def exactInnerRate {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) (i : Fin k) (b : Fin B) : ℝ :=
  sInf {z : ℝ | ∃ x ∈ Icc (P.y (P.ib b) b) (P.y i b),
    z = exactInnerIntegrand P α i b x}

/-- The exact outer-comparison rate `LDR̃_{j,i*}` of Theorem 1. For `j ≠ i*`, `A_j` is
nonempty (the constant mapping with value `j` belongs to it), so the finite infimum below is a
genuine minimum. -/
def exactOuterRate {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) (j : Fin k) : ℝ :=
  sInf {z : ℝ | ∃ M ∈ badMappings P j,
    z = ∑ x ∈ misspecified P M, exactInnerRate P α x.1 x.2}

/-- The exact false-selection rate, the minimum of the outer-comparison rates over `j ≠ i*`. -/
def exactFSRate {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : ℝ :=
  sInf {z : ℝ | ∃ j : Fin k, j ≠ P.istar ∧ z = exactOuterRate P α j}

/-- The balance-weighted exact-rate relaxation in Theorem 2. `Ξ` is nonempty by the published
base definition, so `inf'` cannot return a junk value. -/
def weightedExactRate {k B : ℕ} (P : MPBSelect.Problem k B)
    (α : Fin k → Fin B → ℝ) : ℝ :=
  P.Xi.inf' P.Xi_nonempty fun x => P.W x.1 x.2 * exactInnerRate P α x.1 x.2

/-- An independent Gaussian simulation-output array from Model (4). The variance of coordinate
`(i,b,r)` is `λ_i(θ_b)^2`; all solution-parameter-replication coordinates are mutually
independent. -/
def IsGaussianSamples {k B : ℕ} (P : MPBSelect.Problem k B)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) : Prop :=
  (∀ i b r, Measurable (Y i b r) ∧
    Measure.map (Y i b r) μ = gaussianReal (P.y i b) ⟨P.lam i b ^ 2, sq_nonneg _⟩) ∧
  iIndepFun (fun q : (Fin k × Fin B) × ℕ => Y q.1.1 q.1.2 q.2) μ

/-- The normal prior of Model (4), p.8: prior mean `μ_{i,0}(θ_b)` and prior precision
`1/σ²_{i,0}(θ_b) ≥ 0`. Precision zero is the noninformative prior `σ²_{i,0}(θ_b) = ∞` of p.9. -/
structure GaussianPrior (k B : ℕ) where
  mean : Fin k → Fin B → ℝ
  prec : Fin k → Fin B → ℝ
  prec_nonneg : ∀ i b, 0 ≤ prec i b

/-- The posterior mean (5), p.9, after the static rule has assigned `N n i b` observations to
`(i,θ_b)`: `(μ_{i,0}/σ²_{i,0} + Σ_r Y_{ir}/λ²) / (1/σ²_{i,0} + N/λ²)`. With zero prior precision
it is the sample mean. Its value while a count is zero is immaterial to the asymptotic statements;
the theorems require every count to tend to infinity. -/
def staticMean {k B : ℕ} {Ω : Type*} (lam : Fin k → Fin B → ℝ) (pr : GaussianPrior k B)
    (N : ℕ → Fin k → Fin B → ℕ)
    (Y : Fin k → Fin B → ℕ → Ω → ℝ) (n : ℕ) (i : Fin k) (b : Fin B) (ω : Ω) : ℝ :=
  (pr.prec i b * pr.mean i b + (∑ r ∈ Finset.range (N n i b), Y i b r ω) / lam i b ^ 2) /
    (pr.prec i b + (N n i b : ℝ) / lam i b ^ 2)

/-- A fixed tie-broken minimizer on a nonempty `Fin k`. Ties have probability zero under the
Gaussian model, so the particular fixed choice does not change any event rate. -/
def argminFin {k : ℕ} (hk : 0 < k) (f : Fin k → ℝ) : Fin k :=
  Classical.choose (Finset.exists_min_image Finset.univ f
    (by exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩))

/-- Estimated conditional-optimum mapping `M_n` under the deterministic static rule: at each
`θ_b`, `i^b_n = argmin_i μ_{i,n}(θ_b)` with the posterior means (5), as in (7), p.9. -/
def staticMapping {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B) (pr : GaussianPrior k B)
    (N : ℕ → Fin k → Fin B → ℕ) (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) : Mapping k B :=
  fun b => argminFin (lt_of_lt_of_le (by decide : 0 < 2) P.two_le_k)
    (fun i => staticMean P.lam pr N Y n i b ω)

/-- The set of maximizers of preference probability induced by a mapping. It is set-valued, so
ties at the outer level are retained exactly as in the paper's false-selection event. -/
def mpbSet {k B : ℕ} (p : Fin B → ℝ) (M : Mapping k B) : Finset (Fin k) :=
  Finset.univ.filter fun i => ∀ j, MPBSelect.prefProb p M j ≤ MPBSelect.prefProb p M i

/-- `-log q`, with the correct extended-real value `+∞` when `q=0`. -/
def negLogProb (q : ℝ≥0∞) : EReal := -ENNReal.log q

/-- The lower exponential rate of a sequence of events. The `n=0` value has no effect on the
filter limit. -/
def eventLiminfRate {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : ℕ → Set Ω) : EReal :=
  liminf (fun n : ℕ => negLogProb (μ (E n)) / (n : EReal)) atTop

/-- Event that `i` is the selected conditional optimum at parameter `b`. -/
def innerSelectionEvent {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B)
    (pr : GaussianPrior k B) (N : ℕ → Fin k → Fin B → ℕ) (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (i : Fin k) (b : Fin B) (n : ℕ) : Set Ω :=
  {ω | staticMapping P pr N Y n ω b = i}

/-- Event that the estimated mapping lies in `A_j`. -/
def outerComparisonEvent {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B)
    (pr : GaussianPrior k B) (N : ℕ → Fin k → Fin B → ℕ) (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (j : Fin k) (n : ℕ) : Set Ω :=
  {ω | mappingGap P (staticMapping P pr N Y n ω) j ≤ 0}

/-- The set-valued false-selection event of §2 and Theorem 1. -/
def falseSelectionEvent {k B : ℕ} {Ω : Type*} (P : MPBSelect.Problem k B)
    (pr : GaussianPrior k B) (N : ℕ → Fin k → Fin B → ℕ) (Y : Fin k → Fin B → ℕ → Ω → ℝ)
    (n : ℕ) : Set Ω :=
  {ω | mpbSet P.p (staticMapping P pr N Y n ω) ≠ {P.istar}}

end MPBSelect.Supplement


