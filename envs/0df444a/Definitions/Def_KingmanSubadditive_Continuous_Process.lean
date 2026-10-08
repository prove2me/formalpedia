-- Prove2me | Definitions.Def_KingmanSubadditive_Continuous_Process
-- name    : KingmanSubadditive_Continuous_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:26:12.5378+00:00
-- url     : https://prove2.me/theorems/dc8941f0-94a9-4130-aa1d-1657c928c133
-- title:
--   Continuous-parameter subadditive process, separability, mean rate, and oscillation
-- statement:
--   Let $(S,\mathcal F,P)$ be a probability space. A continuous-parameter subadditive process is a family of real random variables $x_{st}$, indexed by $0\le s<t$, with these properties: $x_{su}\le x_{st}+x_{tu}$ for $s<t<u$; shifting every pair of indices by any $\tau\ge0$ preserves the joint law of the entire family; and every $x_{0t}$ for $t>0$ has finite expectation $g_t$ with $g_t\ge-At$ for some constant $A$.
--
--   The mean rate and oscillation are
--
--   $$
--   \gamma=\inf_{t>0}\frac{g_t}{t},\qquad
--   \Omega_I=\sup_{s<t,\ s,t\in I}|x_{st}|.
--   $$
--
--   A process is separable if, outside one null set, every coordinate value is a limit of values along a sequence from a fixed countable dense set of admissible time pairs. Finite expected oscillation means $E(\Omega_I)<\infty$. These definitions supply the common model for Theorem 4 and its intermediate results.
--
--   **Formalization Note** The sample space is named $S$ to reserve $\Omega_I$ for oscillation. Subadditivity is pointwise, stationarity concerns the full joint law, and oscillation takes values in the extended nonnegative reals so an unbounded supremum remains infinite.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, pp. 883–884, §1.1; pp. 887–889, §1.4, (1.4.1), (1.4.6), (1.4.7); separability convention after Doob (1953)

import Mathlib

namespace KingmanSubadditive.Continuous

open MeasureTheory Filter Topology

variable {S : Type*} [MeasurableSpace S]

/-- Kingman, §1.4, p. 887. The admissible pairs of nonnegative real times. Values of a
two-index family outside this type have no mathematical meaning. -/
abbrev TimePair := {p : ℝ × ℝ // 0 ≤ p.1 ∧ p.1 < p.2}

/-- Kingman, §1.4, p. 887, conditions S₁–S₃. The sample space is called `S` so that the
paper's symbol Ω remains available for oscillation. S₁ is pointwise; S₂ is equality of the
joint laws of all admissible coordinates, for every nonnegative real shift. Each coordinate
is measurable, and "the expectation exists" in S₃ means Bochner integrability. -/
def IsProcess (P : Measure S) (x : ℝ → ℝ → S → ℝ) : Prop :=
  (∀ s t : ℝ, 0 ≤ s → s < t → Measurable (x s t)) ∧
  (∀ s t u : ℝ, 0 ≤ s → s < t → t < u →
    ∀ ω : S, x s u ω ≤ x s t ω + x t u ω) ∧
  (∀ τ : ℝ, 0 ≤ τ →
    Measure.map (fun ω : S => fun p : TimePair =>
      x (p.1.1 + τ) (p.1.2 + τ) ω) P =
    Measure.map (fun ω : S => fun p : TimePair =>
      x p.1.1 p.1.2 ω) P) ∧
  (∀ t : ℝ, 0 < t → Integrable (x 0 t) P) ∧
  (∃ A : ℝ, ∀ t : ℝ, 0 < t → -A * t ≤ ∫ ω, x 0 t ω ∂P)

/-- Kingman, §1.4, pp. 887–889, with the separability convention made explicit.
There is a countable dense family of admissible time pairs whose sample-path graph
approximates every coordinate outside one measurable null set. This is the graph
separability referred to Doob (1953) by the paper; it allows discontinuous paths. -/
def IsSeparable (P : Measure S) (x : ℝ → ℝ → S → ℝ) : Prop :=
  ∃ (D : Set TimePair) (N : Set S), D.Countable ∧ Dense D ∧
    MeasurableSet N ∧ P N = 0 ∧
    ∀ ω : S, ω ∉ N → ∀ p : TimePair,
      ∃ q : ℕ → TimePair, (∀ n, q n ∈ D) ∧
        Tendsto q atTop (𝓝 p) ∧
        Tendsto (fun n => x (q n).1.1 (q n).1.2 ω) atTop
          (𝓝 (x p.1.1 p.1.2 ω))

/-- Kingman, (1.1.2), p. 883, now at every positive real time in §1.4. -/
noncomputable def mean (P : Measure S) (x : ℝ → ℝ → S → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, x 0 t ω ∂P

/-- Kingman, (1.4.1), p. 887. The S₃ lower bound makes this infimum bounded below.
The `TimePair` and positive-time subtypes prevent invalid zero-time values entering it. -/
noncomputable def gamma (P : Measure S) (x : ℝ → ℝ → S → ℝ) : ℝ :=
  ⨅ t : {t : ℝ // 0 < t}, mean P x t / (t : ℝ)

/-- Kingman, (1.4.6), p. 889. The extended nonnegative codomain preserves unbounded
oscillation as infinity instead of Lean's default real supremum value. -/
noncomputable def oscillation (x : ℝ → ℝ → S → ℝ) (I : Set ℝ) (ω : S) : ENNReal :=
  ⨆ (p : TimePair) (_ : p.1.1 ∈ I ∧ p.1.2 ∈ I),
    ENNReal.ofReal (|x p.1.1 p.1.2 ω|)

/-- Kingman, (1.4.7), p. 889: finite expected oscillation. Separability makes
the oscillation almost-everywhere measurable; the nonnegative integral retains ∞. -/
def FiniteOscillation (P : Measure S) (x : ℝ → ℝ → S → ℝ)
    (I : Set ℝ) : Prop :=
  AEMeasurable (oscillation x I) P ∧
    ∫⁻ ω, oscillation x I ω ∂P < ⊤

end KingmanSubadditive.Continuous


