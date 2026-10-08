-- Prove2me | Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds
-- name    : OptStopC1_SpaceDeriv_LocalBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:12.396914+00:00
-- url     : https://prove2.me/theorems/f0aa6446-17d1-4e82-88ee-7ab9e331f91a
-- title:
--   Theorem 8 local integrability and boundary hypotheses
-- statement:
--   At a boundary point $z$, one open Euclidean ball $b(z,r)$, $r>0$, must satisfy all four integrability conditions (4.4)–(4.7) for every coordinate pair $(i,j)$. They control, respectively, the discounted terminal derivative, the time integral of a discounted flow derivative, the discounted terminal reward multiplied by an accumulated flow derivative, and the nested time integral involving the running reward. The hypotheses also require the right limit $\partial_iX^{j,z}_{0+}=\delta_{ij}$ and either strong Feller with probabilistic regularity for $D$, or probabilistic regularity for $D^\circ$.
--
--   The shared hypotheses include well-posedness, the generator representation (2.14), continuity and interior C¹ regularity of $V$, global C¹ regularity of $G$, one positive Lipschitz constant for both $H$ and $\lambda$, and a C¹ spatial flow.
--
--   These conditions are reused without change in the two derivative bounds, the pointwise theorem, and the global goal.
--
--   **Formalization Note** The uncountable suprema under expectations in (4.4)–(4.7) are expressed using integrable common majorants. Measurable time envelopes replace the suprema inside time integrals. Each envelope is required only up to an indexed first entry time; the indexing states $\alpha,\beta,\gamma,\xi,\eta$ remain distinct.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, pp. 11–12, Theorem 8, equations (4.1)–(4.7) and initial derivative condition

import Definitions.Def_OptStopC1_SpaceDeriv_StoppingProblem
import Definitions.Def_OptStopC1_SpaceDeriv_BoundaryRegularity

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

variable {d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
variable {P : Measure Ω} {𝔽 : Filtration ℝ≥0 mΩ}

noncomputable def rewardPartial (p : StoppingProblem d Ω P 𝔽)
    (j : Fin d) (x : State d) : ℝ :=
  (fderiv ℝ p.G x) (EuclideanSpace.single j (1 : ℝ))

/-- The outer expectation in (4.4), represented by an integrable common majorant. -/
noncomputable def Bound44 (p : StoppingProblem d Ω P 𝔽)
    (z : State d) (r : ℝ) (i j : Fin d) : Prop :=
  ∃ g : Ω → ℝ, Integrable g P ∧
    ∀ᵐ ω ∂P, ∀ α ∈ Metric.ball z r, ∀ β ∈ Metric.ball z r,
      ∀ ξ ∈ Metric.ball z r,
        Real.exp (-(discount p β
          (finiteEntryTime p.X α (stoppingSet p) ω) ω)) *
          |rewardPartial p j (p.X ξ
            (finiteEntryTime p.X α (stoppingSet p) ω) ω) *
           flowPartial p.X i j ξ
            (finiteEntryTime p.X α (stoppingSet p) ω) ω| ≤ g ω

/-- The pointwise supremum inside the time integral in (4.5) is replaced by
an envelope k; its integral has an integrable common majorant g. -/
noncomputable def Bound45 (p : StoppingProblem d Ω P 𝔽)
    (z : State d) (r : ℝ) (i j : Fin d) : Prop :=
  ∃ (g : Ω → ℝ) (k : ℝ → Ω → ℝ), Integrable g P ∧
    (∀ᵐ ω ∂P,
      (∀ α ∈ Metric.ball z r, ∀ (t : ℝ), 0 ≤ t →
        t ≤ (finiteEntryTime p.X α (stoppingSet p) ω : ℝ) →
        ∀ β ∈ Metric.ball z r, ∀ η ∈ Metric.ball z r,
          Real.exp (-(discount p β t.toNNReal ω)) *
            |flowPartial p.X i j η t.toNNReal ω| ≤ k t ω) ∧
      (∀ α ∈ Metric.ball z r,
        IntervalIntegrable (fun t => k t ω) volume 0
          (finiteEntryTime p.X α (stoppingSet p) ω : ℝ) ∧
        (∫ t in (0 : ℝ)..(finiteEntryTime p.X α (stoppingSet p) ω : ℝ),
          k t ω) ≤ g ω))

/-- The nested spatial supremum in (4.6) is replaced by a measurable
pathwise envelope k; the complete product is bounded by integrable g. -/
noncomputable def Bound46 (p : StoppingProblem d Ω P 𝔽)
    (z : State d) (r : ℝ) (i j : Fin d) : Prop :=
  ∃ (g : Ω → ℝ) (k : ℝ → Ω → ℝ), Integrable g P ∧
    (∀ᵐ ω ∂P,
      (∀ α ∈ Metric.ball z r, ∀ (t : ℝ), 0 ≤ t →
        t ≤ (finiteEntryTime p.X α (stoppingSet p) ω : ℝ) →
        ∀ η ∈ Metric.ball z r, |flowPartial p.X i j η t.toNNReal ω| ≤ k t ω) ∧
      (∀ α ∈ Metric.ball z r,
        IntervalIntegrable (fun t => k t ω) volume 0
          (finiteEntryTime p.X α (stoppingSet p) ω : ℝ)) ∧
      (∀ α ∈ Metric.ball z r, ∀ β ∈ Metric.ball z r,
        ∀ γ ∈ Metric.ball z r,
          Real.exp (-(discount p β
            (finiteEntryTime p.X α (stoppingSet p) ω) ω)) *
            |p.G (p.X γ (finiteEntryTime p.X α (stoppingSet p) ω) ω)| *
            (∫ t in (0 : ℝ)..(finiteEntryTime p.X α (stoppingSet p) ω : ℝ),
              k t ω) ≤ g ω))

/-- The two nested spatial suprema in (4.7) are represented by timewise
envelopes k and q; the outer integral is dominated by integrable g. -/
noncomputable def Bound47 (p : StoppingProblem d Ω P 𝔽)
    (z : State d) (r : ℝ) (i j : Fin d) : Prop :=
  ∃ (g : Ω → ℝ) (k q : ℝ → Ω → ℝ), Integrable g P ∧
    (∀ᵐ ω ∂P,
      (∀ α ∈ Metric.ball z r, ∀ (s : ℝ), 0 ≤ s →
        s ≤ (finiteEntryTime p.X α (stoppingSet p) ω : ℝ) →
        ∀ η ∈ Metric.ball z r, |flowPartial p.X i j η s.toNNReal ω| ≤ k s ω) ∧
      (∀ α ∈ Metric.ball z r,
        IntervalIntegrable (fun t => q t ω) volume 0
          (finiteEntryTime p.X α (stoppingSet p) ω : ℝ)) ∧
      (∀ α ∈ Metric.ball z r, ∀ (t : ℝ), 0 ≤ t →
        t ≤ (finiteEntryTime p.X α (stoppingSet p) ω : ℝ) →
        IntervalIntegrable (fun s => k s ω) volume 0 t ∧
        ∀ β ∈ Metric.ball z r, ∀ γ ∈ Metric.ball z r,
          Real.exp (-(discount p β t.toNNReal ω)) *
            |p.H (p.X γ t.toNNReal ω)| *
            (∫ s in (0 : ℝ)..t, k s ω) ≤ q t ω) ∧
      (∀ α ∈ Metric.ball z r,
        (∫ t in (0 : ℝ)..(finiteEntryTime p.X α (stoppingSet p) ω : ℝ),
          q t ω) ≤ g ω))

/-- One radius works for every coordinate pair and all four source bounds. -/
noncomputable def LocalBounds (p : StoppingProblem d Ω P 𝔽)
    (z : State d) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ i j : Fin d,
    Bound44 p z r i j ∧ Bound45 p z r i j ∧
    Bound46 p z r i j ∧ Bound47 p z r i j

/-- The right limit of the spatial flow derivative at time zero, p. 12. -/
noncomputable def InitialDerivativeAt (p : StoppingProblem d Ω P 𝔽)
    (z : State d) : Prop :=
  ∀ᵐ ω ∂P, ∀ i j : Fin d,
    Tendsto (fun t : ℝ≥0 => flowPartial p.X i j z t ω)
      (𝓝[Set.Ioi 0] 0) (𝓝 (if i = j then (1 : ℝ) else 0))

/-- The pointwise hypotheses of Theorem 8, including its two alternatives. -/
noncomputable def BoundaryHypotheses (p : StoppingProblem d Ω P 𝔽)
    (z : State d) : Prop :=
  LocalBounds p z ∧ InitialDerivativeAt p z ∧
    ((IsStrongFeller p.X P ∧ IsProbRegular p.X P (stoppingSet p) z) ∨
      IsProbRegular p.X P (interior (stoppingSet p)) z)

/-- Common hypotheses (4.1)-(4.3) and C¹ spatial-flow regularity. -/
noncomputable def Theorem8Common (p : StoppingProblem d Ω P 𝔽) : Prop :=
  WellPosed p ∧
  HasGeneratorForm p ∧
  Continuous (value p) ∧ ContDiffOn ℝ 1 (value p) (continuationSet p) ∧
  ContDiff ℝ 1 p.G ∧
  (∃ K : ℝ, 0 < K ∧ ∀ x y : State d,
    |p.H x - p.H y| ≤ K * ‖x - y‖ ∧
    |p.rate x - p.rate y| ≤ K * ‖x - y‖) ∧
  IsC1Flow p.X P

end OptStopC1.SpaceDeriv


