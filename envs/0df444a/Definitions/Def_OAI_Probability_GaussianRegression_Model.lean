-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Model
-- name    : OAI_Probability_GaussianRegression_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:31:22.554853+00:00
-- url     : https://prove2.me/theorems/c6d98813-f96c-46f4-9d74-bc9daf46fd36
-- title:
--   Success probability and memory lower-bound statements for streaming regression
-- statement:
--   Learners estimate an unknown unit vector $s\in S^{d-1}$ from $T$ noiseless observations $(x_i,\langle x_i,s\rangle)$ with standard Gaussian $x_i$, using $M$ bits of memory and a random seed $\omega$ drawn from a probability law $\rho$.
--
--   1. **Success.** The success probability at $s$ is the probability, over seeds and samples, that the angular error of the estimate is at most $\varepsilon$:
--   $$
--   \mathrm{succ}_\varepsilon(s)=(\rho\otimes\mathrm{samples})\bigl\{\angle(s,\hat s)\le\varepsilon\bigr\}.
--   $$
--   2. **Subquadratic memory statement.** There is $c>0$ such that for every memory budget $M(d)=o(d^2)$, eventually in $d$, every admissible learner with $\varepsilon\le\frac1{10}$ whose average success, or pointwise success for every $s$, is at least $\frac23$ needs $T\ge c\,d\log(1/\varepsilon)$ samples.
--   3. **Fixed quadratic memory statement.** For each $A_0>0$ there are $c>0$ and $d_0$ such that for $d\ge d_0$ and $M\le A_0d^2$, average success at least $\frac23$ forces $T\ge c\,d\log(1/\varepsilon)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments

namespace OAI

/-!
Finite-state Gaussian regression with noiseless labels and angular accuracy.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

namespace Learner

def success {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) (s : UnitSphere d) : ℝ≥0∞ :=
  (ρ.prod (sampleLaw d T))
    {z | angularError s (L.estimate s z.1 z.2) ≤ ε}

end Learner

def SubquadraticMemory : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ → ℕ,
    Asymptotics.IsLittleO atTop (fun d => (M d : ℝ)) (fun d => (d : ℝ) ^ 2) →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ T : ℕ, ∀ ε : ℝ,
    0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d (M d) T Ω, L.Admissible ρ →
    (((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε ∨
      ∀ s, ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.success ρ ε s) →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

def FixedQuadraticMemory : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ,
    ∀ d : ℕ, d₀ ≤ d → ∀ M T : ℕ, (M : ℝ) ≤ A₀ * (d : ℝ) ^ 2 →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (ρ : Measure Ω), IsProbabilityMeasure ρ →
    ∀ L : Learner d M T Ω, L.Admissible ρ →
    ((2 : ℕ) / (3 : ℕ) : ℝ≥0∞) ≤ L.uniformSuccess ρ ε →
    c * (d : ℝ) * Real.log (1 / ε) ≤ (T : ℝ)

end NoiselessRegression

end

end OAI


