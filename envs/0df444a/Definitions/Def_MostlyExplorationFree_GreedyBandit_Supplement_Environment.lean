-- Prove2me | Definitions.Def_MostlyExplorationFree_GreedyBandit_Supplement_Environment
-- name    : MostlyExplorationFree_GreedyBandit_Supplement_Environment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:45:06.933731+00:00
-- url     : https://prove2.me/theorems/b4451354-e590-4383-9a0a-e36d127604b3
-- title:
--   §2 — finite linear contextual bandit environment and standing probability model
-- statement:
--   A finite linear contextual bandit has arms $i\in[K]$, parameters $\beta_i\in\mathbb R^d$, and independent, identically distributed contexts $X_t$ with law $\mu$. Its potential rewards are
--   $$Y_{i,t}=X_t^\top\beta_i+\varepsilon_{i,t}.$$
--   The noises are mutually independent and independent of the contexts, and satisfy the mean-zero two-sided subgaussian MGF bound with variance proxy $\sigma^2$. Independent uniform random permutations order arms for tie-breaking. The joint random vector of initial estimates is measurable and independent of all these variables; its law may otherwise be arbitrary. Assumptions 1 and 2 are the parameter bound and the pairwise linear margin bound, respectively.
--
--   This policy-independent environment is shared by all three algorithms in the supplement. Distributional assumptions are in the separate predicate IsModel; boundedness and the margin condition remain separate predicates.
--
--   **Formalization Note** Arms are Fin K with paper arm $i+1$ represented by $i$, periods start at 1, and vectors use the published Euclidean norm. The probability law need not have a density, consistently with the discrete examples on pp. 9–11. Definition 1's positive-only MGF convention is repaired to a two-sided bound as required by the estimation proofs. Uniform indices of all permutations provide uniform choices among any tied subset. The initial estimates may be dependent across arms. The general K-arm margin predicate is referenced from BastaniBayati.LassoBandit.Model: its body is exactly Assumption 2 here and carries no norm, sparsity or compatibility assumption from that model.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, pp. 7–8, §2, Definition 1, Assumptions 1–2; p. 22, Algorithm 3

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_BastaniBayati_LassoBandit_Model

namespace MostlyExplorationFree.GreedyBandit.Supplement

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A uniform index of the permutations gives a uniform ordering of the arms. -/
abbrev TieIndex (K : ℕ) := Fin (Fintype.card (Equiv.Perm (Fin K)))

/-- The general finite linear contextual bandit, separate from any policy. Times start at 1.
Initial estimates have an arbitrary joint law, independent of the observation sequences. -/
structure Environment (Ω : Type*) (d K : ℕ) where
  β : Fin K → Fin d → ℝ
  X : ℕ → Ω → Fin d → ℝ
  ε : Fin K → ℕ → Ω → ℝ
  W : ℕ → Ω → TieIndex K
  initial : Ω → Fin K → Fin d → ℝ

abbrev PrimitiveIndex (K : ℕ) := (ℕ ⊕ (Fin K × ℕ)) ⊕ (ℕ ⊕ Unit)

@[instance_reducible] def primitiveSigma {Ω : Type*} {d K : ℕ} (E : Environment Ω d K) :
    PrimitiveIndex K → MeasurableSpace Ω :=
  Sum.elim
    (Sum.elim (fun t => MeasurableSpace.comap (E.X (t + 1)) inferInstance)
      (fun p => MeasurableSpace.comap (E.ε p.1 (p.2 + 1)) inferInstance))
    (Sum.elim (fun t => MeasurableSpace.comap (E.W (t + 1)) inferInstance)
      (fun _ => MeasurableSpace.comap E.initial inferInstance))

/-- The standing independent, identically distributed context and independent noise model.
The subgaussian MGF bound is two-sided; no density is required for the context law. -/
structure IsModel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d K : ℕ}
    (μ : Measure (Fin d → ℝ)) (E : Environment Ω d K) (σ : ℝ) : Prop where
  isProbability : IsProbabilityMeasure P
  measurable_X : ∀ t, Measurable (E.X t)
  law_X : ∀ t, 1 ≤ t → P.map (E.X t) = μ
  measurable_ε : ∀ i t, Measurable (E.ε i t)
  subgaussian_ε : ∀ i t, 1 ≤ t → HasSubgaussianMGF (E.ε i t) (σ ^ 2).toNNReal P
  measurable_W : ∀ t, Measurable (E.W t)
  uniform_W : ∀ t, 1 ≤ t → ∀ w, P {ω | E.W t ω = w} =
    (Fintype.card (Equiv.Perm (Fin K)) : ℝ≥0∞)⁻¹
  measurable_initial : Measurable E.initial
  indep : iIndep (primitiveSigma E) P

/-- Assumption 1 for K arms. -/
def ParameterSet {d K : ℕ} (μ : Measure (Fin d → ℝ))
    (β : Fin K → Fin d → ℝ) (xmax bmax : ℝ) : Prop :=
  0 < xmax ∧ (∀ᵐ x ∂μ, l2norm x ≤ xmax) ∧ ∀ i, l2norm (β i) ≤ bmax

/-- The context, noise and random ordering at local time t are those at absolute time r+t. -/
def Environment.shift {Ω : Type*} {d K : ℕ} (E : Environment Ω d K) (r : ℕ) :
    Environment Ω d K where
  β := E.β
  X t := E.X (r + t)
  ε i t := E.ε i (r + t)
  W t := E.W (r + t)
  initial := E.initial

end MostlyExplorationFree.GreedyBandit.Supplement


