-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_ProbabilityModel
-- name    : ProcurementPoA_DeterministicCap_ProbabilityModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:16.80851+00:00
-- url     : https://prove2.me/theorems/1ff37fef-a08a-4b10-b863-1bd20f4962cd
-- title:
--   Independent private types and mixed best responses
-- statement:
--   There are $n+1$ players, with $n$ an arbitrary natural number. Player $i$ has a Borel probability law $\mu_i$ on a measurable real type domain $D_i$, with $\mu_i(D_i)=1$. A mixed strategy is a Markov kernel $\sigma_i(c,db)$ from the private real type to a real action. Types are independent and each player's randomization depends only on her own type. Thus the joint law of type-action pairs is
--
--   $$P_\sigma=\bigotimes_i[\mu_i(dc_i)\sigma_i(c_i,db_i)].$$
--
--   The marginal action law integrates $\sigma_i$ against $\mu_i$. For an interim payoff $u_i(c,b)$, typewise best response means, for every player and every $c\in D_i$, that $\sigma_i(c)$-almost every drawn action maximizes $u_i(c,\cdot)$ against all real pure deviations simultaneously. This separates the general private-type probability and best-response objects from the auction rule. Laws may have atoms; Dirac kernels include pure strategies.
--
--   **Formalization Note** The source's phrase “bid used” is read probabilistically, rather than as every point of topological support. The quantifier over private types remains universal on the declared domain. Kernels are defined on all reals, extending their values off the measurable type domain without affecting play. Indexing by $\operatorname{Fin}(n+1)$ covers all nonempty finite populations.
-- source:
--   Simone Palazzotto, Andrés Cristi, STOC 2027 submission #293 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/293.pdf, §2, printed p. 4 (PDF p. 6)

import Mathlib

namespace ProcurementPoA.DeterministicCap

open MeasureTheory ProbabilityTheory

/-- There are n+1 suppliers; the index includes every nonempty finite population. -/
abbrev Suppliers (n : ℕ) := Fin (n + 1)

/-- Independent real private types with an explicit measurable domain of possible types.
The probability laws may have atoms and need not have densities. -/
structure IndependentTypes (n : ℕ) where
  types : Suppliers n → Set ℝ
  measurable_types : ∀ i, MeasurableSet (types i)
  law : Suppliers n → Measure ℝ
  probability : ∀ i, IsProbabilityMeasure (law i)
  concentrated : ∀ i, law i (types i)ᶜ = 0

instance {n : ℕ} (D : IndependentTypes n) (i : Suppliers n) :
    IsProbabilityMeasure (D.law i) := D.probability i

/-- Independently randomized real actions, depending measurably only on own type. -/
structure MixedProfile (n : ℕ) where
  bid : Suppliers n → Kernel ℝ ℝ
  markov : ∀ i, IsMarkovKernel (bid i)

instance {n : ℕ} (σ : MixedProfile n) (i : Suppliers n) :
    IsMarkovKernel (σ.bid i) := σ.markov i

/-- The product law of independent private types. -/
noncomputable def typeLaw {n : ℕ} (D : IndependentTypes n) :
    Measure (Suppliers n → ℝ) := Measure.pi D.law

/-- The marginal action law, mixing over the player's own private type. -/
noncomputable def marginalBidLaw {n : ℕ} (D : IndependentTypes n)
    (σ : MixedProfile n) (i : Suppliers n) : Measure ℝ := σ.bid i ∘ₘ D.law i

instance {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) (i : Suppliers n) :
    IsProbabilityMeasure (marginalBidLaw D σ i) := by
  unfold marginalBidLaw
  infer_instance

/-- Independent draws of each player's (type, own action) pair. -/
noncomputable def playLaw {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n) :
    Measure (Suppliers n → ℝ × ℝ) := Measure.pi fun i => D.law i ⊗ₘ σ.bid i

/-- Generic typewise mixed best response to a specified interim payoff.
The almost-everywhere quantifier concerns drawn actions, not private types.
All pure deviations are tested simultaneously at almost every used action. -/
def IsTypewiseBestResponse {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n)
    (u : Suppliers n → ℝ → ℝ → ℝ) : Prop :=
  ∀ i, ∀ c ∈ D.types i, ∀ᵐ b ∂(σ.bid i c), ∀ a : ℝ, u i c a ≤ u i c b

end ProcurementPoA.DeterministicCap


