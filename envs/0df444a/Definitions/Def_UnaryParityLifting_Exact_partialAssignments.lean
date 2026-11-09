-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_partialAssignments
-- name    : UnaryParityLifting_Exact_partialAssignments
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:09:40.537722+00:00
-- url     : https://prove2.me/theorems/d0d28c05-fcd7-4d5f-99fe-89986f3ffca9
-- title:
--   Output-independent paired partial assignments and completion laws
-- statement:
--   A partial assignment on $m$ coordinates fixes a bit at each selected coordinate and leaves a star at the others. A sampler pair is $(\sigma_0,\sigma_1)$. A pair law gives one nonnegative real atom weight to every such pair, with total weight one. It has no desired-output parameter.
--
--   Filling all stars independently and uniformly gives the conditional probability
--   $$q_\tau(x)=2^{-s(\tau)}\mathbf 1\{x\text{ agrees with every fixed bit of }\tau\},$$
--   where $s(\tau)$ counts stars. With no stars this is a point mass. For a law $\mu$, its completion law at output $b$ is $\sum_\sigma\mu(\sigma)q_{\sigma_b}(x)$, and its star probability at coordinate $j$ is $\sum_\sigma\mu(\sigma)\mathbf 1\{\sigma_b(j)=*\}$.
--
--   These are finite sums, so no measurability or integrability convention is needed. The common-star property and equality to uniform gadget-fiber sampling are conclusions of Lemma 3.6, not fields of the definition. Choosing one law before $b$ expresses the source's independence from the desired output.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), citation_basis: published; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/567.pdf; pp.9–10, Section 3.1, Lemma 3.6 and equation (3.4)

import Mathlib
import Definitions.Def_UnaryParityLifting_Exact_averaging

namespace UnaryParityLifting.Exact

open scoped BigOperators

/-- none is a free star; some b fixes the coordinate to b. -/
abbrev PartialAssignment (m : ℕ) := Fin m → Option Bool

abbrev SamplerPair (m : ℕ) := PartialAssignment m × PartialAssignment m

def selectPartial {m : ℕ} (σ : SamplerPair m) (b : Bool) : PartialAssignment m :=
  if b then σ.2 else σ.1

/-- One finite probability law on pairs; there is no output-bit parameter. -/
structure PairLaw (m : ℕ) where
  probability : SamplerPair m → NNReal
  total_one : ∑ σ, probability σ = 1

/-- Uniform independent filling of all free bits, even if there are none. -/
noncomputable def completionProbability {m : ℕ} (τ : PartialAssignment m)
    (x : Fin m → Bool) : ℝ := by
  classical
  exact if ∀ j b, τ j = some b → x j = b then
    ((2 : ℝ) ^ ((Finset.univ.filter (fun j => τ j = none)).card))⁻¹ else 0

noncomputable def starProbability {m : ℕ} (μ : PairLaw m) (b : Bool) (j : Fin m) : ℝ :=
  ∑ σ : SamplerPair m, (μ.probability σ : ℝ) *
    (if selectPartial σ b j = none then 1 else 0)

/-- The mixture's atom probabilities, with independent uniform completion after drawing σ. -/
noncomputable def completionLaw {m : ℕ} (μ : PairLaw m) (b : Bool)
    (x : Fin m → Bool) : ℝ :=
  ∑ σ : SamplerPair m, (μ.probability σ : ℝ) * completionProbability (selectPartial σ b) x

end UnaryParityLifting.Exact


