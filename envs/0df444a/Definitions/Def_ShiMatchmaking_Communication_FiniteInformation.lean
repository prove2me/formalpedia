-- Prove2me | Definitions.Def_ShiMatchmaking_Communication_FiniteInformation
-- name    : ShiMatchmaking_Communication_FiniteInformation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:46:42.442755+00:00
-- url     : https://prove2.me/theorems/3dd00cda-f011-4767-b327-1ccb43db0703
-- title:
--   Finite laws, conditional masses, and mutual information in bits
-- statement:
--   For a finite sample space $\Omega$ with real probability masses $w_\omega$, expectation is $\sum_\omega w_\omega f(\omega)$ and event probability is the sum of its masses. Pushforward mass at $z$ is the sum over inputs mapped to $z$. Conditional mass divides the joint event mass by the conditioning-event probability; uses in the mission have strictly positive denominators.
--
--   For finite-range random variables $X,Y$, mutual information in bits is
--   $$I(X;Y)=\sum_x\sum_y p_{xy}\log_2\frac{p_{xy}}{p_xp_y},$$
--   where the joint and marginal masses are computed from $w$ and each zero joint mass contributes zero. The sums range once over each value in the finite images, even when the ambient type of messages is infinite. Full $L^1$ distance is $\sum_z|p_z-q_z|$ over the common finite image, not half of that quantity.
--
--   The independent Bernoulli product mass on a finite coordinate set $K$ is $\prod_k d_k^{x_k}(1-d_k)^{1-x_k}$, implemented by a case distinction on each flag. At parameters zero and one deterministic coordinates are retained. These formulas accept raw real weights, and have their probability interpretation when the weights are nonnegative and sum to one; the binary market constructs precisely those weights in every theorem regime. For positive joint mass its marginal factors are positive, so no logarithm or division totalization changes mutual information there.
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; §2.2, p. 8; Appendix D.5, pp. 40–43, equations (D.33), (D.35)–(D.36), (D.43)–(D.54).

import Mathlib

noncomputable section

namespace ShiMatchmaking.Communication

/-- Finite expectation with explicit real probability masses. -/
def expectation {Ω : Type} [Fintype Ω] (w f : Ω → ℝ) : ℝ :=
  ∑ ω, w ω * f ω

/-- Probability of an event; all events on a finite space are measurable. -/
def probability {Ω : Type} [Fintype Ω] (w : Ω → ℝ) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then w ω else 0

/-- Actual pushforward mass, allowing an infinite ambient codomain. -/
def mass {Ω Z : Type} [Fintype Ω] (w : Ω → ℝ) (f : Ω → Z) (z : Z) : ℝ :=
  probability w (fun ω => f ω = z)

/-- Conditional probability mass. Used only for positive-probability events. -/
def conditionalMass {Ω Z : Type} [Fintype Ω] (w : Ω → ℝ)
    (f : Ω → Z) (E : Ω → Prop) (z : Z) : ℝ :=
  probability w (fun ω => E ω ∧ f ω = z) / probability w E

/-- The full L1 distance, summed once over each value in the common finite range. -/
def rangeL1 {Ω Z : Type} [Fintype Ω] (f : Ω → Z) (p q : Z → ℝ) : ℝ := by
  classical
  exact ∑ z ∈ Finset.univ.image f, |p z - q z|

/-- Mutual information in bits, from the actual joint and marginal masses.
Zero joint masses contribute zero. -/
def mutualInformationBits {Ω X Y : Type} [Fintype Ω] (w : Ω → ℝ)
    (f : Ω → X) (g : Ω → Y) : ℝ := by
  classical
  exact ∑ x ∈ Finset.univ.image f, ∑ y ∈ Finset.univ.image g,
    let p := mass w (fun ω => (f ω, g ω)) (x, y)
    if p = 0 then 0 else p * Real.logb 2 (p / (mass w f x * mass w g y))

/-- Product of independent Bernoulli coordinate masses; parameters in [0,1]
give a probability law, including deterministic coordinates at the endpoints. -/
def bernoulliProduct {K : Type} [Fintype K] (d : K → ℝ) (x : K → Bool) : ℝ :=
  ∏ k, if x k then d k else 1 - d k

end ShiMatchmaking.Communication


