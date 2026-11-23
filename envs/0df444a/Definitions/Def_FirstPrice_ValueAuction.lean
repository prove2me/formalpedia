-- Prove2me | Definitions.Def_FirstPrice_ValueAuction
-- name    : FirstPrice_ValueAuction
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:42:27.617795+00:00
-- url     : https://prove2.me/theorems/4e5c7c8a-5f62-443c-8ab8-0650125a8be5
-- title:
--   Single-unit first-price value auction with arbitrary measurable tie rules
-- statement:
--   This module defines the independent-private-value single-unit first-price auction in the same mixed-kernel formalism as the procurement mission. There are $n+1$ bidders, independent real private values, Markov mixed strategies, and an arbitrary measurable tie kernel. Applying a procurement lowest-bid tie kernel to the negated bid vector makes it a highest-bid rule.
--
--   For bidder $i$, value $v_i$, and bid $b$, the interim utility is
--   $$u_i(v_i,b)=(v_i-b)\,x_i(b),$$
--   where $x_i(b)$ integrates winning against the independent marginal bid laws. `FirstPrice.IsBNE` requires nonnegative bids, no overbidding, and exact best response to every nonnegative real deviation at almost every bid used by every declared type. The module also defines expected equilibrium welfare, expected maximum value, and the nonempty finite maximum. Values may be bounded by separate theorem hypotheses; the structural definitions themselves do not impose a bound.
--
--   **Formalization Note** Reusing `IndependentTypes`, `MixedProfile`, `playLaw`, and `TieRule` avoids a second probability model and permits direct measure-preserving transformations to and from procurement instances. Extended-nonnegative-real integrals allow arbitrary laws, while value bounds needed for finiteness belong in theorem statements.
-- source:
--   Jin and Lu model for a single-item first-price auction (Cristi procurement paper §2 and §4 with exact locations).
--   Palazzotto and Cristi, pp. 6 and 8–9 (printed pp. 4 and 6–7), §2 Model and §4 Bounded Bids and Reduction to the Value Auction.
--   Jin–Lu, Definition 1 (equilibrium) and Section 1 (first-price auction), arXiv:2207.01761.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction

open MeasureTheory ProbabilityTheory
open scoped Classical
open ProcurementPoA.DeterministicCap

namespace FirstPrice

/-- Largest of a nonempty finite vector of values. -/
noncomputable def highest {n : ℕ} (x : ProcurementPoA.DeterministicCap.Suppliers n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- Winning probability of a value bid against independent opponents. The generic
procurement tie kernel is evaluated on negated bids, hence selects a highest value bid. -/
noncomputable def win {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (i : Suppliers n) (b : ℝ) : ENNReal :=
  ∫⁻ bs, τ.select (fun j => -(Function.update bs i b j)) {i}
    ∂(Measure.pi (marginalBidLaw D σ))

/-- First-price utility; values and bids are real numbers. -/
noncomputable def utility {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (i : Suppliers n) (v b : ℝ) : ℝ :=
  (v - b) * (win D τ σ i b).toReal

/-- Exact mixed Bayes--Nash equilibrium with nonnegative bids, no overbidding,
and every nonnegative pure deviation tested simultaneously almost everywhere. -/
def IsBNE {n : ℕ} (D : IndependentTypes n) (τ : TieRule n) (σ : MixedProfile n) : Prop :=
  ∀ i, ∀ v ∈ D.types i, ∀ᵐ b ∂(σ.bid i v),
    0 ≤ b ∧ b ≤ v ∧ ∀ a : ℝ, 0 ≤ a → utility D τ σ i v a ≤ utility D τ σ i v b

/-- Expected value of the selected bidder under an arbitrary highest-bid tie rule. -/
noncomputable def welfare {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) : ENNReal :=
  ∫⁻ x, ∑ i, ENNReal.ofReal (x i).1 * τ.select (fun j => -(x j).2) {i}
    ∂(playLaw D σ)

/-- Expected maximum value. -/
noncomputable def optimalWelfare {n : ℕ} (D : IndependentTypes n) : ENNReal :=
  ∫⁻ v, ENNReal.ofReal (highest v) ∂(typeLaw D)

end FirstPrice


