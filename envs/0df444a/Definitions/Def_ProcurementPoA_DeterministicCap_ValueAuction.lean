-- Prove2me | Definitions.Def_ProcurementPoA_DeterministicCap_ValueAuction
-- name    : ProcurementPoA_DeterministicCap_ValueAuction
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-23T02:31:14.639161+00:00
-- url     : https://prove2.me/theorems/3916892f-acbe-43e5-b21f-5c127784c6e0
-- title:
--   First-price value auction with measurable type-dependent values
-- statement:
--   This module encodes a single-item first-price auction with a nonempty finite set of bidders. A bidder's private type $c$ is real-valued, types are independent, and her value is a measurable deterministic function $v_i(c)$. Mixed bids are independent conditional on types. A measurable randomized tie rule always selects a highest bidder.
--
--   The standing action convention extends the usual nonnegative bid domain to all real bids by rejecting every negative bid. Thus a negative bid has zero winning probability and contributes zero welfare. Used bids satisfy the no-overbidding condition $\beta\le v_i(c)$ almost surely. Equilibrium is typewise: almost every used bid maximizes interim utility against every real deviation.
--
--   This rejected-negative-bid convention is useful for the transformation $\beta=T-b$, $v_i(c)=(T-c)_+$ in Appendix A.1.1 of Palazzotto–Cristi. Unlike the clipped transformation $(T-b)_+$, it preserves the distinction between $b=T$ and $b>T$, so no exceptional zero-bid tie priority is required.
--
--   **Formalization Note** Private types and mixed profiles reuse `IndependentTypes` and `MixedProfile`; no boundedness or nonnegativity of values is baked into the structure and is instead supplied as a hypothesis to theorems.
-- source:
--   Y. Jin and P. Lu, First Price Auction is 1−1/e² Efficient, J. ACM 70(5), 2023, Theorem 1, standard independent-private-value first-price auction model; S. Palazzotto and A. Cristi, STOC 2027 submission 293, Appendix A.1.1, p.16 (PDF p.18), value-auction transformation. The real-bid extension rejects precisely the additional negative actions.

import Mathlib
import Definitions.Def_ProcurementPoA_DeterministicCap_Auction

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace ProcurementPoA.DeterministicCap.ValueAuction

/-- Nonempty finite maximum. -/
noncomputable def highest {n : ℕ} (x : Suppliers n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- A randomized tie rule selecting a highest bidder. Negative bids are later rejected. -/
structure TieRule (n : ℕ) where
  select : Kernel (Suppliers n → ℝ) (Suppliers n)
  markov : IsMarkovKernel select
  highest_only : ∀ b, ∀ᵐ i ∂(select b), ∀ j, b j ≤ b i

instance {n : ℕ} (τ : TieRule n) : IsMarkovKernel τ.select := τ.markov

/-- Probability of winning at a pure bid; negative bids are rejected. -/
noncomputable def interimWin {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (i : Suppliers n) (b : ℝ) : ENNReal :=
  if 0 ≤ b then
    ∫⁻ bs, τ.select (Function.update bs i b) {i} ∂(Measure.pi (marginalBidLaw D σ))
  else 0

/-- Utility in the first-price value auction, with measurable deterministic values of types. -/
noncomputable def utility {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (v : Suppliers n → ℝ → ℝ)
    (i : Suppliers n) (c b : ℝ) : ℝ :=
  (v i c - b) * (interimWin D τ σ i b).toReal

/-- Used bids do not exceed value. Negative used bids are permitted but rejected. -/
def NoOverbidding {n : ℕ} (D : IndependentTypes n) (σ : MixedProfile n)
    (v : Suppliers n → ℝ → ℝ) : Prop :=
  ∀ i, ∀ c ∈ D.types i, ∀ᵐ b ∂(σ.bid i c), b ≤ v i c

/-- Typewise mixed BNE; every real deviation is tested, with negative bids rejected. -/
def IsBNE {n : ℕ} (D : IndependentTypes n) (τ : TieRule n)
    (σ : MixedProfile n) (v : Suppliers n → ℝ → ℝ) : Prop :=
  NoOverbidding D σ v ∧ IsTypewiseBestResponse D σ (utility D τ σ v)

/-- Allocated value; a selected negative bid contributes zero. -/
noncomputable def welfare {n : ℕ} (τ : TieRule n) (v : Suppliers n → ℝ → ℝ)
    (x : Suppliers n → ℝ × ℝ) : ENNReal :=
  ∑ i, (if 0 ≤ (x i).2 then
    ENNReal.ofReal (v i (x i).1) * τ.select (fun j => (x j).2) {i} else 0)

end ProcurementPoA.DeterministicCap.ValueAuction


