-- Prove2me | Definitions.Def_MajorityAttack_NegCost_Fees
-- name    : MajorityAttack_NegCost_Fees
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:36.806463+00:00
-- url     : https://prove2.me/theorems/a4141e6d-f13f-401d-86ae-c72392b0ab2e
-- title:
--   §4.3 — top-b transaction fees and their expected block value
-- statement:
--   A block can hold at most $b$ unit-size transactions. For a vector of $n$ available nonnegative fees $\varphi$, define its block fee as the greatest sum over sets of at most $b$ transactions:
--
--   $$T_b(\varphi)=\max_{S\subseteq\{1,\ldots,n\},\ |S|\le b}\sum_{t\in S}\varphi_t.$$
--
--   If the fees are independent with common probability law $\mu$, the expected block fee is $\Phi_b(n)=\mathbb E[T_b(\varphi)]$. A fee law used for the strict comparison is a probability law concentrated on nonnegative values, with a finite first moment and support containing more than one point. This definition supplies the fee model for Lemma 2 and Proposition 1.
--
--   **Formalization Note** The maximum includes the empty set. With nonnegative fees and $b\le n$, it is the sum of the $b$ highest fees. The finite first moment guarantees that the real-valued expectation is integrable.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, pp. 11–13, §4.3 and proof of Lemma 2

import Mathlib

namespace MajorityAttack.NegCost

open MeasureTheory

/-- Sum of the largest at most `b` fees among `n` available transactions. -/
noncomputable def topFees (b : ℕ) {n : ℕ} (φ : Fin n → ℝ) : ℝ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card ≤ b)).sup'
    ⟨∅, by simp⟩ (fun s => ∑ t ∈ s, φ t)

/-- Expected fees in a block whose `n` transaction fees are independent with law `μ`. -/
noncomputable def blockFees (μ : Measure ℝ) (b n : ℕ) : ℝ :=
  ∫ φ, topFees b φ ∂(Measure.pi fun _ : Fin n => μ)

/-- The common nonnegative, integrable, non-degenerate fee law used in §4.3. -/
structure FeeLaw (μ : Measure ℝ) : Prop where
  prob : IsProbabilityMeasure μ
  nonneg : μ (Set.Iio 0) = 0
  integrable : Integrable id μ
  nondegenerate : ∀ a : ℝ, μ ≠ Measure.dirac a

end MajorityAttack.NegCost


