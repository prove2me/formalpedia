-- Prove2me | Definitions.Def_BulowKlemperer429_Bundling_ScalarAuction
-- name    : BulowKlemperer429_Bundling_ScalarAuction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:45:17.264302+00:00
-- url     : https://prove2.me/theorems/f4785fc8-231b-45c6-9c0d-3f01f9e6e42c
-- title:
--   Single-object DSIC auctions and optimal k-bidder bundle revenue
-- statement:
--   A scalar auction among $k$ bidders specifies allocation probabilities $a_i(v)$ and payments $p_i(v)$ at every reported profile $v\in[0,\infty)^k$. Admissibility requires measurable allocations and payments, nonnegative allocations and payments, $\sum_i a_i(v)\le1$, ex-post individual rationality, and dominant-strategy truthfulness against every unilateral report.
--
--   For a scalar law $F$, define
--   $$\mathrm{REV}_k(F)=\sup_A\sum_{i=1}^k\mathbb E[p_i(V)],\qquad \mathrm{BREV}_k(D)=\mathrm{REV}_k(\operatorname{law}(S)),$$
--   where the supremum ranges over admissible scalar auctions and bidders are independent draws from $F$.
--
--   This provides the optimal scalar-auction benchmark used in Lemma 2.1, allowing lotteries, reserves and ironing. The DSIC reading follows Appendix A, p. 23. Payment normalization permits the nonnegative-payment convention without reducing optimal revenue. Expected payments and the supremum are extended nonnegative reals.
-- source:
--   Yichen Huang, STOC 2027 submission #429 (October 2026), p. 7, §2, REV_k and BREV_k; Appendix A p. 23 (PDF p. 24) (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/429.pdf

import Mathlib
import Definitions.Def_BulowKlemperer429_Bundling_Revenue
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace BulowKlemperer429.Bundling

/-- A single-object auction among k bidders, with allocation probabilities and payments. -/
structure ScalarAuction (k : ℕ) where
  allocation : (Fin k → ℝ≥0) → Fin k → ℝ
  payment : (Fin k → ℝ≥0) → Fin k → ℝ

/-- Feasible, measurable, DSIC, ex-post IR auctions with nonnegative payments.
Section 2 p. 7, with the auction-class reading specified in Appendix A p. 23. -/
def ScalarAuction.IsAdmissible {k : ℕ} (A : ScalarAuction k) : Prop :=
  (∀ i, Measurable (fun v => A.allocation v i) ∧ Measurable (fun v => A.payment v i)) ∧
  (∀ v i, 0 ≤ A.allocation v i ∧ 0 ≤ A.payment v i) ∧
  (∀ v, ∑ i, A.allocation v i ≤ 1) ∧
  (∀ v i, 0 ≤ (v i : ℝ) * A.allocation v i - A.payment v i) ∧
  (∀ v i t, (v i : ℝ) * A.allocation (Function.update v i t) i -
      A.payment (Function.update v i t) i ≤
      (v i : ℝ) * A.allocation v i - A.payment v i)

noncomputable def scalarAuctionRevenue {k : ℕ} (F : Measure ℝ≥0)
    (A : ScalarAuction k) : ℝ≥0∞ :=
  ∑ i, ∫⁻ v, ENNReal.ofReal (A.payment v i) ∂Measure.pi (fun _ : Fin k => F)

noncomputable def REVk (k : ℕ) (F : Measure ℝ≥0) : ℝ≥0∞ :=
  ⨆ (A : ScalarAuction k) (_ : A.IsAdmissible), scalarAuctionRevenue F A

noncomputable def BREVk {ι : Type} [Fintype ι] (k : ℕ)
    (ν : ι → Measure ℝ≥0) : ℝ≥0∞ := REVk k (bundleLaw ν)

end BulowKlemperer429.Bundling


