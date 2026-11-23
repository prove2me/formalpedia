-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_Mechanism
-- name    : SPPRevenue_SingleUnit_Supplement_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:12:19.527889+00:00
-- url     : https://prove2.me/theorems/0ec91421-b1ea-4ad0-8391-da0056a7f39a
-- title:
--   §3.1, §6.1, pp. 9, 20–21 — direct mechanisms, truthfulness, individual rationality, optimality, unit feasibility, threshold mechanisms
-- statement:
--   The benchmark mechanisms of §3.1 and §6.1, for $n$ buyers with independent values $v_i\sim\mu_i$.
--
--   1. **Direct mechanism.** Maps reported values $v$ to an (expected) allocation $x_i(v)$ (units, or expected clicks) and an (expected) payment $\pi_i(v)$ for each buyer.
--   2. **Truthful and individually rational** for a feasibility constraint on allocation vectors: allocations and payments are measurable and integrable at every report; the allocation is feasible at every reported profile; for all values $v_i$ and reports $\hat v_i$ (p. 21)
--   $$\mathbb E_{v_{-i}}\big[x_i(v_i,v_{-i})v_i-\pi_i(v_i,v_{-i})\big]\ \ge\ \mathbb E_{v_{-i}}\big[x_i(\hat v_i,v_{-i})v_i-\pi_i(\hat v_i,v_{-i})\big];$$
--   and the interim expected utility of reporting truthfully is nonnegative.
--   3. **Revenue and optimality.** The revenue is the signed extended expectation $\mathbb E[\sum_i\pi_i(v)]$, obtained from separate lower integrals of the positive and negative parts. For each individual expected payment and for total revenue, the class excludes the undefined case in which both parts are infinite. A mechanism is *optimal* when it is truthful and individually rational and its revenue is at least that of every truthful, individually rational mechanism.
--   4. **$H$-unit feasibility.** $0\le x_i\le1$ for all $i$ and $\sum_ix_i\le H$; this allows randomized allocations.
--   5. **Threshold mechanism.** For thresholds $t_i(v_{-i})$, buyer $i$ gets a unit and pays $t_i$ when $v_i\ge t_i$, and nothing otherwise (Lemma 1).
--
--   These objects state Lemma 6 and Theorem 4, where optimal mechanisms for $j$ units are combined into an optimal position-auction mechanism.
--
--   **Formalization Note** Truthfulness and individual rationality are interim (in expectation over the other buyers), as on p. 21, and are required for every real value and report. Payments must be integrable at each fixed report for the interim IC/IR expectations; global revenue may be infinite. The fields `payment_defined` and `revenue_defined` exclude undefined differences of two infinite expectations for each payment and for their sum; in particular, undefined individual payments cannot cancel to create an artificial revenue comparison.
--   The predicate `IsThresholdRepresentation μ M t` states that the actual mechanism and the weak-threshold formula have identical allocations and payments almost surely. The actual mechanism retains its feasible tie-breaking at every reported profile, including null tie profiles. This relation does not assume that a threshold perturbation preserves payments.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 9 (§3.1, Lemma 1), 20–21 (§6.1, truthfulness)

import Mathlib

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

/-- A direct mechanism for `n` single-parameter buyers (§3.1, p. 9; §6.1, p. 20): at the reported
profile `v` it gives buyer `i` the (expected) allocation `alloc v i` (units, or expected clicks)
and charges the (expected) payment `pay v i`. -/
structure DirectMech (n : ℕ) where
  alloc : (Fin n → ℝ) → Fin n → ℝ
  pay : (Fin n → ℝ) → Fin n → ℝ

/-- Buyer `i`'s interim expected allocation `E_{v_{-i}}[x_i(b, v_{-i})]` when reporting `b`. -/
noncomputable def interimAlloc {n : ℕ} (μ : Fin n → Measure ℝ) (M : DirectMech n) (i : Fin n)
    (b : ℝ) : ℝ :=
  ∫ v, M.alloc (Function.update v i b) i ∂(Measure.pi μ)

/-- Buyer `i`'s interim expected payment `E_{v_{-i}}[π_i(b, v_{-i})]` when reporting `b`. -/
noncomputable def interimPay {n : ℕ} (μ : Fin n → Measure ℝ) (M : DirectMech n) (i : Fin n)
    (b : ℝ) : ℝ :=
  ∫ v, M.pay (Function.update v i b) i ∂(Measure.pi μ)

/-- Positive and negative parts of total revenue. Their separate lower integrals permit infinite
expected revenue without assigning zero to a nonintegrable Bochner integral. -/
noncomputable def DirectMech.positiveRevenue {n : ℕ} (μ : Fin n → Measure ℝ)
    (M : DirectMech n) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (∑ i, M.pay v i) ∂(Measure.pi μ)

noncomputable def DirectMech.negativeRevenue {n : ℕ} (μ : Fin n → Measure ℝ)
    (M : DirectMech n) : ℝ≥0∞ :=
  ∫⁻ v, ENNReal.ofReal (-(∑ i, M.pay v i)) ∂(Measure.pi μ)

/-- Signed extended expected revenue. `IsTruthfulIR.revenue_defined` rules out the undefined
case in which both positive and negative parts have infinite expectation. -/
noncomputable def DirectMech.revenue {n : ℕ} (μ : Fin n → Measure ℝ) (M : DirectMech n) : EReal :=
  (M.positiveRevenue μ : EReal) - (M.negativeRevenue μ : EReal)

/-- A truthful, individually rational mechanism respecting the feasibility constraint `feasible` on
allocation vectors (§3.1, p. 9; §6.1, p. 21), for independent values `v ∼ Π μ_i`:
* allocations and payments are measurable and integrable at every fixed report of every buyer;
* each expected payment and total expected revenue are defined (their positive and negative
  parts are not both infinite);
* the allocation is feasible at every reported profile;
* truthfulness (p. 21): for all values `v_i` and reports `v̂_i`,
  `E[x_i(v_i, v_{-i}) v_i − π_i(v_i, v_{-i})] ≥ E[x_i(v̂_i, v_{-i}) v_i − π_i(v̂_i, v_{-i})]`;
* individual rationality: the interim expected utility of truthful reporting is nonnegative. -/
structure IsTruthfulIR {n : ℕ} (μ : Fin n → Measure ℝ) (feasible : (Fin n → ℝ) → Prop)
    (M : DirectMech n) : Prop where
  measurable_alloc : ∀ i, Measurable (fun v => M.alloc v i)
  measurable_pay : ∀ i, Measurable (fun v => M.pay v i)
  integrable_alloc : ∀ i b, Integrable (fun v => M.alloc (Function.update v i b) i) (Measure.pi μ)
  integrable_pay : ∀ i b, Integrable (fun v => M.pay (Function.update v i b) i) (Measure.pi μ)
  payment_defined : ∀ i,
    (∫⁻ v, ENNReal.ofReal (M.pay v i) ∂(Measure.pi μ)) ≠ ⊤ ∨
      (∫⁻ v, ENNReal.ofReal (-M.pay v i) ∂(Measure.pi μ)) ≠ ⊤
  revenue_defined : M.positiveRevenue μ ≠ ⊤ ∨ M.negativeRevenue μ ≠ ⊤
  feasible_all : ∀ v, feasible (M.alloc v)
  truthful : ∀ i (vi b : ℝ),
    interimAlloc μ M i b * vi - interimPay μ M i b ≤ interimAlloc μ M i vi * vi - interimPay μ M i vi
  ir : ∀ i (vi : ℝ), 0 ≤ interimAlloc μ M i vi * vi - interimPay μ M i vi

/-- `M` is an optimal mechanism (the benchmark Opt, §3.1, p. 9): truthful and individually rational,
with revenue at least that of every truthful, individually rational mechanism. -/
def IsOptimal {n : ℕ} (μ : Fin n → Measure ℝ) (feasible : (Fin n → ℝ) → Prop)
    (M : DirectMech n) : Prop :=
  IsTruthfulIR μ feasible M ∧
    ∀ M' : DirectMech n, IsTruthfulIR μ feasible M' → M'.revenue μ ≤ M.revenue μ

/-- `H`-unit feasibility for (possibly randomized) allocations (§3, p. 8): each buyer gets at most one
unit in expectation and at most `H` units are allocated: `x_i ∈ [0, 1]`, `Σ_i x_i ≤ H`. -/
def UnitFeasible {n : ℕ} (H : ℕ) (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ H

/-- The direct mechanism of thresholds `t` (Lemma 1, p. 9): buyer `i` gets a unit and pays
`t_i(v_{-i})` when `v_i ≥ t_i(v_{-i})`, and gets nothing and pays nothing otherwise. -/
noncomputable def thresholdMech {n : ℕ} (t : Fin n → (Fin n → ℝ) → ℝ) : DirectMech n where
  alloc v i := if t i v ≤ v i then 1 else 0
  pay v i := if t i v ≤ v i then t i v else 0

/-- A threshold formula represents the allocation and payment of an actual mechanism almost
surely. This keeps the mechanism's feasible tie-breaking at exceptional profiles separate from
the weak-threshold formula used to compute revenues and re-sampled prices (§3.1, pp. 10–11). -/
def IsThresholdRepresentation {n : ℕ} (μ : Fin n → Measure ℝ) (M : DirectMech n)
    (t : Fin n → (Fin n → ℝ) → ℝ) : Prop :=
  ∀ᵐ v ∂(Measure.pi μ), ∀ i,
    M.alloc v i = (thresholdMech t).alloc v i ∧ M.pay v i = (thresholdMech t).pay v i

end SPPRevenue.SingleUnit.Supplement


