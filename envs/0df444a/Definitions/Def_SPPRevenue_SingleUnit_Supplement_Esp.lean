-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_Esp
-- name    : SPPRevenue_SingleUnit_Supplement_Esp
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:12:07.738695+00:00
-- url     : https://prove2.me/theorems/58d1a48b-982f-42f7-b7e0-0b00d7553ba5
-- title:
--   §7, p. 26 — the eager second-price auction ESP(p) and its revenue
-- statement:
--   **Eager second-price auction ESP(p)** for nonnegative reserves $p_i\ge0$ (§7, p. 26) with personalized reserve prices $p=(p_1,\dots,p_n)$:
--
--   1. every buyer bids its value $v_i$;
--   2. buyers with $v_i<p_i$ are eliminated first, leaving $S=\{i:v_i\ge p_i\}$;
--   3. the item goes to $i^\star=\arg\max_{i\in S}v_i$, who pays $\max(p_{i^\star},\max_{i\in S,i\ne i^\star}v_i)$; other buyers pay $0$, and nobody pays if $S=\emptyset$.
--
--   $\mathrm{ESP}(p)$ is the expected payment when the values are independent, $v_i\sim\mu_i$.
--
--   ESP auctions are the second mechanism family whose revenue Theorems 5 and 6 compare with the optimal revenue.
--
--   **Formalization Note** Ties for the highest value in $S$ go to the lowest index; the payment does not depend on the tie-break, since a tied competitor's value equals the winner's. When $i^\star$ is the only survivor, the inner maximum is over the empty set and is $0$ in $[0,\infty]$, so the payment is $p_{i^\star}$. Revenues are in $[0,\infty]$. Outside the nonnegative-reserve domain the Lean definition clips negative payments to zero; no using theorem makes a claim on that domain.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, p. 26, §7, Eager Second-Price Auctions ESP(p)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

open Classical in
/-- The buyers who clear their reserve prices in ESP(p): `S = {i : v_i ≥ p_i}` (§7, p. 26). -/
noncomputable def espSurvivors {n : ℕ} (p v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≤ v i)

/-- Buyer `i` wins ESP(p) at `v`: `i ∈ S` has the highest value in `S` (ties to the lowest index). -/
def espWins {n : ℕ} (p v : Fin n → ℝ) (i : Fin n) : Prop :=
  i ∈ espSurvivors p v ∧ ∀ k ∈ espSurvivors p v, v k < v i ∨ (v k = v i ∧ i ≤ k)

open Classical in
/-- Revenue of the eager second-price auction ESP(p) at `v` (§7, p. 26): buyers with `v_i < p_i` are
eliminated first; the item goes to the highest-value survivor `i*`, who pays
`max(p_{i*}, max_{i ∈ S, i ≠ i*} v_i)` (only `p_{i*}` if `i*` is the only survivor); revenue `0` if
nobody survives. -/
noncomputable def espRevAt {n : ℕ} (p v : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ i, if espWins p v i then
      max (ENNReal.ofReal (p i)) (((espSurvivors p v).erase i).sup (fun k => ENNReal.ofReal (v k)))
    else 0

/-- `ESP(p)`, the expected revenue of ESP(p) under independent values `v ∼ Π μ_i`. -/
noncomputable def espRev {n : ℕ} (μ : Fin n → Measure ℝ) (p : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, espRevAt p v ∂(Measure.pi μ)

end SPPRevenue.SingleUnit.Supplement


