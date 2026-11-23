-- Prove2me | Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiUnit
-- name    : SPPRevenue_SingleUnit_Supplement_MultiUnit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T20:10:41.759379+00:00
-- url     : https://prove2.me/theorems/9669157e-913e-4971-84dc-1f0dcfb3f78a
-- title:
--   §3 and §5, pp. 8–19, 34 — H-unit threshold mechanisms, SPP_H(p), MP and UP for H units, m(τ)
-- statement:
--   Objects of the multi-unit setting with $H$ identical units and $n$ unit-demand buyers with independent values $v_i\sim\mu_i$.
--
--   1. **$H$-unit threshold mechanism.** Thresholds $t_i(v_{-i})\ge0$, measurable and independent of buyer $i$'s own value, such that almost surely at most $H$ buyers have $v_i\ge t_i(v_{-i})$. Buyer $i$ wins and pays $t_i$ exactly when $v_i\ge t_i$; its expected revenue is $\mathbb E[\sum_i t_i\mathbf 1\{v_i\ge t_i\}]$ and $s^\star(\tau)=\sum_i\mathbb P[v_i\ge t_i\ge\tau]$, as in the single-unit setting.
--   2. **SPP$_H(p)$.** Buyers are approached in decreasing order of price (equal prices by index); each buyer with $v_i\ge p_i$ buys at $p_i$ while units remain. Buyer $i$ is served iff $v_i\ge p_i$ and fewer than $H$ accepting buyers precede it. $\mathrm{SPP}_H(p)$ is the expected sum of the prices paid.
--   3. **MP and UP for $H$ units.** MP is the expected revenue of SPP$_H$ with the Myersonian prices $t'_i=t_i(v'_{-i})$ computed from a fresh independent profile for each buyer, over both the prices and the values; UP is $\sup_{\tau\ge0}\mathrm{SPP}_H(\tau,\dots,\tau)$.
--   4. **$m(\tau)$.** The expected number of units that the Myersonian SPP$_H$ mechanism sells at a price of at least $\tau$.
--
--   These are the mechanisms compared in Theorem 3, Lemma 3 and Theorem 4.
--
--   **Formalization Note** Buyers are `Fin n`. Revenues and counts are in $[0,\infty]$ (lower integrals). The re-sampled profiles are the same `resampleLaw` as in the published single-unit setting; `optRev` and `sStar` are the published definitions, which apply to any thresholds. Ties among equal prices change who is served but not the revenue.
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 8–9 (§3, SPP), 11 (§3.2), 18–19 (§5), 34 (§8.3)

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

/-- An `H`-unit threshold mechanism (Lemma 1, p. 9; §3, p. 8; §5, p. 18). `t i v` is the threshold
`t_i(v_{-i})`: buyer `i` wins and pays `t i v` exactly when `t i v ≤ v i`. The thresholds are
measurable, nonnegative and do not depend on the buyer's own value, and almost surely at most `H`
buyers weakly exceed their thresholds. -/
structure IsMultiThresholdMech {n : ℕ} (H : ℕ) (μ : Fin n → Measure ℝ)
    (t : Fin n → (Fin n → ℝ) → ℝ) : Prop where
  measurable : ∀ i, Measurable (t i)
  nonneg : ∀ i v, 0 ≤ t i v
  indep_own : ∀ i (v w : Fin n → ℝ), (∀ j, j ≠ i → v j = w j) → t i v = t i w
  capacity : ∀ᵐ v ∂(Measure.pi μ), (Finset.univ.filter (fun i => t i v ≤ v i)).card ≤ H

open Classical in
/-- The buyers served by the `H`-unit sequential posted-price mechanism SPP_H(p) at the value
profile `v` (§3, p. 9; §5, p. 18): buyers are approached in decreasing order of price (ties by
index) and each accepting buyer (`p i ≤ v i`) is served while units remain. So buyer `i` is served
iff it accepts and fewer than `H` accepting buyers precede it in that order. -/
noncomputable def sppHWinners {n : ℕ} (H : ℕ) (p v : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≤ v i ∧
    (Finset.univ.filter (fun k => p k ≤ v k ∧ (p i < p k ∨ (p k = p i ∧ k < i)))).card < H)

/-- Revenue of SPP_H(p) at `v`: the sum of the prices paid by the served buyers. -/
noncomputable def sppHRevAt {n : ℕ} (H : ℕ) (p v : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ sppHWinners H p v, ENNReal.ofReal (p i)

/-- `SPP_H(p)`, the expected revenue of SPP_H(p) under independent values `v ∼ Π μ_i`. -/
noncomputable def sppHRev {n : ℕ} (H : ℕ) (μ : Fin n → Measure ℝ) (p : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ v, sppHRevAt H p v ∂(Measure.pi μ)

/-- MP for `H` units (§8.3, p. 34): expected revenue of SPP_H with the Myersonian prices
`t′_i = t i (W i)`, over both the re-sampled profiles `W` and the values `v`. -/
noncomputable def mpHRev {n : ℕ} (H : ℕ) (μ : Fin n → Measure ℝ)
    (t : Fin n → (Fin n → ℝ) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, sppHRevAt H (fun i => t i (x.1 i)) x.2 ∂(resampleLaw μ)

/-- UP for `H` units (§3.2, p. 11; §8.3, p. 34): `sup_{τ ≥ 0} SPP_H(τ, …, τ)`. -/
noncomputable def upHRev {n : ℕ} (H : ℕ) (μ : Fin n → Measure ℝ) : ℝ≥0∞ :=
  ⨆ (τ : ℝ) (_ : 0 ≤ τ), sppHRev H μ (fun _ => τ)

open Classical in
/-- `m(τ)` (Lemma 3, p. 19): the expected number of units that the Myersonian SPP_H mechanism sells
at a price of at least `τ`. -/
noncomputable def mH {n : ℕ} (H : ℕ) (μ : Fin n → Measure ℝ) (t : Fin n → (Fin n → ℝ) → ℝ)
    (τ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, (((sppHWinners H (fun i => t i (x.1 i)) x.2).filter
    (fun i => τ ≤ t i (x.1 i))).card : ℝ≥0∞) ∂(resampleLaw μ)

end SPPRevenue.SingleUnit.Supplement


