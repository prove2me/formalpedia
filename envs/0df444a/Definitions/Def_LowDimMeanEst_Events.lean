-- Prove2me | Definitions.Def_LowDimMeanEst_Events
-- name    : LowDimMeanEst_Events
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:52:44.40264+00:00
-- url     : https://prove2.me/theorems/8a8ce601-ec98-45dd-8ebd-acf2d1c09e84
-- title:
--   Events F, T and B (Definitions 15, 21, 22)
-- statement:
--   For samples $x_1,\dots,x_n\in\mathbb R^d$, $\delta$, and $\tau=\sqrt{nd}$:
--
--   1. **Event F** (Definition 15): $\displaystyle\frac1n\sum_{i:\|x_i\|\le\tau}\|x_i\|^2\le 2d+4d\log\frac{100}\delta$.
--   2. **Event T** (Definition 21): the number of samples with $\|x_i\|\ge\sqrt{nd}$ is at most $4\log\frac1\delta\big/\log\log\frac1\delta$.
--   3. **Event B** (Definition 22), for a trimming matrix $A$:
--   $$\mathrm{Tr}(A)\ge\frac{10^{-10}\log(1/\delta)}{n\,(1+d/\log(1/\delta))}\quad\text{and}\quad \alpha\le\frac{10^{10}}3\Big(1+\frac d{\log(1/\delta)}\Big),$$
--   where $\alpha=\max_{\|v\|=1}\frac1n\sum_i(1-\min(1,x_i^\top Ax_i))\langle x_i,v\rangle^2$ is the largest trimmed empirical variance.
--
--   Events F and T control the samples of small and of large norm in the net argument of §8; event B keeps the trimming matrix away from $0$ and the trimmed variance bounded.
--
--   **Formalization Note** Definition 22 writes $\alpha\le O(1+d/\log(1/\delta))$ for the bound established in Lemma 44; that bound is $\frac{10^{10}}3(1+d/\log(1/\delta))$, obtained from Lemma 43 with the trace bound $10^{-10}\log(1/\delta)/(n(1+d/\log(1/\delta)))$ (p.84). $\alpha$ is read as in the proof of Lemma 43 ("recalling α as the trimmed empirical variance").
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Definition 15, p.24; Definition 21 and Definition 22, p.27; Lemma 43–44, pp.83–84

import Mathlib
import Definitions.Def_LowDimMeanEst_TrimmingMatrix
import Definitions.Def_LowDimMeanEst_Parameters

namespace LowDimMeanEst

/-!
# Events F, T and B (Definitions 15, 21, 22)

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

* Definition 15 (Event F), p.24: "(1/n) Σ_{i:∥xᵢ∥≤τ} ∥xᵢ∥² ≤ 2d + 4d log(100/δ)", with `τ = √(nd)`
  (Table 1).
* Definition 21 (Event T), p.27: "the total number of elements with ∥xᵢ∥ ≥ √(nd) is at most
  4 log(1/δ)/log log(1/δ)."
* Definition 22 (Event B), p.27: "Tr(A) ≥ ξ (log(1/δ)/n)/(1 + d/log(1/δ)) and α ≤ O(1 + d/log(1/δ)),
  where α is as defined in Algorithm 2 and ξ = 10⁻¹⁰ is the constant established in Lemma 44."

**Formalization Note.**
* In Event B, `α` is the largest trimmed empirical variance `max_{‖v‖=1} (1/n) Σᵢ (1 − min(1,
  xᵢ⊤Axᵢ))⟨xᵢ, v⟩²`, as the proof of Lemma 43 reads it ("recalling α as the trimmed empirical
  variance", p.83). Its `O(·)` is the constant `10¹⁰/3` that Lemma 43 yields from Lemma 44's trace
  bound `10⁻¹⁰ log(1/δ)/(n(1 + d/log(1/δ)))` (p.84).
* The samples are `x : Fin n → E d`, so `n` is the number of samples.
-/

/-- Event F (Definition 15): `(1/n) Σ_{i : ‖xᵢ‖ ≤ τ} ‖xᵢ‖² ≤ 2d + 4d log(100/δ)`, `τ = √(nd)`. -/
def EventF {d n : ℕ} (x : Fin n → E d) (δ : ℝ) : Prop :=
  (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.filter (fun i => ‖x i‖ ≤ paramTau d n), ‖x i‖ ^ 2 ≤
    2 * d + 4 * d * Real.log (100 / δ)

/-- Event T (Definition 21): `#{i : ‖xᵢ‖ ≥ √(nd)} ≤ 4 log(1/δ) / log log(1/δ)`. -/
def EventT {d n : ℕ} (x : Fin n → E d) (δ : ℝ) : Prop :=
  ((Finset.univ.filter (fun i => Real.sqrt (n * d) ≤ ‖x i‖)).card : ℝ) ≤
    4 * logInv δ / loglogInv δ

/-- Event B (Definition 22) for the trimming matrix `A`:
`Tr(A) ≥ 10⁻¹⁰ log(1/δ)/(n(1 + d/log(1/δ)))` and, for every unit `v`,
`(1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))⟨xᵢ, v⟩² ≤ (10¹⁰/3)(1 + d/log(1/δ))`. -/
def EventB {d n : ℕ} (x : Fin n → E d) (δ : ℝ) (A : E d →L[ℝ] E d) : Prop :=
  (10 : ℝ) ^ (-10 : ℤ) * logInv δ / (n * (1 + d / logInv δ)) ≤ tr A ∧
    ∀ v : E d, ‖v‖ = 1 →
      (1 / (n : ℝ)) * trimmedQuad x A v ≤ ((10 : ℝ) ^ 10 / 3) * (1 + d / logInv δ)

end LowDimMeanEst


