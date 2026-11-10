-- Prove2me | Definitions.Def_GoodHypotheses_Proper_Proxies
-- name    : GoodHypotheses_Proper_Proxies
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:14:53.036895+00:00
-- url     : https://prove2.me/theorems/869a7df5-b83a-4b91-8857-7bc55b148e4f
-- title:
--   Weighted quantiles, the mixture, the weighted-median proxy and its Scheffé values, the empirical loss and the score estimator
-- statement:
--   For reals $v_1,\dots,v_n$ with weights $w_1,\dots,w_n$ and $\lambda\in[0,1]$, the **weighted $\lambda$-quantile** is the smallest $v_j$ whose cumulative weight $\sum_{i:v_i\le v_j}w_i$ is at least $\lambda$ (Definition 4; Lemma C.1); it is set to $0$ if no value qualifies. For hypotheses $h_i$ and normalized weights $\tilde W$ the **quantile proxy** is $\rho(x)=$ the weighted $\lambda$-quantile of $h_1(x),\dots,h_n(x)$, the **weighted median** is the case $\lambda=\frac12$, and the **mixture** is $h_{mix}=\sum_i\tilde W_ih_i$. For the weighted median, $w_0(x)=\sum_i\tilde W_i\mathbf 1\{h_i(x)>\rho(x)\}$, $\sum_i\tilde W_i\mathbf 1\{h_i(x)<\rho(x)\}$ and $w_1(x)=\sum_i\tilde W_i\mathbf 1\{h_i(x)=\rho(x)\}$, and the chosen Scheffé values are $S_i(x)=1$ above $\rho$, $0$ below and $(\frac12-w_0(x))/w_1(x)$ at ties (p. 20). With $r=\rho/\nu$ the **empirical loss** (Eq. (18)) is
--   $$\hat\ell_i(x,y)=-S_i(y)+r(x)S_i(x)+\frac{1-r(x)}2,$$
--   and with $r=\rho/h_{mix}$ the **score estimator** (§4.4) is $\hat\sigma_i(x)=\frac{1+r(x)}2-\frac{\min\{h_i(x),\rho(x)\}}{h_{mix}(x)}$.
--
--   **Formalization Note.** Weights are passed as a vector `W`; statements assume $W_i\ge0$, $\sum_iW_i=1$. Lean division gives $a/0=0$.
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), p. 19 Definition 4 and Eq. (18); p. 20 (tie values); p. 21 (mixture); p. 21 (score estimator); p. 37 Lemma C.1

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Densities

open MeasureTheory

namespace GoodHypotheses.Proper

/-!
# Weighted quantiles, mixtures, the median proxy and its Scheffé values, the estimators

Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, *A Good Way to Find Good Hypotheses*,
STOC 2027 submission (manuscript sha256 a428fbe0…), §4.2–§4.4 pp. 18–22 (Definition 4, p. 19;
Eq. (18), p. 19; the tie values of p. 20; the mixture, p. 21; the score estimator, p. 21) and
Appendix C, p. 37.

Weights `W : Fin n → ℝ` stand for the normalized weights `W̃` (nonnegative, summing to `1`);
statements carry these hypotheses.
-/

open Classical in
/-- The weighted `λ`-quantile of reals `v_1, …, v_n` with weights `w_1, …, w_n`
(Definition 4, p. 19; Lemma C.1, p. 37): the smallest `v_j` whose cumulative weight
`∑_{i : v_i ≤ v_j} w_i` is at least `λ`. It is `0` when no value qualifies. For `n ≥ 1`,
the maximum input value qualifies whenever the weights sum to at least `λ`; at `n = 0`
there is no qualifying input value, even when `λ = 0`. -/
noncomputable def wQuantile {n : ℕ} (v w : Fin n → ℝ) (lam : ℝ) : ℝ :=
  let S : Finset ℝ :=
    (Finset.univ.filter fun j => lam ≤ ∑ i ∈ Finset.univ.filter (fun i => v i ≤ v j), w i).image v
  if hS : S.Nonempty then S.min' hS else 0

/-- The weighted `λ`-quantile proxy of the hypotheses (Definition 4, p. 19):
`ρ(x) = min { z ∈ {h_1(x), …, h_n(x)} : ∑_{i : h_i(x) ≤ z} W̃_i ≥ λ }`. -/
noncomputable def quantileProxy {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ)
    (lam : ℝ) (x : X) : ℝ :=
  wQuantile (fun i => h i x) W lam

/-- The mixture `h_mix = ∑_i W̃_i h_i` (p. 21). -/
noncomputable def mixture {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ) (x : X) : ℝ :=
  ∑ i, W i * h i x

/-- The weighted median `ρ`, the weighted `1/2`-quantile (p. 20). -/
noncomputable def medianProxy {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ) (x : X) :
    ℝ :=
  quantileProxy h W (1 / 2) x

open Classical in
/-- `w_0(x) = ∑_i W̃_i 1{h_i(x) > ρ(x)}` for the weighted median `ρ` (p. 20). -/
noncomputable def weightAbove {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ) (x : X) :
    ℝ :=
  ∑ i, if medianProxy h W x < h i x then W i else 0

open Classical in
/-- `∑_i W̃_i 1{h_i(x) < ρ(x)}` for the weighted median `ρ` (p. 20). -/
noncomputable def weightBelow {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ) (x : X) :
    ℝ :=
  ∑ i, if h i x < medianProxy h W x then W i else 0

open Classical in
/-- `w_1(x) = ∑_i W̃_i 1{h_i(x) = ρ(x)}` for the weighted median `ρ` (p. 20). -/
noncomputable def weightTie {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ) (x : X) :
    ℝ :=
  ∑ i, if h i x = medianProxy h W x then W i else 0

/-- The Scheffé function `S_i` of `(h_i, ρ)` chosen on p. 20 for the weighted median `ρ`:
`1` where `h_i(x) > ρ(x)`, `0` where `h_i(x) < ρ(x)`, and `(1/2 − w_0(x)) / w_1(x)` where
`h_i(x) = ρ(x)`. -/
noncomputable def medianScheffe {X : Type*} {n : ℕ} (h : Fin n → X → ℝ) (W : Fin n → ℝ)
    (i : Fin n) (x : X) : ℝ :=
  if medianProxy h W x < h i x then 1
  else if h i x < medianProxy h W x then 0
  else (1 / 2 - weightAbove h W x) / weightTie h W x

/-- The empirical loss of Eq. (18), p. 19, at `X = x ∼ ν`, `Y = y ∼ p`, with `r = ρ/ν`:
`ℓ̂ = −S(y) + r(x) S(x) + (1 − r(x))/2` (Lean division: `a / 0 = 0`). -/
noncomputable def empiricalLoss {X : Type*} (S ρ ν : X → ℝ) (x y : X) : ℝ :=
  -S y + ρ x / ν x * S x + (1 - ρ x / ν x) / 2

/-- The score estimator of §4.4, p. 21, at `X = x ∼ h_mix`, with `r = ρ/h_mix`:
`σ̂_i = (1 + r(x))/2 − min{h_i(x), ρ(x)} / h_mix(x)` (Lean division: `a / 0 = 0`). -/
noncomputable def scoreEstimate {X : Type*} (hi ρ hmix : X → ℝ) (x : X) : ℝ :=
  (1 + ρ x / hmix x) / 2 - min (hi x) (ρ x) / hmix x

end GoodHypotheses.Proper


