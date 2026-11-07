-- Prove2me | Definitions.Def_ContinualCounting_sigmaL
-- name    : ContinualCounting_sigmaL
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:54.610844+00:00
-- url     : https://prove2.me/theorems/d866d002-78df-4a1b-9d01-b3928ed92826
-- title:
--   The residual noises $\sigma_{u,\ell}$ and $\sigma_{u,r}$
-- statement:
--   For a node $u$ whose children are not leaves, $\sigma_{u,\ell}$ measures how well $b_{r(u)}$ can be predicted from the noise $\Delta^{<\ell(\ell(u))}(z),\Delta^{<\ell(r(u))}(z)$, where $\Delta^{<w}(z)=(b_v)_{v\in\mathcal V(\mathcal T^w)\setminus\{w\}}$:
--   $$\sigma_{u,\ell}=\mathbb E\Big[\inf_m\mathbb E\big[|b_{r(u)}-m|\ \big|\ \Delta^{<\ell(\ell(u))}(z),\Delta^{<\ell(r(u))}(z)\big]\Big].$$
--   Likewise
--   $$\sigma_{u,r}=\mathbb E\Big[\inf_m\mathbb E\big[|b_{r(\ell(u))}-b_{r(u)}-b_{r(r(u))}-m|\ \big|\ \Delta^{<r(\ell(u))}(z),\Delta^{<r(r(u))}(z)\big]\Big].$$
--
--   These are the residual noises that the lower bound accumulates along the tree.
--
--   **Formalization Note** Each is encoded as the infimum, over measurable functions $\varphi$ of the conditioning coefficients, of $\mathbb E|t(z)-\varphi(\Delta)|$, with values in $[0,\infty]$. This has the same value as the displayed formula: on $\mathbb R$ a regular conditional law exists, its smallest median attains the inner infimum as a measurable function of the conditioning variables, and every measurable predictor does at least as badly. The predictor reads only the listed coefficients. If it could read $z$, $\sigma$ would be $0$.
-- source:
--   Bairaktari, Dahl, Larsen, The Binary Tree Mechanism is Optimal for Differentially Private Continual Counting, arXiv:2607.00876 (sha256 986e6426…), §5, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_ContinualCounting_Node

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace ContinualCounting

/-- The node set `(V(T^{ℓ(ℓ(u))}) ∖ {ℓ(ℓ(u))}) ∪ (V(T^{ℓ(r(u))}) ∖ {ℓ(r(u))})` of the coefficients
`∆^{<ℓ(ℓ(u))}(z), ∆^{<ℓ(r(u))}(z)` (Bairaktari, Dahl, Larsen, arXiv:2607.00876, sha256 986e6426…, p.19). -/
def condSetL (h : ℕ) (u : Node) : Finset Node :=
  (treeV h (left (left u))).erase (left (left u)) ∪
    (treeV h (left (right u))).erase (left (right u))

/-- The node set `(V(T^{r(ℓ(u))}) ∖ {r(ℓ(u))}) ∪ (V(T^{r(r(u))}) ∖ {r(r(u))})` of the coefficients
`∆^{<r(ℓ(u))}(z), ∆^{<r(r(u))}(z)`, p.19. -/
def condSetR (h : ℕ) (u : Node) : Finset Node :=
  (treeV h (right (left u))).erase (right (left u)) ∪
    (treeV h (right (right u))).erase (right (right u))

/-- The target `b_{r(u)}` predicted in `σ_{u,ℓ}`, as a linear form of the vector `y`. -/
def targetL (h : ℕ) (u : Node) (y : Fin (2 ^ h) → ℝ) : ℝ := coef h (right u) y

/-- The target `b_{r(ℓ(u))} − b_{r(u)} − b_{r(r(u))}` predicted in `σ_{u,r}`, as a linear form of `y`. -/
def targetR (h : ℕ) (u : Node) (y : Fin (2 ^ h) → ℝ) : ℝ :=
  coef h (right (left u)) y - coef h (right u) y - coef h (right (right u)) y

/-- The best expected absolute error of predicting `t(z)` by a measurable function of the
coefficients `(b_v)_{v ∈ S}`. Every prediction reads only those coefficients. -/
noncomputable def residual {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ)) (S : Finset Node)
    (t : (Fin (2 ^ h) → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨅ (φ : (S → ℝ) → ℝ) (_ : Measurable φ), ∫⁻ z, ‖t z - φ (fun v => coef h v.1 z)‖ₑ ∂ν

/-- **The residual noise `σ_{u,ℓ}`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), §5,
p.19: `σ_{u,ℓ}(∆^{<ℓ(ℓ(u))}(z), ∆^{<ℓ(r(u))}(z)) := inf_m E[|b_{r(u)} − m| | ∆^{<ℓ(ℓ(u))}(z), ∆^{<ℓ(r(u))}(z)]`
and `σ_{u,ℓ} = E[σ_{u,ℓ}(∆^{<ℓ(ℓ(u))}(z), ∆^{<ℓ(r(u))}(z))]`.

**Formalization Note.** Encoded as an infimum over measurable predictors of the conditioning
coefficients, in `ℝ≥0∞`. This has the same value as the paper's `E[inf_m E[·|·]]`: on `ℝ` a regular
conditional law exists, its smallest median attains the inner infimum and is a measurable function
of the conditioning variables (the paper's `m^u_ℓ`), and every measurable predictor does at least as
badly pointwise. That the infimum is attained is the theorem `sigma_attained`. When
`d(u) = h − 2` the grandchildren are leaves, the conditioning set is empty and the predictor
is a constant. -/
noncomputable def sigmaL {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ)) (u : Node) : ℝ≥0∞ :=
  residual ν (condSetL h u) (targetL h u)

/-- **The residual noise `σ_{u,r}`.** Bairaktari, Dahl, Larsen, arXiv:2607.00876 (sha256 986e6426…), §5,
p.19: `σ_{u,r}(∆^{<r(ℓ(u))}(z), ∆^{<r(r(u))}(z)) := inf_m E[|b_{r(ℓ(u))} − b_{r(u)} − b_{r(r(u))} − m| | ∆^{<r(ℓ(u))}(z), ∆^{<r(r(u))}(z)]`
and `σ_{u,r} = E[σ_{u,r}(∆^{<r(ℓ(u))}(z), ∆^{<r(r(u))}(z))]`. Same encoding as `sigmaL`. -/
noncomputable def sigmaR {h : ℕ} (ν : Measure (Fin (2 ^ h) → ℝ)) (u : Node) : ℝ≥0∞ :=
  residual ν (condSetR h u) (targetR h u)

end ContinualCounting


