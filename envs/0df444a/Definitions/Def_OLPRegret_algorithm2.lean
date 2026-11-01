-- Prove2me | Definitions.Def_OLPRegret_algorithm2
-- name    : OLPRegret_algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:03:30.136182+00:00
-- url     : https://prove2.me/theorems/cdab2294-2cb9-412c-907a-ad24bddc8bb6
-- title:
--   Algorithm 2
-- statement:
--   **Algorithm 2** accepts the customer of period $t$ exactly when it fits, $tb_t\ge a_t$, and has positive surplus at the limiting shadow price of the current inventory, $\Delta_t(y_\infty^{b_t})>0$:
--   $$
--   x_t=\mathbb 1\{\Delta_t(y_\infty^{b_t})>0\}\,\mathbb 1\{tb_t\ge a_t\},\qquad b_{t-1}=\psi_t^{b_t}(x_ta_t).
--   $$
--   Near $\beta$ the inventory under this rule is a martingale. It is the comparison policy behind the upper bound.
--
--   **Formalization Note** Since $y_\infty^b$ is defined only near $\beta$, the algorithm takes a selection $y$ with `IsLimitPrice`: $y(b)$ minimizes $\Lambda_\infty^b$ for $b$ near $\beta$, and $y$ is arbitrary elsewhere. The test $tb_t\ge a_t$ is the feasibility mask.
-- source:
--   Bray, arXiv:1912.08917v6, Algorithm 2, pp.25–26; (26), p.26

import Mathlib
import Definitions.Def_OLPRegret_Policy

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace OLPRegret

/-- `y` is a selection of limiting shadow prices: `y b` minimizes `Λ∞ᵇ` for every `b` near `β`, and
`y` is arbitrary elsewhere (Lemma 2 of Bray, arXiv:1912.08917v6, p.20, makes the minimizer near `β`
unique, so such a `y` equals `y∞ᵇ` there). -/
def IsLimitPrice {m : ℕ} (μ : Measure (Customer m)) (β : E m) (y : E m → E m) : Prop :=
  ∀ᶠ b in 𝓝 β, IsMinimizer (LambdaInf μ b) (y b)

open scoped Classical in
/-- **Algorithm 2** (Bray, arXiv:1912.08917v6, pp.25–26), run with the selection `y` of limiting
shadow prices: accept in period `t` iff `Δₜ(y(bₜ)) > 0`; the inventory test `tbₜ ≥ aₜ` is the
feasibility mask of `Accepts`. The output of `remaining` is step 3(b), `bₜ₋₁ = ψₜ^{bₜ}(xₜaₜ)`. -/
noncomputable def algorithm2 {m n : ℕ} (y : E m → E m) : Scheme m n :=
  ruleScheme fun _ b z => decide (0 < surplus z (y b))

end OLPRegret


