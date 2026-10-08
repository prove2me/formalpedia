-- Prove2me | Definitions.Def_FeaturePricing_Ellipsoid_EllipsoidPricing
-- name    : FeaturePricing_Ellipsoid_EllipsoidPricing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:52.993089+00:00
-- url     : https://prove2.me/theorems/ece4a4c5-b3db-448e-a072-d46843c9a0e9
-- title:
--   §5, p. 11 — EllipsoidPricing: gap test, explore/exploit prices, central-cut update (4), from E₁ = B(0, R); regret (1)
-- statement:
--   This module defines the EllipsoidPricing algorithm of Cohen, Lobel and Paes Leme and its regret.
--
--   **Model (§3, pp. 7–8).** In each period $t=1,\dots,T$ a product with feature vector $x_t\in\mathbb R^d$ arrives; its market value is $\theta'x_t$ for an unknown parameter $\theta\in\mathbb R^d$. The seller posts a price $p_t$; a sale occurs iff $p_t\le\theta'x_t$, and then the seller earns $p_t$.
--
--   **Ellipsoids.** For a center $a\in\mathbb R^d$ and a positive definite matrix $A$, $E(A,a)=\{\theta : (\theta-a)'A^{-1}(\theta-a)\le1\}$. The state of the algorithm in period $t$ is the pair $(a_t,A_t)$, i.e. the ellipsoid $E_t=E(A_t,a_t)$. Given $x_t$ put
--   $$
--   \underline b_t = x_t'a_t-\sqrt{x_t'A_tx_t},\qquad \bar b_t = x_t'a_t+\sqrt{x_t'A_tx_t},
--   $$
--   the closed forms (§5.2, p. 15) of $\min_{\hat\theta\in E_t}\hat\theta'x_t$ and $\max_{\hat\theta\in E_t}\hat\theta'x_t$ of Eq. (3).
--
--   **One period (§5, p. 11).**
--   1. *Exploit* if $\bar b_t-\underline b_t\le\epsilon$: post $p_t=\underline b_t$ and keep $E_{t+1}=E_t$.
--   2. *Explore* if $\bar b_t-\underline b_t>\epsilon$: post $p_t=\tfrac12(\bar b_t+\underline b_t)$. With $b=A_tx_t/\sqrt{x_t'A_tx_t}$ and
--   $$
--   \tilde A=\frac{d^2}{d^2-1}\Big(A_t-\frac{2}{d+1}bb'\Big)\qquad\text{(Eq. (4))},
--   $$
--   set $E_{t+1}=E(\tilde A,\,a_t+\tfrac1{d+1}b)$ after a sale and $E_{t+1}=E(\tilde A,\,a_t-\tfrac1{d+1}b)$ after no sale.
--
--   **Start.** $E_1=B(0,R)=E(R^2I,0)$, the ball of radius $R$.
--
--   **Regret (Eq. (1), p. 8).** For a parameter $\theta$ and a feature sequence $(x_t)$,
--   $$
--   \mathrm{Regret}_T=\sum_{t=1}^T\big[\theta'x_t-p_t\,\mathbb I\{\theta'x_t\ge p_t\}\big].
--   $$
--   The paper's worst-case regret is the maximum of this quantity over $\theta$ and over nature's (closed-loop) choice of features.
--
--   **Formalization Note** Periods are indexed from $0$ in Lean: Lean period $t$ is the paper's period $t+1$, `state … 0` is $E_1$, and `regret … T` sums over $t<T$. The paper defines $E_{t+1}$ as the smallest ellipsoid containing the half-ellipsoid $H_{t+1}=E_t\cap\{\theta'x_t\ge p_t\}$ (sale) or $E_t\cap\{\theta'x_t\le p_t\}$ (no sale) and gives (4) as its closed form (p. 14); the recursion uses (4) directly, via the published `ellipsoidUpdateCenter`/`ellipsoidUpdateMatrix` (the no-sale center is `ellipsoidUpdateCenter a A (-x)`, and `ellipsoidUpdateMatrix A x` is used in both branches since $\tilde A$ is even in $x$). The paper allows "the smallest ellipsoid $E_1$ that contains $K_1$, or in fact any ellipsoid that contains $K_1$" (p. 11); the ball $B(0,R)$ contains $K_1\subseteq\{\|\theta\|\le R\}$ by the normalization of §3 and is the choice made here. Since the algorithm is deterministic, a closed-loop nature produces the same play as the fixed feature sequence it generates, so the worst case over nature is a universal quantifier over sequences `x : ℕ → Fin d → ℝ` in the theorems. The parameter $\epsilon$ is an argument; $d\ge2$ is assumed in the theorems, since (4) divides by $d^2-1$.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 11, §5 (EllipsoidPricing, Eq. (3)); p. 14, §5.1, Eq. (4); p. 15, §5.2; pp. 7–8, §3, Eq. (1)

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization

/-- **§5.2, p. 15.** The lower value `b̲ = x′a − √(x′Ax)` of the linear functional `θ ↦ x′θ` on the
ellipsoid `E(A, a) = {θ : (θ − a)′A⁻¹(θ − a) ≤ 1}` (closed form of the `min` in Eq. (3)). -/
noncomputable def bLow {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ :=
  x ⬝ᵥ a - Real.sqrt (x ⬝ᵥ A *ᵥ x)

/-- **§5.2, p. 15.** The upper value `b̄ = x′a + √(x′Ax)` (closed form of the `max` in Eq. (3)). -/
noncomputable def bHigh {d : ℕ} (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ :=
  x ⬝ᵥ a + Real.sqrt (x ⬝ᵥ A *ᵥ x)

/-- **§5, p. 11.** The price EllipsoidPricing posts on the current ellipsoid `E(A, a)` for the
feature vector `x`: if `b̄ − b̲ ≤ ε` the exploit price `b̲`, otherwise the explore price
`½(b̄ + b̲)`. -/
noncomputable def priceOf {d : ℕ} (ε : ℝ) (a : Fin d → ℝ) (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ :=
  if bHigh a A x - bLow a A x ≤ ε then bLow a A x
  else (bHigh a A x + bLow a A x) / 2

/-- **§5, p. 11, with the closed form (4) of p. 14.** One period of EllipsoidPricing on the state
`s = (a, A)` (center and shape matrix of `E(A, a)`), with true parameter `θ` and feature vector `x`.

* Exploit (`b̄ − b̲ ≤ ε`): the ellipsoid is kept, `E_{t+1} = E_t`.
* Explore (`b̄ − b̲ > ε`), price `p = ½(b̄ + b̲)`. A sale occurs iff `p ≤ θ′x` (§3, p. 7).
  - Sale: `H_{t+1} = E_t ∩ {θ′x ≥ p}`, and `E_{t+1} = E(Ã, a + b/(d+1))`.
  - No sale: `H_{t+1} = E_t ∩ {θ′x ≤ p}`, and `E_{t+1} = E(Ã, a − b/(d+1))`.

  Here `b = Ax/√(x′Ax)` and `Ã = (d²/(d²−1))(A − (2/(d+1))bb′)` is Eq. (4). The paper defines
  `E_{t+1}` as the smallest ellipsoid containing `H_{t+1}` and gives (4) as its closed form (p. 14);
  the recursion uses (4) directly. The new center `a + b/(d+1)` is `ellipsoidUpdateCenter a A x`
  and `a − b/(d+1)` is `ellipsoidUpdateCenter a A (-x)`; the matrix `Ã` is
  `ellipsoidUpdateMatrix A x` in both branches (it is even in `x`). -/
noncomputable def step {d : ℕ} (ε : ℝ) (θ x : Fin d → ℝ)
    (s : (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ) : (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ :=
  if bHigh s.1 s.2 x - bLow s.1 s.2 x ≤ ε then s
  else if priceOf ε s.1 s.2 x ≤ θ ⬝ᵥ x then
    (ellipsoidUpdateCenter s.1 s.2 x, ellipsoidUpdateMatrix s.2 x)
  else
    (ellipsoidUpdateCenter s.1 s.2 (-x), ellipsoidUpdateMatrix s.2 x)

/-- **§5, p. 11; §5.2, p. 15.** The state `(a_t, A_t)` of EllipsoidPricing, `E_t = E(A_t, a_t)`,
run with parameter `ε`, true parameter `θ` and feature sequence `x`. Periods are indexed from `0`:
Lean period `t` is the paper's period `t + 1`, so `state … 0` is the paper's `E₁`, which is the
ball `B(0, R) = E(R²I, 0)` (an ellipsoid containing `K₁ ⊆ {‖θ‖ ≤ R}`, p. 11). -/
noncomputable def state {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) :
    ℕ → (Fin d → ℝ) × Matrix (Fin d) (Fin d) ℝ
  | 0 => (0, (R ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
  | t + 1 => step ε θ (x t) (state R ε θ x t)

/-- The center `a_t` of `E_t` (Lean period `t` = paper period `t + 1`). -/
noncomputable def center {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    Fin d → ℝ :=
  (state R ε θ x t).1

/-- The shape matrix `A_t` of `E_t` (Lean period `t` = paper period `t + 1`). -/
noncomputable def shape {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  (state R ε θ x t).2

/-- **§5, p. 11.** Period `t` is an exploration period: `b̄_t − b̲_t > ε`. -/
def isExplore {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) : Prop :=
  ε < bHigh (center R ε θ x t) (shape R ε θ x t) (x t) - bLow (center R ε θ x t) (shape R ε θ x t) (x t)

/-- **§5, p. 11.** The price `p_t` posted in period `t`. -/
noncomputable def price {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ) : ℝ :=
  priceOf ε (center R ε θ x t) (shape R ε θ x t) (x t)

/-- **§3, Eq. (1), p. 8.** The regret of EllipsoidPricing over the first `T` periods for the true
parameter `θ` and the feature sequence `x`:
`Σ_{t=1}^T [θ′x_t − p_t · I{θ′x_t ≥ p_t}]` (Lean sums over `t < T`, period `t` = paper's `t + 1`). -/
noncomputable def regret {d : ℕ} (R ε : ℝ) (θ : Fin d → ℝ) (x : ℕ → Fin d → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (θ ⬝ᵥ x t - price R ε θ x t * (if θ ⬝ᵥ x t ≥ price R ε θ x t then 1 else 0))

end FeaturePricing.Ellipsoid


