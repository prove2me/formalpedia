-- Prove2me | Definitions.Def_AdaGrad_Diag_Setup
-- name    : AdaGrad_Diag_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:17:29.359044+00:00
-- url     : https://prove2.me/theorems/a885929a-f53f-4236-a897-4c7a40d2d804
-- title:
--   Regret, per-coordinate gradient norms, diagonal proximal functions and the runs of diagonal AdaGrad (Figure 1)
-- statement:
--   Fix a dimension $d$ and work in $\mathbb R^d$ with the Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|_2$. For $x\in\mathbb R^d$ write $\|x\|_\infty=\max_i |x_i|$.
--
--   **Online convex optimization with a regularizer.** At rounds $t=1,2,\dots$ a learner plays $x_t\in\mathcal X$, a loss $f_t:\mathbb R^d\to\mathbb R$ is revealed, and the learner observes a subgradient $g_t\in\partial f_t(x_t)$, i.e. $f_t(y)\ge f_t(x_t)+\langle g_t,y-x_t\rangle$ for all $y$. A fixed regularizer $\varphi:\mathbb R^d\to\mathbb R$ is added to every loss. The **regret** against a comparator $x^*$ is (2)
--   $$R_\varphi(T)=\sum_{t=1}^T\big[f_t(x_t)+\varphi(x_t)-f_t(x^*)-\varphi(x^*)\big].$$
--
--   **Per-coordinate gradient norms.** For a coordinate $i$, $g_{1:t,i}=(g_{1,i},\dots,g_{t,i})$ collects the $i$-th coordinates of the first $t$ subgradients, and
--   $$s_{t,i}=\|g_{1:t,i}\|_2=\Big(\sum_{\tau=1}^t g_{\tau,i}^2\Big)^{1/2},\qquad s_{0,i}=0 .$$
--
--   **Diagonal quadratic proximal functions.** For a weight vector $h\in\mathbb R^d$ let
--   $$\psi(y)=\tfrac12\sum_{i}h_i y_i^2,\qquad B_\psi(y,z)=\tfrac12\sum_i h_i(y_i-z_i)^2,\qquad \|v\|_{\psi^*}^2=\sum_i \frac{v_i^2}{h_i},$$
--   the proximal function, its Bregman divergence and its squared dual norm, with the convention $0/0=0$ of the paper.
--
--   **The two updates.** Given a step size $\eta$, a closed convex $\mathcal X\subseteq\mathbb R^d$ and weights $h_t$ for every round, a run of the **composite mirror descent update** (4) is a sequence with, for every $t\ge1$, $g_t\in\partial f_t(x_t)$ and
--   $$x_{t+1}\in\operatorname*{argmin}_{y\in\mathcal X}\big\{\eta\langle g_t,y\rangle+\eta\varphi(y)+B_{\psi_t}(y,x_t)\big\};$$
--   a run of the **primal-dual subgradient update** (3) has instead
--   $$x_{t+1}\in\operatorname*{argmin}_{y\in\mathcal X}\Big\{\eta\Big\langle \frac1t\sum_{\tau=1}^t g_\tau,y\Big\rangle+\eta\varphi(y)+\frac1t\psi_t(y)\Big\}.$$
--
--   **Diagonal AdaGrad (Figure 1).** With parameters $\eta>0$, $\delta\ge0$, AdaGrad starts at $x_1=0$ and uses $H_t=\delta I+\mathrm{diag}(s_t)$, $\psi_t(x)=\frac12\langle x,H_tx\rangle$, i.e. the weights $h_{t,i}=\delta+s_{t,i}$. Its runs are the runs of (3) or of (4) with these weights and $x_1=0$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin d)`, so `‖·‖` is the Euclidean norm; `supNorm x = ⨆ i, |x i|` is $\|x\|_\infty$ (and $0$ when $d=0$). Rounds are 1-based; values at index $0$ of the sequences are never used, except $s_0=0$ as an empty sum. The subgradient relation is the published platform definition `ShorNonsmooth.AlmostDiff.IsSubgradient`. The argmin is a predicate (`x (t+1) ∈ X` together with `IsMinOn`), not a function, because it need not be unique (e.g. $\delta=0$) and need not exist for every $\mathcal X$; the theorems hold for every run. The losses and the regularizer are real-valued, so extended-valued regularizers (indicator functions) are excluded; the constraint is carried by $\mathcal X$. The factor $\tfrac12$ in $\psi_t$ is Figure 1's. The losses form a fixed sequence (an oblivious adversary); since the run is determined by the losses, a bound for every loss sequence also covers adaptive adversaries.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2122 (§1.1 notation, Bregman divergence), p. 2123 (regret (2), updates (3), (4)), p. 2130 (Figure 1), p. 2131 (dual norm)

import Mathlib
import Definitions.Def_ShorNonsmooth_AlmostDiff_IsSubgradient

namespace AdaGrad.Diag

open ShorNonsmooth.AlmostDiff

/-- The sup norm `‖x‖∞ = max_i |x_i|` of a vector of `ℝ^d` (Duchi, Hazan, Singer, JMLR 12 (2011),
§1.1, p. 2122). It is `0` when `d = 0`. (On `EuclideanSpace ℝ (Fin d)` the norm `‖·‖` is the
Euclidean norm `‖·‖₂`, so `‖·‖∞` is defined separately.) -/
noncomputable def supNorm {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ⨆ i : Fin d, |x i|

/-- `s_{t,i} = ‖g_{1:t,i}‖₂ = (∑_{τ=1}^t g_{τ,i}²)^{1/2}` (Figure 1, p. 2130; notation p. 2122): the
Euclidean norm of the `i`-th coordinates of the subgradients of rounds `1, …, t`. Rounds are 1-based;
`s g 0 i = 0` (empty sum). -/
noncomputable def s {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (i : Fin d) : ℝ :=
  Real.sqrt (∑ τ ∈ Finset.Icc 1 t, (g τ i) ^ 2)

/-- The regret (2), p. 2123, against a fixed comparator `x*`:
`R_φ(T) = ∑_{t=1}^T [f_t(x_t) + ϕ(x_t) − f_t(x*) − ϕ(x*)]`. -/
def regret {d : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (ϕ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin d)) (xstar : EuclideanSpace ℝ (Fin d)) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, (f t (x t) + ϕ (x t) - f t xstar - ϕ xstar)

/-- The diagonal quadratic proximal function `ψ(y) = ½ ⟨y, diag(h) y⟩ = ½ ∑_i h_i y_i²` with
weight vector `h` (Figure 1: `ψ_t(x) = ½⟨x, H_t x⟩` with `H_t = δI + diag(s_t)`). -/
noncomputable def prox {d : ℕ} (h : Fin d → ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * ∑ i, h i * (y i) ^ 2

/-- The Bregman divergence (p. 2122) of the diagonal quadratic proximal function `prox h`:
`B_ψ(y, z) = ψ(y) − ψ(z) − ⟨∇ψ(z), y − z⟩ = ½ ∑_i h_i (y_i − z_i)²`. -/
noncomputable def bregman {d : ℕ} (h : Fin d → ℝ) (y z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / 2) * ∑ i, h i * (y i - z i) ^ 2

/-- The squared dual norm `‖v‖²_{ψ*} = ⟨v, diag(h)⁻¹ v⟩ = ∑_i v_i² / h_i` of the diagonal quadratic
proximal function `prox h` (p. 2131). Lean's `a / 0 = 0` is the paper's convention `0/0 = 0`
(p. 2149); every theorem using it either assumes `h_i > 0` or that `h_i = 0` forces `v_i = 0`. -/
noncomputable def dualNormSq {d : ℕ} (h : Fin d → ℝ) (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i, (v i) ^ 2 / h i

/-- A run of the **composite mirror descent update (4)** (p. 2123) with diagonal quadratic proximal
functions `ψ_t = prox (h t)`: for every round `t ≥ 1`, `g_t` is a subgradient of `f_t` at `x_t`, and
`x_{t+1} ∈ X` minimizes `η⟨g_t, y⟩ + ηϕ(y) + B_{ψ_t}(y, x_t)` over `y ∈ X`.
The argmin is a predicate (it need not be unique or exist for every data). -/
def IsCompositeMDRun {d : ℕ} (η : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℕ → Fin d → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    IsSubgradient (f t) (x t) (g t) ∧ x (t + 1) ∈ X ∧
      IsMinOn (fun y => η * inner ℝ (g t) y + η * ϕ y + bregman (h t) y (x t)) X (x (t + 1))

/-- A run of the **primal-dual subgradient update (3)** (p. 2123) with diagonal quadratic proximal
functions `ψ_t = prox (h t)`: for every round `t ≥ 1`, `g_t` is a subgradient of `f_t` at `x_t`, and
`x_{t+1} ∈ X` minimizes `η⟨(1/t) ∑_{τ=1}^t g_τ, y⟩ + ηϕ(y) + (1/t) ψ_t(y)` over `y ∈ X`. -/
def IsDualAveragingRun {d : ℕ} (η : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (h : ℕ → Fin d → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    IsSubgradient (f t) (x t) (g t) ∧ x (t + 1) ∈ X ∧
      IsMinOn (fun y => η * inner ℝ ((1 / (t : ℝ)) • ∑ τ ∈ Finset.Icc 1 t, g τ) y + η * ϕ y
        + (1 / (t : ℝ)) * prox (h t) y) X (x (t + 1))

/-- AdaGrad's diagonal weights (Figure 1, p. 2130): `H_t = δI + diag(s_t)`, i.e. the weight of
coordinate `i` in round `t` is `δ + s_{t,i}`. In round `0` it is `δ` (`s_0 = 0`). -/
noncomputable def adaWeights {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ)
    (i : Fin d) : ℝ :=
  δ + s g t i

/-- A run of **ADAGRAD with diagonal matrices** (Figure 1, p. 2130) using the primal-dual
subgradient update (3): `x_1 = 0`, and the run of (3) with `ψ_t(x) = ½⟨x, (δI + diag(s_t)) x⟩`. -/
def IsPrimalDualRun {d : ℕ} (η δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 1 = 0 ∧ IsDualAveragingRun η X ϕ f (adaWeights δ g) x g

/-- A run of **ADAGRAD with diagonal matrices** (Figure 1, p. 2130) using the composite mirror
descent update (4): `x_1 = 0`, and the run of (4) with `ψ_t(x) = ½⟨x, (δI + diag(s_t)) x⟩`. -/
def IsMirrorDescentRun {d : ℕ} (η δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) : Prop :=
  x 1 = 0 ∧ IsCompositeMDRun η X ϕ f (adaWeights δ g) x g

end AdaGrad.Diag


