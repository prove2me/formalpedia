-- Prove2me | Definitions.Def_RobustSDP_FullPert_Supplement_NonlinearProgram
-- name    : RobustSDP_FullPert_Supplement_NonlinearProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T00:43:44.58085+00:00
-- url     : https://prove2.me/theorems/8a660a4e-53ef-4f0d-8b4b-ecd7a6958800
-- title:
--   Corrected §4.2–§4.3 objects: (16), KKT multipliers, Lagrangian and quadratic growth
-- statement:
--   This entry fixes the objects of §4.2–§4.3 of El Ghaoui, Oustry and Lebret that Theorem 4.1 is stated with. The setting is the robust SDP (15) of §4: full perturbations, $D = 0$, $\rho = 1$, with affine maps $F(x) = F_0 + \sum_i x_i F_i \in \mathbb{R}^{n\times n}$ and $R(x) = R_0 + \sum_i x_i R_i \in \mathbb{R}^{q\times n}$, a matrix $L \in \mathbb{R}^{n\times p}$, and an objective vector $c \in \mathbb{R}^m$. Write $y = (x,\tau) \in \mathbb{R}^{m+1}$, $d = (c, 0)$, and fix a number $\tau_{\mathrm{opt}}$ (the $\tau$-component of an optimal point of (15)).
--
--   1. **Constraint map.** For $\tau > 0$,
--   $$G(y) = F(x) - \tau LL^T - \tfrac{1}{\tau} R(x)^T R(x), \qquad \mathcal{G}(y) = \mathrm{diag}\bigl(G(y),\ \tau - 0.99\,\tau_{\mathrm{opt}}\bigr),$$
--   an $(n+1)\times(n+1)$ symmetric matrix.
--
--   2. **Problem (16).** A point $y$ is feasible for (16) when $\tau > 0$ and $\mathcal{G}(y) \succeq 0$; problem (16) minimizes $d^T y = c^T x$ over this set.
--
--   3. **Lagrangian.** For a dual variable $Y = \mathrm{diag}(Z, \mu)$ with $Z \in \mathbb{R}^{n\times n}$, $\mu \in \mathbb{R}$,
--   $$\mathcal{L}(y, Y) = d^T y - \operatorname{Tr} Y \mathcal{G}(y).$$
--
--   4. **Corrected dual set.** For a point $y_{\mathrm{opt}}$,
--   $$\mathcal{Y}(y_{\mathrm{opt}}) = \Bigl\{ Y = \mathrm{diag}(Z,\mu) \;:\; Y \succeq 0,\ \operatorname{Tr}(Y\mathcal{G}(y_{\mathrm{opt}}))=0,\ \operatorname{Tr} Y \tfrac{\partial \mathcal{G}}{\partial y_i}(y_{\mathrm{opt}}) = d_i,\ i = 1,\dots,m+1 \Bigr\}.$$
--
--   5. **Quadratic growth condition (QGC) for (16).** It holds at $y^\star$ if there are $\alpha > 0$ and $\varepsilon > 0$ such that every $y$ feasible for (16) with $\|y - y^\star\| < \varepsilon$ satisfies
--   $$d^T y \ \ge\ d^T y^\star + \alpha \|y - y^\star\|^2,$$
--   where $\|\cdot\|$ is the Euclidean norm on $\mathbb{R}^{m+1}$.
--
--   These objects carry the curvature criterion of Theorem 4.1, which is the step from optimality in (15) to uniqueness and stability of robust solutions.
--
--   **Formalization Note** The data of (15) are the published structure `RobustSDP.Uniqueness.SDPData`, with its matrix `G` and squared distance `sqDist`. The scalar block of $\mathcal{G}$ and $Y$ is indexed by `Fin 1`, and the factor $0.99$ is written `99/100`. The trace condition $\operatorname{Tr} Y\,\partial\mathcal{G}/\partial y_i(y_{\mathrm{opt}}) = d_i$ is written as the partial derivative at $y_{\mathrm{opt}}$ of the scalar map $y \mapsto \operatorname{Tr} Y\mathcal{G}(y)$ in the $i$-th coordinate direction. This is the same quantity because trace and multiplication by $Y$ are linear, and $\mathcal{G}$ is differentiable near any point with $\tau > 0$. The paper states the QGC with a remainder $o(\|y - y^\star\|^2)$ for every feasible $y$. The local form used here is equivalent: halve $\alpha$ in one direction, take a zero remainder near $y^\star$ in the other. The condition $\tau > 0$ in feasibility is the domain of the notation of §4.2; it is implied by $\tau \ge 0.99\,\tau_{\mathrm{opt}}$ whenever $\tau_{\mathrm{opt}} > 0$.
--
--
--   **Source correction.** Complementary slackness $\operatorname{Tr}(Y\mathcal G(y_{\mathrm{opt}}))=0$ is added to the printed stationarity-only dual set. Without it Theorem 4.1 is false: $F(x)=\mathrm{diag}(x,100)$, $L=(0,1)^T$, $R(x)=\left[\begin{smallmatrix}0&1\\0&x\end{smallmatrix}\right]$, $c=1$, $y_{\mathrm{opt}}=(0,1)$, $Y=\mathrm{diag}(1,1,0)$ have Hessian $2I$ while nearby optimal points have the same cost. Appendix A explicitly uses complementary slackness; DISPROOF.md records every assumption. The corrected set excludes noncomplementary stationary matrices, while retaining all KKT multipliers.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 39, §4.2 (notation and Eq. (16)) and §4.3 (QGC and 𝒴(y_opt)); p. 38, Eq. (15)

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.FullPert.Supplement

open RobustSDP.Uniqueness

/-- The block-diagonal constraint map `𝒢(y) = diag(G(y), τ − .99 τ_opt)` of §4.2, p. 39
(El Ghaoui–Oustry–Lebret 1998), for `y = (x, τ)`, where
`G(y) = F(x) − τLLᵀ − (1/τ) R(x)ᵀR(x)` is `SDPData.G` and `τopt` is the `τ`-component of a
fixed optimal point of (15). The scalar block is indexed by `Fin 1`. -/
noncomputable def Gcal {m n p q : ℕ} (D : SDPData m n p q) (τopt : ℝ) (y : (Fin m → ℝ) × ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  fromBlocks (D.G y) 0 0 (Matrix.of fun _ _ => y.2 - (99 / 100 : ℝ) * τopt)

/-- The block-diagonal dual variable `Y = diag(Z, μ)` of §4.2, p. 39. -/
def dualMat {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
  fromBlocks Z 0 0 (Matrix.of fun _ _ => μ)

/-- Feasibility for the nonlinear program (16), p. 39: `y = (x, τ)` with `τ > 0` (the domain of
the notation of §4.2) and `𝒢(y) ⪰ 0`. -/
def Feasible16 {m n p q : ℕ} (D : SDPData m n p q) (τopt : ℝ) (y : (Fin m → ℝ) × ℝ) : Prop :=
  0 < y.2 ∧ (Gcal D τopt y).PosSemidef

/-- The Lagrangian `ℒ(y, Y) = dᵀy − Tr Y 𝒢(y)` of §4.2, p. 39, with `d = (c, 0)`, so that
`dᵀy = cᵀx`. -/
noncomputable def lagrangian {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (τopt : ℝ)
    (Y : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (y : (Fin m → ℝ) × ℝ) : ℝ :=
  c ⬝ᵥ y.1 - (Y * Gcal D τopt y).trace

/-- The corrected set `𝒴(y_opt)` of KKT dual variables associated with `y_opt` (§4.3, p. 39): matrices
`Y = diag(Z, μ) ⪰ 0` with `Tr Y ∂𝒢/∂yᵢ (y_opt) = dᵢ` for `i = 1, …, m+1`, where `d = (c, 0)`.
Complementary slackness `Tr(Y𝒢(y_opt)) = 0` is added: the printed stationarity-only
set makes Theorem 4.1 false (see DISPROOF.md). Appendix A explicitly uses complementarity.
The partial derivative `Tr Y ∂𝒢/∂yᵢ` is written as the partial derivative at `y_opt` of the scalar
map `y ↦ Tr Y 𝒢(y)` in the `i`-th coordinate direction: the coordinates of `x` give `cᵢ`, the
`τ` coordinate gives `0`. -/
def dualSet {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (τopt : ℝ)
    (yopt : (Fin m → ℝ) × ℝ) : Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
  {Y | (∃ (Z : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ), Y = dualMat Z μ) ∧ Y.PosSemidef ∧
    (∀ i : Fin m,
      fderiv ℝ (fun y : (Fin m → ℝ) × ℝ => (Y * Gcal D τopt y).trace) yopt
        (Pi.single i 1, 0) = c i) ∧
    fderiv ℝ (fun y : (Fin m → ℝ) × ℝ => (Y * Gcal D τopt y).trace) yopt (0, 1) = 0 ∧
    (Y * Gcal D τopt yopt).trace = 0}

/-- The quadratic growth condition (QGC, §4.3, p. 39) for problem (16) at `y⋆`: there are `α > 0`
and a Euclidean radius `ε > 0` such that every `y` feasible for (16) with `‖y − y⋆‖ < ε` satisfies
`dᵀy ≥ dᵀy⋆ + α‖y − y⋆‖²` (`d = (c, 0)`, `‖·‖` Euclidean on `ℝ^{m+1}`). -/
def QGC16 {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (τopt : ℝ)
    (ystar : (Fin m → ℝ) × ℝ) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ y : (Fin m → ℝ) × ℝ, Feasible16 D τopt y →
    SDPData.sqDist y ystar < ε ^ 2 → c ⬝ᵥ ystar.1 + α * SDPData.sqDist y ystar ≤ c ⬝ᵥ y.1

end RobustSDP.FullPert.Supplement


