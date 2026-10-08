-- Prove2me | Definitions.Def_AdaGrad_Full_Algorithm2
-- name    : AdaGrad_Full_Algorithm2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T03:19:53.832618+00:00
-- url     : https://prove2.me/theorems/98315f8e-3d45-4948-92b5-47ba094ac7b0
-- title:
--   ADAGRAD with full matrices (Figure 2): $G_t$, $S_t=G_t^{1/2}$, $H_t=\delta I+S_t$ and its two runs
-- statement:
--   Given the subgradients $g_1,g_2,\dots\in\mathbb R^d$ observed so far, ADAGRAD with full matrices (Figure 2) maintains
--
--   1. the **outer product matrix** $G_t=\sum_{\tau=1}^t g_\tau g_\tau^\top$ (so $G_0=0$);
--   2. its positive semidefinite square root $S_t=G_t^{1/2}$;
--   3. the proximal matrix $H_t=\delta I+S_t$, with proximal function $\psi_t(x)=\tfrac12\langle x,H_tx\rangle$.
--
--   With step size $\eta>0$ and $\delta\ge0$, a **primal-dual run** (resp. **mirror-descent run**) of $T$ rounds starts at $x_1=0$ and, for $t=1,\dots,T$, receives $g_t\in\partial f_t(x_t)$ and computes $x_{t+1}$ by the update (3) (resp. (4)) with these $\psi_t$:
--   $$x_{t+1}\in\operatorname*{argmin}_{x\in\mathcal X}\Big\{\eta\Big\langle\tfrac1t\textstyle\sum_{\tau=1}^t g_\tau,x\Big\rangle+\eta\varphi(x)+\tfrac1t\psi_t(x)\Big\},\qquad x_{t+1}\in\operatorname*{argmin}_{x\in\mathcal X}\big\{\eta\langle g_t,x\rangle+\eta\varphi(x)+B_{\psi_t}(x,x_t)\big\}.$$
--
--   This is the algorithm whose regret Theorem 7 bounds by $\operatorname{tr}(G_T^{1/2})$.
--
--   **Formalization Note** $G_t^{1/2}$ is Mathlib's `CFC.sqrt` (the unique positive semidefinite square root, via the continuous functional calculus and the Loewner order of `MatrixOrder`). The matrix $H_t=\delta I+S_t$ is defined for every $t\ge0$; at $t=0$ it is $\delta I$, the value the analysis on p. 2135 uses in the dual norm $\|\cdot\|_{\psi_0^*}$. Figure 2's initialization $H_0=0$ is never used by either update, so this choice affects no run. The input conditions $\eta>0$, $\delta\ge0$ are hypotheses of the theorems, not part of the run predicate.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2134, Figure 2; p. 2122 (G_t)

import Mathlib
import Definitions.Def_AdaGrad_Full_QuadProx

namespace AdaGrad.Full

open scoped MatrixOrder

/-- The rank-one outer product `g g⊤` of a vector `g ∈ ℝ^d`. -/
def outer {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.vecMulVec (WithLp.ofLp g) (WithLp.ofLp g)

/-- The outer product matrix `G_t = ∑_{τ=1}^t g_τ g_τ⊤` (p. 2122; Figure 2, p. 2134). Rounds are
1-based; `G_0 = 0` (empty sum). -/
def G {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ τ ∈ Finset.Icc 1 t, outer (g τ)

/-- `S_t = G_t^{1/2}` (Figure 2, p. 2134): the positive semidefinite square root of `G_t`
(Mathlib's `CFC.sqrt` for the Loewner order on symmetric matrices). `S_0 = 0`. -/
noncomputable def S {d : ℕ} (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  CFC.sqrt (G g t)

/-- `H_t = δI + S_t` (Figure 2, p. 2134), so that `ψ_t(x) = ½⟨x, H_t x⟩ = psi (H δ g t) x`.
For `t = 0` this gives `H_0 = δI` (`S_0 = 0`), the value the analysis of p. 2135 uses for the dual
norm `‖·‖_{ψ*_0}`; Figure 2's initialization `H_0 = 0` is never used by the updates. -/
noncomputable def H {d : ℕ} (δ : ℝ) (g : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  δ • (1 : Matrix (Fin d) (Fin d) ℝ) + S g t

/-- `T` rounds of **ADAGRAD with full matrices** (Figure 2, p. 2134) using the primal-dual
subgradient update (3): `x_1 = 0`, and for `t = 1, …, T` the update (3) with
`ψ_t(x) = ½⟨x, (δI + G_t^{1/2}) x⟩`, where `g_t` is the subgradient received in round `t`. -/
def IsPrimalDualRun {d : ℕ} (η δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  x 1 = 0 ∧ IsQuadPrimalDualRun η X ϕ f (H δ g) x g T

/-- `T` rounds of **ADAGRAD with full matrices** (Figure 2, p. 2134) using the composite mirror
descent update (4): `x_1 = 0`, and for `t = 1, …, T` the update (4) with
`ψ_t(x) = ½⟨x, (δI + G_t^{1/2}) x⟩`, where `g_t` is the subgradient received in round `t`. -/
def IsMirrorDescentRun {d : ℕ} (η δ : ℝ) (X : Set (EuclideanSpace ℝ (Fin d)))
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (T : ℕ) : Prop :=
  x 1 = 0 ∧ IsQuadMirrorDescentRun η X ϕ f (H δ g) x g T

end AdaGrad.Full


