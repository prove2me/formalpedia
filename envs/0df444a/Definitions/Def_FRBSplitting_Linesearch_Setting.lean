-- Prove2me | Definitions.Def_FRBSplitting_Linesearch_Setting
-- name    : FRBSplitting_Linesearch_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:59.906876+00:00
-- url     : https://prove2.me/theorems/9793c51e-b960-4a86-95a9-04a9d0bed27a
-- title:
--   Algorithm 1, p. 10 — the zero set (A+B)⁻¹(0), the linesearch trial point, and runs of the forward-reflected-backward method with linesearch
-- statement:
--   The objects of §3 of Malitsky and Tam. Throughout, $H$ is a real inner product space, $A:H\rightrightarrows H$ is set-valued and $B:H\to H$ is single-valued. The resolvent $J_{tA}=(I+tA)^{-1}$ is represented by a family of maps $J_t:H\to H$, $t>0$.
--
--   1. **Zero set** (imported from the shared module `FRBSplitting.Weak.Setting` as `FRBSplitting.Weak.zeroSet`, not redeclared here). $(A+B)^{-1}(0)=\{x\in H: 0\in A(x)+B(x)\}=\{x : -B(x)\in A(x)\}$.
--   2. **Trial point.** Given the current point $x_k$, the previous point $x_{k-1}$, the previous step $\lambda_{k-1}$ and a trial step $t$, the trial point of the linesearch is
--   $$x_{k+1}(t)=J_{t}\big(x_k-tB(x_k)-\lambda_{k-1}(B(x_k)-B(x_{k-1}))\big).$$
--   3. **Runs of Algorithm 1.** Fix $\delta,\sigma$. Sequences $(x_k)_{k\ge -1}$ and $(\lambda_k)_{k\ge -1}$ form a run of the forward-reflected-backward method with linesearch if for every $k\in\mathbb N$ there are $\rho\in\{1,\sigma^{-1}\}$ and $i\in\mathbb N$ such that
--   $$\lambda_k=\rho\lambda_{k-1}\sigma^i,\qquad x_{k+1}=x_{k+1}(\lambda_k),\qquad \lambda_k\|B(x_{k+1})-B(x_k)\|\le\frac{\delta}{2}\|x_{k+1}-x_k\| \quad(30),$$
--   and $i$ is the smallest such index: for every $j<i$ the trial step $t_j=\rho\lambda_{k-1}\sigma^j$ violates (30), i.e. $\frac{\delta}{2}\|x_{k+1}(t_j)-x_k\|<t_j\|B(x_{k+1}(t_j))-B(x_k)\|$.
--
--   The parameter $\rho$ may be chosen afresh in every iteration (Remark 3.1), so every sequence of such choices is a run. These are the objects every statement of the mission is phrased in; the operator vocabulary (monotone, maximally monotone, resolvent) is the published module `ThreeOpSplitting.Accel.MonotoneOperators`.
--
--   **Formalization Note.** Indices are shifted by one: Lean's `x j` is $x_{j-1}$ and `lam j` is $\lambda_{j-1}$, so `x 0` $=x_{-1}$, `x 1` $=x_0$, `lam 0` $=\lambda_{-1}$. The run predicate places no condition on the initial points. Algorithm 1's initialization also chooses $\lambda_0$, but the iteration recomputes $\lambda_k=\rho\lambda_{k-1}\sigma^i$ for every $k\ge0$, so $\lambda_0$ is never used and is not a parameter; only $\lambda_{-1}$ (`lam 0`) is data. The resolvent is a family `J` with values unconstrained for $t\le 0$; theorems assume it is a resolvent family of $A$.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, pp. 4, 9–10, (12), Algorithm 1 (29)–(30), Remark 3.1, proof of Lemma 3.2

import Mathlib
import Definitions.Def_FRBSplitting_Weak_Setting

namespace FRBSplitting.Linesearch

/-- The trial point x_{k+1}(t) := J_{tA}(x_k − tB(x_k) − λ_{k−1}(B(x_k) − B(x_{k−1}))) of the
linesearch (proof of Lemma 3.2, p. 10), for the current point `xk`, the previous point `xkm1`, the
previous step `lamPrev` = λ_{k−1} and the trial step `t`. -/
def trialPoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : ℝ → H → H) (B : H → H) (lamPrev t : ℝ) (xk xkm1 : H) : H :=
  J t (xk - t • B xk - lamPrev • (B xk - B xkm1))

/-- A run of Algorithm 1 with parameters `δ`, `σ`, with the index shift of the series:
`x j` is x_{j−1} and `lam j` is λ_{j−1} (so `lam 0` = λ_{−1}). In every iteration some
`ρ ∈ {1, σ⁻¹}` is chosen, `λ_k = ρ λ_{k−1} σ^i` with `i` the least index for which (30) holds, and
`x_{k+1}` is the trial point at `λ_k`. -/
def IsLinesearchRun {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (J : ℝ → H → H) (B : H → H) (δ σ : ℝ) (lam : ℕ → ℝ) (x : ℕ → H) : Prop :=
  ∀ k : ℕ, ∃ ρ : ℝ, (ρ = 1 ∨ ρ = σ⁻¹) ∧ ∃ i : ℕ,
    lam (k + 1) = ρ * lam k * σ ^ i ∧
    x (k + 2) = trialPoint J B (lam k) (lam (k + 1)) (x (k + 1)) (x k) ∧
    lam (k + 1) * ‖B (x (k + 2)) - B (x (k + 1))‖ ≤ δ / 2 * ‖x (k + 2) - x (k + 1)‖ ∧
    ∀ j < i, δ / 2 * ‖trialPoint J B (lam k) (ρ * lam k * σ ^ j) (x (k + 1)) (x k) - x (k + 1)‖ <
      ρ * lam k * σ ^ j *
        ‖B (trialPoint J B (lam k) (ρ * lam k * σ ^ j) (x (k + 1)) (x k)) - B (x (k + 1))‖

end FRBSplitting.Linesearch


