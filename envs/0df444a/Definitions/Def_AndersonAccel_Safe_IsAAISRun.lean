-- Prove2me | Definitions.Def_AndersonAccel_Safe_IsAAISRun
-- name    : AndersonAccel_Safe_IsAAISRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T22:05:52.541502+00:00
-- url     : https://prove2.me/theorems/913b0ee2-50aa-4087-93f5-f1b4e41b6ad4
-- title:
--   A run of Algorithm 3.1 (stabilized type-I Anderson acceleration, AA-I-S-m)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$, let $\bar\theta,\tau,\alpha,D,\epsilon\in\mathbb R$ and let $m\in\mathbb N$ be the max-memory. Write $g(x)=x-f(x)$, $g_k=g(x^k)$, $f_\alpha(x)=(1-\alpha)x+\alpha f(x)$, and $\bar U=\|g_0\|_2$. The predicate says that the sequences $x^k,\tilde x^k,s_k,y_k,\hat s_k,\tilde y_k$, the matrices $H_k$, the memories $m_k$ and the counter $n_{AA}$ are those produced by Algorithm 3.1 from the initial point $x^0$:
--
--   **Initialization.** $H_0=I$, $m_0=0$, $n_{AA}=0$, and $x^1=\tilde x^1=f_\alpha(x^0)$.
--
--   **Iteration $k=1,2,\dots$**
--   1. $m_k=m_{k-1}+1$.
--   2. $s_{k-1}=\tilde x^k-x^{k-1}$, $y_{k-1}=g(\tilde x^k)-g(x^{k-1})$.
--   3. $\hat s_{k-1}=s_{k-1}-\sum_{j=k-m_k}^{k-2}\dfrac{\hat s_j^Ts_{k-1}}{\hat s_j^T\hat s_j}\hat s_j$.
--   4. **Restart.** If $m_k=m+1$ or $\|\hat s_{k-1}\|_2<\tau\|s_{k-1}\|_2$, reset $m_k=1$, $\hat s_{k-1}=s_{k-1}$ and $H_{k-1}=I$ (for the remaining steps of this iteration only).
--   5. **Powell regularization.** $\theta_{k-1}=\phi_{\bar\theta}(\gamma_{k-1})$ with $\gamma_{k-1}=\hat s_{k-1}^TH_{k-1}y_{k-1}/\|\hat s_{k-1}\|^2$, and
--   $$\tilde y_{k-1}=\begin{cases}\theta_{k-1}y_{k-1}-(1-\theta_{k-1})g_{k-1} & \text{if } m_k\ge2,\\ \theta_{k-1}y_{k-1}+(1-\theta_{k-1})s_{k-1} & \text{if } m_k=1.\end{cases}$$
--   6. $H_k=H_{k-1}+\dfrac{(s_{k-1}-H_{k-1}\tilde y_{k-1})\hat s_{k-1}^TH_{k-1}}{\hat s_{k-1}^TH_{k-1}\tilde y_{k-1}}$ and $\tilde x^{k+1}=x^k-H_kg_k$.
--   7. **Safeguard.** If $\|g_k\|_2\le D\bar U(n_{AA}+1)^{-(1+\epsilon)}$, then $x^{k+1}=\tilde x^{k+1}$ and $n_{AA}$ increases by one; otherwise $x^{k+1}=f_\alpha(x^k)$.
--
--   The algorithm interleaves Anderson-type quasi-Newton steps with averaged fixed-point steps, and accepts an accelerated step only when the residual is below a summable threshold. Given $f$, the parameters and $x^0$, every sequence of a run is determined by this recursion.
--
--   **Formalization Note** `nAA k` is the counter's value when iteration $k\ge1$ reaches the safeguard test (so `nAA 1 = 0`); `mem k` is $m_k$ after the restart test. The reset of $H_{k-1}$ in step 4 is local (`Hp`): the stored `H (k-1)` is unchanged. Vectors live in `EuclideanSpace ℝ (Fin n)` and matrices are continuous linear maps. The parameter ranges $\bar\theta,\tau,\alpha\in(0,1)$, $D,\epsilon>0$, $m\ge1$ are hypotheses of the theorems, not of this predicate. **Line 9 is stated as in Eq. (3.3).** The paper prints $\tilde y_{k-1}=\theta_{k-1}y_{k-1}-(1-\theta_{k-1})g_{k-1}$ for every $k$, derived from (3.3) via $B_{k-1}s_{k-1}=-g_{k-1}$ (p. 3178). That identity fails at a window start ($m_k=1$: at $k=1$, where $s_0=-\alpha g_0$, and right after a restart, where the matrix of (3.3) is $B^0=I$); there (3.3) gives $\theta_{k-1}y_{k-1}+(1-\theta_{k-1})s_{k-1}$, which is what is used. The two expressions agree whenever $m_k\ge2$. Division by zero ($x/0=0$ in Lean) can occur only once some $g_k=0$, after which all later iterates equal $x^k$.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3180, Algorithm 3.1 (line 9 as in Eq. (3.3), p. 3176, at m_k = 1); p. 3177, rule (3.7); p. 3178, Section 3.3

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic

namespace AndersonAccel.Safe

open InnerProductSpace

/-- `IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA` says that the sequences are the
iterates and internal quantities of Algorithm 3.1 (AA-I-S-m) of Zhang–O'Donoghue–Boyd (2020, p. 3180)
started from `x 0`, with line 9 as in Eq. (3.3) at a window start (see the natural-language statement).

* `x k = x^k`, `xt k = x̃^k`, `s k = s_k`, `y k = y_k`, `shat k = ŝ_k`, `ytil k = ỹ_k`, `H k = H_k`;
* `mem k = m_k` (the memory after the restart check of iteration `k`);
* `nAA k` = the value of the counter `n_AA` when iteration `k ≥ 1` reaches line 12;
* `Ū = ‖g(x^0)‖`.

Initialisation (line 2): `H_0 = I`, `m_0 = 0`, `n_AA = 0`, `x^1 = x̃^1 = f_α(x^0)`.
Iteration `k ≥ 1` (lines 4–14): see the body. -/
def IsAAISRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (θbar τ α D ε : ℝ) (m : ℕ)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (mem nAA : ℕ → ℕ) : Prop :=
  -- line 2
  H 0 = 1 ∧ mem 0 = 0 ∧ nAA 1 = 0 ∧ x 1 = fAlpha f α (x 0) ∧ xt 1 = fAlpha f α (x 0) ∧
  ∀ k : ℕ, 1 ≤ k →
    -- line 4: tentative memory
    let mk := mem (k - 1) + 1
    -- line 6: orthogonalization against the stored ŝ_j, j = k - m_k, …, k - 2
    let sGS := s (k - 1) - ∑ j ∈ Finset.Ico (k - mk) (k - 1),
      (inner ℝ (shat j) (s (k - 1)) / inner ℝ (shat j) (shat j)) • shat j
    -- line 7: restart test
    let restart : Prop := mk = m + 1 ∨ ‖sGS‖ < τ * ‖s (k - 1)‖
    -- line 8: the local reset of H_{k-1} (used only in lines 9–11 of this iteration)
    let Hp := if restart then (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      else H (k - 1)
    -- line 10
    let γ := inner ℝ (shat (k - 1)) (Hp (y (k - 1))) / ‖shat (k - 1)‖ ^ 2
    let θ := phiTheta θbar γ
    -- line 12: the safeguard threshold
    let Ubar := ‖residual f (x 0)‖
    let accept : Prop :=
      ‖residual f (x k)‖ ≤ D * Ubar * ((nAA k : ℝ) + 1) ^ (-(1 + ε))
    -- line 5
    s (k - 1) = xt k - x (k - 1) ∧
    y (k - 1) = residual f (xt k) - residual f (x (k - 1)) ∧
    -- lines 7–8
    mem k = (if restart then 1 else mk) ∧
    shat (k - 1) = (if restart then s (k - 1) else sGS) ∧
    -- line 9 (Eq. (3.3): at a window start, B s_{k-1} is s_{k-1} since B = I)
    ytil (k - 1) = (if mem k = 1 then θ • y (k - 1) + (1 - θ) • s (k - 1)
      else θ • y (k - 1) - (1 - θ) • residual f (x (k - 1))) ∧
    -- line 11
    H k = Hp + (inner ℝ (shat (k - 1)) (Hp (ytil (k - 1))))⁻¹ •
      ((rankOne ℝ (s (k - 1) - Hp (ytil (k - 1))) (shat (k - 1))).comp Hp) ∧
    xt (k + 1) = x k - H k (residual f (x k)) ∧
    -- lines 12–14
    (accept → x (k + 1) = xt (k + 1) ∧ nAA (k + 1) = nAA k + 1) ∧
    (¬ accept → x (k + 1) = fAlpha f α (x k) ∧ nAA (k + 1) = nAA k)

end AndersonAccel.Safe


