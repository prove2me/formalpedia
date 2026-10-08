-- Prove2me | Definitions.Def_AdamDyn_DecConv_ProofQuantities
-- name    : AdamDyn_DecConv_ProofQuantities
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:47.71742+00:00
-- url     : https://prove2.me/theorems/1201bdf5-c492-4d48-b1aa-00f0a29f76fd
-- title:
--   §9.1: the shifted iterates $\bar z_n$, the remainder $\varsigma_{n+1}$, the times $\tau_n$ and the interpolated process
-- statement:
--   Let $z_n = (x_n, m_n, v_n)$, $n \in \mathbb N$, be a run of Algorithm 5.1 with stepsizes $(\gamma_n, \alpha_n, \beta_n)$, constant $\varepsilon$ and bias-correction weights $r_n$, $\bar r_n$; write $\hat m_n = m_n / r_n$ and $\hat v_n = v_n / \bar r_n$. Fix $a, b$, a function $F$ and a map $S$ (in the mission, those of (2.2)).
--
--   1. The **shifted iterates** are $\bar z_n = (x_{n-1}, m_n, v_n)$; at $n = 0$ the convention $x_{-1} := x_0$ gives $\bar z_0 = (x_0, 0, 0)$.
--   2. The **remainder** $\varsigma_{n+1} = (\varsigma^x_{n+1}, \varsigma^m_{n+1}, \varsigma^v_{n+1})$ is
--   $$
--   \begin{aligned}
--   \varsigma^x_{n+1} &= \frac{m_n}{\varepsilon + \sqrt{v_n}} - \frac{\gamma_n}{\gamma_{n+1}} \frac{\hat m_n}{\varepsilon + \sqrt{\hat v_n}},\\
--   \varsigma^m_{n+1} &= \Big(\frac{1 - \alpha_{n+1}}{\gamma_{n+1}} - a\Big)(\nabla F(x_n) - m_n) + a(\nabla F(x_n) - \nabla F(x_{n-1})),\\
--   \varsigma^v_{n+1} &= \Big(\frac{1 - \beta_{n+1}}{\gamma_{n+1}} - b\Big)(S(x_n) - v_n) + b(S(x_n) - S(x_{n-1})),
--   \end{aligned}
--   $$
--   the first line coordinatewise. With the martingale increment $\chi_{n+1}$ of §9.1 one has the identity $\bar z_{n+1} = \bar z_n + \gamma_{n+1} h_\infty(\bar z_n) + \gamma_{n+1}\chi_{n+1} + \gamma_{n+1}\varsigma_{n+1}$.
--   3. The **interpolation times** are $\tau_n = \sum_{k=0}^n \gamma_k$.
--   4. The **interpolated process** is the piecewise-affine path
--   $$ \bar z(t) = \bar z_n + (t - \tau_n)\frac{\bar z_{n+1} - \bar z_n}{\gamma_{n+1}}, \qquad t \in [\tau_n, \tau_{n+1}),\ n \in \mathbb N, $$
--   and $\bar z(t) = \bar z_0$ for $0 \le t < \tau_0$.
--
--   These are the objects of the proof of Theorem 5.2: the iterates are read as a perturbed Euler scheme for $(\mathrm{ODE}_\infty)$, and the interpolated process is compared with the semiflow of that ODE.
--
--   **Formalization Note** `remainder … n` is $\varsigma_{n+1}$ and is used by the paper for $n \ge 1$; at $n = 0$ it is evaluated with $x_{-1} := x_0$ and has no role in any limit. The page defines $\bar z(t)$ only for $t \ge \tau_0 = \gamma_0$; the constant value $\bar z_0$ on $[0, \tau_0)$ keeps the path continuous and does not affect any asymptotic property. If $t \ge \tau_0$ lies in no interval $[\tau_n, \tau_{n+1})$ (impossible when $\gamma_n > 0$ and $\sum\gamma_n = \infty$), the value is $0$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, pp. 25–26, §9.1 (z̄_n, ς_{n+1}, τ_n, the interpolated process z̄)

import Mathlib
import Definitions.Def_AdamDyn_DecConv_Algorithm

namespace AdamDyn.DecConv

/-- The shifted iterate `z̄_n = (x_{n-1}, m_n, v_n)` of §9.1 (p. 25), computed from the run
`z_k = (x_k, m_k, v_k)` of Algorithm 5.1. At `n = 0` the convention `x_{-1} := x_0` is used
(natural-number subtraction), so `z̄_0 = (x_0, 0, 0)`. -/
noncomputable def zbar {d : ℕ} (z : ℕ → AdamDyn.WellPosed.State d) (n : ℕ) : AdamDyn.WellPosed.State d :=
  ((z (n - 1)).1, (z n).2.1, (z n).2.2)

/-- The remainder `ς_{n+1} = (ς^x_{n+1}, ς^m_{n+1}, ς^v_{n+1})` of §9.1 (pp. 25–26), as a
function of `n` and of the run `z_k = (x_k, m_k, v_k)` of Algorithm 5.1:
`ς^x_{n+1} = m_n/(ε + √v_n) − (γ_n/γ_{n+1}) m̂_n/(ε + √v̂_n)`,
`ς^m_{n+1} = ((1 − α_{n+1})/γ_{n+1} − a)(∇F(x_n) − m_n) + a(∇F(x_n) − ∇F(x_{n−1}))`,
`ς^v_{n+1} = ((1 − β_{n+1})/γ_{n+1} − b)(S(x_n) − v_n) + b(S(x_n) − S(x_{n−1}))`,
the first block coordinatewise. The page uses it for `n ≥ 1`; at `n = 0` the value
(with `x_{-1} := x_0`) plays no role in any limit. -/
noncomputable def remainder {d : ℕ} (γ α β : ℕ → ℝ) (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ)
    (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) (z : ℕ → AdamDyn.WellPosed.State d) (n : ℕ) : AdamDyn.WellPosed.State d :=
  (WithLp.toLp 2 (fun i => (z n).2.1 i / (ε + Real.sqrt ((z n).2.2 i)) -
      (γ n / γ (n + 1)) * (mHat α n (z n) i / (ε + Real.sqrt (vHat β n (z n) i)))),
    ((1 - α (n + 1)) / γ (n + 1) - a) • (gradient F (z n).1 - (z n).2.1) +
      a • (gradient F (z n).1 - gradient F (z (n - 1)).1),
    ((1 - β (n + 1)) / γ (n + 1) - b) • (S (z n).1 - (z n).2.2) +
      b • (S (z n).1 - S (z (n - 1)).1))

/-- The interpolation times `τ_n = Σ_{k=0}^{n} γ_k` of §9.1 (p. 26). -/
noncomputable def tau (γ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), γ k

open Classical in
/-- The interpolated process of §9.1 (p. 26):
`z̄(t) = z̄_n + (t − τ_n)(z̄_{n+1} − z̄_n)/γ_{n+1}` for `t ∈ [τ_n, τ_{n+1})`, `n ∈ ℕ`.
Here `zb n` stands for `z̄_n`. Before `τ_0 = γ_0` (an interval the page leaves out) the process
is set equal to `z̄_0`; if `t` lies in no interval `[τ_n, τ_{n+1})` and `t ≥ τ_0` (impossible
when `γ_n > 0` and `Σ γ_n = +∞`) the value is `0`. -/
noncomputable def interpProcess {d : ℕ} (γ : ℕ → ℝ) (zb : ℕ → AdamDyn.WellPosed.State d) (t : ℝ) : AdamDyn.WellPosed.State d :=
  if h : ∃ n, tau γ n ≤ t ∧ t < tau γ (n + 1) then
    zb (Classical.choose h) + ((t - tau γ (Classical.choose h)) / γ (Classical.choose h + 1)) •
      (zb (Classical.choose h + 1) - zb (Classical.choose h))
  else if t < tau γ 0 then zb 0 else 0

end AdamDyn.DecConv


