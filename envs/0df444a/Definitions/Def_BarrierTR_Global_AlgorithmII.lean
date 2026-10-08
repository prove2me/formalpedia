-- Prove2me | Definitions.Def_BarrierTR_Global_AlgorithmII
-- name    : BarrierTR_Global_AlgorithmII
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:12.20272+00:00
-- url     : https://prove2.me/theorems/1dd255b0-77b7-472b-a750-a1e66812512b
-- title:
--   §5, p. 34 — Algorithm II: Algorithm I for barrier parameters μ_l ↓ 0 with stopping test (5.1)–(5.2)
-- statement:
--   **Algorithm II** (p. 34) chooses $\mu_1>0$, $a\in(0,1)$, tolerances $\varepsilon_l\to0$ and a starting point $(x_1,s_1)$. At outer iteration $l$ it applies Algorithm I with barrier parameter $\mu_l$, from the point where the previous outer iteration stopped, until it finds a point $(x_{k_l},s_{k_l})$ with
--   $$\|g_{k_l}+s_{k_l}\|\le\varepsilon_l\quad(5.1),\qquad\|\nabla f_{k_l}+A_{k_l}\lambda_{k_l}\|\le\varepsilon_l\quad(5.2),\qquad\lambda_{k_l}=\mu_l S_{k_l}^{-1}e,$$
--   then chooses $\mu_{l+1}\in(0,a\mu_l)$ and continues.
--
--   In the formalization outer iterations are numbered from $l=0$; run $l$ is a run of Algorithm I with data $P_l$ (barrier parameter $\mu_l$) and $K_l\in\mathbb N\cup\{\infty\}$ is the first index at which it passes (5.1)–(5.2), $K_l=\infty$ if it never does. The run is required to be valid up to $K_l$, and run $l+1$ starts at run $l$'s point of index $K_l$. All conditions on run $l$ are imposed only when every earlier run stopped, since otherwise outer iteration $l$ never happens.
--
--   This is the overall method whose convergence is Theorem 5.1.
--
--   **Formalization Note** The starting point of each inner run (index $0$) is tested too. The tolerances are positive, $\varepsilon_l>0$. The other constants of Algorithm I ($\Delta_0$, $\nu_{-1}$, $\xi,\dots$) may differ between inner runs, which is more general than restarting with the same ones.
-- source:
--   Byrd, Gilbert, Nocedal, A trust region method based on interior point techniques for nonlinear programming, INRIA RR-2896 (1996), HAL inria-00073794v1, p. 34, Algorithm II, (5.1)–(5.2)

import Mathlib
import Definitions.Def_BarrierTR_Global_AlgorithmI

namespace BarrierTR.Global

open scoped RealInnerProductSpace
open Filter Topology

variable {n m : ℕ}

/-- The stopping test (5.1)–(5.2) of Algorithm II at `(x, s)` for the barrier parameter `μ` and the
tolerance `ε`: `‖g(x) + s‖ ≤ ε` and `‖∇f(x) + A(x)λ‖ ≤ ε` with `λ = μ S⁻¹ e`. -/
def StopTest (f : E n → ℝ) (g : E n → F m) (μ ε : ℝ) (x : E n) (s : F m) : Prop :=
  ‖g x + s‖ ≤ ε ∧ ‖gradient f x + A g x (μ • sInvE s)‖ ≤ ε

/-- A run of Algorithm II (§5, p. 34), with outer iterations indexed from `l = 0` (the paper's
`l = 1`): barrier parameters `μ_l` with `μ_0 > 0` and `μ_{l+1} ∈ (0, a μ_l)`, `a ∈ (0, 1)`;
positive tolerances `ε_l → 0`; and for outer iteration `l` a run `R l` of Algorithm I with data
`P l` (barrier parameter `μ_l`), started at `(x₁, s₁)` for `l = 0` and at the point where run
`l − 1` stopped otherwise. `K l` is the first index (index `0`, the starting point, included) at
which run `l` passes the stopping test (5.1)–(5.2), and `K l = ⊤` if it never does; then run `l`
is infinite and there is no outer iteration after it. Conditions on run `l` are imposed only when
every earlier run stopped. -/
structure IsAlgIIRun (f : E n → ℝ) (g : E n → F m) (μ ε : ℕ → ℝ) (a : ℝ) (x₁ : E n) (s₁ : F m)
    (P : ℕ → Params n m) (R : ℕ → RunData n m) (K : ℕ → ℕ∞) : Prop where
  μ_pos : 0 < μ 0
  a_mem : 0 < a ∧ a < 1
  μ_next : ∀ l, 0 < μ (l + 1) ∧ μ (l + 1) < a * μ l
  ε_pos : ∀ l, 0 < ε l
  ε_lim : Tendsto ε atTop (𝓝 0)
  barrier : ∀ l, (P l).μ = μ l
  start : (R 0).x 0 = x₁ ∧ (R 0).s 0 = s₁
  restart : ∀ l (k : ℕ), (∀ j < l, K j ≠ ⊤) → K l = k →
    (R (l + 1)).x 0 = (R l).x k ∧ (R (l + 1)).s 0 = (R l).s k
  run : ∀ l, (∀ j < l, K j ≠ ⊤) → IsRunUpTo (P l) f g (R l) (K l)
  stop : ∀ l (k : ℕ), (∀ j < l, K j ≠ ⊤) → K l = k →
    StopTest f g (μ l) (ε l) ((R l).x k) ((R l).s k)
  no_stop_before : ∀ l (k : ℕ), (∀ j < l, K j ≠ ⊤) → (k : ℕ∞) < K l →
    ¬ StopTest f g (μ l) (ε l) ((R l).x k) ((R l).s k)

end BarrierTR.Global


