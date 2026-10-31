-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_MSLP
-- name    : KallMayerSLP_Multistage_MSLP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:54.287712+00:00
-- url     : https://prove2.me/theorems/9db236e4-69b0-4e12-8193-6b15bd1e35e9
-- title:
--   Data of the multi-stage SLP (3.10): only the right-hand sides random
-- statement:
--   The data of the multi-stage stochastic linear program
--   $$
--   \min\Big\{c_1^{\mathsf T}x_1+\mathbb E\sum_{t=2}^T c_t^{\mathsf T}x_t(\zeta_t)\Big\}
--   \quad\text{s.t.}\quad A_{11}x_1=b_1,\quad A_{t1}x_1+\sum_{\tau=2}^tA_{t\tau}x_\tau(\zeta_\tau)=b_t(\zeta_t)\ \text{a.s.},\quad x_1\ge0,\ x_t(\zeta_t)\ge0\ \text{a.s.}
--   $$
--   are a number $T\ge1$ of stages; dimensions $n_t$ (decisions), $m_t$ (constraints), $r_t$ (random entries); deterministic cost vectors $c_t\in\mathbb R^{n_t}$; deterministic matrices $A_{t\tau}\in\mathbb R^{m_t\times n_\tau}$, $\tau\le t$; and right-hand sides $b_t$ that are linear affine functions of the state $\zeta_t$.
--
--   This is the deterministic part of problem (3.10), on which every statement of the mission is built.
--
--   **Formalization Note** Every field is indexed by the book's stage $t\in\mathbb N$; only $t\in\{1,\dots,T\}$ is used. Since the state space of stage 1 is a point, $b_1$ is a constant.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.10), p.261 (PDF 270), and Assumption 3.2, first item, p.262 (PDF 271)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_Hist

namespace KallMayerSLP.Multistage

/-- The data of the multi-stage stochastic linear program (3.10) with only the right-hand sides
random (Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, (3.10), p.261, PDF 270, and
Assumption 3.2, first item, p.262, PDF 271):

* `T ≥ 1` stages; `n t` decision variables, `m t` constraints and `r t` random entries at stage `t`;
* deterministic cost vectors `c t` and deterministic matrices `A t τ` (used for `τ ≤ t`);
* right-hand sides `b t`, linear affine in the state `ζ_t ∈ Hist r t`.

**Formalization Note.** Every field is indexed by the book's 1-based stage `t : ℕ`; only
`t ∈ {1, …, T}` (and `τ ≤ t` for `A t τ`) is ever used. Since `Hist r 1` is a single point, `b 1` is
the constant `b_1`. "Linear affine in `ζ_t`" (the book's phrase, which also allows `b_t` to depend
on every earlier `ξ_s`) is `→ᵃ[ℝ]` on `Hist r t`. Randomness itself (the probability space and the
vectors `ξ_t`) is not part of this structure. -/
structure MSLP where
  /-- The number of stages. -/
  T : ℕ
  one_le_T : 1 ≤ T
  /-- `n t` is the dimension of the decision `x_t`. -/
  n : ℕ → ℕ
  /-- `m t` is the number of constraints of stage `t`. -/
  m : ℕ → ℕ
  /-- `r t` is the dimension of the random vector `ξ_t`. -/
  r : ℕ → ℕ
  /-- The cost vector `c_t`. -/
  c : ∀ t, Fin (n t) → ℝ
  /-- The matrix `A_{tτ}`. -/
  A : ∀ t τ, Matrix (Fin (m t)) (Fin (n τ)) ℝ
  /-- The right-hand side `b_t(ζ_t)`. -/
  b : ∀ t, Hist r t →ᵃ[ℝ] (Fin (m t) → ℝ)

end KallMayerSLP.Multistage


