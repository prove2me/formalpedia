-- Prove2me | Definitions.Def_KallMayerSLP_Multistage_stageMin
-- name    : KallMayerSLP_Multistage_stageMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:52.898988+00:00
-- url     : https://prove2.me/theorems/8e1eba3b-0828-408f-934a-ee0e725a3bbc
-- title:
--   The stage problem of the recursions (3.15) and (3.17)
-- statement:
--   For a right-hand side $\rho$, a cost-to-go $\Phi$ and earlier decisions $z_{t-1}=\{x_1,\dots,x_{t-1}\}$, the stage problem is
--   $$
--   \min_{x_t}\ \{c_t^{\mathsf T}x_t+\Phi(z_t)\}\quad\text{s.t.}\quad A_{tt}x_t=\rho-\sum_{\tau=1}^{t-1}A_{t\tau}x_\tau,\quad x_t\ge0,
--   $$
--   with $z_t=\{x_1,\dots,x_t\}$. Both recursions are built from it, with different $\rho$ and $\Phi$.
--
--   **Formalization Note** The sequence $z_{t-1}$ is a full family of decisions, of which only the coordinates $\tau<t$ enter; $z_t$ updates coordinate $t$. The $\min$ is an infimum in the extended reals.
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 3, (3.15) and (3.17), pp.263–264 (PDF 272–273)

import Mathlib
import Definitions.Def_KallMayerSLP_Multistage_MSLP

namespace KallMayerSLP.Multistage

open scoped Matrix

/-- The stage problem shared by the recursions (3.15) and (3.17) (Kall & Mayer, *Stochastic Linear
Programming* (2005), Chapter 3, pp.263–264, PDF 272–273): for a right-hand side `rhs`, a cost-to-go
`Φ` and earlier decisions `z`,
`min_{x_t} {c_tᵀ x_t + Φ(z_t)}` s.t. `A_tt x_t = rhs − Σ_{τ=1}^{t-1} A_{tτ} x_τ`, `x_t ≥ 0`.

**Formalization Note.** The sequence `z_{t-1} = {x_1, …, x_{t-1}}` of the book is a full family
`z : ∀ τ, Fin (D.n τ) → ℝ`, of which only the coordinates `τ < t` enter here, and
`z_t = {x_1, …, x_t}` is `Function.update z t x`. The `min` is an infimum in `EReal`: `+∞` when the
constraints are infeasible, `-∞` when unbounded. -/
noncomputable def stageMin (D : MSLP) (t : ℕ) (rhs : Fin (D.m t) → ℝ)
    (Φ : (∀ τ, Fin (D.n τ) → ℝ) → EReal) (z : ∀ τ, Fin (D.n τ) → ℝ) : EReal :=
  ⨅ (x : Fin (D.n t) → ℝ)
    (_ : 0 ≤ x ∧ D.A t t *ᵥ x = rhs - ∑ τ ∈ Finset.Ico 1 t, D.A t τ *ᵥ z τ),
    ((D.c t ⬝ᵥ x : ℝ) : EReal) + Φ (Function.update z t x)

end KallMayerSLP.Multistage


