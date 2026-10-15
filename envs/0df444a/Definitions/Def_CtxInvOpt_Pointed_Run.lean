-- Prove2me | Definitions.Def_CtxInvOpt_Pointed_Run
-- name    : CtxInvOpt_Pointed_Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T10:13:22.243064+00:00
-- url     : https://prove2.me/theorems/8e1b87e1-029a-4061-a2c0-b0e30d8edfdb
-- title:
--   Algorithm 2 (EllipsoidalCones), p. 21; I^π_T, p. 20 — runs of EllipsoidalCones and the number of cone-update periods
-- statement:
--   Algorithm EllipsoidalCones (p. 21) with parameter $\epsilon$ keeps an ellipsoidal cone $E(W_t,U_t)\supseteq C(\mathcal I_t)$ and uses its axis $U_te_1$ as the proxy cost.
--
--   1. **Initialization.** $W_1=\tan^2\alpha(C_0)\,I_{d-1}$, and $U_1$ is orthonormal with first column a circumcenter of $C_0$ ("rotate $C_0$ to place the circumcenter of $C_0$ at $e_1$").
--   2. **Period $t$.** The policy plays any $x^\pi_t\in\psi(U_te_1,\mathcal X_t,f_t)$; nature reveals some $x^\star_t\in\psi(c^\star,\mathcal X_t,f_t)$; let $\delta^\pi_t$ be the effective difference of $f_t(x^\pi_t)-f_t(x^\star_t)$ and $\bar\delta=U_t^{-1}\delta^\pi_t$. If
--   $$\bar\delta_{[2:d]}'\,W_t\,\bar\delta_{[2:d]}\le\epsilon^2\qquad(12)$$
--   then $(W_{t+1},U_{t+1})=(W_t,U_t)$; otherwise $(W_{t+1},U_{t+1})$ is an output of $\mathrm{ConeUpdate}(W_t,U_t,\delta^\pi_t,0,I_d,d)$, and $t$ is a **cone-update period**.
--   3. $I^\pi_t$ is the number of cone-update periods among the first $t$ periods.
--
--   The run predicate quantifies over every admissible behaviour of nature, which may be adaptive, and every tie-breaking of the policy.
--
--   **Formalization Note** Periods are $0$-based: Lean period $t$ is the paper's $t+1$, and `w t`, `U t` are the paper's $W_{t+1}$, $U_{t+1}$. The printed "$U_1\leftarrow I_{d-1}$" has the wrong size and the rotation is left implicit; the run requires $U_1$ orthonormal with a circumcenter of $C_0$ as first column, and the cones are $E(W_t,U_t)$. `updateCount … t` counts the Lean periods $s<t$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 19 (12), p. 20 (I^π_T), p. 21 Algorithm 2 (EllipsoidalCones)

import Mathlib
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Pointed_ConeUpdate

namespace CtxInvOpt.Pointed

open Matrix

/-- **(12), p. 19; Algorithm 2, p. 21.** Lean period `t` is a cone-update period of the run: with
`δ^π_t = effDiff (f_t(x^π_t) − f_t(x⋆_t))` and `δ̄ = U_t⁻¹δ^π_t`, the test (12)
`δ̄′_{[2:d]} W_t δ̄_{[2:d]} ≤ ε²` fails. -/
def IsUpdatePeriod {n m : ℕ} (ε : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
    (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (t : ℕ) : Prop :=
  ε ^ 2 < tailQuad (w t) (rotCoord (U t) (effDiff (f t (xpi t) - f t (xstar t))))

/-- **p. 20.** The number `I^π_t = Σ_s 1{δ̄′_{s,[2:d]} W_s δ̄_{s,[2:d]} > ε²}` of cone-update periods among
the Lean periods `s < t` (the paper's periods `1, …, t`). -/
noncomputable def updateCount {n m : ℕ} (ε : ℝ)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
    (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (t : ℕ) : ℕ := by
  classical
  exact ((Finset.range t).filter (fun s => IsUpdatePeriod ε f xpi xstar w U s)).card

/-- **Algorithm 2 (EllipsoidalCones), p. 21.** `(w, U)` is a run of EllipsoidalCones with parameter `ε`
from the initial knowledge set `C0 ⊆ S^{m+1}`, against the (arbitrary, adaptive) instance sequence
`X, f`, true cost `cstar` and expert actions `xstar`. Lean period `t` is the paper's period `t + 1`;
`w t`, `U t` are the paper's `W_{t+1}`, `U_{t+1}`.

* Initialization: `W₁ = tan² α(C₀) I_{d−1}`, and `U₁` is an orthonormal matrix whose first column is a
  circumcenter of `C₀` ("rotate `C₀` to place the circumcenter of `C₀` at `e₁`").
* Every period: `x^π_t ∈ ψ(U_t e₁, X_t, f_t)` (any minimizer), `x⋆_t ∈ ψ(c⋆, X_t, f_t)` (any
  minimizer); if (12) holds, `(W_{t+1}, U_{t+1}) = (W_t, U_t)`, otherwise `(W_{t+1}, U_{t+1})` is an output
  of `ConeUpdate(W_t, U_t, δ^π_t, 0, I_d, d)`. -/
def IsEllConesRun {n m : ℕ} (ε : ℝ) (C0 : Set (EuclideanSpace ℝ (Fin (m + 1))))
    (cstar : EuclideanSpace ℝ (Fin (m + 1)))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (m + 1)))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (w : ℕ → Fin m → ℝ)
    (U : ℕ → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) : Prop :=
  w 0 = (fun _ => Real.tan (CtxInvOpt.Offline.uncAngle C0) ^ 2) ∧
  U 0 ∈ Matrix.orthogonalGroup (Fin (m + 1)) ℝ ∧
  CtxInvOpt.Offline.IsCircumcenter C0 (axisVec (U 0)) ∧
  ∀ t, xpi t ∈ CtxInvOpt.Offline.argminSet (axisVec (U t)) (X t) (f t) ∧
    xstar t ∈ CtxInvOpt.Offline.argminSet cstar (X t) (f t) ∧
    (¬ IsUpdatePeriod ε f xpi xstar w U t → w (t + 1) = w t ∧ U (t + 1) = U t) ∧
    (IsUpdatePeriod ε f xpi xstar w U t →
      IsConeUpdate (w t) (U t) (effDiff (f t (xpi t) - f t (xstar t))) (w (t + 1)) (U (t + 1)))

end CtxInvOpt.Pointed


