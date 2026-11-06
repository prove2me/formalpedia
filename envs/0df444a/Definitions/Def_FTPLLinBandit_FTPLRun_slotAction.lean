-- Prove2me | Definitions.Def_FTPLLinBandit_FTPLRun_slotAction
-- name    : FTPLLinBandit_FTPLRun_slotAction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:05:13.779731+00:00
-- url     : https://prove2.me/theorems/98189a79-01e1-471b-a3ee-b43553b98157
-- title:
--   SampleAction$(\hat\Theta_t,\rho_t)$: the action of slot $j$ in round $t$
-- statement:
--   Given a run and the estimates $\hat\theta_\tau$ of the earlier rounds $\tau<t$, slot $j$ of round $t$ returns
--   $$\begin{cases}X & \text{if } U<\gamma,\\ x\big(\hat\Theta_t+Z\big) & \text{otherwise,}\end{cases}\qquad \hat\Theta_t=\sum_{\tau<t}\hat\theta_\tau,$$
--   with the slot's own draws $U,X,W,\xi$ and perturbation $Z=\sqrt\lambda\,W+\sum_{\tau<t}\xi_\tau\hat\theta_\tau$ (random weighting) or $Z=B(\Sigma_t)W$, $\Sigma_t=\lambda I+\sum_{\tau<t}\hat\theta_\tau\hat\theta_\tau^\top$ (elliptical). This is the procedure SampleAction of Algorithm 1 (lines 10–16): explore with probability $\gamma$, otherwise play the perturbed leader.
--
--   **Formalization Note** Only the estimates of rounds $\tau<t$ are read. $\hat\Theta_0=0$ is the initialization $\hat\Theta_1\leftarrow0$ in $0$-based indexing.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Algorithm 1, lines 10–16, p.8

import Mathlib
import Definitions.Def_FTPLLinBandit_FTPLRun
import Definitions.Def_FTPLLinBandit_shapeMat

open MeasureTheory

namespace FTPLLinBandit

variable {d : ℕ} {A : Set (EuclideanSpace ℝ (Fin d))} {ν : Measure (EuclideanSpace ℝ (Fin d))}
  {x : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)} {s : Scheme} {γ β : ℝ} {N : ℕ}
  {lam : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`SampleAction(Θ̂_t, ρ_t)` of Algorithm 1, slot `j` of round `t`.** Wei, arXiv:2610.17818,
Algorithm 1, lines 10–16, p.8: "Draw e ∼ Bernoulli(γ). if e = 1 then Draw an action a ∼ ν and
return a. else Draw a perturbation Z ∼ ρ. return an action in arg max_{a∈A}⟨a, Θ + Z⟩, using a
fixed tie-breaking rule."

Given the estimates `past τ` of the earlier rounds `τ < t`, the slot returns the exploration draw
`X` if its coin `U < γ`, and otherwise `x(Θ̂_t + Z)` with `Θ̂_t = ∑_{τ<t} past τ` and
`Z = √λ W + ∑_{τ<t} ξ_τ past τ` (random weighting) or `Z = sq(Σ_t) W`,
`Σ_t = λI + ∑_{τ<t} past τ (past τ)ᵀ` (elliptical).

**Formalization Note.** Only `past τ` for `τ < t` is read. Rounds are indexed from `0`, so
`Θ̂_0 = 0` is Algorithm 1's initialization `Θ̂_1 ← 0`. Matrices act on coordinate vectors
(`Matrix.toEuclideanLin`). -/
noncomputable def FTPLRun.slotAction (run : FTPLRun A ν x s γ β N lam Ω P)
    (past : ℕ → EuclideanSpace ℝ (Fin d)) (t : ℕ) (j : Fin (2 * N + 2)) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  if run.U t j ω < γ then run.X t j ω
  else x ((∑ τ ∈ Finset.range t, past τ) +
    match s with
    | .randomWeighting _ _ => Real.sqrt lam • run.W t j ω + ∑ τ : Fin t, run.ξ t j ω τ • past τ
    | .elliptical _ =>
        Matrix.toEuclideanLin (run.sq (shapeMat lam (fun τ : Fin t => past τ))) (run.W t j ω))

end FTPLLinBandit


