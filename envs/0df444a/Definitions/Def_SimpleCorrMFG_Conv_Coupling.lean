-- Prove2me | Definitions.Def_SimpleCorrMFG_Conv_Coupling
-- name    : SimpleCorrMFG_Conv_Coupling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:17:31.893489+00:00
-- url     : https://prove2.me/theorems/a93a2d34-0fc5-43e6-aaa2-84eead279ffc
-- title:
--   Proof of Theorem 6.1, Steps Two–Three, pp. 20–22, (6.1) — the coupled systems $\tilde X^N$ and $\hat X^N$
-- statement:
--   This file defines the two auxiliary $N$-player systems used in the proof of Theorem 6.1, both on the canonical $N$-player sample space and driven by the same initial states, recommendations and noises.
--
--   **The system $\tilde X$ (Step Two, p. 20).** For a strategy modification $u$, $\tilde X_j(0)=X_j(0)$, player 1 moves by $\tilde X_1(t+1)=\Psi(t,\tilde X_1(t),\tilde\mu_1(t),u\circ\Phi_1(t,\tilde X_1(t)),\xi_1(t+1))$ and every $j\neq1$ by $\tilde X_j(t+1)=\Psi(t,\tilde X_j(t),\tilde\mu_j(t),\Phi_j(t,\tilde X_j(t)),\xi_j(t+1))$, where
--   $$\tilde\mu_j(t)=\frac1{N-1}\sum_{l\neq j}\delta_{\tilde X_l(t)}.$$
--   This is the state process of the realization of $(\mathfrak m^N,\gamma^N,u)$ for player 1.
--
--   **The system $\hat X$ (Step Three, p. 21).** For $j\in\{2,\dots,N\}$, $\hat X_j(0)=X_j(0)$ and
--   $$\hat X_j(t+1)=\Psi\big(t,\hat X_j(t),\hat\mu_1(t),\Phi_j(t,\hat X_j(t)),\xi_j(t+1)\big),\qquad \hat\mu_1(t)=\frac1{N-1}\sum_{l=2}^N\delta_{\hat X_l(t)}.\tag{6.1}$$
--   Every player uses the same measure $\hat\mu_1(t)$, which excludes player 1.
--
--   **Formalization Note** The paper's player 1 is index `0`. `hatPath` also computes a component of index `0` by the same rule; it does not enter $\hat\mu_1$ and no statement uses it. `tildePath` is `nPath` with deviating player `0`.
-- source:
--   Campi & Fischer, Correlated equilibria and mean field games: a simple model, arXiv:2004.06185v2, pp. 20–22 (proof of Theorem 6.1, Step Two: X̃, μ̃; Step Three: X̂, (6.1))

import Mathlib
import Definitions.Def_SimpleCorrMFG_Conv_Model
import Definitions.Def_SimpleCorrMFG_Conv_NPlayer

namespace SimpleCorrMFG.Conv

open MeasureTheory ProbabilityTheory unitInterval

variable {T : ℕ} {X Γ : Type} [Fintype X] [DecidableEq X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSpace Γ]

/-- The decoupled system of Step Three (p. 21) on the canonical `N`-player sample space:
`X̂_j(0) = X_j(0)` and `X̂_j(t+1) = Ψ(t, X̂_j(t), μ̂_1(t), Φ_j(t, X̂_j(t)), ξ_j(t+1))`, where every
player uses the same measure `μ̂_1(t) = (N−1)⁻¹ ∑_{l=2}^N δ_{X̂_l(t)}` of (6.1). The paper's player 1
is index `0`; the component of index `0` is computed by the same rule but is not used (the paper
defines `X̂_j` only for `j ∈ {2, …, N}`, and `μ̂_1` does not involve it). -/
noncomputable def hatPath (M : Model T X Γ) {N : ℕ} [NeZero N] (ω : NOmega T N X Γ) :
    Fin (T + 1) → Fin N → X :=
  iterFin ω.1 (fun t x j => M.Ψ t (x j) (empOthers x 0) (ω.2.1 j t (x j)) (ω.2.2 t j))

/-- `μ̂_1^N(t) = (N−1)⁻¹ ∑_{l=2}^N δ_{X̂_l^N(t)}`, (6.1), p. 22. -/
noncomputable def hatEmp (M : Model T X Γ) {N : ℕ} [NeZero N] (ω : NOmega T N X Γ)
    (t : Fin (T + 1)) : Meas X :=
  empOthers (hatPath M ω t) 0

/-- The system `X̃` of Step Two (p. 20) for the strategy modification `u`: player 1 (index `0`)
plays `u ∘ Φ_1`, every other player follows `Φ_j`, each against the empirical measure
`μ̃_j(t) = (N−1)⁻¹ ∑_{l ≠ j} δ_{X̃_l(t)}` of the others, and `X̃(0) = X(0)`. It is the state process
of the realization of `(m^N, γ^N, u)` for player 1 on the canonical sample space. -/
noncomputable def tildePath (M : Model T X Γ) {N : ℕ} [NeZero N] (u : Strat T X Γ → Strat T X Γ)
    (ω : NOmega T N X Γ) : Fin (T + 1) → Fin N → X :=
  nPath M 0 u ω

/-- `μ̃_j^N(t) = (N−1)⁻¹ ∑_{l ≠ j} δ_{X̃_l^N(t)}` (p. 20). -/
noncomputable def tildeEmp (M : Model T X Γ) {N : ℕ} [NeZero N] (u : Strat T X Γ → Strat T X Γ)
    (ω : NOmega T N X Γ) (j : Fin N) (t : Fin (T + 1)) : Meas X :=
  empOthers (tildePath M u ω t) j

end SimpleCorrMFG.Conv


