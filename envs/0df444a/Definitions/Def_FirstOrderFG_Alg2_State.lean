-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_State
-- name    : FirstOrderFG_Alg2_State
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:29.594117+00:00
-- url     : https://prove2.me/theorems/9a9a713e-9c13-489f-bb53-dca192c718d4
-- title:
--   State of an instance of Algorithm 2
-- statement:
--   An instance of Algorithm 2 (the self-aware learner with a complement-barrier master) carries, between rounds:
--
--   1. its inputs: the bound $A\ge1$ and the master rate $\theta>0$;
--   2. the base OMD distribution $p_t\in\mathcal P$;
--   3. the master distribution $x_t\in\mathcal X$;
--   4. the meta-action learning rate $\theta_{t,0}$ and the threshold $\rho_t$;
--   5. the running sum $\sum_{\tau<t}\tilde g_{\tau,0}/x_{\tau,0}$ over its own earlier rounds, which sets $\eta_t$;
--   6. the number of rounds it has played.
--
--   **Formalization Note** The round counter is bookkeeping; Algorithm 4 uses it to recognize the first round of an epoch.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, p.10

import Mathlib

namespace FirstOrderFG

/-- **The state of one instance of Algorithm 2 between rounds.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, p.10.

Fields: the instance's inputs `A` (the bound `A ≥ 1`) and `θ` (the master rate of `V̄_self`); the
base OMD distribution `p_t ∈ 𝒫` (line 13); the master distribution `x_t ∈ 𝒳` (line 14); the
meta-action rate `θ_{t,0}` and the threshold `ρ_t` (lines 15–16); the running sum
`gsum = ∑_{τ<t} g̃_{τ,0}/x_{τ,0}` over this instance's earlier rounds (line 5); and the number `n`
of rounds this instance has played.

**Formalization Note.** `n` is bookkeeping (it is not read by Algorithm 2); Algorithm 4 uses it to
recognise the first round of an epoch. Base distributions are `Fin K → ℝ` (read on `V_self`),
master distributions are `Option (Fin K) → ℝ` with `none` the meta-action `0`. -/
structure Alg2.State (K : ℕ) where
  A : ℝ
  θ : ℝ
  p : Fin K → ℝ
  x : Option (Fin K) → ℝ
  θ0 : ℝ
  ρ : ℝ
  gsum : ℝ
  n : ℕ

end FirstOrderFG


