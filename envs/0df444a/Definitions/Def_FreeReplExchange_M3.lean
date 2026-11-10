-- Prove2me | Definitions.Def_FreeReplExchange_M3
-- name    : FreeReplExchange_M3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:18:24.981666+00:00
-- url     : https://prove2.me/theorems/28b9ada6-668a-4009-9142-e9be8fa172bc
-- title:
--   The multi-round protocol M3 (Myopic Maximum Matching)
-- statement:
--   Given a selection rule, the matching protocol of §4.3 runs as follows from $x=x^{(0)}$, $D=\varnothing$:
--
--   1. Construct $G(x,P)$ and remove each edge whose exchange belongs to $D$; call the result $G_t=(V_t,E_t)$. If $E_t=\varnothing$, terminate with allocation $x$.
--   2. Select a matching $\mu_t$ of $G_t$ by the rule and propose $P_t=\{p(e):e\in\mu_t\}$.
--   3. Execute the exchanges $A_t$ accepted by both participants: $x\leftarrow x[A_t]$, $D\leftarrow D\cup(P_t\setminus A_t)$.
--   4. Proceed to the next round.
--
--   **Myopic Maximum Matching (M3)** is the protocol whose rule selects the unique matching of $G_t$ maximizing $\Phi(\mu)=(|\mu|,g(\mu),T(\mu))$ for a fixed global tie order.
--
--   This is the protocol of the main theorem.
--
--   **Formalization Note** The selection rule may depend on the participating set and the history; M3's ignores them. Steps 3–4 are the run of a protocol. M3 is defined for any rank; the theorems say which require it to be injective.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), §4.3, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_FreeReplExchange_Protocol
import Definitions.Def_FreeReplExchange_m3Select

namespace FreeReplExchange

open Classical in
/-- The multi-round matching protocol of §4.3, Yang–Kandasamy, *Pairwise Exchanges of Freely
Replicable Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…),
p.33 (PDF p.35), with selection rule `sel`: at the current allocation `x` and rejected set `D`,
construct `G(x, P)` and remove each edge whose exchange belongs to `D` (step 1, giving `E_t`); if
`E_t = ∅` propose nothing (terminate); otherwise propose `sel(P, H, E_t)` (step 2). Steps 3–4
(execution, update of `x` and `D`) are the run `hist` of a protocol. -/
noncomputable def matchProtocol {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ)
    (sel : Finset A → History A m → Finset (Exchange A m) → Finset (Exchange A m)) :
    Protocol A m :=
  fun P H =>
    if edges x0 U P (alloc x0 H) \ rejectedSet H = ∅ then ∅
    else sel P H (edges x0 U P (alloc x0 H) \ rejectedSet H)

/-- **Myopic Maximum Matching (M3)**, §4.3, p.33: the matching protocol whose round rule selects
the matching maximizing `Φ = (|μ|, g(μ), T(μ))` (18) in `G_t`, for the global tie order given by the
rank `rk` (smaller rank first; injective in every theorem). -/
noncomputable def M3 {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ}
    (x0 : A → Fin m → Bool) (U : A → A → Fin m → ℝ) (rk : Exchange A m → ℕ) : Protocol A m :=
  matchProtocol x0 U fun _ _ E => m3Select U rk E

end FreeReplExchange


