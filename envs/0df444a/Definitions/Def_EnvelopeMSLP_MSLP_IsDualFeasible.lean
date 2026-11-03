-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_IsDualFeasible
-- name    : EnvelopeMSLP_MSLP_IsDualFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:28:26.592739+00:00
-- url     : https://prove2.me/theorems/02f77743-578c-4427-bb3f-71bcd90a05c9
-- title:
--   Dual feasible joint multiplier of (7)
-- statement:
--   A nonanticipative multiplier process $\lambda\ge0$ is dual feasible at $\theta$ when the Lagrangian of (7) is constant in the free nonanticipative variables: for every nonanticipative $y$,
--   $$\mathbb E\Big[\sum_{t=1}^T\big(\langle c_t,y_t\rangle-\langle\lambda_t,W_ty_t+T_ty_{t-1}\rangle\big)\Big]=0,\qquad y_0=0.$$
--   This is the dual constraint of the monolithic deterministic equivalent of (7).
--
--   **Formalization Note** The multipliers are normalised by probability: the dual variable of the deterministic equivalent at a node is the node's probability times $\lambda$ at that node, so that the expectation counts the probability once.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 3, p.13; §3.1, p.14

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_IsNonanticipative
import Definitions.Def_EnvelopeMSLP_MSLP_IsNonanticipativeMultiplier
import Definitions.Def_EnvelopeMSLP_MSLP_path
open Matrix

namespace EnvelopeMSLP

/-- **Dual feasible joint multiplier at `θ`.** The dual constraint of (7) as one linear program, the
monolithic deterministic equivalent of Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), §3.1, p.14: `lam ≥ 0`, `lam` is nonanticipative, and the
Lagrangian of (7) is constant in the free nonanticipative variables, i.e. for every nonanticipative
`y`,
`E[Σ_t (⟨c_t, y_t⟩ − ⟨λ_t, W_t y_t + T_t y_{t−1}⟩)] = 0`, with `y_0 = 0`.

**Formalization Note.** The multipliers are normalised by probability: the dual variable of the
deterministic equivalent at a node is `P(node)` times `lam` at that node, so the expectation carries
the probabilities once. A multiplier of a stage LP (8) alone is not
meant: with those, (9) is false. -/
def MSLP.IsDualFeasible {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (lam : P.Multiplier) : Prop :=
  (∀ t ω, 0 ≤ lam t ω) ∧ P.IsNonanticipativeMultiplier lam ∧
    ∀ y : P.Policy, P.IsNonanticipative y →
      ∑ ω, P.p ω * ∑ t : Fin T,
        (P.c t θ (P.ξ t ω) ⬝ᵥ y t ω -
          lam t ω ⬝ᵥ (P.W t θ (P.ξ t ω) *ᵥ y t ω +
            P.Tmat t θ (P.ξ t ω) *ᵥ P.path 0 y ω t.castSucc)) = 0

end EnvelopeMSLP


