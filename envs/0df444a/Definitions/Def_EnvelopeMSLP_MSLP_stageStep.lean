-- Prove2me | Definitions.Def_EnvelopeMSLP_MSLP_stageStep
-- name    : EnvelopeMSLP_MSLP_stageStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:26:22.366653+00:00
-- url     : https://prove2.me/theorems/a24004ad-af31-4f1a-ad06-855fde23c29d
-- title:
--   One step of the recursion (8)
-- statement:
--   Given a next post-decision value $\bar V$, one step of (8) is
--   $$x\mapsto\sup\{\langle c_t,y\rangle+\bar V(y): W_ty+T_tx\le h_t\}$$
--   in the extended reals. It equals $-\infty$ when no $y$ is feasible.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), display (8), p.12

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP
open Matrix

namespace EnvelopeMSLP

/-- **One step of the recursion (8).** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), display (8), p.12: given the next post-decision value
`next`, this is `sup {⟨c_t, y⟩ + next(y) : W_t y + T_t x ≤ h_t}` in `EReal`, at the node of `ω`. It is `⊥`
when no `y` is feasible or when `next` is `⊥` at every feasible `y`. -/
noncomputable def MSLP.stageStep {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (θ : ℝ) (t : Fin T)
    (next : (Fin (P.n t.succ) → ℝ) → Ω → EReal) (x : Fin (P.n t.castSucc) → ℝ) (ω : Ω) : EReal :=
  sSup {v | ∃ y : Fin (P.n t.succ) → ℝ,
    P.W t θ (P.ξ t ω) *ᵥ y + P.Tmat t θ (P.ξ t ω) *ᵥ x ≤ P.h t θ (P.ξ t ω) ∧
      v = ((P.c t θ (P.ξ t ω) ⬝ᵥ y : ℝ) : EReal) + next y ω}

end EnvelopeMSLP


