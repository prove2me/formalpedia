-- Prove2me | Definitions.Def_QStateSearch_Verifier
-- name    : QStateSearch_Verifier
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:22.311537+00:00
-- url     : https://prove2.me/theorems/17213b2e-99cb-42d6-a938-fc210e8288ba
-- title:
--   Classical-message verifier
-- statement:
--   A **classical-message verifier** $V$ consists of
--
--   1. a finite list of steps (unitary gates, oracle-query slots, verifier messages and prover messages),
--   2. an initial unit vector $\phi_0$ of the register $\{0,1\}\times[D]\times W$,
--   3. an accept effect $A$ with $0\le A\le I$,
--
--   such that every verifier-message instrument is complete, $\sum_a K_a^\dagger K_a=I$.
--
--   The verifier and prover start in a fixed product state and exchange only classical strings. No restriction is placed on the number, order or alphabet of the messages, and no efficiency condition is imposed; the alternating order of p.9 is one instance.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 2.2, pp.8–10

import Mathlib
import Definitions.Def_QStateSearch_Step
open Matrix
open scoped ComplexOrder

namespace QStateSearch

/-- A verifier that exchanges only classical messages: a finite list of steps, an initial unit
vector, and an accept effect `0 ≤ A ≤ I`, with every verifier-message instrument complete.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 2.2, pp.8–10 ("The verifier and prover start in a fixed product state … They
exchange only classical strings … The verifier and prover may retain arbitrary private quantum
registers.").

**Formalization Note.** Vectors on `Reg D W` are functions `Reg D W → ℂ`, acted on by
`Matrix.mulVec`. Kraus completeness is `∑ₐ (K a)ᴴ * K a = 1`. The order of messages is not
restricted (the paper's alternation convention on p.9 is one case; "padding by ignored
messages makes equivalent conventions harmless"), and no bound on the number or alphabet of
verifier messages, and no efficiency condition, is imposed. -/
structure Verifier (D : ℕ) (W : Type) [Fintype W] [DecidableEq W] where
  /-- The chronological list of steps. -/
  steps : List (Step D W)
  /-- The initial state, a unit vector. -/
  init : Reg D W → ℂ
  /-- The accept effect. -/
  accept : Matrix (Reg D W) (Reg D W) ℂ
  init_norm : ∑ x, ‖init x‖ ^ 2 = 1
  kraus_complete : ∀ (m : ℕ) (K : Fin m → Matrix (Reg D W) (Reg D W) ℂ),
    Step.vmsg m K ∈ steps → ∑ a, (K a)ᴴ * K a = 1
  accept_psd : accept.PosSemidef
  accept_le_one : (1 - accept).PosSemidef

end QStateSearch


