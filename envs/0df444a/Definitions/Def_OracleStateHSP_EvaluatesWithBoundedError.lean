-- Prove2me | Definitions.Def_OracleStateHSP_EvaluatesWithBoundedError
-- name    : OracleStateHSP_EvaluatesWithBoundedError
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:32:42.619743+00:00
-- url     : https://prove2.me/theorems/8b0def1b-3be7-418e-a9b1-3ad895eba586
-- title:
--   Bounded-error evaluation of $s : X \to E$
-- statement:
--   Let $X$ be a set of instances, $\{O_x\}_{x \in X}$ a family of oracles and $s : X \to E$ an answer function. A $T$-query algorithm $A$ with initial state $|\psi_0\rangle$ and output map $\mathrm{out}$ **evaluates $s$ with bounded error** if $\|\psi_0\| = 1$ and, for every $x \in X$,
--   $$
--   \Pr[A^{O_x} \text{ outputs } s(x)] \ge \tfrac23 .
--   $$
--   The initial state and the output map do not depend on $x$.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.3, p.35

import Mathlib
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb

namespace OracleStateHSP

/-- Bounded-error evaluation (Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656, Definition 4.3, p.35): the algorithm `A`, with the fixed,
input-independent initial state `ψ₀` (a unit vector) and output map `out`, evaluates
`s : X → E` on the oracle family `{O_x}` with bounded error if for **every** `x ∈ X` it outputs
`s(x)` with probability at least `2/3`. -/
def EvaluatesWithBoundedError {X E Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ} (A : QueryAlgorithm Q S W T)
    (ψ₀ : EuclideanSpace ℂ (S ⊕ (Q × W))) (out : S ⊕ (Q × W) → E) (O : X → Matrix Q Q ℂ)
    (s : X → E) : Prop :=
  ‖ψ₀‖ = 1 ∧ ∀ x, (2 : ℝ) / 3 ≤ A.outputProb (O x) ψ₀ out (s x)

end OracleStateHSP


