-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_StPolicy
-- name    : MultiSelectPandora_Supplement_StPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:28:44.924213+00:00
-- url     : https://prove2.me/theorems/0e753e05-88ce-403f-abb1-53d18a3b0703
-- title:
--   Stationary state policies $\pi(U,\alpha)$
-- statement:
--   A **state policy** assigns an action to every state $(U,\alpha)$, where $U\subseteq M$ is the set of boxes neither opened nor claimed closed and $\alpha=(\alpha_1\ge\dots\ge\alpha_k)$ is the vector of the $k$ best values secured so far. With one closed claim, the remaining budget is $1$ at every state at which the policy still acts, so it is not part of the state.
--
--   The state $(U,\alpha)$ summarizes everything relevant from the history (§2.2), so optimal policies can be taken of this form. Theorem 4.10 compares the actions of one policy at two states, $(U,\alpha)$ and $(U,(\alpha[1:k-1],0))$, which requires the policy to be defined on all states.
--
--   **Formalization Note** A state policy is a function from pairs (finite set of boxes, vector $\alpha:\mathrm{Fin}\,k\to\mathbb R$) to actions, deterministic and defined on every pair, including unsorted vectors and unreachable states.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.6 (PDF p.7); §4.2, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Supplement_StAct

namespace MultiSelectPandora.Supplement

/-- **A (deterministic, stationary) policy on states `(U, α)`.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.2, p.6 (PDF p.7), and §4.2, p.22
(PDF p.23): a state is `(U, α)`, `U` the boxes neither opened nor claimed closed and `α = (α_1 ≥ ⋯ ≥ α_k)` the `k` best
values secured so far; with `k̂ = 1` the remaining budget is 1 at every state at which the policy still acts.

**Formalization Note.** A policy is a function of the state, total on all pairs `(U, α)` (Theorem 4.10 compares the
action at `(U, α)` with the action at `(U, (α[1 : k−1], 0))`, which need not be reachable). Since `(U, α)` is a
sufficient statistic of the history (§2.2), restricting to such policies does not change the optimal value. -/
def StPolicy (I : Inst) (k : ℕ) : Type := Finset (Fin I.n) → (Fin k → ℝ) → StAct I

end MultiSelectPandora.Supplement


