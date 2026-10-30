-- Prove2me | Definitions.Def_LindenReversibility_IsKrausFamily
-- name    : LindenReversibility_IsKrausFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:16:36.508153+00:00
-- url     : https://prove2.me/theorems/db0a8f11-fe05-45b4-a44c-cc30760977e3
-- title:
--   Complete family of measurement operators $\sum_k K_k^\dagger K_k = I$
-- statement:
--   A finite family $K_1,\dots,K_n$ of operators on one party's (finite-dimensional) system is a **complete family of measurement operators** if
--
--   $$
--   \sum_{k=1}^n K_k^\dagger K_k = I .
--   $$
--
--   Outcome $k$ then occurs with probability $\|K_k\psi\|^2$ and leaves the (unnormalized) pure state $K_k\psi$. The paper's local operations are of this kind: a measurement with spectral projectors $P_k$ (eq. (7)), the projectors followed by outcome-dependent unitaries $U_kP_k$, and a single unitary $U$.
--
--   **Formalization Note** The operators are square: the local Hilbert space, ancillas included, is fixed from the start (p.2). The outcomes are indexed by $\{0,\dots,n-1\}$.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, p.2 (local operations; eq. (7)) and p.3 (eq. (14))

import Mathlib

open scoped Matrix

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, p.2 (the local
operations: "measurements" with spectral projectors `P_k`, eq. (7), followed by unitary
transformations, eq. (14)): a finite family `K_1, …, K_n` of operators on one party's local system
is a (complete) family of measurement operators, `∑_k K_kᴴ K_k = 1`.

**Formalization Note.** This is the class of local steps of the mission's protocols. It contains
the paper's steps: spectral projectors `{P_k}` (`∑ P_k = 1`), projectors followed by unitaries
`{U_k P_k}`, and a single unitary `{U}`. The operators are square: the local Hilbert space,
"including ancilla's" (p.2), is fixed throughout. -/
def IsKrausFamily {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}
    (K : Fin n → Matrix X X ℂ) : Prop :=
  ∑ k, (K k)ᴴ * K k = 1

end LindenReversibility


