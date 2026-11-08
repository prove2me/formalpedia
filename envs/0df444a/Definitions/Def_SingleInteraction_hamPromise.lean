-- Prove2me | Definitions.Def_SingleInteraction_hamPromise
-- name    : SingleInteraction_hamPromise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:13.320521+00:00
-- url     : https://prove2.me/theorems/f828a81e-aced-4b84-a5fd-b42d1f803625
-- title:
--   Ground-energy promise problem of a family of Hamiltonians
-- statement:
--   For valid instances $x$ with a Hamiltonian $H_x$ on $n_x$ qubits and thresholds $a_x<b_x$, the promise problem has
--
--   1. YES-instances: there is an $n_x$-qubit state $|\phi\rangle$ with $\langle\phi|H_x|\phi\rangle\le a_x$;
--   2. NO-instances: every $n_x$-qubit state $|\phi\rangle$ has $\langle\phi|H_x|\phi\rangle\ge b_x$.
--
--   Invalid instances are in neither set. All Hamiltonian problems of the mission (SIH, DSIH and the XY source problems) are instances of this construction.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 6, pp.17–18; Definition 31, p.30

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_energy

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- The ground-energy promise problem of a family of qubit Hamiltonians (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 6,
pp.17–18, and Definition 31, p.30): for a valid instance `x` on `nq x` qubits with Hamiltonian `H x` and
thresholds `a x < b x`,

* YES: there is an `nq x`-qubit state `|ϕ⟩` with `⟨ϕ| H x |ϕ⟩ ≤ a x`;
* NO: every `nq x`-qubit state `|ϕ⟩` has `⟨ϕ| H x |ϕ⟩ ≥ b x`.

Invalid instances are in neither set.

**Formalization Note** States are unit vectors of `EuclideanSpace ℂ (Fin (nq x) → Fin 2)`. Both sets
require `Valid x`; disjointness follows from `a x < b x` on valid instances (`gap`). -/
def hamPromise {α : Type} (Valid : α → Prop) (nq : α → ℕ)
    (H : (x : α) → Matrix (Fin (nq x) → Fin 2) (Fin (nq x) → Fin 2) ℂ) (a b : α → ℝ)
    (gap : ∀ x, Valid x → a x < b x) : PromiseProblem α where
  yes := {x | Valid x ∧ ∃ φ : EuclideanSpace ℂ (Fin (nq x) → Fin 2), ‖φ‖ = 1 ∧ energy (H x) φ ≤ a x}
  no := {x | Valid x ∧ ∀ φ : EuclideanSpace ℂ (Fin (nq x) → Fin 2), ‖φ‖ = 1 → b x ≤ energy (H x) φ}
  disjoint := by
    rw [Set.disjoint_left]
    rintro x ⟨hv, φ, hφ, hle⟩ ⟨-, hall⟩
    exact absurd ((hall φ hφ).trans hle) (not_le.mpr (gap x hv))

end SingleInteraction


