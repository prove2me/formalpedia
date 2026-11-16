-- Prove2me | Definitions.Def_PelagicFF_Supplement_PreparedWithin
-- name    : PelagicFF_Supplement_PreparedWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:28:33.906312+00:00
-- url     : https://prove2.me/theorems/fa67ed39-c798-47e7-846b-79db659606d3
-- title:
--   Finite one- and two-qubit gate sets and states prepared with at most $G$ gates
-- statement:
--   A **finite gate set of one- and two-qubit gates** is a finite set $\Gamma$ of unitary gates, each acting on one or two qubits. A circuit over $\Gamma$ on $n$ wires is a sequence of gates of $\Gamma$, each placed on one or two distinct wires and tensored with the identity on the others; its size is its number of gates.
--
--   An $n$-qubit state $\rho$ is **prepared by at most $G$ gates of $\Gamma$** if some circuit $C$ over $\Gamma$ of size at most $G$ satisfies
--
--   $$
--   \rho=C|0^n\rangle\langle0^n|C^\dagger ,
--   $$
--
--   that is, $C|0^n\rangle$ equals the state up to a global phase.
--
--   These notions state the gate-count clauses of Theorem 6.2: Alice's messages can be prepared with $O_d(n^d/\log n)$ gates, and this is optimal.
--
--   **Formalization Note** Gates and circuits are the published `QAlgorithms.Gate` and `QAlgorithms.Circuit`. The bound $G$ is a real number, so that $G=Cn^d/\log n$ can be written directly.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), p.5 (fixed finite gate set of one- and two-qubit gates); §6.4, p.54; Corollary 6.14, p.54

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_PelagicFF_Supplement_LevelMessage

namespace PelagicFF.Supplement

/-- `Γ` is a **finite gate set of one- and two-qubit gates**: finitely many gates, each a unitary
on one or two qubits.

arXiv:2610.05585 (held version, sha256 4564aef3…), p.5 ("prepared using at most G gates from a
fixed finite gate set of one- and two-qubit gates") and §6.4, p.54 ("Fix a finite gate set of one-
and two-qubit gates").

**Formalization Note.** Gates are the published `QAlgorithms.Gate` (a matrix on `arity` qubits);
unitarity is `QAlgorithms.Gate.IsUnitary`. -/
def IsGateSet12 (Γ : Set QAlgorithms.Gate) : Prop :=
  Γ.Finite ∧ ∀ g ∈ Γ, (g.arity = 1 ∨ g.arity = 2) ∧ g.IsUnitary

/-- The `n`-qubit state `ρ` is **prepared by at most `G` gates of `Γ`**: there is a circuit `C`
over `Γ` on `n` wires (each gate placed on distinct wires, tensored with the identity elsewhere)
with at most `G` gates and `ρ = C|0ⁿ⟩⟨0ⁿ|C†`.

arXiv:2610.05585 (held version, sha256 4564aef3…), p.5 and §6.4, p.54 ("If every n-qubit message
can be prepared by a circuit of at most G gates"); Corollary 6.14, p.54 ("can be prepared using …
gates up to global phase").

**Formalization Note.** Circuits are the published `QAlgorithms.Circuit Γ n`, their size is
`QAlgorithms.Circuit.size`. A density matrix forgets the global phase, so preparation "up to global
phase" is equality of density matrices. `G` is a real bound so that `G = C nᵈ / log n` can be
written directly. -/
def PreparedWithin {n : ℕ} (Γ : Set QAlgorithms.Gate) (G : ℝ)
    (ρ : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) : Prop :=
  ∃ C : QAlgorithms.Circuit Γ n, (C.size : ℝ) ≤ G ∧ ρ = pureDensity (Matrix.mulVec C.unitary (zeroKet n))

end PelagicFF.Supplement


