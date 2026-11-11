-- Prove2me | Definitions.Def_PelagicFF_Q1
-- name    : PelagicFF_Q1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:38.619555+00:00
-- url     : https://prove2.me/theorems/354dace3-7a56-4142-b19b-24511df51004
-- title:
--   Quantum one-way communication complexity $Q^1(P)$ at error $1/3$
-- statement:
--   For a two-party search problem $P$ with finite output set, $Q^1(P)=Q^1_{1/3}(P)$ is the least number $m$ of qubits of a quantum one-way protocol (shared randomness, no entanglement) that succeeds with probability at least $1-\varepsilon=2/3$ on every input:
--   $$Q^1(P)=\min\{m\in\mathbb N:\ \exists\text{ an $m$-qubit protocol with }\Pr[\text{success on }(x,y)]\ge 2/3\ \ \forall x,y\}.$$
--
--   This is the quantum side of the separation in Theorem 4.2.
--
--   **Formalization Note** The minimum is `sInf` on `ℕ`, which is `0` on the empty set; for $\mathrm{PFF}_n$ the set is nonempty by clause (a) of Theorem 4.2.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14

import Mathlib
import Definitions.Def_PelagicFF_OneWayQProtocol

namespace PelagicFF

/-- **`Q¹(R)`, the quantum one-way communication complexity at error `ε = 1/3`**: the least number
of qubits `m` of a quantum one-way protocol (shared randomness, no entanglement) that succeeds with
probability at least `2/3` on every input.

arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14: "We write Rε(P), R¹ε(P), and Q¹ε(P)
for the minimum costs of … quantum one-way protocols for a problem P … that succeed with probability
at least 1 − ε on every input. An omitted error subscript means ε = 1/3."

**Formalization Note.** `sInf` on `ℕ` is `0` on the empty set; for a relation without any
successful protocol the value is a junk `0`. For `PFFₙ` the set is nonempty by clause (a) of
Theorem 4.2. -/
noncomputable def Q1 {X Y Z : Type} [Fintype Z] (R : X → Y → Z → Prop) : ℕ :=
  sInf {m : ℕ | ∃ P : OneWayQProtocol X Y Z m, ∀ x y, (2 : ℝ) / 3 ≤ P.succProb R x y}

end PelagicFF


