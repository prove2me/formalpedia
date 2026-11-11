-- Prove2me | Definitions.Def_PelagicFF_Rcc
-- name    : PelagicFF_Rcc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:55:30.186312+00:00
-- url     : https://prove2.me/theorems/448dcdf3-46d4-4a7c-90a4-406ba516bde3
-- title:
--   Randomized two-way communication complexity $R(P)$ at error $1/3$
-- statement:
--   For a two-party search problem $P$, $R(P)=R_{1/3}(P)$ is the least cost of a randomized public-coin two-way protocol that succeeds with probability at least $2/3$ on every input:
--   $$R(P)=\min\{c\in\mathbb N:\ \exists\text{ a protocol of cost }c\text{ with }\Pr[\text{success on }(x,y)]\ge 2/3\ \ \forall x,y\}.$$
--
--   This is the classical side of the separation in Theorem 4.2.
--
--   **Formalization Note** The minimum is `sInf` on `ℕ` (`0` on the empty set). For $\mathrm{PFF}_n$ the set is nonempty: Alice can send her whole truth table (p.27).
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14

import Mathlib
import Definitions.Def_PelagicFF_PubCoinProtocol

namespace PelagicFF

/-- **`R(R)`, the randomized two-way (public-coin) communication complexity at error `ε = 1/3`**:
the least cost of a public-coin two-way protocol that succeeds with probability at least `2/3` on
every input.

arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14: "We write Rε(P) … for the minimum
costs of randomized classical two-way … protocols for a problem P … that succeed with probability at
least 1 − ε on every input. An omitted error subscript means ε = 1/3. In all communication models we
consider, the players have access to shared randomness".

**Formalization Note.** `sInf` on `ℕ` is `0` on the empty set; for `PFFₙ` the set is nonempty
(Alice can send her whole truth table, p.27), and clause (d) of Theorem 4.2 forces this. -/
noncomputable def Rcc {X Y Z : Type} (R : X → Y → Z → Prop) : ℕ :=
  sInf {c : ℕ | ∃ P : PubCoinProtocol X Y Z, P.cost = c ∧ ∀ x y, (2 : ℝ) / 3 ≤ P.succProb R x y}

end PelagicFF


