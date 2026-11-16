-- Prove2me | Definitions.Def_PelagicFF_Supplement_R1
-- name    : PelagicFF_Supplement_R1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T21:25:19.116243+00:00
-- url     : https://prove2.me/theorems/b7c18fb3-3b0e-4827-8562-27b219365a88
-- title:
--   Randomized one-way communication complexity $R^1(P)$ at error $1/3$
-- statement:
--   For a two-party search problem $P$ given by a relation $R$, $R^1(P)=R^1_{1/3}(P)$ is the least message length $c$ of a randomized public-coin one-way protocol that succeeds with probability at least $2/3$ on **every** input:
--
--   $$
--   R^1(P)=\min\Big\{c\in\mathbb N : \exists\text{ a one-way protocol with $c$-bit messages and }\ \mathrm{succ}(x,y)\ge\tfrac23\ \ \forall (x,y)\Big\}.
--   $$
--
--   It is the classical one-way quantity of Theorem 5.2 ($R^1(\mathrm{APFF}_n)=\Theta(2^n)$).
--
--   **Formalization Note** Written as `sInf` over $\mathbb N$, which is $0$ on the empty set; for $\mathrm{APFF}_n$ the set is nonempty because Alice can send her whole truth table.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14

import Mathlib
import Definitions.Def_PelagicFF_Supplement_OneWayProtocol

namespace PelagicFF.Supplement

/-- **`R¹(R)`, the randomized classical one-way communication complexity at error `ε = 1/3`**: the
least message length `c` of a public-coin one-way protocol that succeeds with probability at least
`2/3` on every input.

arXiv:2610.05585 (held version, sha256 4564aef3…), §2.1, p.14: "We write Rε(P), R¹ε(P), and
Q¹ε(P) for the minimum costs of randomized classical two-way, randomized classical one-way, and
quantum one-way protocols for a problem P, respectively, that succeed with probability at least
1 − ε on every input. An omitted error subscript means ε = 1/3."

**Formalization Note.** `sInf` on `ℕ` is `0` on the empty set; for a relation without any
successful protocol the value is a junk `0`. For `APFFₙ` the set is nonempty (Alice can send her
whole truth table). -/
noncomputable def R1 {X Y Z : Type} (R : X → Y → Z → Prop) : ℕ :=
  sInf {c : ℕ | ∃ P : OneWayProtocol X Y Z c, ∀ x y, (2 : ℝ) / 3 ≤ P.succProb R x y}

end PelagicFF.Supplement


