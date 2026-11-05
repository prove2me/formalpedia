-- Prove2me | Definitions.Def_BaconOQEC_symp
-- name    : BaconOQEC_symp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:23:32.709514+00:00
-- url     : https://prove2.me/theorems/57f37362-90ab-4590-a160-72106701dcae
-- title:
--   Commutation bit of two Pauli operators
-- statement:
--   For Pauli operators $P(a,b)$ and $P(a',b')$ (each given by its pair of bit matrices) put
--
--   $$
--   \langle (a,b),(a',b')\rangle = \sum_{i,j} \big(a_{i,j}b'_{i,j} + b_{i,j}a'_{i,j}\big) \in \mathbb Z_2 .
--   $$
--
--   The two operators commute when this bit is $0$ and anticommute when it is $1$. This is the binary symplectic form; the paper uses it implicitly whenever it says which operators commute (e.g. "S … is an Abelian subgroup of T", p.4).
--
--   **Formalization Note** A Pauli operator modulo phase is the pair $(a,b)$ of its $X$-part and $Z$-part.
-- source:
--   D. Bacon, Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories, arXiv:quant-ph/0506023v4, §IV.A, pp.4–5

import Mathlib
import Definitions.Def_BaconOQEC_Bits

namespace BaconOQEC

/-- Bacon, *Operator Quantum Error Correcting Subsystems for Self-Correcting Quantum Memories*,
arXiv:quant-ph/0506023v4, §IV.A, pp.4–5 (used in "S … is an Abelian subgroup of T. Further all of
the elements of S commute not just with each other, but with all of the elements of T", p.4): the
commutation bit of two Pauli operators `P(a, b)` and `P(a', b')` of (7),
`Σ_{i,j} (a_{i,j} b'_{i,j} + b_{i,j} a'_{i,j}) ∈ Z₂`. The two operators commute if it is `0` and
anticommute if it is `1` (milestone `BaconOQEC.syndrome_parity` proves this at the level of
matrices for the stabilizer generators).

**Formalization Note.** A Pauli operator up to phase is the pair `v = (a, b)` of bit matrices
(the `X`-part and the `Z`-part). This is the standard binary symplectic form; the paper uses it
implicitly when it says which operators commute. -/
def symp {m : ℕ} (v w : Bits m × Bits m) : ZMod 2 :=
  ∑ i, ∑ j, (v.1 i j * w.2 i j + v.2 i j * w.1 i j)

end BaconOQEC


