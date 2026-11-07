-- Prove2me | Definitions.Def_QPACLarge_qa
-- name    : QPACLarge_qa
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:29.732729+00:00
-- url     : https://prove2.me/theorems/e758185b-1b49-4d21-b646-b06283d4924b
-- title:
--   Quadratic Boolean function $q_a$
-- statement:
--   For a seed $a$, the multilinear quadratic polynomial over $\mathbb F_2$
--   $$
--   q_a(x) = a_\emptyset \oplus \bigoplus_{i=1}^n a_i x_i \oplus \bigoplus_{1 \le i < j \le n} a_{ij} x_i x_j ,
--   $$
--   defines $h_a = q_a$ and $H_a = (-1)^{q_a}$. These are the hypotheses of the quantum learner.
--
--   **Formalization Note** Arithmetic over $\mathbb F_2$ is Mathlib's Boolean ring on `Bool`.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.1.1, p.19

import Mathlib
import Definitions.Def_QPACLarge_Seed
import Definitions.Def_QAlgorithms_Defs_Basic

namespace QPACLarge

open QAlgorithms

/-- **The quadratic Boolean function `h_a = q_a`.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.1.1, p.19: "Associate with this seed the multilinear quadratic polynomial
`q_a(x) = a_∅ ⊕ ⨁ᵢ aᵢxᵢ ⊕ ⨁_{i<j} aᵢⱼxᵢxⱼ`, where all arithmetic is over `F₂`. Finally, define
`h_a(x) = q_a(x)`, `H_a(x) = (−1)^{q_a(x)}`."

**Formalization Note.** Arithmetic over `F₂` is Mathlib's Boolean ring `Bool` (`+` is xor, `&&` is
multiplication). -/
def qa {n : ℕ} (a : Seed n) (x : Qubits n) : Bool :=
  a.1 + ∑ i : Fin n, (a.2.1 i && x i) +
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (a.2.2 p && (x p.1.1 && x p.1.2))

end QPACLarge


