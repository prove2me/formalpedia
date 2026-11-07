-- Prove2me | Definitions.Def_QPACLarge_seedDot
-- name    : QPACLarge_seedDot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:06:17.235949+00:00
-- url     : https://prove2.me/theorems/f3348b5f-f048-494d-8203-ccf473036abe
-- title:
--   Binary inner product $a\cdot y$ on seeds
-- statement:
--   For seeds $a, y$, the **binary inner product** is
--   $$
--   a \cdot y = a_\emptyset y_\emptyset \oplus \bigoplus_i a_i y_i \oplus \bigoplus_{i<j} a_{ij} y_{ij} \in \mathbb F_2,
--   $$
--   the ordinary inner product of $\{0,1\}^r$ in the chosen encoding of seeds.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.22

import Mathlib
import Definitions.Def_QPACLarge_Seed

namespace QPACLarge

/-- **The binary inner product `a · y` on seeds.**
Oliveira, *Unconditional Quantum PAC Learning Advantage in the Large Error Regime*, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 3.2.1, p.22: "expressions such as `a · J(x)` below are ordinary binary inner products
in this chosen encoding", i.e. `a · y = a_∅y_∅ ⊕ ⨁ᵢ aᵢyᵢ ⊕ ⨁_{i<j} aᵢⱼyᵢⱼ` over `F₂`. -/
def seedDot {n : ℕ} (a y : Seed n) : Bool :=
  (a.1 && y.1) + ∑ i : Fin n, (a.2.1 i && y.2.1 i) +
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (a.2.2 p && y.2.2 p)

end QPACLarge


