-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_qPoly
-- name    : QAdvFew_PoQOracle_qPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:55.328911+00:00
-- url     : https://prove2.me/theorems/f196d19f-0d33-43c8-ac1f-03cfa8297b9b
-- title:
--   Modulus fixing the bit representation of $\mathbb F_{2^d}$
-- statement:
--   The field $\mathbb F_{2^d}$ is represented as $\mathbb F_2[X]/(q_d)$, where $q_d$ is the monic irreducible polynomial $X^d+\sum_{i<d}k_iX^i$ with the least number $k=\sum_i k_i2^i$. An element is given by the $d$ coefficients of its reduced representative.
--
--   **Formalization Note** The paper says only "with field elements represented by bit strings"; this is one explicit choice. For $d\ge1$ an irreducible polynomial exists; the branch for $d=0$ is not used by the oracle.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.5, p. 14 (PDF p. 16); Theorem 4.4, p. 23 (PDF p. 25)

import Mathlib

open Polynomial

namespace QAdvFew.PoQOracle

/-- The monic polynomial `X^d + Σ_{i<d} k_i X^i` over `F₂` whose lower coefficients are the binary
digits `k_i` of `k`. -/
noncomputable def candPoly (d k : ℕ) : (ZMod 2)[X] :=
  X ^ d + ∑ i ∈ Finset.range d, C (if k.testBit i then (1 : ZMod 2) else 0) * X ^ i

open Classical in
/-- The modulus fixing the bit representation of `F_{2^d}` (Goldin, Lombardi, Morimae, *Quantum
Advantage has Few Complexity Implications*, arXiv:2611.05303v1, Theorem 4.4, p. 23 (PDF p. 25):
"with field elements represented by bit strings"; §3.2.5, p. 14 (PDF p. 16)): the irreducible
polynomial `X^d + Σ_{i<d} k_i X^i` with the least `k < 2^d`. Then `F_{2^d} = F₂[X]/(qPoly d)`, and
an element is represented by the `d` coefficients of its reduced representative.

**Formalization Note** One explicit representation, computable in time `2^{O(d)}`; the paper does
not fix one. For `d ≥ 1` an irreducible polynomial of degree `d` exists, so the first branch is
taken; the second (`X^d`) only serves `d = 0`, which the oracle does not use. -/
noncomputable def qPoly (d : ℕ) : (ZMod 2)[X] :=
  if h : ∃ k, k < 2 ^ d ∧ Irreducible (candPoly d k) then candPoly d (Nat.find h) else X ^ d

end QAdvFew.PoQOracle


