-- Prove2me | Definitions.Def_RSBDDHard_recipProd
-- name    : RSBDDHard_recipProd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:52.932404+00:00
-- url     : https://prove2.me/theorems/87b79256-5c66-44cf-ac58-a942f82df419
-- title:
--   Reciprocal products $P_S$, power sums $M_j$ and the Artin–Schreier map $\mathcal L$
-- statement:
--   For a finite set $S$ of elements of a commutative ring, the **reciprocal product** is
--   $$P_S(Z)=\prod_{a\in S}(1-aZ)=\sum_{j\ge0}(-1)^jE_j(S)Z^j,$$
--   and the **power sums** are $M_j(S)=\sum_{a\in S}a^j$.
--
--   In characteristic $p$ the **Artin–Schreier map** is $\mathcal L(x)=x^p-x$. It is additive, and its zeros are the elements of $\mathbb F_p$.
--
--   The reduction prescribes the low coefficients of $P_S$; the identity relating them to $M_1,M_2$ and the additivity of $\mathcal L$ drive the soundness proof.
-- source:
--   Gandikota, Grigorescu, Venkitesh, NP-Hardness of Bounded Distance Decoding for Reed-Solomon Codes and Variants, via Non-Archimedean Rings, STOC 2027 submission (sha256 0372e933…), §1.3 p.7, §1.4 p.12, §2 p.17, §3.1 p.19

import Mathlib

set_option autoImplicit false

namespace RSBDDHard

/-- The **reciprocal product** `P_S(Z) = Π_{a ∈ S} (1 − aZ)` of a finite set `S` of ring
elements. STOC 2027 submission (sha256 0372e933…), §1.4, p.12, and §2, p.17, where
`P_S(Z) = Σ_{j ≥ 0} (−1)^j E_j(S) Z^j`. -/
noncomputable def recipProd {R : Type*} [CommRing R] (S : Finset R) : Polynomial R :=
  ∏ a ∈ S, (1 - Polynomial.C a * Polynomial.X)

/-- The **power sum** `M_j(S) = Σ_{a ∈ S} a^j` (§1.3, p.7). -/
def powerSum {R : Type*} [CommRing R] (S : Finset R) (j : ℕ) : R :=
  ∑ a ∈ S, a ^ j

/-- The **Artin–Schreier map** `L(x) = x^p − x` (§3.1, p.19: "Over a finite field with
characteristic p, define L(x) = x^p − x"). -/
def artinSchreier {R : Type*} [CommRing R] (p : ℕ) (x : R) : R :=
  x ^ p - x

end RSBDDHard


