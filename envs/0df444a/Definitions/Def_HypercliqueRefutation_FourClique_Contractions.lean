-- Prove2me | Definitions.Def_HypercliqueRefutation_FourClique_Contractions
-- name    : HypercliqueRefutation_FourClique_Contractions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:58.575264+00:00
-- url     : https://prove2.me/theorems/fff03332-fd2b-44c8-a7e7-042b2493cba2
-- title:
--   Four-array and alternating closed-walk contractions
-- statement:
--   For a nonnegative integer n and four independent three-index arrays P,Q,R,S over a commutative semiring, define
--
--   $$C(P,Q,R,S)=\sum_{a,b,c,d\in[n]}P_{abc}Q_{abd}R_{acd}S_{bcd}.$$
--
--   For matrix families A with n_A colors and B with n_B colors, define
--
--   $$D(A,B)=\sum_{x,y,z,z'\in[n],\,a\in[n_A],\,b\in[n_B]} A_a[x,z]B_b[z,y]A_a[y,z']B_b[z',x].$$
--
--   All indices are ordered and may coincide. D is the expression of Problem 2.2; its input-symmetry hypotheses are imposed by the theorems using it. Neither expression requires nonnegative entries. Empty sums are zero. The formulas themselves make sense over any commutative semiring; the source identities are stated over characteristic-zero fields.
--
--   These definitions share the source's scalar expressions across all statements. They do not assert an algorithm or a running time.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026), held source.pdf SHA-256 fda90f18867fd07883366a1bc49a8afa652b8712f71402e11ccd45e6633b127a; Problems 2.1 and 2.2, p.3.

import Mathlib

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique

/- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
   Problems 2.1 and 2.2, p.3. These are finite scalar expressions, not solvers. -/

def fourArrayContraction {K : Type*} [CommSemiring K] {n : ℕ}
    (P Q R S : Fin n → Fin n → Fin n → K) : K :=
  ∑ a, ∑ b, ∑ c, ∑ d, P a b c * Q a b d * R a c d * S b c d

/-- All ordered tuples occur, including coinciding indices; colors on opposite edges agree. -/
def alternatingContraction {K : Type*} [CommSemiring K] {n nA nB : ℕ}
    (A : Fin nA → Matrix (Fin n) (Fin n) K)
    (B : Fin nB → Matrix (Fin n) (Fin n) K) : K :=
  ∑ x, ∑ y, ∑ z, ∑ z', ∑ a, ∑ b,
    A a x z * B b z y * A a y z' * B b z' x

end HypercliqueRefutation.FourClique


