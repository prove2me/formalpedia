-- Prove2me | Definitions.Def_mme_CW_q6_doubled_hash_arithmetic
-- name    : mme_CW_q6_doubled_hash_arithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T19:40:03.689921+00:00
-- url     : https://prove2.me/theorems/b75e81ce-dcc9-4eed-a47b-66e8994250f7
-- title:
--   Doubled affine hashes for coupled q=6 address words
-- statement:
--   For a coupled $q=6$ address word of length $2N$, introduce affine hashes in an arbitrary commutative semiring. The first- and second-mode grades use doubled codes $0,2$, while the third-mode grades $0,1,2$ use codes $0,2,1$. With offset $b_0$ and weights $w_j$, the hashes are
--
--   $$
--   h_X=2b_0+\sum_j2x_jw_j,\qquad
--   h_Y=2b_0+\sum_j2y_jw_j,\qquad
--   h_Z=2b_0+\sum_jc(z_j)w_j,
--   $$
--
--   where $c(0)=0$, $c(1)=2$, and $c(2)=1$. Doubling avoids division by two while retaining the exact CW90 arithmetic-progression relation over every odd hashing modulus. These definitions contain no randomness, pruning, or tensor semantics.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the affine block hashes and progression identity (equation (6)) on journal pp. 259–260, reused for the coupled q=6 constituent on journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_CW_q6_primary_hash_family

open BigOperators

namespace MME

/-- The doubled affine code of the third-mode grade. -/
def cwQ6CoupledZHashCode (r : Fin 3) : ℕ :=
  if r = 0 then 0 else if r = 1 then 2 else 1

def cwQ6DoubledXHash
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin (2 * N) → R)
    (x : Fin (2 * N) → Fin 3) : R :=
  2 * b0 + ∑ j, ((2 * (x j).val : ℕ) : R) * w j

def cwQ6DoubledYHash
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin (2 * N) → R)
    (y : Fin (2 * N) → Fin 3) : R :=
  2 * b0 + ∑ j, ((2 * (y j).val : ℕ) : R) * w j

def cwQ6DoubledZHash
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin (2 * N) → R)
    (z : Fin (2 * N) → Fin 3) : R :=
  2 * b0 + ∑ j, (cwQ6CoupledZHashCode (z j) : R) * w j

end MME


