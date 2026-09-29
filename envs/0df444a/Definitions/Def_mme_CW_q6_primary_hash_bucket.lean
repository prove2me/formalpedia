-- Prove2me | Definitions.Def_mme_CW_q6_primary_hash_bucket
-- name    : mme_CW_q6_primary_hash_bucket
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T20:48:16.954301+00:00
-- url     : https://prove2.me/theorems/e443a88d-dd29-4d7d-9ba4-dfc0caf436ca
-- title:
--   Finite retained affine-hash bucket for exact q=6 addresses
-- statement:
--   For exact coupled q=6 addresses of profile $(N,L,G)$, fix the odd modulus $M=4X^2+1$, an affine offset $b_0$, a weight vector $w$, and a finite retained label set $S$. The primary hash bucket consists of precisely those exact addresses $e$ for which one common label $s\in S$ satisfies\n\n$$\nh_X(e_X)=h_Y(e_Y)=h_Z(e_Z)=2s\pmod M.\n$$\n\nThe equality uses the doubled X, Y, and Z hash conventions already formalized. Requiring one literal common label makes the bucket's closure interface explicit: the progression-free coherence theorem can show that every supported mix of retained modes lies back in the same bucket. This definition contains no collision deletion, degree truncation, or tensor assertion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine block retention and Salem--Spencer common-label zeroing on journal pp. 259--261, reused for the coupled q=6 profile on pp. 270--271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.ZMod.Basic
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic
import Definitions.Def_mme_CW_q6_exact_address_incidence

namespace MME

/-- Exact q=6 addresses whose three doubled affine hashes all land on one
common retained Salem--Spencer label. -/
noncomputable def cwQ6PrimaryHashBucket
    (N L G Xcount : ℕ) (S : Finset ℕ)
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1)) :
    Finset (CWQ6ExactCoupledAddress N L G) := by
  classical
  letI : Fintype (CWQ6CoupledAddress N) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))
  letI : Fintype (CWQ6ExactCoupledAddress N L G) :=
    Fintype.ofInjective (fun e => e.1) Subtype.val_injective
  exact Finset.univ.filter (fun e =>
    ∃ s ∈ S,
      cwQ6DoubledXHash b0 w (e.1 0) =
          2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
      cwQ6DoubledYHash b0 w (e.1 1) =
          2 * (s : ZMod (4 * Xcount ^ 2 + 1)) ∧
      cwQ6DoubledZHash b0 w (e.1 2) =
          2 * (s : ZMod (4 * Xcount ^ 2 + 1)))

end MME


