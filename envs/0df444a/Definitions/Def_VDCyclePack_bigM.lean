-- Prove2me | Definitions.Def_VDCyclePack_bigM
-- name    : VDCyclePack_bigM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:15.910194+00:00
-- url     : https://prove2.me/theorems/659d47cf-4d6b-45de-a4b5-6c4034faac04
-- title:
--   $M=8q\lceil\log(q+2)\rceil$
-- statement:
--   For a natural number $q$,
--   $$
--   M=8q\lceil\log_2(q+2)\rceil .
--   $$
--   It is the threshold on the number of disjoint $A$-paths in Lemma 4.3 and Proposition 6.3.
--
--   **Formalization Note** The ceiling of the nonnegative real $\log_2(q+2)$.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 4.3, p.13, and Section 6, p.17

import Mathlib

namespace VDCyclePack

/-- **M = 8q⌈log(q + 2)⌉.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 4.3, p.13: "put M = 8q⌈log(q+2)⌉", and Section 6, p.17.

`bigM q = 8·q·⌈log₂(q + 2)⌉`.

**Formalization Note.** Logarithms are base two; the ceiling of the nonnegative real `log₂(q+2)`
is `⌈·⌉₊`. -/
noncomputable def bigM (q : ℕ) : ℕ :=
  8 * q * ⌈Real.logb 2 ((q : ℝ) + 2)⌉₊

end VDCyclePack


