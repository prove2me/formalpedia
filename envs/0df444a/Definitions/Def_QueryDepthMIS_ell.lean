-- Prove2me | Definitions.Def_QueryDepthMIS_ell
-- name    : QueryDepthMIS_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:19.581982+00:00
-- url     : https://prove2.me/theorems/0d503412-6c3b-46c3-b490-512cb136b82b
-- title:
--   Block length $\ell_i = \lfloor |I_{i-1} \setminus P| / s_i \rfloor$
-- statement:
--   For an occupied interval $I_i$,
--   $$
--   \ell_i = \left\lfloor \frac{|I_{i-1} \setminus P|}{s_i} \right\rfloor .
--   $$
--   **Formalization Note** Natural-number division is the floor; the value $0$ for an unoccupied interval is never used.
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14

import Mathlib
import Definitions.Def_QueryDepthMIS_sOcc

set_option autoImplicit false

namespace QueryDepthMIS

/-- The block length `ℓ_i = ⌊|I_{i−1} \ P| / s_i⌋` (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), §3.4, p.14), for an occupied interval
`I_i`.

**Formalization Note** Natural-number division is the floor; for an unoccupied interval
(`s_i = 0`) the value is `0` and is never used. -/
noncomputable def ell (α : ℝ) (n : ℕ) (P : List ℕ) (i : ℕ) : ℕ :=
  (Iv α n (i - 1) \ P.toFinset).card / sOcc α n P i

end QueryDepthMIS


