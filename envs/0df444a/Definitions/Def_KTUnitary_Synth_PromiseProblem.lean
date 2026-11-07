-- Prove2me | Definitions.Def_KTUnitary_Synth_PromiseProblem
-- name    : KTUnitary_Synth_PromiseProblem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:24:11.827914+00:00
-- url     : https://prove2.me/theorems/5e81a3d7-3801-41e4-b43e-959865ba81cc
-- title:
--   Promise problem
-- statement:
--   A **promise problem** is a pair $(Y,N)$ of sets of bit strings: the YES instances and the NO instances. Inputs in neither set are outside the promise.
--
--   A language $A$ is identified with the promise problem $(A,A^{\mathrm c})$.
--
--   **Formalization Note** Disjointness is not part of the type: a pair with $Y\cap N\neq\emptyset$ lies in none of the classes used here, since membership demands answer $1$ on $Y$ and answer $0$ on $N$.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6, p. 15; Definition 6.3, p. 24

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace KTUnitary.Synth

/-- **Promise problem** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.6, p. 15, and Definition 6.3, p. 24): a pair
`(YES, NO)` of sets of bit strings. An input in neither set is outside the promise.

**Formalization Note** Disjointness is not part of the type; a pair with `YES ∩ NO ≠ ∅` belongs to
none of the classes of this mission, since a class membership asks for answer `1` on `YES` and
answer `0` on `NO`. A language `A` is the promise problem `(A, Aᶜ)`. -/
abbrev PromiseProblem := Set Str × Set Str

end KTUnitary.Synth


