-- Prove2me | Definitions.Def_PPSLattice_PolyTimeOn
-- name    : PPSLattice_PolyTimeOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:18.852765+00:00
-- url     : https://prove2.me/theorems/75f126b9-9ea1-4cfc-89e5-e4e45f9675f8
-- title:
--   Deterministic polynomial-time algorithm on coded inputs
-- statement:
--   A function from inputs $a$ to outputs is computed by a **deterministic polynomial-time algorithm** (for the given codes) if a single polynomial-time machine maps the code of every input $a$ to the code of its output.
--
--   **Formalization Note** The machine model is `PolyTimeComputable` of `QAlgorithms_ClassicalStringComputability` (multi-stack Turing machines). Every input is covered, not only those of honest runs.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15; §3.1, p.16; §4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- A **deterministic polynomial-time algorithm**: one polynomial-time machine `M` maps the code
`code a` of every input `a` to the code `out a` of the output.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3, p.15 (PPT algorithms), §4.1, p.17 ("polynomial time algorithms"; "The deterministic decoding
algorithm"), §3.1, p.16 ("two deterministic polynomial-time algorithms").

**Formalization Note.** The machine model is `PolyTimeComputable` (multi-stack Turing machines,
time polynomial in the length of the input code). Every input is covered, not only the inputs of
honest runs. -/
def PolyTimeOn {ι : Type} (code : ι → Str) (out : ι → Str) : Prop :=
  ∃ M : Str → Str, PolyTimeComputable M ∧ ∀ a, M (code a) = out a

end PPSLattice


