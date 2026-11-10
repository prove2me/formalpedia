-- Prove2me | Definitions.Def_PPSLattice_decSet
-- name    : PPSLattice_decSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:22.9089+00:00
-- url     : https://prove2.me/theorems/dd4f0ae1-c8ef-4582-90dc-7a9d4bbe7822
-- title:
--   Parser of set descriptions
-- statement:
--   The set of the binary values of the fields of a string: it inverts the set description and every string denotes some finite set. It reads the set $S$ named by an adversary in the PPS games.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, p.18

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_PPSLattice_decBin
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **parser of set descriptions**: the set of the binary values of the fields of `w`. It
inverts `encSet`, and every string denotes some finite set.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.1, p.18 (the adversary outputs a set S).

**Formalization Note.** Used to read the set `S` that an adversary names in the PPS games. -/
def decSet (w : Str) : Finset ℕ := ((BeyondDS.untup w).map decBin).toFinset

end PPSLattice


