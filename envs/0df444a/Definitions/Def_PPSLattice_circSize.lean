-- Prove2me | Definitions.Def_PPSLattice_circSize
-- name    : PPSLattice_circSize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:28.372018+00:00
-- url     : https://prove2.me/theorems/ebc4f48e-ba1d-4366-a8c5-594e4b7a2c4a
-- title:
--   Size of a Boolean circuit
-- statement:
--   The size of a NAND circuit (`RestrictedDec.Circuit`) is its number of gates.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.19; Claims 4.10–4.11, p.23

import Mathlib
import Definitions.Def_RestrictedDec_Circuit
set_option autoImplicit false

namespace PPSLattice

/-- The **size** of a Boolean circuit: its number of NAND gates.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.2, p.19 ("maximum circuit size s"); Claims 4.10–4.11, p.23 ("size s_f", "size s_C"). -/
def circSize (C : RestrictedDec.Circuit) : ℕ := C.gates.length

end PPSLattice


