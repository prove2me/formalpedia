-- Prove2me | Definitions.Def_PPSLattice_encBin
-- name    : PPSLattice_encBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:16.287225+00:00
-- url     : https://prove2.me/theorems/87cbbaf8-da2c-4d7a-88bb-e4d6c9e0c303
-- title:
--   Binary code $\mathrm{bin}(k)$ of a natural number
-- statement:
--   For $k\in\mathbb N$, $\mathrm{bin}(k)\in\{0,1\}^*$ is the list of the binary digits of $k$, least significant first, with no leading zeros; in particular $\mathrm{bin}(0)$ is the empty string.
--
--   The syntax of a PPS gives the number of indices $N$ to $\mathrm{GSetup}$ in binary; the mission also writes indices $i\in[N]$, moduli $q$ and other parameters in binary.
--
--   **Formalization Note** This is `Nat.bits`; `decBin` inverts it.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17 (N in binary)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **binary code** of a natural number: its bits, least significant first, with no leading
zeros (`encBin 0 = []`).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, p.17 ("number of indices N (in binary)").

**Formalization Note.** Used for the number of indices `N`, for indices `i`, and for binary
outputs (moduli, widths) of parameter machines. `decBin` inverts it. -/
def encBin (k : ℕ) : Str := k.bits

end PPSLattice


