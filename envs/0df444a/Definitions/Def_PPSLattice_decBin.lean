-- Prove2me | Definitions.Def_PPSLattice_decBin
-- name    : PPSLattice_decBin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:22.2252+00:00
-- url     : https://prove2.me/theorems/11adc486-67ba-4a0d-a725-4dc52a28f548
-- title:
--   Value $\mathrm{val}(w)$ of a bit string read in binary
-- statement:
--   For a bit string $w=w_0w_1\cdots w_{\ell-1}$, $\mathrm{val}(w)=\sum_{j<\ell} w_j 2^j$ (least significant bit first).
--
--   It inverts the binary codes of the mission and is defined on every string, so every move of an adversary denotes some number.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17 (N in binary)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The value of a bit string read in binary, least significant bit first:
`decBin [b₀, b₁, …] = b₀ + 2 b₁ + 4 b₂ + ⋯`. It inverts `encBin` and reads every fixed-width code.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, p.17 (N in binary).

**Formalization Note.** Every string has a value, so every move of an adversary parses. -/
def decBin (w : Str) : ℕ := w.foldr (fun b n => Nat.bit b n) 0

end PPSLattice


