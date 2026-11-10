-- Prove2me | Definitions.Def_PPSLattice_xorStr
-- name    : PPSLattice_xorStr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:17.871473+00:00
-- url     : https://prove2.me/theorems/fa03116f-15c3-486c-8fd7-fe669076144d
-- title:
--   Bitwise exclusive or $u\oplus v$ of bit strings
-- statement:
--   $(u\oplus v)_j=u_j\oplus v_j$ for $j<\min(|u|,|v|)$. Construction 4.6 uses it as $T=\mathrm{SEPRF.Eval}(\mathrm{prf.key},t)\oplus\tilde C$ and $\mu'=h\oplus\lceil tg'\rfloor_2$, always on strings of equal length.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **bitwise exclusive or** `u ⊕ v` of two bit strings, position by position.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21 ("T = SEPRF.Eval(prf.key, t) ⊕ C̃", "C̃ = T ⊕ SEPRF.Eval(prf.key, t)",
"µ′ := h ⊕ ⌈tg′⌋₂").

**Formalization Note.** The construction applies it only to strings of equal length; on strings of
different lengths the result has the shorter length. -/
def xorStr (u v : Str) : Str := List.zipWith xor u v

end PPSLattice


