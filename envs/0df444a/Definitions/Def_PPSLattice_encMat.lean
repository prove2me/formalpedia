-- Prove2me | Definitions.Def_PPSLattice_encMat
-- name    : PPSLattice_encMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:27.377346+00:00
-- url     : https://prove2.me/theorems/a4ba6427-127f-4e94-a6dd-d0d954d4818d
-- title:
--   Code of a matrix $M\in\mathbb Z_q^{a\times b}$
-- statement:
--   A matrix $M\in\mathbb Z_q^{a\times b}$ is written row by row (row-major), each row by the code of vectors; its length is $ab\lceil\log q\rceil$, e.g. $|\mathrm{crs}|=nm\lceil\log N\rceil\lceil\log q\rceil$ for $\mathrm{crs}=\mathbf A$.
--
--   Entry $(i,j)$ is block $ib+j$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 4.6, p.21; §4.4, p.23

import Mathlib
import Definitions.Def_PPSLattice_encVec__03e7d1
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **code of a matrix** `M ∈ Z_q^{a×b}`: its rows in order (row-major), each row coded by
`encVec`, so that it has `a · b · ⌈log₂ q⌉` bits.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Construction 4.6, p.21 ("Output crs := A") and §4.4, p.23
(|crs| = nm⌈log N⌉⌈log q⌉).

**Formalization Note.** Entry `(i, j)` occupies the block of index `i · b + j`. `decMat` parses
the same layout. -/
def encMat (q : ℕ) {a b : ℕ} (M : Matrix (Fin a) (Fin b) (ZMod q)) : Str :=
  (List.ofFn fun i => encVec q (M i)).flatten

end PPSLattice


