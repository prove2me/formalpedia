-- Prove2me | Definitions.Def_PPSLattice_decVec
-- name    : PPSLattice_decVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:23.778798+00:00
-- url     : https://prove2.me/theorems/b2e871c4-c918-4200-be20-735c39530709
-- title:
--   Parser of $k$ elements of $\mathbb Z_q$ in $w$-bit blocks
-- statement:
--   For a string $u$, entry $j<k$ of $\mathrm{dec}_{q,w,k}(u)\in\mathbb Z_q^k$ is the value of bits $jw,\dots,jw+w-1$ of $u$ reduced modulo $q$ (missing bits are absent).
--
--   With $w=\lceil\log q\rceil$ it inverts the code of vectors; with $w=\ell_q$ it reads the outputs of the circuit of Figure 1, "Decode reduces it modulo $q$".
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Remark 4.9, p.22; Figure 1, p.22

import Mathlib
import Definitions.Def_PPSLattice_decBin
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **parser of `k` elements of Z_q written in blocks of `wd` bits**: entry `j` is the binary
value of bits `j·wd, …, j·wd + wd − 1` of `w`, reduced modulo `q` (missing bits read as absent).
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Remark 4.9, p.22 ("Decode reduces it modulo q") and Figure 1, p.22 ("Parse input b
as B ∈ Z_q^{n×m}").

**Formalization Note.** With `wd = ⌈log₂ q⌉` it inverts `encVec`; with `wd = ℓ_q` it reads the
outputs of the circuit of Figure 1. -/
def decVec (q wd k : ℕ) (w : Str) : Fin k → ZMod q :=
  fun j => ((decBin ((w.drop (j.val * wd)).take wd) : ℕ) : ZMod q)

end PPSLattice


