-- Prove2me | Definitions.Def_PPSLattice_encSet
-- name    : PPSLattice_encSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:19.557598+00:00
-- url     : https://prove2.me/theorems/f7b287b0-3a54-4bb0-abff-3eb92beea096
-- title:
--   Description $\langle S\rangle$ of a finite set
-- statement:
--   A finite set $S\subseteq\mathbb N$ is described by the list of its elements in increasing order, each in binary, packed with the self-delimiting tuple code `tup`. For $S\subseteq[N]$ the description has length $O(|S|\log N)$.
--
--   This is the input that $\mathrm{KGen}$ and $\mathrm{Decode}$ read, so their running time may grow with $|S|$ but not with $N$ ("none of our algorithms have running times growing with $N$ (beyond the set description $|S|$)").
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, Syntax, p.17; §4.4, p.24

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_PPSLattice_encBin
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **description of a finite set** `S ⊆ ℕ` as a bit string: the list of its elements in
increasing order, each in binary (`encBin`), packed with `tup`. For `S ⊆ [N]` its length is
`O(|S| · ⌈log N⌉)`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.1, p.17 (KGen takes "set S ⊆ [N]"), and p.24 ("none of our algorithms have
running times growing with N (beyond the set description |S|)").

**Formalization Note.** This is the code a polynomial-time `KGen` or `Decode` reads, so their
running time may grow with `|S|`, but not with `N`. `decSet` parses it. -/
def encSet (S : Finset ℕ) : Str := BeyondDS.tup ((S.sort (· ≤ ·)).map encBin)

end PPSLattice


