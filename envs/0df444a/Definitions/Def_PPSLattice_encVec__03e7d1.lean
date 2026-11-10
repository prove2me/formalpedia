-- Prove2me | Definitions.Def_PPSLattice_encVec__03e7d1
-- name    : PPSLattice_encVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:22.427208+00:00
-- url     : https://prove2.me/theorems/03e7d159-a27b-4e33-989e-16973495e070
-- title:
--   Code of a vector $v\in\mathbb Z_q^k$
-- statement:
--   A vector $v\in\mathbb Z_q^k$ is written as the concatenation of the $\lceil\log_2 q\rceil$-bit binary codes $\mathrm{bin}_{\lceil\log_2 q\rceil}(v_j)$ (least significant bit first, the published `AvoidPlast.fixedBits`), $j=0,\dots,k-1$, where $v_j$ is represented in $[0,q)$. Its length is $k\lceil\log q\rceil$.
--
--   **Formalization Note** $\mathbb Z_q$ is `ZMod q`, $\lceil\log_2 q\rceil$ is `Nat.clog 2 q`.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16; §4.4, p.23

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_AvoidPlast_fixedBits
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **code of a vector** `v ∈ Z_q^k`: the entries in order, each as the `⌈log₂ q⌉`-bit binary
code of its representative in `[0, q)`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §3.1, p.16 (vectors over Z_q) and §4.4, p.23 (|crs| = nm⌈log N⌉⌈log q⌉).

**Formalization Note.** `⌈log₂ q⌉` is `Nat.clog 2 q`; the representative is `ZMod.val`; the fixed-width
binary code is the published `AvoidPlast.fixedBits` (least significant bit first). -/
def encVec (q : ℕ) {k : ℕ} (v : Fin k → ZMod q) : Str :=
  (List.ofFn fun j => AvoidPlast.fixedBits (Nat.clog 2 q) (v j).val).flatten

end PPSLattice


