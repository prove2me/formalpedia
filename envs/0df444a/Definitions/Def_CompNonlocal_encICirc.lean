-- Prove2me | Definitions.Def_CompNonlocal_encICirc
-- name    : CompNonlocal_encICirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:25.764736+00:00
-- url     : https://prove2.me/theorems/9e26c024-046c-4819-8b53-d605c1c3a8ee
-- title:
--   Binary code of a circuit with interface
-- statement:
--   A fixed binary code of a circuit: the wire counts $n_c,n_q,n_a$, the measured and retained wire lists, then the gate list, each field self-delimiting (unary numbers, length prefixes). It is injective, and it is used only to state uniformity.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, p.17

import Mathlib
import Definitions.Def_CompNonlocal_ICirc

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The binary code of a circuit with interface, used to state uniformity. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), §4, p.17 ("QPT denotes a uniform quantum polynomial-time algorithm")
fixes no encoding; this one is fixed once for the whole mission.

**Formalization Note** The wire counts `nc, nq, na`, the length and the entries of `outC` and of
`outQ` (each a self-delimiting unary `encNat`), then the published `encCirc` of the gates (a
length-prefixed list of length-prefixed layers of self-delimiting instruction codes). Every field
is self-delimiting given the previous ones, so the code is injective. -/
def encICirc (C : ICirc) : Str :=
  encNat C.nc ++ encNat C.nq ++ encNat C.na ++
    encNat C.outC.length ++ (C.outC.map fun i => encNat (i : ℕ)).flatten ++
    encNat C.outQ.length ++ (C.outQ.map fun i => encNat (i : ℕ)).flatten ++
    encCirc C.gates

end CompNonlocal


