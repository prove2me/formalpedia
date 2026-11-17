-- Prove2me | Definitions.Def_GroupIsoPoly_Supplement_encFlagData
-- name    : GroupIsoPoly_Supplement_encFlagData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:25:35.529653+00:00
-- url     : https://prove2.me/theorems/538abe5f-32c3-4ff5-9176-628a16bcb73f
-- title:
--   Binary codes of the input and output of Theorem 5.1
-- statement:
--   The **input** of Theorem 5.1 is the code of a prime $p$, a dimension $d$, the number of generators and each generator of $H\le\mathrm{GL}(d,p)$ as its $d\times d$ matrix, row by row, each entry in $\{0,\dots,p-1\}$; every number is written with the self-delimiting binary code `encodeNat`. Its length is $\mathrm{InSize}$.
--
--   The **output** is the code of $\ell$, then each basis of $V_0,\dots,V_\ell$, then for each factor the number of blocks and the basis of each block's subspace; a list of vectors is its length followed by the vectors, and a vector is the self-delimiting list of its coordinates (`encNatList`).
--
--   These are the codes of the running-time statement of Theorem 5.1.
--
--   **Formalization Note** Numbers use the published `ExponomialAssortment.FPTAS.encodeNat`, lists the base mission's `GroupIsoPoly.encNatList`. The prime $p$ is part of the input, and dimensions come first, as in the base mission's codes.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 5.1, p.42 (PDF p.46); §3.5, pp.18–19 (PDF pp.22–23)

import Mathlib
import Definitions.Def_GroupIsoPoly_encAnswer
import Definitions.Def_GroupIsoPoly_Supplement_FlagValid

set_option autoImplicit false

namespace GroupIsoPoly

namespace Supplement

open ExponomialAssortment.FPTAS (encodeNat)

/-- The code of a vector of `F_p^d`: the self-delimiting list of its coordinates `0, …, p−1`. -/
def encVec {p d : ℕ} (v : Fin d → ZMod p) : List Bool :=
  encNatList (List.ofFn fun r => (v r).val)

/-- The code of a list of vectors: its length, then each vector. -/
def encVecs {p d : ℕ} (l : List (Fin d → ZMod p)) : List Bool :=
  encodeNat l.length ++ (l.map encVec).flatten

/-- **The binary input of Theorem 5.1**: generators of `H ≤ GL(d, p)`.

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 5.1, p.42 (PDF p.46): "Let H ≤ GL(d, p) be
given by generators. The following can be computed in time p^O(d) · poly(InSize)."

The code is `p`, `d`, the number of generators, then each generator's `d × d` matrix row by row, every
entry `0, …, p−1` by `encodeNat`. Its length is `InSize`.

**Formalization Note.** The prime `p` is part of the input; dimensions come first, as in the base
mission's `encMTC` and `encTransInst`. -/
def encMatGroupInst (p d : ℕ) (gens : List (GL (Fin d) (ZMod p))) : List Bool :=
  encodeNat p ++ encodeNat d ++ encodeNat gens.length ++
    (gens.map fun g =>
      ((List.ofFn fun r : Fin d => List.ofFn fun c : Fin d =>
        ((g : Matrix (Fin d) (Fin d) (ZMod p)) r c).val).flatten.map encodeNat).flatten).flatten

/-- **The binary output of Theorem 5.1**: `ℓ`, the bases of `V_0, …, V_ℓ`, then for each factor the
number of blocks and the basis of each block's subspace. -/
def encFlagData {p d : ℕ} (D : FlagData p d) : List Bool :=
  encodeNat D.ℓ ++ (List.ofFn fun j => encVecs (D.V j)).flatten ++
    (List.ofFn fun i => encodeNat (D.k i) ++ (List.ofFn fun a => encVecs (D.blk i a)).flatten).flatten

end Supplement

end GroupIsoPoly


