-- Prove2me | Definitions.Def_NearOptOWF_NmCAPPInst_enc
-- name    : NearOptOWF_NmCAPPInst_enc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:14:13.880327+00:00
-- url     : https://prove2.me/theorems/7fa27a1b-645f-4e2f-a3da-c932d7f166cc
-- title:
--   Encoding of an nmCAPP instance
-- statement:
--   An nmCAPP instance is given to the verifier as the tuple $(1^n, 1^w, \langle C\rangle, \beta \text{ in binary}, 1^k)$, with the published fixed circuit code. The encoding is injective; writing $k = 1/\epsilon$ in unary matches a running time polynomial in $\epsilon^{-1}$.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition 3.1, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_NearOptOWF_NmCAPPInst
import Definitions.Def_KarpLiptonOM_circuitCode
import Definitions.Def_KarpLiptonOM_binW
import Definitions.Def_LaconicBarrier_RunsWithin

namespace NearOptOWF

open LaconicBarrier

/-- The **encoding of an nmCAPP instance** as the input tuple of the verifier (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), Definition
3.1, p.8 (PDF p.10)): `(1ⁿ, 1^w, code of C, β in binary, 1^k)`, with the published fixed circuit code
`KarpLiptonOM.circuitCode`.

**Formalization Note** The encoding is injective; `k = 1/ε` is written in unary, consistent with a
running time polynomial in `ε^{-1}`. -/
def NmCAPPInst.enc (I : NmCAPPInst) : List (List Bool) :=
  [unary I.n, unary I.w, KarpLiptonOM.circuitCode (I.n + I.w) I.C.gates.length I.C,
    KarpLiptonOM.binW (Nat.size I.β) I.β, unary I.k]

end NearOptOWF


