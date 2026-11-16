-- Prove2me | Definitions.Def_MaxCompForest_Supplement_encQuantIn
-- name    : MaxCompForest_Supplement_encQuantIn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:14:49.544497+00:00
-- url     : https://prove2.me/theorems/191038e0-974f-4ff7-8a0a-874172a8c2cc
-- title:
--   Input word of the quantization algorithm (Theorem 2.1)
-- statement:
--   The binary input of the rational quantization algorithm of Theorem 2.1: the budget parameters $q$ and $s$, the dimension $d$, the explicit rational graph (vertex and edge counts, endpoints, positive rational conductances), and the rational $d\times n$ feature matrix whose column $v$ is the feature vector $\Phi_v$, all in binary and separated by a separator symbol. Its length is the total binary input length $L$.
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem 2.1, p.6 (PDF p.8); binary input convention, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_MaxCompForest_graphWords
import Definitions.Def_MaxCompForest_encWords
import Definitions.Def_MaxCompForest_matWords
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_OnlineCRS_Combine_encNat
open OnlineCRS.Combine (Sym encNat)
set_option autoImplicit false

namespace MaxCompForest.Supplement

/-- **The input word of the quantization algorithm of Theorem 2.1**: `q`, `s`, `d`, the rational graph, and the
`d × n` rational feature matrix (the row of vertex `v` is column `v`), all in binary.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), Theorem 2.1 ("For rational graph and feature inputs"), p.6; the binary convention of p.14. -/
def encQuantIn (I : MaxCompForest.RInst) (q s : ℕ) {d : ℕ} (x : Fin d → Fin I.n → ℚ) : List Sym :=
  MaxCompForest.encWords ([encNat q, encNat s, encNat d] ++ MaxCompForest.graphWords I ++
    MaxCompForest.matWords x)

end MaxCompForest.Supplement


