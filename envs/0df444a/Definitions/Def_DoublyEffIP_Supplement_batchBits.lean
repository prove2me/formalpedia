-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_batchBits
-- name    : DoublyEffIP_Supplement_batchBits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:40:12.548899+00:00
-- url     : https://prove2.me/theorems/f66ad70e-5bab-40a8-b4c8-c84db6ac541c
-- title:
--   A batch of transition claims as a bit string
-- statement:
--   A batch $y=((y_{i,\mathrm{start}},y_{i,\mathrm{end}}))_{i<k}$ of $k$ pairs of space-$S$ configurations is written as the bit string listing, for each $i$ in order, the encoding of $y_{i,\mathrm{start}}$ followed by that of $y_{i,\mathrm{end}}$. Its length is $k\cdot 2w(M,S)$; it is the input batch $x\in\{0,1\}^{2S\cdot k}$ of Protocol 1.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Table 1, p.20; Protocol 1, p.21

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_WinCfg
import Definitions.Def_DoublyEffIP_Supplement_winEnc
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **A batch of transition claims as a bit string** — "Input Batch: x ∈ {0,1}^{2S·k}"
(Protocol 1, p.21) and `x = ((x_{i,start}, x_{i,end}))_{i∈[k]}` (Table 1, p.20) of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…).

The `k` claims in order, each as the encoding of its start configuration followed by that of its
end configuration. -/
def batchBits {M : PrimitiveMachine} {S k : ℕ} (y : Fin k → WinCfg M S × WinCfg M S) :
    List Bool :=
  (List.ofFn fun i => winEnc (y i).1 ++ winEnc (y i).2).flatten

end DoublyEffIP.Supplement


