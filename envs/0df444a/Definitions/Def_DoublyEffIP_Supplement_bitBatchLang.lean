-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_bitBatchLang
-- name    : DoublyEffIP_Supplement_bitBatchLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:41:05.128257+00:00
-- url     : https://prove2.me/theorems/eade742c-63f7-47d4-bbef-1f2e2d6534b8
-- title:
--   The batch language $L^k_t$ on bit strings
-- statement:
--   The **batch language** $L^k_t$ of $M$ with space $S$ is the set of bit strings $x$ that encode a batch $y$ of $k$ pairs of space-$S$ configurations in which every pair is a correct $t$-step transition,
--
--   $$
--   L^k_t=\big\{x=\mathrm{bits}(y) : \forall i<k,\ \mathrm{step}^t(y_{i,\mathrm{start}})=y_{i,\mathrm{end}}\big\}.
--   $$
--
--   A string that does not encode configurations is not in the language. This is the paper's $L^k_t:=\{((x_{i,\mathrm{start}},x_{i,\mathrm{end}}))_{i\in[k]}\mid\forall i\ (x_{i,\mathrm{start}},x_{i,\mathrm{end}})\in L_t\}$, built on the published `DoublyEffIP.Lkt`.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 4.1, p.14

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_WinCfg
import Definitions.Def_DoublyEffIP_Supplement_winStep
import Definitions.Def_DoublyEffIP_Supplement_batchBits
import Definitions.Def_DoublyEffIP_Lkt
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP.Supplement

/-- **The batch language `L^k_t` on bit strings** — Section 4.1 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.14: "let the language
L_t consist of all pairs (x_start, x_end) ∈ {0,1}^{S(n)} × {0,1}^{S(n)} such that M transitions
from configuration x_start to configuration x_end in exactly t steps … L^k_t :=
{((x_{i,start}, x_{i,end}))_{i∈[k]} | ∀ i ∈ [k] (x_{i,start}, x_{i,end}) ∈ L_t}".

The bit strings `batchBits y` of the batches `y` of `k` pairs of space-`S` configurations of `M` in
the published `L^k_t` (`DoublyEffIP.Lkt`) of the step `winStep M S`.

**Formalization Note.** A string that does not encode configurations is not in the language. -/
def bitBatchLang (M : PrimitiveMachine) (S t k : ℕ) : Set (List Bool) :=
  {x | ∃ y : Fin k → WinCfg M S × WinCfg M S,
    y ∈ DoublyEffIP.Lkt (winStep M S) t (Fin k) ∧ x = batchBits y}

end DoublyEffIP.Supplement


