-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01New256CompactReference
-- name    : TaoFivePrimes_RHBatch01New256CompactReference
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T13:16:59.05223+00:00
-- url     : https://prove2.me/theorems/7cd56c32-9b3a-4f0f-a014-81faf26d37f1
-- title:
--   Transparent fresh-center Fourier evaluator and packed reference checker; no correctness assertion.
-- statement:
--   Transparent fresh-center Fourier evaluator and packed reference checker; no correctness assertion.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198. Original mathematical attribution: sometik179, submission c9908072-d99a-4431-aad8-a72c6352619a, and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01New256PackedReference00
import Definitions.Def_TaoFivePrimes_RHBatch01New256PackedReference01
import Definitions.Def_TaoFivePrimes_RHBatch01New256PackedReference02
import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyProgram256
import Definitions.Def_TaoFivePrimes_RHBatch01New256Common
namespace RHBatch01New256CompactReference
noncomputable def packets:List (List Nat):=[RHBatch01New256PackedReference00.p00,RHBatch01New256PackedReference00.p01,RHBatch01New256PackedReference00.p02,RHBatch01New256PackedReference00.p03,RHBatch01New256PackedReference00.p04,RHBatch01New256PackedReference00.p05,RHBatch01New256PackedReference00.p06,RHBatch01New256PackedReference00.p07,RHBatch01New256PackedReference01.p08,RHBatch01New256PackedReference01.p09,RHBatch01New256PackedReference01.p10,RHBatch01New256PackedReference01.p11,RHBatch01New256PackedReference01.p12,RHBatch01New256PackedReference01.p13,RHBatch01New256PackedReference01.p14,RHBatch01New256PackedReference01.p15,RHBatch01New256PackedReference02.p16,RHBatch01New256PackedReference02.p17,RHBatch01New256PackedReference02.p18,RHBatch01New256PackedReference02.p19,RHBatch01New256PackedReference02.p20,RHBatch01New256PackedReference02.p21,RHBatch01New256PackedReference02.p22,RHBatch01New256PackedReference02.p23]
noncomputable def raw (k j:Nat):Nat:=
 let chunks:=(packets[k]?).getD []
 Nat.shiftRight ((chunks[j/128]?).getD 0) (192*(j%128))%2^192
noncomputable def sample (k j:Nat):Int×Int:=
 let p:=raw k j
 (((p%2^96:Nat):Int)-2^95,((p/2^96%2^96:Nat):Int)-2^95)
noncomputable def signed (k j:Nat):Int×Int:=
 let p:=sample k j
 if j%2=0 then p else (-p.1,-p.2)
noncomputable def references (j:Nat):List (Int×Int):=(List.range 24).map (fun k=>signed k j)
noncomputable def checked (j:Nat):Bool:=
 RHFastBallFrequencyProgram256.checked j RHBatch01New256Common.anchor RHBatch01New256Common.pi
  RHBatch01New256Common.root RHBatch01New256Common.omega RHBatch01New256Common.qs RHBatch01New256Common.factors
  (references j) &&
 (references j).all (fun p=>decide (p.1.natAbs+p.2.natAbs≤65536*2^85))
noncomputable def block (start count:Nat):Bool:=(List.range count).all (fun i=>checked (start+i))
end RHBatch01New256CompactReference
noncomputable def TaoFivePrimes_RHBatch01New256CompactReference : Nat:=1954


