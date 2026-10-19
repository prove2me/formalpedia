-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastWindow256CompactReference
-- name    : TaoFivePrimes_RHFastWindow256CompactReference
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:53:28.938696+00:00
-- url     : https://prove2.me/theorems/9763f886-7765-4125-8687-f5c8cf08eeaf
-- title:
--   Packed-reference checker for the256-bit window method
-- statement:
--   The256-bit Fourier checker uses losslessly packed proposed reference data for constant-size bit extraction. Equality with the original data and analytic soundness require separate proofs.
-- source:
--   Platt DOI10.1090/mcom/3198. Proposed data sometik179 c9908072-d99a-4431-aad8-a72c6352619a and surrounding attribution Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastWindowPackedReference00
import Definitions.Def_TaoFivePrimes_RHFastWindowPackedReference01
import Definitions.Def_TaoFivePrimes_RHFastWindowPackedReference02
import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyProgram256
import Definitions.Def_TaoFivePrimes_RHFastWindow256Common
namespace RHFastWindow256CompactReference
noncomputable def packets:List (List Nat):=[RHFastWindowPackedReference00.p00,RHFastWindowPackedReference00.p01,RHFastWindowPackedReference00.p02,RHFastWindowPackedReference00.p03,RHFastWindowPackedReference00.p04,RHFastWindowPackedReference00.p05,RHFastWindowPackedReference00.p06,RHFastWindowPackedReference00.p07,RHFastWindowPackedReference01.p08,RHFastWindowPackedReference01.p09,RHFastWindowPackedReference01.p10,RHFastWindowPackedReference01.p11,RHFastWindowPackedReference01.p12,RHFastWindowPackedReference01.p13,RHFastWindowPackedReference01.p14,RHFastWindowPackedReference01.p15,RHFastWindowPackedReference02.p16,RHFastWindowPackedReference02.p17,RHFastWindowPackedReference02.p18,RHFastWindowPackedReference02.p19,RHFastWindowPackedReference02.p20,RHFastWindowPackedReference02.p21,RHFastWindowPackedReference02.p22,RHFastWindowPackedReference02.p23]
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
 RHFastBallFrequencyProgram256.checked j RHFastWindow256Common.anchor RHFastWindow256Common.pi
  RHFastWindow256Common.root RHFastWindow256Common.omega RHFastWindow256Common.qs RHFastWindow256Common.factors
  (references j) &&
 (references j).all (fun p=>decide (p.1.natAbs+p.2.natAbs≤65536*2^85))
noncomputable def block (start count:Nat):Bool:=(List.range count).all (fun i=>checked (start+i))
end RHFastWindow256CompactReference
noncomputable def TaoFivePrimes_RHFastWindow256CompactReference : Nat:=1954


