-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastWindow256Reference
-- name    : TaoFivePrimes_RHFastWindow256Reference
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:40:37.22841+00:00
-- url     : https://prove2.me/theorems/66c1413b-f455-4974-988f-1f38b66b1879
-- title:
--   Direct reference table checker for the new128-unit window method
-- statement:
--   The256-bit checker compares directly with the original proposed signed integer Fourier tables. This definition imports only their data, carries no old Gamma or Fourier accuracy certificate, and also checks a coarse reference magnitude bound.
-- source:
--   Platt DOI10.1090/mcom/3198. Original proposed data attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastBallFrequencyProgram256
import Definitions.Def_TaoFivePrimes_RHFastWindow256Common
import Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
namespace RHFastWindow256Reference
noncomputable def references (j:Nat):List (Int×Int):=
 (List.range 24).map (fun k=>RHHighZetaCorrelation.signed (RHHighGammaFourierTable.values k) j)
noncomputable def checked (j:Nat):Bool:=
 RHFastBallFrequencyProgram256.checked j RHFastWindow256Common.anchor RHFastWindow256Common.pi
  RHFastWindow256Common.root RHFastWindow256Common.omega RHFastWindow256Common.qs RHFastWindow256Common.factors
  (references j) &&
 (references j).all (fun p=>decide (p.1.natAbs+p.2.natAbs≤65536*2^85))
noncomputable def block (start count:Nat):Bool:=(List.range count).all (fun i=>checked (start+i))
end RHFastWindow256Reference
noncomputable def TaoFivePrimes_RHFastWindow256Reference : Nat:=1954


