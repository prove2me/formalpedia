-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighGammaFourierTable
-- name    : TaoFivePrimes_RHHighGammaFourierTable
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T09:16:25.624667+00:00
-- url     : https://prove2.me/theorems/45a69766-4fd8-41a3-bc97-d63f970eadda
-- title:
--   The24 proposed signed gamma moment Fourier tables
-- statement:
--   Transparent lookup into the24 existing gamma FFT output tables, with the(-1)^j factor and scaling by2^85. Defines only proposed values, without analytic accuracy, sign, winding, count or RH assertions.
-- source:
--   Platt DOI10.1090/mcom/3198. Original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive00
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive01
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive02
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive03
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive04
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive05
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive06
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive07
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive08
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive09
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive10
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive11
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive12
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive13
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive14
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive15
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive16
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive17
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive18
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive19
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive20
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive21
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive22
import Definitions.Def_TaoFivePrimes_RHHighFFTPositive23
namespace RHHighGammaFourierTable
noncomputable def packets : List (List Nat) := [RHHighFFTPositive00.rows.flatten,RHHighFFTPositive01.rows.flatten,RHHighFFTPositive02.rows.flatten,RHHighFFTPositive03.rows.flatten,RHHighFFTPositive04.rows.flatten,RHHighFFTPositive05.rows.flatten,RHHighFFTPositive06.rows.flatten,RHHighFFTPositive07.rows.flatten,RHHighFFTPositive08.rows.flatten,RHHighFFTPositive09.rows.flatten,RHHighFFTPositive10.rows.flatten,RHHighFFTPositive11.rows.flatten,RHHighFFTPositive12.rows.flatten,RHHighFFTPositive13.rows.flatten,RHHighFFTPositive14.rows.flatten,RHHighFFTPositive15.rows.flatten,RHHighFFTPositive16.rows.flatten,RHHighFFTPositive17.rows.flatten,RHHighFFTPositive18.rows.flatten,RHHighFFTPositive19.rows.flatten,RHHighFFTPositive20.rows.flatten,RHHighFFTPositive21.rows.flatten,RHHighFFTPositive22.rows.flatten,RHHighFFTPositive23.rows.flatten]
noncomputable def values (k : Nat) : List Nat := (packets[k]?).getD []
noncomputable def value (k j : Nat) : ℂ :=
 let p:=RHHighZetaCorrelation.signed (values k) j
 ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85
end RHHighGammaFourierTable
noncomputable def TaoFivePrimes_RHHighGammaFourierTable : Nat := 24


