-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01GammaFourierTable
-- name    : TaoFivePrimes_RHBatch01GammaFourierTable
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T15:33:46.789087+00:00
-- url     : https://prove2.me/theorems/e528613c-fe33-4cb9-af22-50c494bcbe33
-- title:
--   The24 proposed signed gamma moment Fourier tables
-- statement:
--   Transparent lookup into the24 existing gamma FFT output tables, with the(-1)^j factor and scaling by2^85. Defines only proposed values, without analytic accuracy, sign, winding, count or RH assertions.
-- source:
--   Platt DOI10.1090/mcom/3198. Original attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ZetaCorrelation
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive00
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive01
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive02
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive03
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive04
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive05
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive06
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive07
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive08
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive09
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive10
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive11
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive12
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive13
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive14
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive15
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive16
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive17
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive18
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive19
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive20
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive21
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive22
import Definitions.Def_TaoFivePrimes_RHBatch01FFTPositive23
namespace RHBatch01GammaFourierTable
noncomputable def packets : List (List Nat) := [RHBatch01FFTPositive00.rows.flatten,RHBatch01FFTPositive01.rows.flatten,RHBatch01FFTPositive02.rows.flatten,RHBatch01FFTPositive03.rows.flatten,RHBatch01FFTPositive04.rows.flatten,RHBatch01FFTPositive05.rows.flatten,RHBatch01FFTPositive06.rows.flatten,RHBatch01FFTPositive07.rows.flatten,RHBatch01FFTPositive08.rows.flatten,RHBatch01FFTPositive09.rows.flatten,RHBatch01FFTPositive10.rows.flatten,RHBatch01FFTPositive11.rows.flatten,RHBatch01FFTPositive12.rows.flatten,RHBatch01FFTPositive13.rows.flatten,RHBatch01FFTPositive14.rows.flatten,RHBatch01FFTPositive15.rows.flatten,RHBatch01FFTPositive16.rows.flatten,RHBatch01FFTPositive17.rows.flatten,RHBatch01FFTPositive18.rows.flatten,RHBatch01FFTPositive19.rows.flatten,RHBatch01FFTPositive20.rows.flatten,RHBatch01FFTPositive21.rows.flatten,RHBatch01FFTPositive22.rows.flatten,RHBatch01FFTPositive23.rows.flatten]
noncomputable def values (k : Nat) : List Nat := (packets[k]?).getD []
noncomputable def value (k j : Nat) : ℂ :=
 let p:=RHBatch01ZetaCorrelation.signed (values k) j
 ((p.1:ℂ)+(p.2:ℂ)*Complex.I)/(2:ℂ)^85
end RHBatch01GammaFourierTable
noncomputable def TaoFivePrimes_RHBatch01GammaFourierTable : Nat := 24


