-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighRealGrid
-- name    : TaoFivePrimes_RHHighRealGrid
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T08:22:12.91077+00:00
-- url     : https://prove2.me/theorems/8531b7bd-1046-46a4-a3e2-d9db0ad49c3c
-- title:
--   Transparent proposed real-axis FFT grid
-- statement:
--   Lookup for4096 proposed real polynomial sample integers and two proposed sparse spectra. Defines data only, with no analytic approximation, sign, winding, count or RH assertion.
-- source:
--   Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighContourOutputRealNeg64
import Definitions.Def_TaoFivePrimes_RHHighContourOutputRealZero
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumNeg64
import Definitions.Def_TaoFivePrimes_RHHighRealSpectrumZero
import Definitions.Def_TaoFivePrimes_RHHighContourVector
set_option autoImplicit false
namespace RHHighRealGrid
noncomputable def outputRows : List (List (List Nat)) :=
 [RHHighContourOutputRealNeg64.rows,RHHighContourOutputRealZero.rows]
noncomputable def word (i : Nat) : Nat :=
 (((((outputRows[i/2048]?).getD [])[i%2048/512]?).getD [])[i%512]?).getD 0
noncomputable def value (i : Nat) : Int := (RHHighContourVector.decode (word i)).1
noncomputable def spectrumRows : List (List (List Nat)) :=
 [RHHighRealSpectrumNeg64.rows,RHHighRealSpectrumZero.rows]
noncomputable def spectrum (t : Nat) : List Nat := ((spectrumRows[t]?).getD []).flatten
end RHHighRealGrid
noncomputable def TaoFivePrimes_RHHighRealGrid : Nat := 4096


