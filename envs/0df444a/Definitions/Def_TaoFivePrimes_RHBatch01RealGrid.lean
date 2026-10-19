-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01RealGrid
-- name    : TaoFivePrimes_RHBatch01RealGrid
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T17:43:48.778077+00:00
-- url     : https://prove2.me/theorems/6670a627-f142-43d9-bd60-5a48af9102e7
-- title:
--   Transparent proposed real-axis FFT grid
-- statement:
--   Lookup for4096 proposed real polynomial sample integers and two proposed sparse spectra. Defines data only, with no analytic approximation, sign, winding, count or RH assertion.
-- source:
--   Platt Fourier polynomial DOI10.1090/mcom/3198. Attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputRealNeg64
import Definitions.Def_TaoFivePrimes_RHBatch01ContourOutputRealZero
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumNeg64
import Definitions.Def_TaoFivePrimes_RHBatch01RealSpectrumZero
import Definitions.Def_TaoFivePrimes_RHHighContourVector
set_option autoImplicit false
namespace RHBatch01RealGrid
noncomputable def outputRows : List (List (List Nat)) :=
 [RHBatch01ContourOutputRealNeg64.rows,RHBatch01ContourOutputRealZero.rows]
noncomputable def word (i : Nat) : Nat :=
 (((((outputRows[i/2048]?).getD [])[i%2048/512]?).getD [])[i%512]?).getD 0
noncomputable def value (i : Nat) : Int := (RHHighContourVector.decode (word i)).1
noncomputable def spectrumRows : List (List (List Nat)) :=
 [RHBatch01RealSpectrumNeg64.rows,RHBatch01RealSpectrumZero.rows]
noncomputable def spectrum (t : Nat) : List Nat := ((spectrumRows[t]?).getD []).flatten
end RHBatch01RealGrid
noncomputable def TaoFivePrimes_RHBatch01RealGrid : Nat := 4096


