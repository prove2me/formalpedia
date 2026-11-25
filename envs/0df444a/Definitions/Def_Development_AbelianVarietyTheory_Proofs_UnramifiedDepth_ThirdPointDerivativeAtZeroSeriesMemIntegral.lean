-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:45.010802+00:00
-- url     : https://prove2.me/theorems/c6f864ce-17b0-4cc5-98e7-abc948f56d5b
-- title:
--   Third Point Derivative At Zero Series Mem Integral
-- statement:
--   Definitions and structural lemmas for Third Point Derivative At Zero Series Mem Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
namespace GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}
def DD (F : Pt k 2 d) (a : Fin 2) (u : Fin d → k) (G : PS k 2 d) : PS k 2 d :=
  ∑ j, ev (n := 2) ![pt k d a] (dy u (F j)) * pderiv k (a, j) G
def dz3 (v : Fin d → k) (f : PS k 3 d) : PS k 2 d :=
  ∑ i, C (v i) * ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) f)
def al (u : Fin d → k) (g : PS k 2 d) : PS k 1 d :=
  ∑ i, C (u i) * ev (n := 1) ![0, pt k d 0] (pderiv k ((0 : Fin 2), i) g)
end GlobalTheory.GaugeDiv
namespace GlobalTheory
open GaugeDiv
end GlobalTheory


