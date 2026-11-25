-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T23:54:14.357955+00:00
-- url     : https://prove2.me/theorems/d93bfe06-ee15-426e-9647-b6a4b7f11d5a
-- title:
--   Canon Gauge Dmon Of HLIntegral
-- statement:
--   Definitions and structural lemmas for Canon Gauge Dmon Of HLIntegral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
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
open GlobalTheory.QuadDeriv
namespace GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
def IntS (n d : ℕ) : Subring (PS k n d) := (MvPowerSeries.map (σ := Fin n × Fin d) φ).range
def IP {n : ℕ} (a : Pt k n d) : Prop := ∃ a' : Pt R n d, GP a' ∧ mapP φ a' = a
def DI {n : ℕ} (f : PS k n d) : Prop := ∀ s, pderiv k s f ∈ IntS φ n d
variable {φ}
def defL (F : Pt k 2 d) (g : PS k 2 d) : PS k 3 d :=
  ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g -
    ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g
def defR (F : Pt k 2 d) (g : PS k 2 d) : PS k 3 d :=
  ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g -
    ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g
end GlobalTheory.GaugeInt
namespace GlobalTheory
open GaugeInt
end GlobalTheory


