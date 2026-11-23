-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:15.513672+00:00
-- url     : https://prove2.me/theorems/b09ef897-a5f2-4965-a841-2b3728fc1fe1
-- title:
--   SCWick
-- statement:
--   Definitions and structural lemmas for SCWick, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/SCWick.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
def kapW (m : ℕ) {ι : Type} (s : ι → Bool) (ξa ξb : ι → (Fin d → k) × (Fin d → k)) (l l' : ι) : k :=
  if s l = true ∧ s l' = false then (m : k) * betaH k (ξb l) (ξa l') else 0
end ReciprocityTheory.ChartRestriction.G.TB.SCPf


