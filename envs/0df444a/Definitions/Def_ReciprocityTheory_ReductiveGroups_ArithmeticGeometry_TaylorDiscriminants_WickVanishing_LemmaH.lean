-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LemmaH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:56.759503+00:00
-- url     : https://prove2.me/theorems/f0be515f-f891-417c-b8e1-9f1a2a649d23
-- title:
--   Lemma H
-- statement:
--   Definitions and structural lemmas for Lemma H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LemmaH.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SCWick
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
abbrev kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k) (l l' : ι) : k :=
  if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0
end ReciprocityTheory.ChartRestriction.G.TB.SCPf


