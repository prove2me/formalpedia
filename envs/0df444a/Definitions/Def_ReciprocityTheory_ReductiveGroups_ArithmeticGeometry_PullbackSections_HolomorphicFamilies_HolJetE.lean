-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T15:10:31.308199+00:00
-- url     : https://prove2.me/theorems/0b9dc2b2-8a45-40de-ba62-153de854c09c
-- title:
--   Hol Jet E
-- statement:
--   Definitions and structural lemmas for Hol Jet E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetE.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
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
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {g : ℕ} {Y Y' : Scheme.{0}}
theorem isHolFam_const (u : Sp ℂ ⟶ Y) : IsHolFam (g := g) (fun _ => u) := by
  intro U f
  exact ⟨isOpen_const, differentiableOn_const _⟩
def jetZero (m : ℕ) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m :=
  jetMap (fun _ => 0) fun _ => Ideal.zero_mem _
end ReciprocityTheory.ChartRestriction.G.PullbackSections


