-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsAdFam
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsAdFam
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:08:26.684804+00:00
-- url     : https://prove2.me/theorems/6cdf3be8-dfd5-485c-8e87-342b32b8cf63
-- title:
--   Exists Ad Fam
-- statement:
--   Definitions and structural lemmas for Exists Ad Fam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsAdFam.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.CompanionTheory.LKInvLift
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC (KStab)
open CompanionTheory.D.LK
variable {n : ℕ}
def AdFam {ι : Type} [Fintype ι] (w : ι → FreeAlgebra ℂ (Fin n × Fin n)) (M : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ c d i j, star (M c d j i) = M d c i j) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
    ∀ c d i, E c d * ev E (w i) - ev E (w i) * E c d = ∑ j, M c d j i • ev E (w j)
end GlobalTheory.CompanionTheory.LKInvLift


