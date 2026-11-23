-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:00:40.906265+00:00
-- url     : https://prove2.me/theorems/8ad4f31c-16c1-4f86-bd0c-684163e1ced5
-- title:
--   Word Monomial
-- statement:
--   Definitions and structural lemmas for Word Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/WordMonomial.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open MvPolynomial
noncomputable section
namespace GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
section Pol
variable {σ : Type}
def pd (i : σ) : Module.End ℂ (MvPolynomial σ ℂ) := (pderiv i : Derivation ℂ (MvPolynomial σ ℂ) _).toLinearMap
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Pol
end GlobalTheory.CompanionTheory.DSCover


