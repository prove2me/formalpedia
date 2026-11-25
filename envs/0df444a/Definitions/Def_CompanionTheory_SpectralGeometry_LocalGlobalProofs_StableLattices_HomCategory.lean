-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:50:27.631243+00:00
-- url     : https://prove2.me/theorems/079c5219-a726-4f54-84d8-a5dd210dde67
-- title:
--   Hom Category
-- statement:
--   Definitions and structural lemmas for Hom Category, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HomCategory.lean

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
namespace GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}
def Dom (X : Obj k r) (φ : M X → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W' ∈ Ws, LieWd k r W') ∧
    ∀ x, φ x ≤ C * (Ws.map fun W' => sn X W' x).sum
end GlobalTheory.CompanionTheory.ZuckHomCat
end


