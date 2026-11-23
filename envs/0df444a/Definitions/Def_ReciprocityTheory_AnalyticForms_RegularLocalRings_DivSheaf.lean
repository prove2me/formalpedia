-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:40.360802+00:00
-- url     : https://prove2.me/theorems/599f2c74-c8d1-4e5b-9266-036386b54529
-- title:
--   Div Sheaf
-- statement:
--   Definitions and structural lemmas for Div Sheaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
section LocGen
variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}
end LocGen
end
end ReciprocityTheory.AnForm.R


