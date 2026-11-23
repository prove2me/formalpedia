-- Prove2me | Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
-- name    : Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:10.544752+00:00
-- url     : https://prove2.me/theorems/23182132-b5c2-445b-83c3-45c3d5a6423f
-- title:
--   Comps Of Mem Map
-- statement:
--   Definitions and structural lemmas for Comps Of Mem Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/CompsOfMemMap.lean

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LIFT
open Finset
section XH
variable {ℓ : ℕ} {A : Type} [CommRing A] (φA : A →+* A) (ε : A) (aa : Ideal A)
def Comps (ℓ : ℕ) (x : A) : Prop :=
  ∃ e : Fin ℓ → A, (∀ i, e i ∈ aa) ∧ x = ∑ i : Fin ℓ, ε ^ (i : ℕ) * φA (e i)
end XH
end Formalism.LIFT


