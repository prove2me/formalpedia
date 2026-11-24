-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBasisIsoFree
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBasisIsoFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:38:06.626812+00:00
-- url     : https://prove2.me/theorems/98eb2fa9-b880-474d-b711-effb93b628a9
-- title:
--   PBasis Iso Free
-- statement:
--   Definitions and structural lemmas for PBasis Iso Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PBasisIsoFree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
variable {Y : Scheme.{u}}
def globalSectionFamily (M : Y.Modules) (t : Γ(M, ⊤)) : M.sections :=
  PresheafOfModules.sectionsMk
    (fun V => (M.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op).hom t)
    (fun V W f => by
      change (M.presheaf.map f).hom ((M.presheaf.map _).hom t) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)
def basisHom (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤)) : freeModule Y n ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm (fun i => globalSectionFamily M (s i.down))
end
end GroundTheory.Heights₂.Heights.Model


