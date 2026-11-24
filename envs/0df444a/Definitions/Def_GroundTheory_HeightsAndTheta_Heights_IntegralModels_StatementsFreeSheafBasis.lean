-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:43.579596+00:00
-- url     : https://prove2.me/theorems/abe4e91c-f660-4241-b8da-23d987f6d2fc
-- title:
--   Statements Free Sheaf Basis
-- statement:
--   Definitions and structural lemmas for Statements Free Sheaf Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsFreeSheafBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
abbrev freeModule (Y : Scheme.{u}) (n : ℕ) : Y.Modules :=
  SheafOfModules.free (R := Y.ringCatSheaf) (ULift.{u} (Fin n))
def stdSection (Y : Scheme.{u}) (n : ℕ) (i : Fin n) : Γ(freeModule Y n, ⊤) :=
  (Scheme.Modules.Hom.app (M := structureModule Y)
    (SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i)) ⊤).hom (1 : Γ(Y, ⊤))
def FreeSheafBasis.Statement : Prop :=
  ∀ (Y : Scheme.{u}) (n : ℕ), IsBasisOn (freeModule Y n) ⊤ (stdSection Y n)
end
end GroundTheory.Heights₂.Heights.Model


