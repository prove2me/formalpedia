-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PFreeSheafBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:25.054335+00:00
-- url     : https://prove2.me/theorems/1d00b97f-fc08-4be4-a9a5-457db4acce56
-- title:
--   PFree Sheaf Basis
-- statement:
--   Definitions and structural lemmas for PFree Sheaf Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PFreeSheafBasis.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
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
namespace FreeSheafBasis
section Coproduct
variable {C : Type*} [Category C] [Preadditive C] (A : C) (n : ℕ)
  [HasCoproduct (fun _ : ULift.{u} (Fin n) => A)]
def projC (j : Fin n) : ∐ (fun _ : ULift.{u} (Fin n) => A) ⟶ A :=
  Sigma.desc (fun i : ULift.{u} (Fin n) => if i.down = j then 𝟙 A else 0)
end Coproduct
variable (Y : Scheme.{u}) (n : ℕ)
def incl (i : Fin n) : structureModule Y ⟶ freeModule Y n :=
  SheafOfModules.ιFree (R := Y.ringCatSheaf) (ULift.up i)
def proj (j : Fin n) : freeModule Y n ⟶ structureModule Y :=
  projC (C := SheafOfModules.{u} Y.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf) n j
variable {Y} in

def evalHom {M N : Y.Modules} (V : Y.Opens) (x : Γ(M, V)) : (M ⟶ N) →+ Γ(N, V) where
  toFun φ := (φ.app V).hom x
  map_zero' := rfl
  map_add' _ _ := rfl
variable {Y n}
end FreeSheafBasis
end
end GroundTheory.Heights₂.Heights.Model


