-- Prove2me | Definitions.Def_TunnellMap_ResidualTargetTest
-- name    : TunnellMap_ResidualTargetTest
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:44:25.914583+00:00
-- url     : https://prove2.me/theorems/5b0a2ba5-ef5f-4c59-bf75-e1e56ac9f6d8
-- title:
--   Residual Target Test
-- statement:
--   Definitions and structural lemmas for Residual Target Test, from Aakash Gurung (GrgAakash/tunnell-two-to-one-map; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Two-to-one executable map between Tunnell representation sets development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean

import Definitions.Def_TunnellMap_OrbitRanking
set_option autoImplicit true
namespace TunnellMap
def ImageUsedTriple (w : Triple) : Prop :=
  (w.x + 4 * w.z - w.y) % 8 = 4 ∨ (w.x - 4 * w.z + w.y) % 8 = 4 ∨ w.x % 4 = 2
instance imageUsedTripleDecidable (w : Triple) : Decidable (ImageUsedTriple w) := by
  unfold ImageUsedTriple
  infer_instance
def IsResidualTargetLift (n : ℤ) (v : Triple) : Prop :=
  (4 : ℤ) ∣ v.z ∧ aForm ⟨v.x, v.y, v.z / 4⟩ = n ∧
    ¬ ImageUsedTriple ⟨v.x, v.y, v.z / 4⟩
instance isResidualTargetLiftDecidable (n : ℤ) (v : Triple) :
    Decidable (IsResidualTargetLift n v) := by
  unfold IsResidualTargetLift
  infer_instance
def tripleLexLtExec (u w : Triple) : Bool :=
  u.x < w.x || (u.x == w.x && (u.y < w.y || (u.y == w.y && u.z < w.z)))
def canonicalTargetLift (v : Triple) : Triple :=
  if tripleLexLtExec v (negTriple v) then v else negTriple v
def targetLiftSign (v : Triple) : ℤ :=
  if tripleLexLtExec v (negTriple v) then 1 else -1
end TunnellMap


