-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassLinesProj
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassLinesProj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:01.829494+00:00
-- url     : https://prove2.me/theorems/32d21ae4-b9cc-4e41-a611-5bff07fd2abf
-- title:
--   Statements Grass Lines Proj
-- statement:
--   Definitions and structural lemmas for Statements Grass Lines Proj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassLinesProj.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def GrassLinesProj.Statement : Prop :=
  ∀ (m : ℕ) (II : IntersectionSystem), IsIntersectionSystem II →
    II (Fin 1) (plBlocks 1 1 m) (grassIdeal 1 1 m) (1 * 1 * m + 1) (fun _ => fsMulti (plBlocks 1 1 m)) =
      II Unit (PBlk (m + 1)) ⊥ (m + 1) (fun _ => fsMulti (PBlk (m + 1)))
example (m : ℕ) : Fintype.card (PlIdx 1 m) = m + 1 := by
  rw [Fintype.card_subtype, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin, Nat.choose_one_right, add_comm]
example : (Ideal (MRing (plBlocks 1 1 1)) × HermLine (plBlocks 1 1 1)) ×
    (Ideal (MRing (PBlk 2)) × HermLine (PBlk 2)) :=
  ⟨⟨grassIdeal 1 1 1, fsMulti (plBlocks 1 1 1)⟩, ⟨⊥, fsMulti (PBlk 2)⟩⟩
end
end GroundTheory.Heights₂.Heights


