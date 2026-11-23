-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
-- name    : ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:33:35.104291+00:00
-- url     : https://prove2.me/theorems/3839af80-bb0f-4221-880c-389a4b09eaf5
-- title:
--   Exists Reduction Of Coordinate Combination
-- statement:
--   Definitions and structural lemmas for Exists Reduction Of Coordinate Combination, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/ExistsReductionOfCoordinateCombination.lean

import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
section Lift
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
def nbAct (H : HodgeTateDatum p g v R O σ cp) (a : O) (y : Nb p g) : Nb p g :=
  (H.ρ a).map PadicInt.toZMod *ᵥ y
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)
end Lift
end ReciprocityTheory.PGsh.Up


