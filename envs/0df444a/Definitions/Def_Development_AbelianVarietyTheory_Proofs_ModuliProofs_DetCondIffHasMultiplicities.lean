-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetCondIffHasMultiplicities
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:25.566242+00:00
-- url     : https://prove2.me/theorems/f2f4fe5a-0484-4fc7-b203-a7f23b61ff62
-- title:
--   Det Cond Iff Has Multiplicities
-- statement:
--   Definitions and structural lemmas for Det Cond Iff Has Multiplicities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DetCondIffHasMultiplicities.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsTangentModuleUniversalGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_TanMod_smT_zero_of
import Theorems.Thm_GlobalTheory_TanMod_unit_of_smT_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DetCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs GlobalTheory.TanMod GlobalTheory.EigenSplit
section Linear
variable {k N : Type} [Field k] [AddCommGroup N] [Module k N]
end Linear
variable {S : Scheme.{0}} {k : Type} [Field k]
variable {G : Over S} [GrpObj G] {O : Type} [CommRing O]
theorem mem_lie_iff (t : Sp k ⟶ S) (v : epsPt t ⟶ G) :
    v ∈ Lie G t ↔ spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk t ⟶ G).left :=
  ⟨fun h => congrArg (fun φ => φ.left) (show origin t ≫ v = 1 from h), fun h => Over.OverMorphism.ext h⟩
variable [IsCommMonObj G]
def lieEquiv (t : Sp k ⟶ S) : Lie G t ≃ TanSp t G where
  toFun v := TanSp.mk v.1 (smT_zero_of t _ ((mem_lie_iff t _).1 v.2))
  invFun m := ⟨m.pt, (mem_lie_iff t _).2 (unit_of_smT_zero t _ m.tan)⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
end GlobalTheory.DetCompare


