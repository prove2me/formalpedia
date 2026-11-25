-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SabBaseChangeStIffFree
-- name    : Development_AbelianVarietyTheory_Proofs_JetHarmonics_SabBaseChangeStIffFree
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:04:20.699689+00:00
-- url     : https://prove2.me/theorems/150d9326-5a4e-4ea6-b6e3-14eff20bb7ff
-- title:
--   Sab Base Change St Iff Free
-- statement:
--   Definitions and structural lemmas for Sab Base Change St Iff Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SabBaseChangeStIffFree.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PullbackGroupAction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsRigidifiedIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSymmetricIffExistsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PullbackGroupAction
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.SabPullCompare
variable {S S' : Scheme.{0}}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def FreeConcl (t : SAB H S) (f : S' ⟶ S) (PP' : RigLB ((Over.pullback f).obj t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
    (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
    (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
      (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
    (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L)),
    Nonempty (SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f)
def PinnedConcl (t : SAB H S) (f : S' ⟶ S) (PP' : RigLB ((Over.pullback f).obj t.G)) : Prop :=
  ∃ (semi : IsSemiAbelian ((Over.pullback f).obj t.G)) (act : OAct (𝓞 E) ((Over.pullback f).obj t.G))
    (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric)
    (adj : ∀ a, LBIso (cubeLB _ ![fst _ _ ≫ act.act a, snd _ _] PP'.L)
      (cubeLB _ ![fst _ _, snd _ _ ≫ act.act (H.bar a)] PP'.L))
    (prim : LBIso PP'.L (cubeLB _ ![𝟙 _, act.act H.w0] PP'.L))
    (m : SABMap ⟨(Over.pullback f).obj t.G, semi, act, PP', cub, sym, adj, prim⟩ t f),
    m.φ = pullback.fst t.G.hom f
end GlobalTheory.SabPullCompare


