-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_UniformizationPowerGroup
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T14:09:09.025087+00:00
-- url     : https://prove2.me/theorems/21dd88d9-ca63-504d-b623-7bf682d36049
-- title:
--   Uniformization Power Group
-- statement:
--   Definitions and structural lemmas for Uniformization Power Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/UniformizationPowerGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdExpPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gm_linCombIso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mem_finf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowAlongIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.DVR (bw gm_linCombIso mem_finf)
section Stalk
variable {X X' X'' Y Y' Y₀ Z : Scheme.{0}}
variable {M : LB X} {M' : LB X'} {M'' : LB X''} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
end Stalk
section Square
variable {B B' X X' X'' T T' T'' : Scheme.{0}} {M : LB B} {M' : LB B'} {L : LB X} {L' : LB X'} {L'' : LB X''} {j : ℕ}
  {prB : Fin j → (B' ⟶ B)} {pr : Fin j → (X' ⟶ X)} {p : T ⟶ B} {f : T ⟶ X} {p' : T' ⟶ B'} {f' : T' ⟶ X'}
def Sq (wD : LB.Iso M' (LB.LinComb M prB (fun _ => 1))) (wL : LB.Iso L' (LB.LinComb L pr (fun _ => 1)))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) (ρ : Fin j → (T' ⟶ T)) : Prop :=
  ∀ (jNM : Fin j → M.ι) (jM' : M'.ι) (jL' : L'.ι) (jNL : Fin j → L.ι),
    res (X := T') (inf_le_left.trans (inf_le_left.trans inf_le_left) :
        p' ⁻¹ᵁ (LB.div (LB.LinComb M prB (fun _ => 1)) M').U (jNM, jM') ⊓
          (LB.div (M'.pull p') (L'.pull f')).U (fun _ => jM', fun _ => jL') ⊓
          (⨅ i, ρ i ⁻¹ᵁ (LB.div (M.pull p) (L.pull f)).U (fun _ => jNM i, fun _ => jNL i)) ⊓
          f' ⁻¹ᵁ (LB.div (LB.LinComb L pr (fun _ => 1)) L').U (jNL, jL') ≤
        p' ⁻¹ᵁ (LB.div (LB.LinComb M prB (fun _ => 1)) M').U (jNM, jM'))
      (pullU p' _ (wD.s (jNM, jM'))) *
    res (X := T') (inf_le_left.trans (inf_le_left.trans inf_le_right)) (w'.s (fun _ => jM', fun _ => jL')) =
    (∏ i, res (X := T') (inf_le_left.trans (inf_le_right.trans (iInf_le _ i)))
      (pullU (ρ i) _ (w.s (fun _ => jNM i, fun _ => jNL i)))) *
    res (X := T') inf_le_right (pullU f' _ (wL.s (jNL, jL')))
end Square
end GlobalTheory.PowAlongIso


