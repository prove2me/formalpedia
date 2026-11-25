-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_GeoSys
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianPullbackLattices_GeoSys
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:47.586417+00:00
-- url     : https://prove2.me/theorems/647daa58-305e-48a0-9005-01fd029adc9a
-- title:
--   Geo Sys
-- statement:
--   Definitions and structural lemmas for Geo Sys, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/AbelianDeRham/AbelianPullbackLattices/GeoSys.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_FinSys
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianSchemeCharts_IsOpenImmersionProdChart
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory
namespace MainStatements.Hodge.Pf.AXO
variable {R : Type} [CommRing R]
def Sq (P : Type) : Type := P × P
instance (P : Type) [SemilatticeInf P] : SemilatticeInf (Sq P) := inferInstanceAs (SemilatticeInf (P × P))
instance (P : Type) [Finite P] : Finite (Sq P) := inferInstanceAs (Finite (P × P))
def prodSys (A : Over (Sp R)) {P : Type} [SemilatticeInf P] (S : Sys A.left P) : Sys (A ⊗ A).left (Sq P) where
  u ab := MainStatements.Hodge.Sh.prodAff A A (S.u (Prod.fst ab)) (S.u (Prod.snd ab))
  map_inf ab cd := by
    change MainStatements.Hodge.Sh.prodW A A (S.u (ab.1 ⊓ cd.1)).1 (S.u (ab.2 ⊓ cd.2)).1 =
      MainStatements.Hodge.Sh.prodW A A (S.u ab.1).1 (S.u ab.2).1 ⊓ MainStatements.Hodge.Sh.prodW A A (S.u cd.1).1 (S.u cd.2).1
    simp only [MainStatements.Hodge.Sh.prodW, S.map_inf, Scheme.Hom.preimage_inf]
    ac_rfl
  cover := by
    change ⨆ ab : P × P, MainStatements.Hodge.Sh.prodW A A (S.u ab.1).1 (S.u ab.2).1 = ⊤
    simp only [MainStatements.Hodge.Sh.prodW]
    rw [← iSup_inf_iSup (f := fun a ↦ (fst A A).left ⁻¹ᵁ (S.u a).1) (g := fun b ↦ (snd A A).left ⁻¹ᵁ (S.u b).1)]
    rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, S.cover]
    simp
end MainStatements.Hodge.Pf.AXO


