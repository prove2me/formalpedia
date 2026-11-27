-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsValueAtJetPointCmFrameSection
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-27T04:43:33.334594+00:00
-- url     : https://prove2.me/theorems/9d158ba8-2b4d-4628-87b8-59c1fdb3e137
-- title:
--   Is Value At Jet Point Cm Frame Section
-- statement:
--   Definitions and structural lemmas for Is Value At Jet Point Cm Frame Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsValueAtJetPointCmFrameSection.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_over

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
namespace GlobalTheory.JetVal
open AlgebraicGeometry CategoryTheory Opposite Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
section Pt
variable {K : Type} [Field K] {σ : Type} {m : ℕ}
end Pt
section PullSec
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (a : ℤ) {T T' : Over S} (h : T' ⊗ A ⟶ T ⊗ A)
  (hh : h ≫ snd T A = snd T' A)
def pullSecF (s : LB.Sec (LPow A L a T)) (j : Fin 1 → L.ι) : Γ((T' ⊗ A).left, (LPow A L a T').U j) :=
  ((T' ⊗ A).left.presheaf.map (homOfLE (chart_le_res A L h hh a j)).op).hom ((h.left.app _).hom (s.f j))
def pullSecLP (s : LB.Sec (LPow A L a T)) : LB.Sec (LPow A L a T') where
  f := pullSecF A L a h hh s
  compat i j := fn_ext fun y hy => by
    have hi : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) i := chart_le_res A L h hh a i hy.1
    have hj : (𝟙 _ ≫ h.left) y ∈ LB.wchart L (fun _ : Fin 1 => (snd T A).left) j := chart_le_res A L h hh a j hy.2
    have v : ∀ j', y ∈ (LPow A L a T').U j' → gs (𝟙 _) y _ (pullSecF A L a h hh s j') =
        gs (𝟙 _ ≫ h.left) y (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j') (s.f j') := fun j' hj' =>
      (gs_res _ y _ hj' _).trans (gs_pull _ h.left y _ (chart_le_res A L h hh a j' hj') _)
    refine ((gs_res (𝟙 _) y _ hy _).trans ((v i hy.1).trans (sec_trans s (𝟙 _ ≫ h.left) y hi hj))).trans ?_
    refine Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm
    refine congrArg₂ (· * ·) ?_ ((v j hy.2).symm.trans (gs_res (𝟙 _) y _ hy _).symm)
    refine Eq.trans ?_ (gs_unit (𝟙 _) y _ hy _).symm
    refine congrArg Units.val (Eq.trans ?_
      (gm_linComb L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) (𝟙 _) y i j hy.1 hy.2).symm)
    simp only [trF, Category.assoc, ← Over.comp_left, hh]
end PullSec
section Fam
variable {X : Scheme.{0}} {G : Over X} [GrpObj G] (L : LB G.left) {x0 : Sp ℂ ⟶ X} {g : ℕ}
variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ G.left)) (hol : IsHolFam e) (he : ∀ z, e z ≫ G.hom = x0)
def jB (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ Over.mk x0 :=
  Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m))) rfl
def xJ (m : ℕ) : overAt x0 (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt e hol m) (jetPt_over e hol G.hom x0 he m)
def ePt (z : Fin g → ℂ) : Over.mk x0 ⟶ G := Over.homMk (e z) (he z)
def lftJ (z : Fin g → ℂ) : Sp ℂ ⟶ (Over.mk x0 ⊗ G).left := (ptSecT G (ePt e he z)).left
end Fam
def onePr (g : ℕ) : (Fin (1 * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (1 * g) => ℂ)
    (finProdFinEquiv ((0 : Fin 1), j))
end GlobalTheory.JetVal


