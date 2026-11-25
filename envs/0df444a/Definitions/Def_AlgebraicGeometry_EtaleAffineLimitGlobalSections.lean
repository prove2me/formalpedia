-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAffineLimitGlobalSections
-- name    : AlgebraicGeometry_EtaleAffineLimitGlobalSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T05:51:26.006953+00:00
-- url     : https://prove2.me/theorems/7c78c37f-1364-5dfd-85a4-f2e436481740
-- title:
--   Global sections and canonical stage maps on an affine inverse limit
-- statement:
--   Sections of the limit sheaf form the filtered colimit of the stage sections. The colimit injection is evaluation of the canonical coefficient map followed by the identification of global sections for direct image.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitCoefficientMaps

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleBaseChangeComparison (baseChange)
namespace PhilipponEtaleAcyclicCohomology
universe u
private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- The identity chart is terminal in the small étale site. -/
def isTerminal (X : Scheme.{u}) : IsTerminal (terminal X) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

/-- The base change of the terminal chart is the terminal chart. -/
def terminalComparison {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (baseChange f).obj (terminal X) ≅ terminal Y := by
  have : PreservesFiniteLimits (baseChange f) :=
    inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.pullback (@Etale) ⊤ f))
  exact (IsTerminal.isTerminalObj (baseChange f) _ (isTerminal X)).uniqueUpToIso (isTerminal Y)

end PhilipponEtaleAcyclicCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts)
open PhilipponEtaleLimitAffinePresheaf (affineCharts AffineModel)
open PhilipponEtaleLimitRepresentatives (modelFunctor modelLimitSectionsIso)
open PhilipponEtaleLimitFunctor (limitFunctor)
open PhilipponEtaleLimitExactness (atStageSheaf)
open PhilipponEtaleModeledSections (reversedBaseChangeIso)
open PhilipponEtaleAcyclicCohomology (globalSections terminalComparison)


namespace PhilipponEtaleLimitGlobalSections

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)

private def terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def limitTerminal : (affineCharts c.pt).FullSubcategory :=
  ⟨terminal c.pt, Scheme.isAffine_of_isLimit c hc⟩

private def terminalModel : AffineModel c (limitTerminal c hc).obj where
  chart := ⟨i, terminal (D.obj i)⟩
  affine := inferInstanceAs (IsAffine (D.obj i))
  comparison := (terminalComparison (c.π.app i)).symm

/-- The diagram computing global sections on the limit. -/
def sectionsDiagram : System (directImages D) ⥤ (Over i)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  modelFunctor c (limitTerminal c hc) (terminalModel c hc i)

instance : (sectionsDiagram c hc i).PreservesZeroMorphisms :=
  inferInstanceAs ((modelFunctor c (limitTerminal c hc) (terminalModel c hc i)).PreservesZeroMorphisms)

/-- The global sections of the limit sheaf are the colimit of this
diagram, naturally in the system. -/
def colimIso : sectionsDiagram c hc i ⋙ colim ≅ limitFunctor c hc ⋙ globalSections c.pt :=
  modelLimitSectionsIso c (limitTerminal c hc) (terminalModel c hc i) hc

/-- Each term of the diagram is the corresponding stage's global sections. -/
def evalIso (j : (Over i)ᵒᵖ) :
    sectionsDiagram c hc i ⋙ (evaluation _ _).obj j ≅
      atStageSheaf j.unop.left ⋙ globalSections (D.obj j.unop.left) := by
  let A : StageChart D := ⟨i, terminal (D.obj i)⟩
  let B := (stageCharts A).obj j.unop
  let r := D.map j.unop.hom
  let e : B.etale ≅ terminal (D.obj j.unop.left) :=
    (reversedBaseChangeIso r).app A.etale ≪≫ terminalComparison r
  refine NatIso.ofComponents (fun F => (F.obj j.unop.left).obj.mapIso e.symm.op) ?_
  intro F G f
  exact ((f.app j.unop.left).hom.naturality e.symm.op.hom).symm

end PhilipponEtaleLimitGlobalSections

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponCompatibleInjectiveSystems (System)
open PhilipponEtaleDirectImageSystem (directImages)
open PhilipponEtaleTotalStageSite (StageChart atStage toLimit)
open PhilipponEtaleChartLimitDiagram (stageCharts)
open PhilipponEtaleSystemPresheaf (presheaf map_atStage)
open PhilipponEtaleLimitAffinePresheaf (affineCharts AffineModel affineColimit)
open PhilipponEtaleLimitRepresentatives (modelIndices modelCocone modelCoconeIsColimit)
open PhilipponEtaleLimitGlobalSections (sectionsDiagram evalIso colimIso)
open PhilipponEtaleLimitSheaf (limitSheaf restrictionIso)
open PhilipponEtaleLimitCanonical (naturalMap naturalMap_affine fromStage)
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso terminalComparison isTerminal)
open PhilipponEtaleModeledSections (reversedBaseChangeIso)


namespace PhilipponEtaleLimitSectionProjections

universe u

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} [IsCofiltered I]
  [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)
  (F : System (directImages D))

private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

private def terminalChart : (affineCharts c.pt).FullSubcategory :=
  ⟨terminal c.pt, Scheme.isAffine_of_isLimit c hc⟩

private def terminalModel : AffineModel c (terminalChart c hc).obj where
  chart := ⟨i, terminal (D.obj i)⟩
  affine := inferInstanceAs (IsAffine (D.obj i))
  comparison := (terminalComparison (c.π.app i)).symm

/-- The map on global sections induced by a stage projection and its
coefficient map. -/
def stageSections (j : I) : (globalSections (D.obj j)).obj (F.obj j) ⟶
    (globalSections c.pt).obj (limitSheaf c hc F) :=
  (globalSections (D.obj j)).map (fromStage c hc F j) ≫
    (globalSectionsIso (c.π.app j)).hom.app (limitSheaf c hc F)

/-- Under the section colimit formula, the colimit injections are the
global-section maps of the corresponding stage projections. -/
theorem ι_colimIso (j : (Over i)ᵒᵖ) :
    colimit.ι ((sectionsDiagram c hc i).obj F) j ≫ ((colimIso c hc i).app F).hom =
      ((evalIso c hc i j).app F).hom ≫ stageSections c hc F j.unop.left := by
  let T := terminalChart c hc
  let M := terminalModel c hc i
  let k := (modelIndices c T M).obj j
  let E := (sectionsDiagram c hc i).obj F
  let P := limitSheaf c hc F
  let Q := presheaf F
  let d := modelCocone c T M hc F
  let e := (colimit.isColimit E).coconePointUniqueUpToIso (modelCoconeIsColimit c T M hc F)
  let v := (restrictionIso c hc F).inv.hom.app (op T)
  let τ := (reversedBaseChangeIso (D.map j.unop.hom)).app (terminal (D.obj i)) ≪≫
    terminalComparison (D.map j.unop.hom)
  let V : StageChart D := ⟨j.unop.left, terminal (D.obj j.unop.left)⟩
  let φ : V ⟶ k.left.unop := (atStage (D := D) j.unop.left).map τ.inv
  let p := c.π.app j.unop.left
  let t := (terminalComparison p).inv
  have hk : k.hom.unop = t ≫ (toLimit c).map φ := by
    let hT := (isTerminal c.pt).ofIso (terminalComparison p).symm
    let e' := (atStage (D := D) j.unop.left ⋙ toLimit c).mapIso τ.symm
    exact (hT.ofIso e').hom_ext _ _
  change colimit.ι E j ≫ e.hom ≫ v =
    (F.obj j.unop.left).obj.map τ.inv.op ≫ (naturalMap c hc F).app (op V) ≫ P.obj.map t.op
  have hι : colimit.ι E j ≫ e.hom = d.ι.app j := (colimit.isColimit E).fac d j
  have hφ : Q.map φ.op = (F.obj j.unop.left).obj.map τ.inv.op :=
    map_atStage F τ.inv
  rw [← Category.assoc, hι]
  change (affineColimit c hc F T).cocone.ι.app k ≫ v = _
  rw [← naturalMap_affine c hc F T k]
  have h : k.hom = ((toLimit c).map φ).op ≫ t.op := Quiver.Hom.unop_inj <|
    hk.trans unop_comp.symm
  have hn : Q.map φ.op ≫ (naturalMap c hc F).app (op V) =
      (naturalMap c hc F).app k.left ≫ P.obj.map ((toLimit c).map φ).op :=
    (naturalMap c hc F).naturality φ.op
  rw [h, P.obj.map_comp, ← Category.assoc, ← hn, hφ, Category.assoc]

end PhilipponEtaleLimitSectionProjections

end

end


