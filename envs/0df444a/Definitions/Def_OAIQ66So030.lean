-- Prove2me | Definitions.Def_OAIQ66So030
-- name    : OAIQ66So030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:47:09.183757+00:00
-- url     : https://prove2.me/theorems/b7100fe4-a4be-4c04-acd4-ca717e9bf50f
-- title:
--   Definitions bundle OAIQ66So030 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 99 declarations of OpenAI's Lean: 45 definitions, 4 instances and 50 theorems. The definitions and types are `OAI.PresentationGeometry.FiniteStage.finalCore`, `OAI.PresentationGeometry.PresentationComplex.initialStage`, `OAI.PresentationGeometry.PresentationComplex.presentationEquiv`, `OAI.PresentationGeometry.PresentationComplex.transportedBasepoint`, `OAI.PresentationGeometry.PresentationComplex.transportedCore`, `OAI.ProductBrown.M`, `OAI.ProductCoefficient.unitIso`, `OAI.ProductCriterion.coordinates`, `OAI.RegularProductR.homologyRelabel`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticDouble.calculus`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticDouble.interpretation`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.calculus`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.columnMap`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.groupKey`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.groupValue`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.interpretation`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.matrixMap`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.pointKey`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.pointValue`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.rootValue`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticMatrix.seven`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.I`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.N`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.N₂`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.Symbols`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.baseC`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.baseI`, `OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.evaluation`, `OAI.SimpleFInftyOvergroups.SourceModel.Acting`, `OAI.SimpleFInftyOvergroups.SourceModel.ActionMon`, `OAI.SimpleFInftyOvergroups.SourceModel.B`, `OAI.SimpleFInftyOvergroups.SourceModel.K`, `OAI.SimpleFInftyOvergroups.SourceModel.KAlphabet`, `OAI.SimpleFInftyOvergroups.SourceModel.KMachine`, `OAI.SimpleFInftyOvergroups.SourceModel.L`, `OAI.SimpleFInftyOvergroups.SourceModel.Points`, `OAI.SimpleFInftyOvergroups.SourceModel.P₂`, `OAI.SimpleFInftyOvergroups.SourceModel.index`, `OAI.SimpleFInftyOvergroups.SourceModel.processor`, `OAI.StageConstruction.Q` and 5 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `FiniteType_CoreDeckLeftQuotientCovering`, `FiniteType_FiniteIndexRegular`, `FiniteType_InducedFree`, `FiniteType_PresentationGeometryFiniteStage`, `FiniteType_PresentationGeometryRose`, `FiniteType_PresentationVanKampenRectanglePaths`, `FiniteType_ProductCriterion`, `FiniteType_StageConstruction`, `FiniteType_SteinbergSixThree`, `FiniteType_TorusAction`, `SimpleOvergroups_SemanticActions`, `SimpleOvergroups_SemanticDouble`, `SimpleOvergroups_SemanticEnlargements`, `SimpleOvergroups_SemanticTests`, `SimpleOvergroups_SourceModel`.
--
--   **Imports.** It imports the bundles `OAIQ66So027`, `OAIQ66So028` and `OAIQ66So029` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ66So032` and `OAIQ66So033`; the statements `OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data` and `OAI.StageGeometry.simple_geometric_overgroup_of_corner_ring_data`; the proofs of `OAI.OrderBrown.vanishing`, `OAI.ProductFiniteResolution.finite_free_resolution_of_products`, `OAI.SimpleFInftyOvergroups.SplittingTorusModel.products`, `OAI.StageGeometry.simple_geometric_overgroup_of_corner_ring_data`, `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` and `OAI.TwistedBrin.Basis.pair_regular_products`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So027
import Definitions.Def_OAIQ66So028
import Definitions.Def_OAIQ66So029

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationVanKampenRectanglePaths
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.PresentationComplex
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

theorem presentedToFundamental_surjective :
    Function.Surjective (presentedToFundamental w) := by
  intro g
  obtain ⟨a,ha⟩ := freeToFundamental_surjective w g
  exact ⟨PresentedGroup.mk (relatorSet w) a,ha⟩

end PresentationGeometry.PresentationComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryRose
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.PresentationComplex
section
open Set DiscreteCoverCharts
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (g : Fin k → Q) (hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1)

theorem monodromyRepresentation_comp :
    (monodromyRepresentation w g hw).comp (freeToFundamental w) =
      (MulAction.toPermHom Q Q).comp (FreeGroup.lift g) := by
  apply FreeGroup.ext_hom
  intro i
  ext q
  simp only [MonoidHom.comp_apply,monodromyRepresentation_generator,
    FreeGroup.lift_apply_of,MulAction.toPermHom_apply]
  rfl

end

section
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))

theorem presentedToFundamental_injective : Function.Injective (presentedToFundamental w) := by
  let Q := PresentedGroup (relatorSet w)
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  let g : Fin k → Q := PresentedGroup.of
  have hg : FreeGroup.lift g = PresentedGroup.mk (relatorSet w) := by
    apply FreeGroup.ext_hom
    intro i
    rw [FreeGroup.lift_apply_of]
    rfl
  have hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (w i)) = 1 := by
    intro i
    rw [hg]
    exact PresentedGroup.one_of_mem ⟨i,rfl⟩
  let m := monodromyRepresentation w g hw
  have hm := monodromyRepresentation_comp w g hw
  rw [hg] at hm
  intro a b hab
  obtain ⟨a,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) a
  obtain ⟨b,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) b
  rw [presentedToFundamental_mk,presentedToFundamental_mk] at hab
  have h := congrArg m hab
  have ha := DFunLike.congr_fun hm a
  have hb := DFunLike.congr_fun hm b
  change m (freeToFundamental w a) = _ at ha
  change m (freeToFundamental w b) = _ at hb
  rw [ha,hb] at h
  have h' := DFunLike.congr_fun h (1 : Q)
  simpa using h'

def presentationEquiv : PresentedGroup (relatorSet w) ≃*
    FundamentalGroup (Space w) (basepoint w) :=
  MulEquiv.ofBijective (presentedToFundamental w)
    ⟨presentedToFundamental_injective w,presentedToFundamental_surjective w⟩

end

open DiscreteCoverCharts

end PresentationGeometry.PresentationComplex

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_CoreDeckLeftQuotientCovering
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PresentationGeometry.FiniteStage
attribute [-instance] AddCommGroup.toIntModule
open Set Topology Metric _root_.CategoryTheory CategoryTheory.Limits Cells CWExtension CellCoverExtension
open HurewiczConstruction

attribute [instance] Stage.topology Stage.t2 Stage.compact Stage.cw Stage.finite Stage.simply

attribute [instance] AddCommGroup.toIntModule
end PresentationGeometry.FiniteStage

namespace PresentationGeometry.PresentationComplex
open DiscreteCoverCharts
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable {k r : ℕ} (w : Fin r → List (Fin k × Bool))
variable (eQ : Q ≃* PresentedGroup (relatorSet w))
def transportedCore := coveringCore w (transportedGenerators w eQ) (transported_relators w eQ)
def transportedBasepoint : (transportedCore w eQ).TotalSpace :=
  point (transportedCore w eQ) (.inl none) (basepoint w) 1
lemma transported_monodromyRepresentation (a : PresentedGroup (relatorSet w)) (q : Q) :
    monodromyRepresentation w (transportedGenerators w eQ) (transported_relators w eQ)
      (presentationEquiv w a) q = eQ.symm a * q := by
  obtain ⟨z,rfl⟩ := PresentedGroup.mk_surjective (relatorSet w) a
  have h := DFunLike.congr_fun
    (monodromyRepresentation_comp w (transportedGenerators w eQ) (transported_relators w eQ)) z
  rw [lift_transportedGenerators] at h
  change monodromyRepresentation w (transportedGenerators w eQ) (transported_relators w eQ)
    (freeToFundamental w z) = _ at h
  change monodromyRepresentation w (transportedGenerators w eQ) (transported_relators w eQ)
    (presentedToFundamental w (PresentedGroup.mk _ z)) q = _
  rw [presentedToFundamental_mk,h]
  rfl
lemma transported_monodromy_bijective : Function.Bijective
    (fun γ : FundamentalGroup (Space w) (basepoint w) =>
      (covering (transportedCore w eQ)).monodromy γ ⟨transportedBasepoint w eQ,rfl⟩) := by
  let e := fiberEquiv (transportedCore w eQ) (.inl none) (basepoint w)
    (basepoint_mem_coveringCore w (transportedGenerators w eQ) (transported_relators w eQ))
  have h (γ : FundamentalGroup (Space w) (basepoint w)) :
      (covering (transportedCore w eQ)).monodromy γ ⟨transportedBasepoint w eQ,rfl⟩ =
        e (eQ.symm ((presentationEquiv w).symm γ)) := by
    have hm := transported_monodromyRepresentation w eQ ((presentationEquiv w).symm γ) 1
    rw [(presentationEquiv w).apply_symm_apply] at hm
    have he := congrArg e (hm.trans (mul_one _))
    exact (e.apply_symm_apply _).symm.trans he
  have heq : (fun γ : FundamentalGroup (Space w) (basepoint w) =>
      (covering (transportedCore w eQ)).monodromy γ ⟨transportedBasepoint w eQ,rfl⟩) =
      e ∘ eQ.symm ∘ (presentationEquiv w).symm := funext h
  rw [heq]
  exact e.bijective.comp (eQ.symm.bijective.comp (presentationEquiv w).symm.bijective)
instance transported_simplyConnected : SimplyConnectedSpace (transportedCore w eQ).TotalSpace :=
  RegularCoverGeometry.simplyConnected_of_monodromy_bijective
    (covering (transportedCore w eQ)) (transportedBasepoint w eQ) (transported_monodromy_bijective w eQ)
noncomputable def initialStage : FiniteStage.Stage Q 0 where
  X := Space w
  topology := inferInstance
  t2 := inferInstance
  compact := inferInstance
  cw := inferInstance
  finite := inferInstance
  point := basepoint w
  dimension := dimension w
  I := Option (Fin k) ⊕ Fin r
  core := transportedCore w eQ
  pot := CellCoverExtension.potential (AttachingLoops.relators w) (Rose.basepoint k)
    (Rose.coveringCore (transportedGenerators w eQ)) (Rose.potential (transportedGenerators w eQ))
    (AttachingLoops.relatorSection w (transportedGenerators w eQ) (transported_relators w eQ))
  coord := fun _ _ _ _ => rfl
  simply := inferInstance
  connectivity := by
    intro p hp z
    interval_cases p
    · exact HurewiczConstruction.homotopy_zero z
    · exact HurewiczConstruction.homotopy_one z
end PresentationGeometry.PresentationComplex
namespace PresentationGeometry.FiniteStage

open Set Topology Metric
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, CategoryTheory.Limits.IsZero
  (groupHomology (RegularProductR.rep ℤ Q I) m))

lemma stage_pot (i j : ℕ) (h : i ≤ j) (a : stageI S₀ hzero i) (x : stageX S₀ hzero i) :
    (stages S₀ hzero j).pot (stageIndex S₀ hzero i j h a) (stageMap S₀ hzero i j h x) =
      (stages S₀ hzero i).pot a x := by
  induction j,h using Nat.le_induction with
  | base => simp only [DirectedSystem.map_self']
  | succ j h ih =>
    rw [stageMap_succ S₀ hzero i j h,stageIndex_succ S₀ hzero i j h]
    exact (step_pot _ (attachments S₀ hzero j) _ _).trans ih
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_PresentationGeometryFiniteStage
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PresentationGeometry.FiniteStage
open Set Topology _root_.CategoryTheory CategoryTheory.Limits
variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
variable (S₀ : Stage Q 0)
variable (hzero : ∀ I : Type, ∀ m ≥ 2, IsZero (groupHomology (RegularProductR.rep ℤ Q I) m))
noncomputable def finalCore :=
  SequentialCoreTower.core (stageX S₀ hzero) (stageMap S₀ hzero)
    (stageI S₀ hzero) (stageIndex S₀ hzero) (fun n => (stages S₀ hzero n).core)
    (fun n => (stages S₀ hzero n).pot) (stage_base S₀ hzero) (stage_pot S₀ hzero)
    (fun n => (stages S₀ hzero n).coord)
end PresentationGeometry.FiniteStage

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_FiniteIndexRegular
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RegularProductR
open _root_.CategoryTheory _root_.OAI.CategoryTheory
variable {G H : Type} [Group G] [Group H] (e : G ≃* H) (I : Type)

lemma relabel_comm (g : G) :
    (relabel e I).toLinearMap.comp ((rep ℤ G I).ρ g) =
      ((rep ℤ H I).ρ (e g)).comp (relabel e I).toLinearMap := by
  apply LinearMap.ext
  intro a
  funext i
  have h : (Finsupp.domLCongr (R := ℤ) (M := ℤ) e.toEquiv).toLinearMap.comp
      (rightShift ℤ G g) = (rightShift ℤ H (e g)).comp
        (Finsupp.domLCongr (R := ℤ) e.toEquiv).toLinearMap := by
    apply Finsupp.lhom_ext
    intro x z
    simp
  exact LinearMap.congr_fun h (a i)

noncomputable def homologyRelabel (n : ℕ) :
    groupHomology (rep ℤ G I) n ≅ groupHomology (rep ℤ H I) n :=
  groupHomology.mapIso e (relabel e I) (relabel_comm e I) n

end RegularProductR

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_InducedFree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction _root_.OAI.groupHomology.chainsFunctor_additive _root_.OAI.groupHomology.functor_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation

namespace OrbitModule
open scoped MonoidalCategory
attribute [instance] Presentation.finiteα Presentation.finiteβ Presentation.epi

end OrbitModule

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCoefficient
variable (G I : Type) [Group G]
lemma unitEquiv_comm (g : G) :
    (unitEquiv G I).toLinearMap.comp ((rep G I PUnit.{1}).ρ g) =
      ((RegularProductR.rep ℤ G I).ρ g).comp (unitEquiv G I).toLinearMap := by
  apply LinearMap.ext
  intro a
  funext i
  have h : (Finsupp.domLCongr (R := ℤ) (M := ℤ) (Equiv.punitProd G)).toLinearMap.comp
      (rightShift G PUnit.{1} g) = (RegularProductR.rightShift ℤ G g).comp
        (Finsupp.domLCongr (Equiv.punitProd G)).toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨c,x⟩ z
    simp
  exact LinearMap.congr_fun h (a i)
def unitIso : rep G I PUnit.{1} ≅ RegularProductR.rep ℤ G I :=
  Rep.mkIso (Representation.Equiv.mk (unitEquiv G I) (unitEquiv_comm G I))
end ProductCoefficient

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_SteinbergSixThree
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement

namespace Steinberg
variable {R : Type*} [Ring R]

@[simp] lemma descended_pi (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)
    (w : Group (Fin 6) R) : descended φ D (pi w)=map φ w := by
  simp [descended]

end Steinberg

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_StageConstruction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
open scoped commutatorElement
namespace StageConstruction
variable {R : Type*} [Ring R]
abbrev Q (R : Type*) [Ring R] := NoncommElementary.elementary (n:=Seven) (R:=R)

def action : Q R →* Equiv.Perm (X R) :=
  NoncommElementary.columnAction.comp NoncommElementary.elementary.subtype

@[simp] lemma action_apply (q : Q R) (x : X R) : action q x=q.val.val.mulVec x := rfl

variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

def transitionUnits : Rˣ →* Q R :=
  (NoncommElementary.compressed φ D first second first_ne_second).comp
    (NonunitalCompression.units φ)

lemma transitionUnits_val (v : Rˣ) :
    (transitionUnits φ D v).val=
      NoncommElementary.position first (NonunitalCompression.units (φ.comp φ) v) := by
  simp only [transitionUnits,MonoidHom.comp_apply,NoncommElementary.compressed_coe,
    Steinberg.units_comp]

variable {ι : Type*}

def fixing (z : ι → X R) : Subgroup (Q R) where
  carrier := {q | ∀ i, action q (z i)=z i}
  one_mem' i := by rw [map_one]; rfl
  mul_mem' ha hb i := by rw [map_mul,Equiv.Perm.mul_apply,hb i,ha i]
  inv_mem' {q} h i := by
    apply (action q).injective
    rw [map_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply,h i]

end StageConstruction

namespace StageConstruction
variable {R : Type*} [Ring R]
variable (φ : R →ₙ+* R) (D : CompressedSplittings.BinaryData φ)

lemma transitionUnits_fixes (v : Rˣ) (a : R) (ha : v.val*a=a) :
    action (transitionUnits φ D v) (Pi.single first (φ (φ a)))=
      Pi.single first (φ (φ a)) := by
  rw [action_apply,transitionUnits_val,NoncommElementary.position_mulVec]
  congr 1
  exact (NonunitalCompression.unitValue_mul_image (φ.comp φ) v.val a).trans
    (congrArg (φ.comp φ) ha)

variable {ι : Type*} (c : ι → R) (a : Q R)
abbrev compressedFixing := fixing (fun i => action a (Pi.single first (φ (φ (c i)))))

def stabilizerEnd
    (v : compressedFixing φ c a →* Rˣ)
    (hv : ∀ u i, (v u).val*c i=c i) : compressedFixing φ c a →* compressedFixing φ c a :=
  ((((MulAut.conj a).toMonoidHom).comp (transitionUnits φ D)).comp v).codRestrict _ (by
    intro u i
    change action (a * transitionUnits φ D (v u) * a⁻¹)
      (action a (Pi.single first (φ (φ (c i)))))=
        action a (Pi.single first (φ (φ (c i))))
    simp only [map_mul,map_inv,Equiv.Perm.mul_apply,Equiv.Perm.inv_def]
    rw [Equiv.symm_apply_apply,transitionUnits_fixes φ D (v u) (c i) (hv u i)])

@[simp] lemma stabilizerEnd_val
    (v : compressedFixing φ c a →* Rˣ)
    (hv : ∀ u i, (v u).val*c i=c i) (u : compressedFixing φ c a) :
    (stabilizerEnd φ D c a v hv u).val=a * transitionUnits φ D (v u) * a⁻¹ := rfl

end StageConstruction

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_TorusAction
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Pointwise
section
open scoped commutatorElement

namespace StageConstruction
variable {R : Type*} [Ring R]

instance columnMulAction : MulAction (Q R) (X R) := MulAction.compHom _ action

@[simp] lemma smul_eq_action (q : Q R) (x : X R) : q • x=action q x := rfl

end StageConstruction

end

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductCriterion
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.ProductGroupHomology.action _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
namespace ProductCriterion
variable {k G I : Type} [CommRing k] [Group G]

def coordinates (C : Rep k G) : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants →ₗ[k] (I → C) :=
  LinearMap.pi (fun i => coordinate C i)

end ProductCriterion

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidalCategory
namespace ProductBrown
attribute [-instance] AddCommGroup.toIntModule
variable {G I : Type} [Group G]
abbrev M := RegularProductR.rep ℤ G I

end ProductBrown

open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits

end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticActions
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.AffinePermutation.action _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful _root_.OAI.FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral.instFintypeK'_solutions _root_.OAI.SourceEnlargement.unitsAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames

namespace SemanticMatrix
open StageConstruction MatrixNames

def seven : Fin 7 ≃ Seven := Fintype.equivOfCardEq (by simp [Seven])

variable {k A R : Type*} [CommRing k] [Ring R] [Algebra k R]
    (π : Raw k A →ₐ[k] R)

def matrixMap : Matrix (Fin 7) (Fin 7) (Raw k A) →+* Matrix Seven Seven R :=
  (Matrix.reindexRingEquiv R seven).toRingHom.comp π.toRingHom.mapMatrix

@[simp] theorem matrixMap_apply (a : Matrix (Fin 7) (Fin 7) (Raw k A)) (i j : Seven) :
    matrixMap π a i j = π (a (seven.symm i) (seven.symm j)) := rfl

def columnMap (x : Fin 7 → Raw k A) : Seven → R := fun i => π (x (seven.symm i))

 theorem matrixMap_mulVec (a : Matrix (Fin 7) (Fin 7) (Raw k A)) (x : Fin 7 → Raw k A) :
    (matrixMap π a).mulVec (columnMap π x) = columnMap π (a.mulVec x) := by
  funext i
  simp only [Matrix.mulVec,dotProduct,columnMap,matrixMap_apply,map_sum,map_mul]
  exact Equiv.sum_comp seven.symm (fun j => π (a (seven.symm i) j) * π (x j))

def rootValue (r : MatrixWords.Root k A 7) : Q R :=
  if h : r.1 ≠ r.2.1 then
    ⟨NoncommElementary.root (seven r.1) (seven r.2.1) (seven.injective.ne h) (π (Polynomial.value r.2.2)),
      NoncommElementary.root_mem _ _ _ _⟩
  else 1

def groupValue (w : MatrixWords.Word k A 7) : Q R := (w.map (rootValue π)).prod

def pointValue (x : MatrixWords.Point k A 7) : X R := groupValue π x.1 • columnMap π (columnValue x.2)

@[simp] theorem rootValue_inverse (r : MatrixWords.Root k A 7) :
    rootValue π (MatrixWords.rootInv r) = (rootValue π r)⁻¹ := by
  by_cases h : r.1 ≠ r.2.1
  · apply Subtype.ext
    simp [rootValue,MatrixWords.rootInv,h,NoncommElementary.root_inv]
  · simp [rootValue,MatrixWords.rootInv,h]

@[simp] theorem groupValue_nil : groupValue π [] = 1 := rfl
@[simp] theorem groupValue_append (a b : MatrixWords.Word k A 7) :
    groupValue π (a++b) = groupValue π a * groupValue π b := by simp [groupValue]
@[simp] theorem groupValue_cons (r : MatrixWords.Root k A 7) (w : MatrixWords.Word k A 7) :
    groupValue π (r::w) = rootValue π r * groupValue π w := rfl
@[simp] theorem groupValue_inverse (w : MatrixWords.Word k A 7) :
    groupValue π (MatrixWords.inverse w) = (groupValue π w)⁻¹ := by
  induction w with
  | nil => simp
  | cons r w ih => simp [ih,mul_inv_rev]

@[simp] theorem pointValue_act (w : MatrixWords.Word k A 7) (x : MatrixWords.Point k A 7) :
    pointValue π (w++x.1,x.2) = groupValue π w • pointValue π x := by
  simp only [pointValue,groupValue_append]
  exact mul_smul (groupValue π w) (groupValue π x.1)
    (show X R from columnMap π (columnValue x.2))

 theorem rootValue_matrix (r : MatrixWords.Root k A 7) :
    (rootValue π r).val.val = matrixMap π (MatrixWords.rootValue r).val := by
  by_cases h : r.1 ≠ r.2.1
  · ext i j
    simp only [rootValue,dite_eq_left h,NoncommElementary.root_val,MatrixWords.rootValue,
      FiniteAlgebraicEnvelopes.Steinberg.elementary_val,matrixMap_apply,map_add,
      Matrix.add_apply,Matrix.one_apply,Matrix.single_apply]
    have hi : r.1 = seven.symm i ↔ seven r.1 = i := seven.eq_symm_apply
    have hj : r.2.1 = seven.symm j ↔ seven r.2.1 = j := seven.eq_symm_apply
    simp only [apply_ite,map_one,map_zero,seven.symm.injective.eq_iff,hi,hj]
    split <;> simp_all only
  · simp [rootValue,MatrixWords.rootValue,h]

 theorem groupValue_matrix (w : MatrixWords.Word k A 7) :
    (groupValue π w).val.val = matrixMap π (MatrixWords.groupValue w).val := by
  induction w with
  | nil => simp
  | cons r w ih => simp only [groupValue_cons,MatrixWords.groupValue_cons,Subgroup.coe_mul,
      Units.val_mul,map_mul,rootValue_matrix,ih]

attribute [local instance] WordCalculus.rawMatrixAction
 theorem pointValue_column (x : MatrixWords.Point k A 7) :
    pointValue π x = columnMap π (MatrixWords.pointValue x) := by
  change (groupValue π x.1).val.val.mulVec _ = _
  rw [groupValue_matrix,matrixMap_mulVec]
  rfl

 theorem groupValue_surjective (hπ : Function.Surjective π) : Function.Surjective (groupValue π) := by
  intro g
  have h : ∃ w, (groupValue π w).val = g.val := by
    apply Subgroup.closure_induction (p:=fun g _ => ∃ w, (groupValue π w).val = g) (hx:=g.property)
    · rintro g ⟨i,j,h,a,rfl⟩
      obtain ⟨a,ha⟩ := hπ a
      obtain ⟨p,rfl⟩ := Polynomial.value_surjective a
      refine ⟨[(seven.symm i,seven.symm j,p)],?_⟩
      simp only [groupValue_cons,groupValue_nil,mul_one,rootValue]
      rw [dite_eq_left (seven.symm.injective.ne h)]
      simp [ha]
    · exact ⟨[],rfl⟩
    · rintro a b ha hb ⟨u,rfl⟩ ⟨v,rfl⟩
      exact ⟨u++v,congrArg Subtype.val (groupValue_append π u v)⟩
    · rintro a ha ⟨u,rfl⟩
      exact ⟨MatrixWords.inverse u,congrArg Subtype.val (groupValue_inverse π u)⟩
  obtain ⟨w,hw⟩ := h
  exact ⟨w,Subtype.ext hw⟩

 theorem pointValue_surjective (hπ : Function.Surjective π) : Function.Surjective (pointValue π) := by
  intro x
  have h : ∀ i : Fin 7, ∃ p : Polynomial.Name k A, π (Polynomial.value p) = x (seven i) :=
    fun i => by
      obtain ⟨a,ha⟩ := hπ (x (seven i))
      obtain ⟨p,rfl⟩ := Polynomial.value_surjective a
      exact ⟨p,ha⟩
  choose p hp using h
  refine ⟨([],p),?_⟩
  simp only [pointValue,groupValue_nil]
  refine (one_smul (Q R) (show X R from columnMap π (columnValue p))).trans ?_
  funext i
  exact (hp (seven.symm i)).trans (congrArg x (seven.apply_symm_apply i))

variable [Primcodable A] [Primcodable k] [Finite k]
variable (σ : R → Raw k A) (hσ : Function.Injective σ)

def groupKey (g : Q R) : (Fin 7 → Fin 7 → ℕ) × (Fin 7 → Fin 7 → ℕ) :=
  MatrixWords.pairedKey (fun i j => σ (g.val.val (seven i) (seven j)),
    fun i j => σ (g.val.inv (seven i) (seven j)))

def pointKey (x : X R) : Fin 7 → ℕ := columnKey (fun i => σ (x (seven i)))

omit [Algebra k R] in
 include hσ in
 theorem groupKey_injective [Algebra k R] : Function.Injective (groupKey σ) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  funext i j
  have hh := congrFun (congrFun (congrArg Prod.fst (MatrixWords.pairedKey_injective he)) (seven.symm i)) (seven.symm j)
  exact hσ (by simpa only [seven.apply_symm_apply] using hh)

omit [Ring R] [Algebra k R] [Finite k] in
 include hσ in
 theorem pointKey_injective [Ring R] [Algebra k R] [Finite k] :
    Function.Injective (pointKey σ) := by
  intro x y he
  funext i
  have hh := congrFun (columnKey_injective he) (seven.symm i)
  exact hσ (by simpa only [seven.apply_symm_apply] using hh)

def calculus (m : ℕ) := globalCalculus (groupKey σ) (pointKey σ)
  (groupKey_injective σ hσ) (pointKey_injective σ hσ) m

def interpretation (grade : List A → ℕ) (m : ℕ) :
    NamedAction.Interpretation (MatrixWords.nameOperations (k:=k) (n:=7) grade) (calculus σ hσ m) where
  group w := ⟨groupValue π w,MatrixWords.gcost grade w,Set.mem_univ _⟩
  point x := ⟨pointValue π x,MatrixWords.xcost grade x,Set.mem_univ _⟩
  group_cost _ := rfl
  point_cost _ := rfl
  one := WithBound.ext' (groupValue_nil π) rfl
  mul a b := WithBound.ext' (groupValue_append π a b) (MatrixWords.gcost_append grade a b)
  inv w := WithBound.ext' (groupValue_inverse π w) (MatrixWords.gcost_inverse grade w)
  act g x := WithBound.ext' (pointValue_act π g x)
    (by change MatrixWords.gcost _ (g++x.1) + columnCost _ x.2 =
          MatrixWords.gcost grade g + MatrixWords.xcost grade x
        simp [MatrixWords.gcost_append,MatrixWords.xcost,Nat.add_assoc])

 theorem gkey_eq {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (w : MatrixWords.Word k A 7) :
    (interpretation π σ hσ (MatrixWords.grade C) m).gkey w =
      (MatrixWords.interpretation C).gkey w := by
  change MatrixWords.pairedKey _ = MatrixWords.pairedKey _
  congr 1
  apply Prod.ext
  · funext i j
    change σ ((groupValue π w).val.val (seven i) (seven j)) =
      C.collect k ((MatrixWords.groupValue w).val i j)
    rw [groupValue_matrix, matrixMap_apply]
    simpa only [seven.symm_apply_apply] using hs ((MatrixWords.groupValue w).val i j)
  · funext i j
    change σ (((groupValue π w)⁻¹).val.val (seven i) (seven j)) =
      C.collect k ((MatrixWords.groupValue w).inv i j)
    rw [← groupValue_inverse,groupValue_matrix,matrixMap_apply]
    simpa only [seven.symm_apply_apply,MatrixWords.groupValue_inverse, ← Units.inv_eq_val_inv] using
      hs ((MatrixWords.groupValue w).inv i j)

 theorem xkey_eq {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (x : MatrixWords.Point k A 7) :
    (interpretation π σ hσ (MatrixWords.grade C) m).xkey x =
      (MatrixWords.interpretation C).xkey x := by
  change columnKey _ = columnKey _
  congr 1
  funext i
  change σ (pointValue π x (seven i)) = C.collect k (MatrixWords.pointValue x i)
  rw [pointValue_column]
  simpa only [columnMap,seven.symm_apply_apply] using hs (MatrixWords.pointValue x i)

 theorem partialGroupKey_full {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (f : List A → Part (List A))
    (w : MatrixWords.Word k A 7) {d : ℕ} (hw : MatrixWords.gcost (MatrixWords.grade C) w ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation π σ hσ (MatrixWords.grade C) m).gkey w ∈
      MatrixWords.partialGroupKey C.omega.toList f w := by
  rw [gkey_eq π σ hσ C hs]
  exact MatrixWords.partialGroupKey_full C f w hw hf

 theorem partialPointKey_full {m : ℕ} (C : WordCalculus (FreeMonoid A) m)
    (hs : ∀ a, σ (π a) = C.collect k a) (f : List A → Part (List A))
    (x : MatrixWords.Point k A 7) {d : ℕ} (hx : MatrixWords.xcost (MatrixWords.grade C) x ≤ d)
    (hf : ∀ u, MatrixWords.grade C u ≤ d → (C.normal (FreeMonoid.ofList u)).toList ∈ f u) :
    (interpretation π σ hσ (MatrixWords.grade C) m).xkey x ∈
      MatrixWords.partialPointKey C.omega.toList f x := by
  rw [xkey_eq π σ hσ C hs]
  exact MatrixWords.partialPointKey_full C f x hx hf

end SemanticMatrix
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticEnlargements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement

namespace SemanticEnlargement
variable {G X V Y K L k : Type} [Group V] [MulAction V Y] [Nonempty Y]
  [CommRing k] [Primcodable k] [Primcodable K] [Primcodable L]
  {m : ℕ} (N : Operations G X) (C : ActionCalculus V Y K L m)
  (I : Interpretation N C)

 theorem pointKey_injective (hx : Function.Injective C.point.key) :
    Function.Injective (calculus (k:=k) C).point.key := by
  intro u v h
  exact Finsupp.mapDomain_injective hx (Enlargement.arrayKey_injective h)

omit [Nonempty Y] [Primcodable k] [Primcodable K] [Primcodable L] in
 theorem groupValue_surjective (hg : Function.Surjective (fun g => (I.group g).val)) :
    Function.Surjective (groupValue (k:=k) N C I) := by
  intro w
  have h : ∃ u, (groupValue N C I u).val = w.val := by
    apply Subgroup.closure_induction (p:=fun w _ => ∃ u, (groupValue N C I u).val = w) (hx:=w.property)
    · rintro _ ⟨p,g,rfl⟩
      obtain ⟨a,rfl⟩ := hg g
      exact ⟨[(p,a)],congrArg Subtype.val (groupValue_singleton N C I p a)⟩
    · exact ⟨[],rfl⟩
    · rintro _ _ _ _ ⟨u,rfl⟩ ⟨v,rfl⟩
      exact ⟨u++v,congrArg Subtype.val (groupValue_append N C I u v)⟩
    · rintro _ _ ⟨u,rfl⟩
      exact ⟨Enlargement.inverse N u,congrArg Subtype.val (groupValue_inverse N C I u)⟩
  obtain ⟨u,hu⟩ := h
  exact ⟨u,Subtype.ext hu⟩

variable [Primcodable G] [Primcodable X]
omit [Primcodable G] [Primcodable X] in
 theorem partialGroupKey_full (f : G → Part K) (w : Word (k:=k) (G:=G)) {d : ℕ}
    (hw : Enlargement.gcost N w ≤ d) (hf : ∀ g, N.gcost g ≤ d → I.gkey g ∈ f g) :
    (interpretation N C I).gkey w ∈ Enlargement.partialGroupKey N IdempotentNames.name f w :=
  Enlargement.partialGroupKey_full _ _ _ _ _ _ hw hf

omit [Primcodable G] [Primcodable X] in
 theorem partialPointKey_full (f : X → Part L) (x : Point (k:=k) (G:=G) (X:=X)) {d : ℕ}
    (hx : Enlargement.xcost N x ≤ d) (hf : ∀ y, N.xcost y ≤ d → I.xkey y ∈ f y) :
    (interpretation N C I).xkey x ∈ Enlargement.partialPointKey N IdempotentNames.name f x :=
  Enlargement.partialPointKey_full _ _ _ _ _ _ hx hf

end SemanticEnlargement
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticDouble
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical
namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction SourceEnlargement
namespace SemanticDouble

theorem orbit_step {V Y : Type} [Group V] [MulAction V Y]
    (w : Double.W V) (v : Double.W₁ V) (y : Y) :
    (w * groupEmbedding (ZMod 3) v) • Double.ambientPoint y =
      w • pointEmbedding (ZMod 3) (v • pointEmbedding (ZMod 2) y) := by
  rw [mul_smul]
  exact congrArg (fun x => w • x) (groupEmbedding_pointEmbedding (ZMod 3) v _)

theorem orbit_surjective {V Y U B P : Type} [Group V] [MulAction V Y]
    (f : U → Double.W V) (t : B → Y) (p : P → Double.Y (Q:=V) (X:=Y))
    (b : U → B → P) (hp : ∀ u x, (p (b u x)).val = f u • Double.ambientPoint (t x))
    (hf : Function.Surjective f) (ht : Function.Surjective t) : Function.Surjective p := by
  intro y
  obtain ⟨w,x,h⟩ := y.property
  obtain ⟨u,hu⟩ := hf w
  obtain ⟨a,ha⟩ := ht x
  refine ⟨b u a,Subtype.ext ?_⟩
  exact (hp u a).trans ((congrArg₂ (fun (w : Double.W V) (x : Double.AmbientY Y) => w • x)
      hu (congrArg Double.ambientPoint ha)).trans h)

variable {G X V Y K L : Type} [Group V] [MulAction V Y] [Nonempty Y]
  [Primcodable K] [Primcodable L] {m : ℕ}
  (N : Operations G X) (C : ActionCalculus V Y K L m) (I : Interpretation N C)

 attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticDouble.instPrimcodableZModOfNatNat_solutions
attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticDouble.instPrimcodableZModOfNatNat_solutions_1
theorem point_in_orbit (x : PointName (G:=G) (X:=X)) :
    (I₂ N C I |>.point x).val ∈ Double.orbitSet (Q:=V) (X:=Y) := by
  refine ⟨(I₂ N C I |>.group x.1).val *
    groupEmbedding (ZMod 3) (I₁ N C I |>.group x.2.1).val, (I.point x.2.2).val, ?_⟩
  exact orbit_step _ _ _

def calculus : ActionCalculus (Double.W V) (Double.Y (Q:=V) (X:=Y)) (ℕ × ℕ) ℕ m where
  group := (C₂ C).group
  point :=
    { ball := fun b y => (C₂ C).point.ball b y.val
      mono := fun _ _ h _ hy => (C₂ C).point.mono h hy
      key := fun y => (C₂ C).point.key y.val }
  one_mem := (C₂ C).one_mem
  inv_mem := (C₂ C).inv_mem
  mul_mem := (C₂ C).mul_mem
  smul_mem := (C₂ C).smul_mem
  inv_congr := (C₂ C).inv_congr
  mul_congr := (C₂ C).mul_congr
  smul_congr := (C₂ C).smul_congr

def interpretation : Interpretation (N₂ N) (calculus C) where
  group := (I₂ N C I).group
  point x := ⟨⟨(I₂ N C I |>.point x).val,point_in_orbit N C I x⟩,
    (I₂ N C I |>.point x).cost, (I₂ N C I |>.point x).mem⟩
  group_cost := (I₂ N C I).group_cost
  point_cost := (I₂ N C I).point_cost
  one := (I₂ N C I).one
  mul := (I₂ N C I).mul
  inv := (I₂ N C I).inv
  act g x := WithBound.ext'
    (Subtype.ext (congrArg WithBound.val ((I₂ N C I).act g x)))
    (congrArg (fun t : WithBound (C₂ C).point => t.cost) ((I₂ N C I).act g x))

 theorem groupKey_injective (hg : Function.Injective C.group.key) :
    Function.Injective (calculus C).group.key :=
  SemanticEnlargement.groupKey_injective (C₁ C)
    (SemanticEnlargement.groupKey_injective C hg)

 theorem pointKey_injective (hx : Function.Injective C.point.key) :
    Function.Injective (calculus C).point.key := by
  intro a b h
  apply Subtype.ext
  exact SemanticEnlargement.pointKey_injective (C₁ C)
    (SemanticEnlargement.pointKey_injective C hx) h

 theorem groupValue_surjective (hg : Function.Surjective (fun g => (I.group g).val)) :
    Function.Surjective (fun g => (interpretation N C I |>.group g).val) :=
  SemanticEnlargement.groupValue_surjective (N₁ N) (C₁ C) (I₁ N C I)
    (SemanticEnlargement.groupValue_surjective N C I hg)

 theorem pointValue_base (u : GroupName (G:=G)) (b : X) :
    (I₂ N C I |>.point (u,([],b))).val =
      (I₂ N C I |>.group u).val • Double.ambientPoint (I.point b).val := by
  exact congrArg (fun y => (I₂ N C I |>.group u).val • pointEmbedding (ZMod 3) y)
    (SemanticEnlargement.pointValue_basis (k:=ZMod 2) N C I b)

 theorem pointValue_surjective (hg : Function.Surjective (fun g => (I.group g).val))
    (hx : Function.Surjective (fun x => (I.point x).val)) :
    Function.Surjective (fun x => (interpretation N C I |>.point x).val) :=
  orbit_surjective (fun g => (I₂ N C I |>.group g).val) (fun x => (I.point x).val)
    (fun x => (interpretation N C I |>.point x).val) (fun u b => (u,([],b)))
    (pointValue_base N C I) (groupValue_surjective N C I hg) hx

variable [Primcodable G] [Primcodable X]
omit [Primcodable G] [Primcodable X] in
 theorem partialGroupKey_full (f : G → Part K) (w : GroupName (G:=G)) {d : ℕ}
    (hw : (N₂ N).gcost w ≤ d) (hf : ∀ g, N.gcost g ≤ d → I.gkey g ∈ f g) :
    (interpretation N C I).gkey w ∈
      Enlargement.partialGroupKey (N₁ N) (IdempotentNames.name (k:=ZMod 3))
        (Enlargement.partialGroupKey N (IdempotentNames.name (k:=ZMod 2)) f) w := by
  apply SemanticEnlargement.partialGroupKey_full (N₁ N) (C₁ C) (I₁ N C I) _ w hw
  intro v hv
  exact SemanticEnlargement.partialGroupKey_full N C I f v hv hf

omit [Primcodable G] [Primcodable X] in
 theorem partialPointKey_full (f : X → Part L) (x : PointName (G:=G) (X:=X)) {d : ℕ}
    (hx : (N₂ N).xcost x ≤ d) (hf : ∀ y, N.xcost y ≤ d → I.xkey y ∈ f y) :
    (interpretation N C I).xkey x ∈
      Enlargement.partialPointKey (N₁ N) (IdempotentNames.name (k:=ZMod 3))
        (Enlargement.partialPointKey N (IdempotentNames.name (k:=ZMod 2)) f) x := by
  apply SemanticEnlargement.partialPointKey_full (N₁ N) (C₁ C) (I₁ N C I) _ x hx
  intro y hy
  exact SemanticEnlargement.partialPointKey_full N C I f y hy hf

end SemanticDouble
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SemanticTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
open scoped Classical

namespace SimpleFInftyOvergroups.SemanticEncoding
open BoundedEncoding EffectiveNames NamedAction StageConstruction
namespace SemanticTests

variable {A R : Type} [Primcodable A] [Ring R] [Algebra (ZMod 2) R]
  (π : SemanticMatrix.Raw (ZMod 2) A →ₐ[ZMod 2] R)
  (σ : R → SemanticMatrix.Raw (ZMod 2) A) (hσ : Function.Injective σ)
  {m : ℕ} (C : WordCalculus (FreeMonoid A) m)

abbrev N := MatrixWords.nameOperations (k:=ZMod 2) (n:=7) (MatrixWords.grade C)
attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.instPrimcodableZModOfNatNat_solutions
attribute [local instance] OAI.SimpleFInftyOvergroups.SemanticEncoding.SemanticTests.instPrimcodableZModOfNatNat_solutions_1
abbrev baseC := SemanticMatrix.calculus σ hσ m
abbrev baseI := SemanticMatrix.interpretation π σ hσ (MatrixWords.grade C) m
abbrev I := SemanticDouble.interpretation (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C)
abbrev N₂ := SemanticDouble.N₂ (N C)
abbrev Symbols := Letter (SemanticDouble.GroupName (G:=MatrixWords.Word (ZMod 2) A 7))
  (SemanticDouble.PointName (G:=MatrixWords.Word (ZMod 2) A 7) (X:=MatrixWords.Point (ZMod 2) A 7))

abbrev evaluation : FreeMonoid (Symbols (A:=A)) →* SourceActionMonoid.M
    (SourceEnlargement.Double.W (Q R)) (SourceEnlargement.Double.Y (Q:=Q R) (X:=X R)) :=
  SemanticActionMonoid.wordMap (I π σ hσ C)

 theorem evaluation_surjective (hπ : Function.Surjective π) :
    Function.Surjective (evaluation π σ hσ C) :=
  SemanticActionMonoid.wordMap_surjective (I π σ hσ C)
    (SemanticDouble.groupValue_surjective (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C)
      (SemanticMatrix.groupValue_surjective π hπ))
    (SemanticDouble.pointValue_surjective (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C)
      (SemanticMatrix.groupValue_surjective π hπ) (SemanticMatrix.pointValue_surjective π hπ))

 theorem full (hs : ∀ a, σ (π a) = C.collect (ZMod 2) a)
    (f : List A → Part (List A))
    (hf : ∀ u, (C.normal (FreeMonoid.ofList u)).toList ∈ f u)
    (w : List (Symbols (A:=A))) :
    (N₂ C).totalTest (I π σ hσ C).gkey (I π σ hσ C).xkey w ∈
      EffectiveNames.Double.test (IdempotentNames.name (k:=ZMod 2))
        (IdempotentNames.name (k:=ZMod 3)) (MatrixWords.grade C) C.omega.toList f w := by
  apply Operations.test_full _ _ _ _ _ (d:=(N₂ C).wordCost w) ?_ ?_ w le_rfl
  · intro g hg
    apply SemanticDouble.partialGroupKey_full (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C) _ g hg
    intro v hv
    exact SemanticMatrix.partialGroupKey_full π σ hσ C hs f v hv (fun u _ => hf u)
  · intro x hx
    apply SemanticDouble.partialPointKey_full (N C) (baseC σ hσ (m:=m)) (baseI π σ hσ C) _ x hx
    intro y hy
    exact SemanticMatrix.partialPointKey_full π σ hσ C hs f y hy (fun u _ => hf u)

end SemanticTests
end SimpleFInftyOvergroups.SemanticEncoding
end

end OAI
end

section
-- module Solutions.OAIQ066_SO.SimpleOvergroups_SourceModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SimpleFInftyOvergroups.SourceModel
noncomputable section
open scoped Classical FiniteAlgebraicEnvelopes.Compiler.HeadCodec
open FiniteAlgebraicEnvelopes Bootstrap Compiler Compiler.Simulator MachineRealization
open ContextualEncoding SemanticEncoding EffectiveNames

abbrev P₂ := IdempotentNames.Index (ZMod 2)

variable {G : Type} [Group G] {k : ℕ} (s : Fin k → G)
local instance instDecidableRelSigmaRel_rb27cc1_1 : DecidableRel ContextualEncoding.Source.rel := fun _ _ => inferInstanceAs (Decidable (_ < _))
variable (h : ComputablePred (fun w => FiniteAlgebraicEnvelopes.evalWord s w = 1))

include h in
theorem bootstrap : ∃ index,
    ContextualEncoding.Source.raw index = tableNormal
      (ContextualEncoding.Source.tables s family.A family.M
        (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) index) ∧
    ∀ n, GoodTable (r:=ContextualEncoding.Source.rel)
      (ContextualEncoding.Source.tables s family.A family.M
        (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) index) n ∧
      PartialBudget (ContextualEncoding.Source.raw index) n :=
  ContextualEncoding.Source.exists_total_fixed_point s family.A family.M
    IdempotentNames.name IdempotentNames.name family.decode family.realizes
    IdempotentNames.idempotent IdempotentNames.idempotent h

def index : ℕ := (bootstrap s h).choose
abbrev processor := ContextualEncoding.Source.tables s family.A family.M
  (IdempotentNames.name (k:=ZMod 2)) (IdempotentNames.name (k:=ZMod 3)) (index s h)

abbrev L := Quotient.Mon (processor s h)

abbrev KAlphabet := ContextualEncoding.Source.terminalAlphabet family.A
abbrev KMachine := ContextualEncoding.Source.terminalMachine family.A family.M (index s h)
abbrev K := Word.Presentation KAlphabet (KMachine s h)
instance kMonoidWithZero : MonoidWithZero (K s h) := Word.monoidWithZero KAlphabet (KMachine s h)

abbrev B := Contracted.Algebra (ZMod 2) (K s h)
instance bRing : Ring (B s h) := inferInstance

 abbrev Acting := SourceEnlargement.Double.W (StageConstruction.Q (B s h))
 abbrev Points := SourceEnlargement.Double.Y
   (Q:=StageConstruction.Q (B s h)) (X:=StageConstruction.X (B s h))
 abbrev ActionMon := SourceActionMonoid.M (Acting s h) (Points s h)

end
end SimpleFInftyOvergroups.SourceModel

end OAI
end


