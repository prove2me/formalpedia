-- Prove2me | Definitions.Def_OAIQ65Sa007
-- name    : OAIQ65Sa007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T04:11:47.162835+00:00
-- url     : https://prove2.me/theorems/d585f674-2a89-4914-9b0a-7ae12b3e85fe
-- title:
--   Definitions bundle OAIQ65Sa007 of the split of OpenAI, An infinite finitely presented simple amenable group (result family 253)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleAmenable.main`, carved from OpenAI's openai/math development (OpenAI, *An infinite finitely presented simple amenable group (result family 253)*, OpenAI Math Release, September 23, 2026, result family 253, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 94 declarations of OpenAI's Lean: 30 definitions, 7 instances and 57 theorems. The definitions and types are `OAI.IntervalBar.Diagram.bar₃Homotopy`, `OAI.IntervalBar.Diagram.binaryCutIso`, `OAI.IntervalBar.Diagram.binaryFaceMiddle`, `OAI.IntervalBar.Diagram.binaryMap`, `OAI.IntervalBar.Diagram.componentRowChainIso`, `OAI.IntervalBar.Diagram.componentRowIso`, `OAI.IntervalBar.Diagram.componentsZeroIso`, `OAI.IntervalBar.Diagram.homotopyMap₃`, `OAI.IntervalBar.Diagram.skeletonSimplexEquiv`, `OAI.MarkedH1.binaryLeft`, `OAI.MarkedH1.binaryLeftTranslate`, `OAI.MarkedH1.binaryRight`, `OAI.MarkedH1.binaryRightTranslate`, `OAI.MarkedH1.linearStable`, `OAI.MarkedH1.lowHomologyIso`, `OAI.MarkedH1.lowOneHomologyIso`, `OAI.MarkedH1.stableOneπ`, `OAI.RegularCoefficient.evalHomology`, `OAI.RegularCoefficient.homologyZeroIso`, `OAI.RegularCoefficient.rowZeroIso`, `OAI.RestrictedNerve.diagramHorizontal`, `OAI.RestrictedNerve.horizontalMap`, `OAI.RestrictedNerve.innerReindexLeft`, `OAI.RestrictedNerve.stringsMap`, `OAI.StableBarOne.cocone`, `OAI.StableBarOne.fromStable`, `OAI.StableBarOne.insert`, `OAI.StableBarOne.linearπ`, `OAI.StableBarOne.oneIso`, `OAI.StableBarOne.π`.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: `SimpleAmenable_Configurations_EmptyStage`, `SimpleAmenable_Configurations_FiberAddition`, `SimpleAmenable_Homology_DoubleCoordinates`, `SimpleAmenable_Homology_MarkedBlockDifferentials`, `SimpleAmenable_Homology_MarkedLowHomology`, `SimpleAmenable_Homology_PowerEquivalence`, `SimpleAmenable_Homology_RegularCoefficientDouble`, `SimpleAmenable_Simplicial_BarBinaryBoundary`, `SimpleAmenable_Simplicial_BarComponents`, `SimpleAmenable_Simplicial_BarContractible`, `SimpleAmenable_Simplicial_BarRowFiniteness`, `SimpleAmenable_Simplicial_BarSegal`, `SimpleAmenable_Simplicial_FirstBarDegreeTwoFinite`, `SimpleAmenable_Simplicial_FirstBarForwardLow`, `SimpleAmenable_Simplicial_FirstBarStableH1`, `SimpleAmenable_Simplicial_IntervalBinary`, `SimpleAmenable_Simplicial_IntervalEquivalence`, `SimpleAmenable_Simplicial_IntervalEssSurj`, `SimpleAmenable_Simplicial_MonoidalCongruence`, `SimpleAmenable_Simplicial_NestedPosReindex`, `SimpleAmenable_Simplicial_RestrictedFunctorial`, `SimpleAmenable_Simplicial_RestrictedMonoidalTranspose`, `SimpleAmenable_Simplicial_TripleBarMaps`, `SimpleAmenable_Simplicial_TripleComposition`, `SimpleAmenable_Simplicial_TripleReindex`.
--
--   **Imports.** It imports the bundles `OAIQ65Sa004` and `OAIQ65Sa005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ65Sa013` and `OAIQ65Sa014`; the statement `OAI_SimpleAmenable_affineNoiseRoot_square_distance`; the proofs of `OAI.IntervalBar.Diagram.bar_finite_of_triple` and `OAI.IntervalBar.Diagram.first_row_two_finite`.
-- source:
--   OpenAI, An infinite finitely presented simple amenable group (result family 253), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 253; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Infinite-Finitely-Presented-Simple-Amenable-Group-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ65Sa004
import Definitions.Def_OAIQ65Sa005

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEssSurj
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapFaithful _root_.OAI.IntervalBar.Diagram.mapFull _root_.OAI.IntervalBar.Diagram.mapIsEquivalence _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_nerve_connected _root_.OAI.IntervalBar.Diagram.zero_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open _root_.CategoryTheory MonoidalCategory
universe u v u' v'
namespace IntervalBar.Diagram

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]

noncomputable instance map₃EssSurj (F : C ⥤ D) [F.Braided] [F.EssSurj] (l m n : ℕ) :
    (map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F))).EssSurj :=
  inferInstance

end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalEquivalence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace IntervalBar.Diagram

section
open _root_.CategoryTheory MonoidalCategory
universe u v u' v'

variable {C : Type u} [Groupoid.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u'} [Groupoid.{v'} D] [MonoidalCategory D] [SymmetricCategory D]
noncomputable instance map₃IsEquivalence (F : C ⥤ D) [F.Braided] [F.IsEquivalence] (l m n : ℕ) :
    (map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F))).IsEquivalence :=
  inferInstance
end

end IntervalBar.Diagram

open _root_.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarContractible
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
variable {I J K L M : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L] [Preorder M]
instance bar₃_connected : (bar₃ (C:=C)).IsConnected := by
  have : ((rows₃ (C:=C)).obj (op ⦋0⦌)).IsConnected := bar₂_connected
  exact SimplicialDiagonal.diagonal_connected (rows₃ (C:=C))
open FreeChains
lemma bar₃_low_zero (n : ℕ) (hn : 0<n) (hd : n<3) :
    Limits.IsZero (SSet.homology (C:=A) (bar₃ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₃ (C:=C)) 2
  · intro _; exact bar₂_connected
  · intro q hq
    change Limits.IsZero (SSet.homology (C:=A) (bar₂ (C:=Diagram C (Fin 1))) Z q)
    exact bar₂_acyclic (fun _ _ => inferInstance) q hq
  · intro _ q hq hd; exact bar₂_H1_zero q hq hd
  · exact hn
  · exact hd
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_EmptyStage
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.ChainTensor.monoidalPreadditive _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ComponentStable.epi_toStable _root_.OAI.ConstantSplit.aug_iso _root_.OAI.ConstantSplit.red_flat _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

open FreeChains
lemma bar₃_acyclic {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
    [∀x y:C,Subsingleton (x ⟶ y)] (hh:∀x y:C,Nonempty (x ⟶ y))
    (n:ℕ) (hn:0<n) : Limits.IsZero (SSet.homology (C:=A) (bar₃ (C:=C)) Z n) := by
  apply SimplicialDiagonal.connectivity (rows₃ (C:=C)) n
  · intro p; exact bar₂_connected
  · intro q hq
    exact bar₂_acyclic (fun x y => ⟨homOfAll hh 0 x y⟩) q hq
  · intro p q hq _
    exact bar₂_acyclic (fun x y => ⟨homOfAll hh p x y⟩) q hq
  · exact hn
  · omega
end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_PowerEquivalence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory
namespace IntervalBar.Diagram
open StageProductColimit MonoidalCategory

variable {C D : Type} [Groupoid.{0} C] [Groupoid.{0} D]
    [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
lemma eval₃_natural (F : C ⥤ D) [F.Braided] (l m n:ℕ) :
    map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (n+1)) F)) ⋙ eval₃ l m n =
      eval₃ l m n ⋙ powerMap (Fin l × (Fin m × Fin n)) F := rfl
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleBarMaps
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
variable {I J K L : Type} [Preorder I] [Preorder J] [Preorder K] [Preorder L]
lemma bar₃Map_homology_isIso (F : C ⥤ D) [F.Braided] [F.IsEquivalence] (n : ℕ) :
    IsIso (SSet.homologyMap (bar₃Map F) DiagonalResolution.Z n) := by
  apply SimplicialDiagonal.homologyMap_isIso
  intro p q
  exact bar₂Map_homology_isIso (map (I:=Fin (p.unop.len+1)) F) q
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleComposition
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D E : Type} [Groupoid.{0} C] [Groupoid.{0} D] [Groupoid.{0} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
variable {I J K : Type} [Preorder I] [Preorder J] [Preorder K]
  (F:C ⥤ D) (G:D ⥤ E) [F.Braided] [G.Braided]
lemma map₂_comp : map (I:=J) (map (I:=I) (F⋙G))=map (map F) ⋙ map (map G) := by
  refine CategoryTheory.Functor.hext (map₂_comp_obj F G) ?_
  intro A B f
  apply hom_hext (map₂_comp_obj F G A) (map₂_comp_obj F G B)
  intro i j hij
  apply hom_hext (mapObj_comp F G _) (mapObj_comp F G _)
  intro l m hlm
  rfl
lemma map₃_comp_obj (l m p : ℕ)
    (A : Diagram (Diagram (Diagram C (Fin (p+1))) (Fin (m+1))) (Fin (l+1))) :
    mapObj (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (F⋙G))) A =
      mapObj (map (map G)) (mapObj (map (map F)) A) := by
  have he (X : Diagram (Diagram C (Fin (p+1))) (Fin (m+1))) :
      mapObj (map (F⋙G)) X=
        mapObj (map G) (mapObj (map F) X) :=
    map₂_comp_obj F G X
  have he₁ (X : Diagram C (Fin (p+1))) : mapObj (F⋙G) X=
      mapObj G (mapObj F X) :=
    mapObj_comp F G X
  refine ext_heq ?_ ?_ ?_
  · funext i j hij; exact he _
  · apply hfunext; intro i
    apply iso_hext (he _) rfl
    apply hom_hext (he _) rfl
    intro j z hjz
    apply hom_hext (he₁ _) rfl
    intro v w hvw
    apply heq_of_eq
    erw [map_unit_component, map_unit_component, map_unit_component]
    erw [comp_app, comp_app, map_η_app, map_η_app]
    erw [map_map_app (I:=Fin (p+1)) G, comp_app,
      map_η_app (I:=Fin (p+1)) F]
    change G.map (F.map (((A.unit i).hom.app j z hjz).app v w hvw)) ≫
        Functor.OplaxMonoidal.η (F ⋙ G) =
      G.map (F.map (((A.unit i).hom.app j z hjz).app v w hvw) ≫
        Functor.OplaxMonoidal.η F) ≫ Functor.OplaxMonoidal.η G
    erw [Functor.OplaxMonoidal.comp_η, Functor.map_comp, Category.assoc]
    rfl
  · apply hfunext; intro i
    apply hfunext; intro j
    apply hfunext; intro z
    apply hfunext; intro hij
    apply hfunext; intro hjz
    apply iso_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he _) (he _)) (he _)
    intro v w hvw
    apply hom_hext (congrArg₂ (fun X Y=>X⊗Y) (he₁ _) (he₁ _)) (he₁ _)
    intro x y hxy
    apply heq_of_eq
    erw [map_cut_component, map_cut_component, map_cut_component]
    change Functor.LaxMonoidal.μ (F ⋙ G)
        (((A.obj i j hij).obj v w hvw).obj x y hxy)
        (((A.obj j z hjz).obj v w hvw).obj x y hxy) ≫
        G.map (F.map (((A.cut i j z hij hjz).hom.app v w hvw).app x y hxy)) =
      Functor.LaxMonoidal.μ G
        (F.obj (((A.obj i j hij).obj v w hvw).obj x y hxy))
        (F.obj (((A.obj j z hjz).obj v w hvw).obj x y hxy)) ≫
        G.map (Functor.LaxMonoidal.μ F
          (((A.obj i j hij).obj v w hvw).obj x y hxy)
          (((A.obj j z hjz).obj v w hvw).obj x y hxy) ≫
            F.map (((A.cut i j z hij hjz).hom.app v w hvw).app x y hxy))
    rw [Functor.LaxMonoidal.comp_μ, Functor.map_comp, Category.assoc]
lemma map₃_comp (l m p : ℕ) :
    map (I:=Fin (l+1)) (map (I:=Fin (m+1)) (map (I:=Fin (p+1)) (F⋙G))) =
      map (map (map F)) ⋙ map (map (map G)) := by
  refine CategoryTheory.Functor.hext (map₃_comp_obj F G l m p) ?_
  intro A B f
  apply hom_hext (map₃_comp_obj F G l m p A) (map₃_comp_obj F G l m p B)
  intro i j hij
  apply hom_hext (map₂_comp_obj F G _) (map₂_comp_obj F G _)
  intro v w hvw
  apply hom_hext
    (congrArg (fun F => F.obj ((A.obj i j hij).obj v w hvw)) (map_comp F G))
    (congrArg (fun F => F.obj ((B.obj i j hij).obj v w hvw)) (map_comp F G))
  intro x y hxy
  rfl
lemma bar₃Map_comp : bar₃Map (F⋙G)=bar₃Map F ≫ bar₃Map G := by
  ext n x
  exact congrArg (fun T => x ⋙ T) (map₃_comp F G n.unop.len n.unop.len n.unop.len)

end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_TripleReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C D : Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
  [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
  {F G : C ⥤ D} [F.Braided] [G.Braided]

noncomputable def homotopyMap₃ (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    bar₃ (C:=C) ⊗ Δ[1] ⟶ bar₃ (C:=D) where
  app n := (NerveHomotopy.homotopyMap (tripleNatTrans α n.unop.len)).app n
  naturality n m f := by
    apply ConcreteCategory.hom_ext
    intro x
    change ((NerveHomotopy.homotopyMap (tripleNatTrans α m.unop.len)).app m
      (((bar₃ (C:=C)).map f x.1), Δ[1].map f x.2)) =
      (bar₃ (C:=D)).map f ((NerveHomotopy.homotopyMap (tripleNatTrans α n.unop.len)).app n x)
    erw [bar₃_map, bar₃_map]
    dsimp only [NerveHomotopy.homotopyMap]
    have hc := NerveHomotopy.cylinder_natural
      (diagonalReindex (C:=C) f.unop.toOrderHom)
      (diagonalReindex (C:=D) f.unop.toOrderHom)
      (natTrans₃ α (Fin (n.unop.len+1))) (natTrans₃ α (Fin (m.unop.len+1)))
      (map₃_diagonalReindex F _) (map₃_diagonalReindex G _)
      (natTrans₃_reindex α _)
    change ((f.unop.toOrderHom.toFunctor ⋙ x.1 ⋙ diagonalReindex f.unop.toOrderHom).prod'
      ((SSet.stdSimplex.objEquiv (Δ[1].map f x.2)).toOrderHom.toFunctor)) ⋙
        NerveHomotopy.cylinder (natTrans₃ α (Fin (m.unop.len+1))) =
      f.unop.toOrderHom.toFunctor ⋙ x.1.prod' ((SSet.stdSimplex.objEquiv x.2).toOrderHom.toFunctor) ⋙
        (NerveHomotopy.cylinder (natTrans₃ α (Fin (n.unop.len+1))) ⋙ diagonalReindex f.unop.toOrderHom)
    erw [hc]
    rfl

noncomputable def bar₃Homotopy (α : F ⟶ G) [NatTrans.IsMonoidal α] :
    SSet.Homotopy (bar₃Map F) (bar₃Map G) where
  h := homotopyMap₃ α
  h₀ := by
    ext n x
    exact congrArg (fun t => t.app n x) (NerveHomotopy.homotopyMap_zero (tripleNatTrans α n.unop.len))
  h₁ := by
    ext n x
    exact congrArg (fun t => t.app n x) (NerveHomotopy.homotopyMap_one (tripleNatTrans α n.unop.len))
  rel := by ext n x; exact x.1.property.elim
lemma bar₃Map_eq_of_monoidalNatTrans (α : F ⟶ G) [NatTrans.IsMonoidal α] (n : ℕ) :
    SSet.homologyMap (bar₃Map F) DiagonalResolution.Z n =
      SSet.homologyMap (bar₃Map G) DiagonalResolution.Z n :=
  (bar₃Homotopy α).congr_homologyMap _ _
end IntervalBar.Diagram

end

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_FiberAddition
attribute [-instance] _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma bar₃Map_id_homology (j:ℕ) :
    SSet.homologyMap (bar₃Map (𝟭 C)) DiagonalResolution.Z j=𝟙 _ := by
  have := bar₃Map_homology_isIso (𝟭 C) j
  apply (cancel_epi (SSet.homologyMap (bar₃Map (𝟭 C)) DiagonalResolution.Z j)).mp
  rw [Category.comp_id,← SSet.homologyMap_comp,←bar₃Map_comp]
  exact bar₃Map_eq_of_monoidalNatTrans (Functor.leftUnitor (𝟭 C)).hom j
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_RegularCoefficientDouble
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.ComponentStable.epi_toStable _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularCoefficient
open CoefficientNerve FreeChains

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
noncomputable def evalHomology (n:ℕ) (p:SingleObj P) :
    (CoefficientNerve.complex F).homology n ≅ ((coeffComplex F).homology n).obj p :=
  ExactShapeHomology.evaluationHomology (representation F ⋙ alternatingFaceMapComplex A) n p
lemma evalHomology_natural (n:ℕ) {p q:SingleObj P} (f:p⟶q) :
    homologyMap (((representation F ⋙ alternatingFaceMapComplex A).map f)) n ≫
      (evalHomology F n q).hom =
      (evalHomology F n p).hom ≫ ((coeffComplex F).homology n).map f := by
  have h:=ShortComplex.homologyMap_mapNatTrans ((coeffComplex F).sc n)
    ((evaluation (SingleObj P) A).map f)
  change homologyMap (((representation F ⋙ alternatingFaceMapComplex A).map f)) n =
    (evalHomology F n p).hom ≫ ((coeffComplex F).homology n).map f ≫
      (evalHomology F n q).inv at h
  exact iso_transport_cancel _ _ _ _ h
noncomputable def homologyZeroIso : (coeffComplex F).homology 0 ≅
    constant (C:=SingleObj P) (colimit F) :=
  NatIso.ofComponents (fun p=>(evalHomology F 0 p).symm ≪≫ zeroIso F) (by
    intro p q f
    have h:=evalHomology_natural F 0 f
    change homologyMap ((alternatingFaceMapComplex A).map (action F f)) 0 ≫
      (evalHomology F 0 q).hom = (evalHomology F 0 p).hom ≫ ((coeffComplex F).homology 0).map f at h
    rw [homology_action_zero] at h
    exact inverse_square_of_identity (evalHomology F 0 p) (evalHomology F 0 q)
      _ (zeroIso F).hom h)

noncomputable def rowZeroIso : TotalFiniteness.row (double F) 0 ≅ complex (constant (C:=SingleObj P) (colimit F)) :=
  CoefficientNerve.rowIso (coeffComplex F) 0 ≪≫
    (alternatingFaceMapComplex A).mapIso (CoefficientNerve.functor.mapIso (homologyZeroIso F))
end RegularCoefficient

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_IntervalBinary
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.IntervalBar.Diagram.hom_thin _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapEssSurj _root_.OAI.IntervalBar.Diagram.mapFaithful _root_.OAI.IntervalBar.Diagram.mapFull _root_.OAI.IntervalBar.Diagram.mapIsEquivalence _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.map₃EssSurj _root_.OAI.IntervalBar.Diagram.map₃IsEquivalence _root_.OAI.IntervalBar.Diagram.zero_hom_nonempty _root_.OAI.IntervalBar.Diagram.zero_nerve_connected _root_.OAI.IntervalBar.Diagram.zero_nonempty _root_.OAI.IntervalBar.Diagram.zero_thin _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable instance oneEval_equivalence : (oneEval (C:=C)).IsEquivalence := by
  have : (Pi.eval (fun _:Fin 1=>C) 0).IsEquivalence := (piOneEquiv (C:=C)).isEquivalence_functor
  dsimp only [oneEval]
  infer_instance
noncomputable def binaryCutIso : eval (C:=C) 2 ⋙ tensorPair ≅
    reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom ⋙ oneEval :=
  NatIso.ofComponents (fun D => D.cut 0 1 2 (by decide) (by decide)) (by
    intro D E f; exact f.cut 0 1 2 (by decide) (by decide))
noncomputable def binaryFaceMiddle : binaryFace (C:=C) 1 ≅ tensorPair :=
  (Functor.isoWhiskerLeft (eval 2).asEquivalence.inverse binaryCutIso).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eval 2).asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_DoubleCoordinates
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.diagramPropertyBraided _root_.OAI.RestrictedNerve.diagramPropertyInverse _root_.OAI.RestrictedNerve.diagramPropertyMonoidal _root_.OAI.RestrictedNerve.diagramProperty_multiplicative _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.posDiagramBraided _root_.OAI.RestrictedNerve.posDiagramInclusionBraided _root_.OAI.RestrictedNerve.posDiagramIsIso _root_.OAI.RestrictedNerve.posDiagramMonoidal _root_.OAI.RestrictedNerve.posDiagramSymmetric _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.RestrictedNerve.transposeBraided _root_.OAI.RestrictedNerve.transposeMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MarkedH1

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def binaryLeft (p:Fin 2→Skeleton C) :
    wordInclude p 0 ⋙ tensorPair ≅ (property (p 0)).ι ⋙ tensorRight (repr (p 1)) := by
  classical
  apply eqToIso
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro object
    simp [wordInclude, tensorPair, tensorRight, Functor.pi']
  · intro source target morphism
    simp [wordInclude, tensorPair, tensorRight, Functor.pi']
    change morphism.hom ▷ repr (p 1) = 𝟙 _ ≫ morphism.hom ▷ repr (p 1)
    exact (Category.id_comp _).symm
noncomputable def binaryRight (p:Fin 2→Skeleton C) :
    wordInclude p 1 ⋙ tensorPair ≅ (property (p 1)).ι ⋙ tensorLeft (repr (p 0)) := by
  classical
  apply eqToIso
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro object
    simp [wordInclude, tensorPair, tensorLeft, Functor.pi']
  · intro source target morphism
    simp [wordInclude, tensorPair, tensorLeft, Functor.pi']
    change repr (p 0) ◁ morphism.hom = 𝟙 _ ≫ repr (p 0) ◁ morphism.hom
    exact (Category.id_comp _).symm
noncomputable def binaryLeftTranslate (p:Fin 2→Skeleton C) :
    wordInclude p 0 ⋙ tensorPair ≅
      translate (p 1) (p 0) (p 1*p 0) rfl ⋙ (property (p 1*p 0)).ι :=
  binaryLeft p ≪≫ Functor.isoWhiskerLeft (property (p 0)).ι
    (BraidedCategory.tensorLeftIsoTensorRight (repr (p 1))).symm
noncomputable def binaryRightTranslate (p:Fin 2→Skeleton C) :
    wordInclude p 1 ⋙ tensorPair ≅
      translate (p 0) (p 1) (p 0*p 1) rfl ⋙ (property (p 0*p 1)).ι := binaryRight p
lemma binary_primitive_middle_stable (p:Fin 2→Skeleton C) (i:Fin 2) :
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 =
        ComponentStable.inclusion (p i) 1 ≫ ComponentStable.toStable 1 := by
  rw [binary_primitive_face_assoc]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p i) (binaryFaceMiddle (C:=C))).hom).congr_homologyMap Z 1
  rw [h]
  fin_cases i
  · change SSet.homologyMap (nerveMap (wordInclude p 0 ⋙ tensorPair)) Z 1 ≫ ComponentStable.toStable 1 =
      ComponentStable.inclusion (p 0) 1 ≫ ComponentStable.toStable 1
    have ht:=(NerveHomotopy.ofNatTrans (binaryLeftTranslate p).hom).congr_homologyMap Z 1
    rw [ht]
    change SSet.homologyMap (nerveMap (translate (p 1) (p 0) (p 1*p 0) rfl) ≫
      nerveMap (property (p 1*p 0)).ι) Z 1 ≫ _ = _
    rw [SSet.homologyMap_comp,Category.assoc]
    exact ComponentStable.translate_toStable _ _ _ rfl 1
  · change SSet.homologyMap (nerveMap (wordInclude p 1 ⋙ tensorPair)) Z 1 ≫ ComponentStable.toStable 1 =
      ComponentStable.inclusion (p 1) 1 ≫ ComponentStable.toStable 1
    have ht:=(NerveHomotopy.ofNatTrans (binaryRightTranslate p).hom).congr_homologyMap Z 1
    rw [ht]
    change SSet.homologyMap (nerveMap (translate (p 0) (p 1) (p 0*p 1) rfl) ≫
      nerveMap (property (p 0*p 1)).ι) Z 1 ≫ _ = _
    rw [SSet.homologyMap_comp,Category.assoc]
    exact ComponentStable.translate_toStable _ _ _ rfl 1
end

end MarkedH1

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedMonoidalTranspose
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallTripleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₂ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinHAddNatOfNatForallProdEval₃ _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.map₂Monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
open IntervalBar IntervalBar.Diagram

variable {C : Type} [Groupoid.{0} C] (W : MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I : Type} [Preorder I]
lemma map_strings_reindex_id (n : ℕ) :
    Diagram.map (I:=I) (reindex W (𝟭 (Fin (n+1))))=𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      erw [Category.comp_id]
      rfl
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      erw [Category.id_comp]
      rfl
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    simp only [Diagram.map]
    erw [Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext; rfl
lemma map_strings_reindex_comp {n m k : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (v : Fin (m+1) ⥤ Fin (k+1)) :
    Diagram.map (I:=I) (reindex W (u ⋙ v)) =
      Diagram.map (reindex W v) ⋙ Diagram.map (reindex W u) := by
  refine CategoryTheory.Functor.ext (fun A => ?_) ?_
  · refine ext_heq rfl ?_ ?_
    · apply heq_of_eq; funext i
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      change (A.unit i).hom.hom.app (v.obj (u.obj t)) ≫ 𝟙 _ =
        (A.unit i).hom.hom.app (v.obj (u.obj t)) ≫ (𝟙 _ ≫ 𝟙 _)
      simp only [Category.comp_id]
    · apply heq_of_eq; funext i j k hij hjk
      apply Iso.ext; apply WideSubcategory.hom_ext; apply NatTrans.ext; funext t
      simp [mapObj]
      change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app (v.obj (u.obj t)) =
        𝟙 _ ≫ 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app (v.obj (u.obj t))
      simp only [Category.id_comp]
  · intro A B f
    apply Hom.ext; intro i j h
    erw [comp_app, comp_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    simp only [Diagram.map]
    erw [Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext; rfl
noncomputable def diagramHorizontal : SimplicialObject Cat.{0,0} where
  obj p := Cat.of (Diagram (Strings W p.unop.len) I)
  map f := (Diagram.map (reindex W f.unop.toOrderHom.toFunctor)).toCatHom
  map_id p := by apply Cat.ext; exact map_strings_reindex_id W _
  map_comp f g := by apply Cat.ext; exact map_strings_reindex_comp (I:=I) W g.unop.toOrderHom.toFunctor f.unop.toOrderHom.toFunctor
lemma transposed_comp_app {n : ℕ}
    {A B D : Strings (diagramProperty W I) n} (f : A ⟶ B) (g : B ⟶ D)
    (t : Fin (n+1)) (i j : I) (h : i ≤ j) :
    ((f ≫ g).hom.app t).hom.app i j h =
      (f.hom.app t).hom.app i j h ≫ (g.hom.app t).hom.app i j h := rfl

lemma eqToHom_vertex_app {A B : PosDiagrams W I} (e : A = B)
    (i j : I) (h : i ≤ j) :
    (eqToHom e).hom.app i j h =
      eqToHom (congrArg (fun A : PosDiagrams W I =>
        ((diagramInclusion W I).obj A).obj i j h) e) := by
  cases e
  rfl

lemma stringVertex_reindex {n m : ℕ} (u : Fin (n+1) ⥤ Fin (m+1))
    (A : Diagram (Strings W m) I) (t : Fin (n+1)) :
    stringVertex W ((Diagram.map (reindex W u)).obj A) t = stringVertex W A (u.obj t) := by
  refine ext_heq rfl ?_ ?_
  · apply heq_of_eq; funext i
    apply Iso.ext; apply WideSubcategory.hom_ext
    change (A.unit i).hom.hom.app (u.obj t) ≫ 𝟙 _ = _
    exact Category.comp_id _
  · apply heq_of_eq; funext i j k hij hjk
    apply Iso.ext; apply WideSubcategory.hom_ext
    change 𝟙 _ ≫ (A.cut i j k hij hjk).hom.hom.app (u.obj t) = _
    exact Category.id_comp _

end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_RestrictedFunctorial
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RestrictedNerve

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory SimplicialObject Simplicial Opposite

section

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  (W:MorphismProperty C) (V:MorphismProperty D) [W.IsMultiplicative] [V.IsMultiplicative]
  (F:C⥤D) (hF:∀{X Y:C} (f:X⟶Y),W f→V (F.map f))
def stringsMap (n:ℕ) : Strings W n ⥤ Strings V n where
  obj A := ⟨A.obj⋙F⟩
  map f := ⟨Functor.whiskerRight f.hom F,fun i=>hF _ (f.property i)⟩
  map_id _ := by apply WideSubcategory.hom_ext; ext i; exact F.map_id _
  map_comp _ _ := by apply WideSubcategory.hom_ext; ext i; exact F.map_comp _ _
def horizontalMap : horizontal W ⟶ horizontal V where
  app p := (stringsMap W V F hF p.unop.len).toCatHom
  naturality _ _ f := by
    apply Cat.ext
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro source target arrow
    erw [Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext; ext index; rfl
lemma diagonalIso_natural :
    SimplicialDiagonal.nerveDiagonal.map (horizontalMap W V F hF) ≫ (diagonalIso V).hom =
      (diagonalIso W).hom ≫ SimplicialDiagonal.nerveDiagonal.map (verticalMapNat W V F hF) := by
  ext p x
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro source target arrow
  erw [Category.id_comp, Category.comp_id]
  apply ObjectProperty.hom_ext; ext index; rfl
end

end

end RestrictedNerve

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_MonoidalCongruence
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.posReindexBraided _root_.OAI.RestrictedNerve.posReindexMonoidal _root_.OAI.RestrictedNerve.widePosReindexBraided _root_.OAI.RestrictedNerve.widePosReindexMonoidal _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
lemma map_congr {I:Type} [Preorder I] {F G:C⥤D} [hF:F.Monoidal] [hG:G.Monoidal]
    (e:F=G) (h:NatTrans.IsMonoidal (eqToHom e)) : map (I:=I) F=map G := by
  have hm := monoidal_congr e h
  cases e
  have hh : hF=hG := eq_of_heq hm
  cases hh
  rfl
end IntervalBar.Diagram

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
lemma map₂_congr {I J:Type} [Preorder I] [Preorder J]
    {F G:C⥤D} [hF:F.Braided] [hG:G.Braided] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) :
    map (I:=J) (map (I:=I) F)=map (map G) := by
  have hm := braided_congr e h
  cases e
  have hh : hF=hG := eq_of_heq hm
  cases hh
  rfl
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_NestedPosReindex
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallDoubleProject _root_.OAI.BarFinitePower.instIsEquivalenceDiagramForallFinHAddNatOfNatForallSingleProject _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.instBraidedFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instEssSurjFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFaithfulFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instFullFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.instIsEquivalenceFinOfNatNatForallOuterFunctor _root_.OAI.IntervalBar.Diagram.mapNatTrans_monoidal _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory SimplicialObject Simplicial Opposite
namespace RestrictedNerve

open IntervalBar IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] (W:MorphismProperty C)
  [Fact W.StableUnderInverse] [MonoidalCategory C] [SymmetricCategory C]
  [W.IsStableUnderBraiding]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
noncomputable abbrev innerReindexLeft (u:I→oJ) (n:ℕ) :=
    Diagram.map (I:=K) (Diagram.reindex (C:=Strings W n) u) ⋙
      Diagram.map (I:=K) (transposeDiagram (I:=I) W n) ⋙
        transposeDiagram (I:=K) (diagramProperty W I) n

end RestrictedNerve

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory
namespace IntervalBar.Diagram

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
variable {I J K:Type} [Preorder I] [Preorder J] [Preorder K]
noncomputable instance reindex_map_monoidal (F:C⥤D) [F.Braided] (u:I→oJ) :
    NatTrans.IsMonoidal (eqToHom (reindex_map F u)) where
  unit := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_ε,map_ε,reindex_ε]
    simp [mapεHom,map,reindex]
    erw [Diagram.eqToHom_app]
    change Functor.LaxMonoidal.ε F ≫ F.map (𝟙 (𝟙_ C)) ≫ 𝟙 _ = 𝟙 _ ≫ Functor.LaxMonoidal.ε F
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  tensor A B := by
    apply Hom.ext; intro i j h
    simp only [CategoryTheory.eqToHom_app]
    simp only [Functor.LaxMonoidal.comp_μ,map_μ,reindex_μ]
    simp [mapμHom,map,reindex]
    erw [Diagram.eqToHom_app, Diagram.eqToHom_app, Diagram.eqToHom_app]
    change Functor.LaxMonoidal.μ F (A.obj (u i) (u j) (u.monotone h)) (B.obj (u i) (u j) (u.monotone h)) ≫
      F.map (𝟙 _) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫
        Functor.LaxMonoidal.μ F (A.obj (u i) (u j) (u.monotone h)) (B.obj (u i) (u j) (u.monotone h))
    simp only [CategoryTheory.Functor.map_id, id_tensorHom_id, Category.id_comp, Category.comp_id]
lemma map_reindex_map (F:C⥤D) [F.Braided] (u:I→oJ) :
    map (I:=K) (reindex (C:=C) u) ⋙ map (I:=K) (map F) =
      map (I:=K) (map F) ⋙ map (I:=K) (reindex u) := by
  have he := map_congr (I:=K) (reindex_map F u) (reindex_map_monoidal F u)
  simpa only [map_comp] using he
end IntervalBar.Diagram

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarSegal
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.IntervalBar.Diagram.oneEval_equivalence _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open BarFinitePower SimplicialDiagonal StageProductColimit

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma outer_project (i:Fin 2) : outerFunctor (C:=C) ⋙ project _ i = reindex (outerOrder i) := rfl
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarRowFiniteness
attribute [-instance] _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite
namespace NerveComponents
open FreeChains

variable {C D:Type} [Groupoid.{0} C] [Groupoid.{0} D]
lemma vertex_natural (F:C⥤D) (x:C) : vertex x ≫ SSet.homologyMap (nerveMap F) Z 0=vertex (F.obj x) := by
  dsimp only [vertex,SSet.homologyMap]
  rw [Category.assoc,HomologicalComplex.homologyπ_naturality,←Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  erw [SSet.ι_chainComplexMap_f]
  have he : (nerveMap F).app (op ⦋0⦌) (nerveEquiv.symm x)=nerveEquiv.symm (F.obj x) :=
    ComposableArrows.ext₀ rfl
  rw [he]
lemma hom_ext {M:A} {f g:(nerve C).homology Z 0 ⟶ M}
    (h:∀x:C,vertex x ≫ f=vertex x ≫ g) : f=g := by
  apply (cancel_epi (zeroIso (C:=C)).inv).mp
  apply ModuleCat.free_hom_ext
  intro p
  obtain ⟨x,rfl⟩ := Quotient.exists_rep p
  have hh:=congrArg (fun k:Z⟶M=>k (1:ℤ)) (h x)
  have hv : ModuleCat.ofHom (Finsupp.lsingle (toSkeleton x)) ≫ (zeroIso (C:=C)).inv=vertex x := by
    erw [←vertex_zeroIso,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  have ht:=congrArg (fun k:Z⟶(nerve C).homology Z 0=>k (1:ℤ)) hv
  change f ((zeroIso (C:=C)).inv (ModuleCat.freeMk (toSkeleton x))) =
    g ((zeroIso (C:=C)).inv (ModuleCat.freeMk (toSkeleton x)))
  change (zeroIso (C:=C)).inv (ModuleCat.freeMk (toSkeleton x))=vertex x (1:ℤ) at ht
  rw [ht]
  exact hh
lemma zeroIso_natural (F:C⥤D) : SSet.homologyMap (nerveMap F) Z 0 ≫ (zeroIso (C:=D)).hom =
    (zeroIso (C:=C)).hom ≫ (ModuleCat.free ℤ).map (↾(map F)) := by
  apply hom_ext; intro x
  rw [←Category.assoc,vertex_natural,vertex_zeroIso,vertex_zeroIso_assoc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change ModuleCat.freeMk (toSkeleton (F.obj x)) =
    (ModuleCat.free ℤ).map (↾(map F)) (ModuleCat.freeMk (toSkeleton x))
  exact (ModuleCat.free_map_apply (R:=ℤ) (↾(map F)) (toSkeleton x)).symm
end NerveComponents

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarComponents
attribute [-instance] _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.QuotientRegular.finite_regular_module
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

section
open NerveComponents FreeChains

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma skeletonSimplex_natural {n m:ℕ} (u:⦋m⦌⟶⦋n⦌) (p:Skeleton (Diagram C (Fin (n+1)))) :
    skeletonSimplex m (NerveComponents.map (reindex u.toOrderHom) p)=
      (nerve (SingleObj (Skeleton C))).map u.op (skeletonSimplex n p) := by
  obtain ⟨D,rfl⟩ := Quotient.exists_rep p
  rfl
lemma skeletonSimplex_injective (n:ℕ) : Function.Injective (skeletonSimplex (C:=C) n) := by
  intro D E h
  obtain ⟨D,rfl⟩ := Quotient.exists_rep D
  obtain ⟨E,rfl⟩ := Quotient.exists_rep E
  apply congr_toSkeleton_of_iso
  apply (eval n).preimageIso
  refine { hom := fun i=>?_,inv:=fun i=>?_,hom_inv_id:=?_,inv_hom_id:=?_ }
  · exact (Skeleton.isoOfEq (congrArg (fun s:ComposableArrows (SingleObj (Skeleton C)) n=>
      s.map (homOfLE (Fin.castSucc_le_succ i))) h)).hom
  · exact (Skeleton.isoOfEq (congrArg (fun s:ComposableArrows (SingleObj (Skeleton C)) n=>
      s.map (homOfLE (Fin.castSucc_le_succ i))) h)).inv
  · funext i; exact Iso.hom_inv_id _
  · funext i; exact Iso.inv_hom_id _
lemma skeletonSimplex_surjective (n:ℕ) : Function.Surjective (skeletonSimplex (C:=C) n) := by
  intro s
  let U : Fin n → C := fun i=>(fromSkeleton C).obj (s.map (homOfLE (Fin.castSucc_le_succ i)))
  refine ⟨toSkeleton ((eval n).objPreimage U),?_⟩
  apply ComposableArrows.ext (fun _=>Subsingleton.elim _ _)
  intro i hi
  have e := ((eval n).objObjPreimageIso U)
  simp only [single_eqToHom,SingleObj.comp_as_mul,one_mul,mul_one]
  exact (congr_toSkeleton_of_iso (asIso (e.hom ⟨i,hi⟩))).trans (toSkeleton_fromSkeleton_obj _)
noncomputable def skeletonSimplexEquiv (n:ℕ) : Skeleton (Diagram C (Fin (n+1))) ≃
    ComposableArrows (SingleObj (Skeleton C)) n :=
  Equiv.ofBijective (skeletonSimplex n) ⟨skeletonSimplex_injective n,skeletonSimplex_surjective n⟩
noncomputable def componentsZeroIso (n:ℕ) :
    (nerve (Diagram C (Fin (n+1)))).homology Z 0 ≅
      (ModuleCat.free ℤ).obj ((nerve (SingleObj (Skeleton C))).obj (op ⦋n⦌)) :=
  NerveComponents.zeroIso ≪≫ (ModuleCat.free ℤ).mapIso (skeletonSimplexEquiv n).toIso
end

open NerveComponents FreeChains AlgebraicTopology

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma componentsZeroIso_natural {n m:ℕ} (u:⦋m⦌⟶⦋n⦌) :
    SSet.homologyMap (nerveMap (reindex (C:=C) u.toOrderHom)) Z 0 ≫ (componentsZeroIso m).hom =
      (componentsZeroIso n).hom ≫ (ModuleCat.free ℤ).map ((nerve (SingleObj (Skeleton C))).map u.op) := by
  change SSet.homologyMap (nerveMap (reindex (C:=C) u.toOrderHom)) Z 0 ≫
      ((zeroIso (C:=Diagram C (Fin (m+1)))).hom ≫
        (ModuleCat.free ℤ).map (skeletonSimplexEquiv m).toIso.hom) =
    ((zeroIso (C:=Diagram C (Fin (n+1)))).hom ≫
      (ModuleCat.free ℤ).map (skeletonSimplexEquiv n).toIso.hom) ≫
        (ModuleCat.free ℤ).map ((nerve (SingleObj (Skeleton C))).map u.op)
  rw [←Category.assoc,NerveComponents.zeroIso_natural,Category.assoc,←Functor.map_comp,
    Category.assoc]
  erw [←Functor.map_comp]
  congr 2
  apply ConcreteCategory.hom_ext
  intro p
  exact skeletonSimplex_natural u p
noncomputable def componentRowIso :
    simplicial (C:=C) ⋙ nerveFunctor ⋙ SSet.homologyFunctor Z 0 ≅
      nerve (SingleObj (Skeleton C)) ⋙ ModuleCat.free ℤ :=
  NatIso.ofComponents (fun p=>componentsZeroIso p.unop.len) (fun {_ _} u=>componentsZeroIso_natural u.unop)
noncomputable def componentRowChainIso :
    AlternatingFaceMapComplex.obj (simplicial (C:=C) ⋙ nerveFunctor ⋙ SSet.homologyFunctor Z 0) ≅
      FreeChains.complex (nerve (SingleObj (Skeleton C))) :=
  (alternatingFaceMapComplex A).mapIso componentRowIso
end IntervalBar.Diagram

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedBlockDifferentials
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma T_comp_congr {M:A} (r p q q':Skeleton C) (h:r*p=q) (h':r*p=q')
    (e:q=q') (f:∀s:Skeleton C,H s ⟶ M) : T r p q h ≫ f q = T r p q' h' ≫ f q' := by
  cases e
  rfl
lemma compat01 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 1 0 ≫ (gradedIso 0).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ (gradedIso 1).hom ≫ (homologyRow (C:=C) 1).d 2 1 := by
  erw [imageP01_assoc]
  erw [Pd_2_1]
  erw [block_d01_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP00 b]
  erw [imageP00 (a*b)]
  simp only [map_arrow_T]
  try erw [mul_comm b a]
  try abel
lemma compat10 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 1 0 ≫ (gradedIso 0).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ (gradedIso 1).hom ≫ (homologyRow (C:=C) 1).d 2 1 := by
  erw [imageP10_assoc]
  erw [Pd_2_0]
  erw [block_d10_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP00 a]
  erw [imageP00 (b*a)]
  simp only [map_arrow_T]
  erw [T_comp_congr b a (b*a) (a*b) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P10 t)]
  try erw [mul_comm b a]
  try abel
lemma compat02 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  erw [imageP02_assoc]
  erw [Pd_3_2]
  erw [block_d02_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP01 b d]
  erw [imageP01 (a*b) d]
  erw [imageP01 a (b*d)]
  simp only [map_arrow_T]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm d b]
  try abel
lemma compat11 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  erw [imageP11_assoc]
  erw [Preadditive.neg_comp,Pd_3_1]
  erw [block_d11_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP01 a b]
  erw [imageP01 a (d*b)]
  erw [imageP10 b d]
  erw [imageP10 (a*b) d]
  simp only [map_arrow_T]
  erw [T_comp_congr d b (d*b) (b*d) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P21 a t)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm d b]
  try abel
lemma compat20 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫ (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  erw [imageP20_assoc]
  erw [Preadditive.neg_comp,Pd_3_0]
  erw [block_d20_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP10 a b]
  erw [imageP10 a (d*b)]
  erw [imageP10 (b*a) d]
  simp only [map_arrow_T]
  erw [T_comp_congr b a (b*a) (a*b) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P20 t d)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm d b]
  try abel
lemma compat03 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP03_assoc]
  erw [Pd_4_3]
  erw [block_d03_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP02 b d e]
  erw [imageP02 (a*b) d e]
  erw [imageP02 a (b*d) e]
  erw [imageP02 a b (d*e)]
  simp only [map_arrow_T]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
lemma compat12 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP12_assoc]
  erw [Pd_4_2]
  erw [block_d12_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP02 a b d]
  erw [imageP02 a b (e*d)]
  erw [imageP11 b d e]
  erw [imageP11 (a*b) d e]
  erw [imageP11 a (b*d) e]
  simp only [map_arrow_T]
  repeat erw [Preadditive.comp_neg]
  erw [T_comp_congr e d (e*d) (d*e) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P32 a b t)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
lemma compat21 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP21_assoc]
  erw [Preadditive.neg_comp,Pd_4_1]
  erw [block_d21_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP11 a b d]
  erw [imageP11 a b (e*d)]
  erw [imageP11 a (d*b) e]
  erw [imageP20 b d e]
  erw [imageP20 (a*b) d e]
  simp only [map_arrow_T]
  repeat erw [Preadditive.comp_neg]
  erw [T_comp_congr d b (d*b) (b*d) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P31 a t e)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
lemma compat30 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP30_assoc]
  erw [Preadditive.neg_comp,Pd_4_0]
  erw [block_d30_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP20 a b d]
  erw [imageP20 a b (e*d)]
  erw [imageP20 a (d*b) e]
  erw [imageP20 (b*a) d e]
  simp only [map_arrow_T]
  repeat erw [Preadditive.comp_neg]
  erw [T_comp_congr b a (b*a) (a*b) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P30 t d e)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_MarkedLowHomology
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
lemma differential1 :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 1 0 ≫ (gradedIso 0).hom =
      (gradedIso 1).hom ≫ (homologyRow (C:=C) 1).d 2 1 := by
  apply total_hom_ext (homologyDiagram (C:=C) 1)
  rintro ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  change h+v=1 at hn
  have hh:h≤1:=by omega
  interval_cases h
  · have hv:v=1:=by omega
    subst v
    have hy:y=![y 0]:=by ext index; fin_cases index; rfl
    have hx:x=![]:=Subsingleton.elim _ _
    rw [hy,hx]
    exact compat01 (y 0) (p)
  · have hv:v=0:=by omega
    subst v
    have hy:y=![]:=Subsingleton.elim _ _
    have hx:x=![x 0]:=by ext index; fin_cases index; rfl
    rw [hy,hx]
    exact compat10 (p) (x 0)
lemma differential2 :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
      (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  apply total_hom_ext (homologyDiagram (C:=C) 1)
  rintro ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  change h+v=2 at hn
  have hh:h≤2:=by omega
  interval_cases h
  · have hv:v=2:=by omega
    subst v
    have hy:y=![y 0,y 1]:=by ext i; fin_cases i <;> rfl
    have hx:x=![]:=Subsingleton.elim _ _
    rw [hy,hx]
    exact compat02 (y 0) (y 1) (p)
  · have hv:v=1:=by omega
    subst v
    have hy:y=![y 0]:=by ext index; fin_cases index; rfl
    have hx:x=![x 0]:=by ext index; fin_cases index; rfl
    rw [hy,hx]
    exact compat11 (y 0) (p) (x 0)
  · have hv:v=0:=by omega
    subst v
    have hy:y=![]:=Subsingleton.elim _ _
    have hx:x=![x 0,x 1]:=by ext i; fin_cases i <;> rfl
    rw [hy,hx]
    exact compat20 (p) (x 1) (x 0)
lemma differential3 :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
      (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  apply total_hom_ext (homologyDiagram (C:=C) 1)
  rintro ⟨⟨⟨h,v⟩,hn⟩,y,p,x⟩
  change h+v=3 at hn
  have hh:h≤3:=by omega
  interval_cases h
  · have hv:v=3:=by omega
    subst v
    have hy:y=![y 0,y 1,y 2]:=by ext i; fin_cases i <;> rfl
    have hx:x=![]:=Subsingleton.elim _ _
    rw [hy,hx]
    exact compat03 (y 0) (y 1) (y 2) (p)
  · have hv:v=2:=by omega
    subst v
    have hy:y=![y 0,y 1]:=by ext i; fin_cases i <;> rfl
    have hx:x=![x 0]:=by ext index; fin_cases index; rfl
    rw [hy,hx]
    exact compat12 (y 0) (y 1) (p) (x 0)
  · have hv:v=1:=by omega
    subst v
    have hy:y=![y 0]:=by ext index; fin_cases index; rfl
    have hx:x=![x 0,x 1]:=by ext i; fin_cases i <;> rfl
    rw [hy,hx]
    exact compat21 (y 0) (p) (x 1) (x 0)
  · have hv:v=0:=by omega
    subst v
    have hy:y=![]:=Subsingleton.elim _ _
    have hx:x=![x 0,x 1,x 2]:=by ext i; fin_cases i <;> rfl
    rw [hy,hx]
    exact compat30 (p) (x 2) (x 1) (x 0)
noncomputable def lowHomologyIso :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).homology 2 ≅
      (homologyRow (C:=C) 1).homology 3 :=
  by
    let K := (RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c
    let L := homologyRow (C:=C) 1
    let e : K.sc' 3 2 1 ≅ L.sc' 4 3 2 :=
      ShortComplex.isoMk (gradedIso 3) (gradedIso 2) (gradedIso 1)
        (differential3 (C:=C)).symm (differential2 (C:=C)).symm
    exact (ShortComplex.homologyFunctor A).mapIso
      (K.isoSc' 3 2 1 (c.prev_eq' rfl) (c.next_eq' rfl) ≪≫ e ≪≫
        (L.isoSc' 4 3 2 (c.prev_eq' rfl) (c.next_eq' rfl)).symm)
end MarkedH1

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarStableH1
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite AlgebraicTopology
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def linearStable : (homologyRow (C:=C) 1).X 1 ⟶ ComponentStable.object (C:=C) 1 :=
  SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1
instance linearStable_epi : Epi (linearStable (C:=C)) := by
  dsimp only [linearStable]
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
    (NerveHomotopy.homologyMap_isIso (oneEval (C:=C)) Z 1))
    (ComponentStable.epi_toStable 1)
omit [SymmetricCategory C] in
lemma rowOne_d10 : (homologyRow (C:=C) 1).d 1 0=0 := by
  have hz:IsZero ((homologyRow (C:=C) 1).X 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply hom_ext
    intro p i
    exact Fin.elim0 i
  exact hz.eq_zero_of_tgt _
lemma linearStable_d : (homologyRow (C:=C) 1).d 2 1 ≫ linearStable=0 := by
  apply hom_ext
  intro p i
  change Fin 2 → Skeleton C at p
  change Fin 2 at i
  rw [SimplicialFirstFinite.d21]
  dsimp only [linearStable]
  simp only [Preadditive.add_comp,Preadditive.sub_comp]
  change primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 -
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 +
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 = 0
  rw [binary_primitive_middle_stable]
  fin_cases i
  all_goals dsimp only at *
  · change primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 -
    ComponentStable.inclusion (p 0) 1 ≫ ComponentStable.toStable 1 +
    primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 = 0
    rw [binary_primitive_zero_other_assoc,zero_comp,
      binary_primitive_last_assoc]
    abel
  · change primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 -
    ComponentStable.inclusion (p 1) 1 ≫ ComponentStable.toStable 1 +
    primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 = 0
    rw [binary_primitive_zero_assoc,
      binary_primitive_last_other_assoc,zero_comp]
    abel
noncomputable def stableOneπ : (homologyRow (C:=C) 1).homology 1 ⟶ ComponentStable.object (C:=C) 1 :=
  ChainComplex.positiveDesc _ 0 rowOne_d10 linearStable linearStable_d
instance stableOneπ_epi : Epi (stableOneπ (C:=C)) := by
  have hh:ChainComplex.positiveπ _ 0 rowOne_d10 ≫ stableOneπ (C:=C)=linearStable :=
    ChainComplex.positiveπ_desc _ 0 rowOne_d10 linearStable linearStable_d
  have :Epi (ChainComplex.positiveπ _ 0 rowOne_d10 ≫ stableOneπ (C:=C)):=by rw [hh]; infer_instance
  exact epi_of_epi (ChainComplex.positiveπ _ 0 rowOne_d10) _
end MarkedH1

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarDegreeTwoFinite
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace StableBarOne
open FreeChains ComponentTranslation IntervalBar.Diagram MarkedH1

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def insert {n:ℕ} (p:Fin n→Skeleton C) (i:Fin n) (q:ℕ) :
    (nerve (Fiber (p i))).homology Z q ⟶ (homologyRow (C:=C) q).X n :=
  SSet.homologyMap (nerveMap (wordDiagram p i)) Z q
@[reassoc] lemma binary_insert_face (p:Fin 2→Skeleton C) (i:Fin 2) (k:Fin 3) (q:ℕ) :
    insert p i q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q =
        SSet.homologyMap (nerveMap (wordInclude p i ⋙ binaryFace k)) Z q := by
  change SSet.homologyMap (nerveMap (wordDiagram p i)) Z q ≫
    SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ k).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q =
    SSet.homologyMap (nerveMap (wordDiagram p i) ≫
      nerveMap (reindex (SimplexCategory.δ k).toOrderHom) ≫ nerveMap oneEval) Z q
  simp only [SSet.homologyMap_comp]
@[reassoc] lemma binary_insert_zero (p:Fin 2→Skeleton C) (q:ℕ) :
    insert p 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=ComponentStable.inclusion (p 1) q := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z q
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
@[reassoc] lemma binary_insert_last (p:Fin 2→Skeleton C) (q:ℕ) :
    insert p 0 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=ComponentStable.inclusion (p 0) q := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z q
  rw [h]
  rw [wordInclude_proj,ite_eq_left rfl]
  rfl
@[reassoc] lemma binary_insert_zero_other (p:Fin 2→Skeleton C) (q:ℕ) (hq:q≠0) :
    insert p 0 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=0 := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 0) (binaryFaceZero (C:=C))).hom).congr_homologyMap Z q
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 0))).obj (repr (p 1))) =
      SSet.const (nerveEquiv.symm (repr (p 1))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ q hq
@[reassoc] lemma binary_insert_last_other (p:Fin 2→Skeleton C) (q:ℕ) (hq:q≠0) :
    insert p 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q=0 := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceLast (C:=C))).hom).congr_homologyMap Z q
  rw [h,wordInclude_proj,ite_eq_right (by decide)]
  have hc : nerveMap ((Functor.const (Fiber (p 1))).obj (repr (p 0))) =
      SSet.const (nerveEquiv.symm (repr (p 0))) := by ext n x; rfl
  rw [hc]
  exact ConnectedProduct.const_homology_zero _ q hq
@[reassoc] lemma binary_insert_middle (p:Fin 2→Skeleton C) (q:ℕ) :
    insert p 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q =
        SSet.homologyMap (nerveMap (translate (p 0) (p 1) (p 0*p 1) rfl)) Z q ≫
          ComponentStable.inclusion (p 0*p 1) q := by
  rw [binary_insert_face]
  have h:=(NerveHomotopy.ofNatTrans (Functor.isoWhiskerLeft (wordInclude p 1) (binaryFaceMiddle (C:=C))).hom).congr_homologyMap Z q
  rw [h]
  have ht:=(NerveHomotopy.ofNatTrans (binaryRightTranslate p).hom).congr_homologyMap Z q
  rw [ht]
  change SSet.homologyMap (nerveMap (translate (p 0) (p 1) (p 0*p 1) rfl) ≫
    nerveMap (property (p 0*p 1)).ι) Z q = _
  rw [SSet.homologyMap_comp]
  rfl
lemma row_d10 (q:ℕ) (hq:q≠0) : (homologyRow (C:=C) q).d 1 0=0 := by
  apply IsZero.eq_zero_of_tgt
  exact nerve.positive_zero (fun U V:IntervalBar.Diagram C (Fin 1)=>⟨zeroHom C U V⟩) q hq
noncomputable def π (q:ℕ) (hq:q≠0) : (homologyRow (C:=C) q).X 1 ⟶ (homologyRow (C:=C) q).homology 1 :=
  ChainComplex.positiveπ _ 0 (row_d10 q hq)
@[reassoc (attr:=simp)] lemma d_π (q:ℕ) (hq:q≠0) : (homologyRow (C:=C) q).d 2 1 ≫ π q hq=0 :=
  ChainComplex.d_positiveπ _ 0 (row_d10 q hq)
noncomputable def oneIso (q:ℕ) : (homologyRow (C:=C) q).X 1 ≅ (nerve C).homology Z q := by
  exact @asIso (ModuleCat ℤ) _ _ _ _
    (NerveHomotopy.homologyMap_isIso (oneEval (C:=C)) Z q)
noncomputable def linearπ (q:ℕ) (hq:q≠0) : (nerve C).homology Z q ⟶ (homologyRow (C:=C) q).homology 1 :=
  (oneIso q).inv ≫ π q hq
@[reassoc (attr:=simp)] lemma oneIso_linearπ (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (nerveMap (oneEval (C:=C))) Z q ≫ linearπ q hq=π q hq := by
  change (oneIso (C:=C) q).hom ≫ (oneIso (C:=C) q).inv ≫ π q hq= _
  simp
lemma boundary_linearπ (v : Fin 2 → Skeleton C) (q : ℕ) (hq : q ≠ 0) :
    insert v 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q ≫ linearπ q hq -
    insert v 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q ≫ linearπ q hq +
    insert v 1 q ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z q ≫
      SSet.homologyMap (nerveMap oneEval) Z q ≫ linearπ q hq=0 := by
  have hd:=congrArg (fun f=>insert v 1 q ≫ f) (d_π (C:=C) q hq)
  rw [SimplicialFirstFinite.d21] at hd
  simp only [Preadditive.add_comp,Preadditive.sub_comp,Preadditive.comp_add,
    Preadditive.comp_sub,comp_zero] at hd
  rw [←oneIso_linearπ q hq] at hd
  exact hd

lemma binary_linearπ (v : Fin 2 → Skeleton C) (q : ℕ) (hq : q ≠ 0) :
    SSet.homologyMap (nerveMap (translate (v 0) (v 1) (v 0 * v 1) rfl)) Z q ≫
        ComponentStable.inclusion (v 0 * v 1) q ≫ linearπ q hq =
      ComponentStable.inclusion (v 1) q ≫ linearπ q hq := by
  have hd := boundary_linearπ v q hq
  have zeroFace := binary_insert_zero_assoc v q (linearπ (C:=C) q hq)
  have middleFace := binary_insert_middle_assoc v q (linearπ (C:=C) q hq)
  have lastFace := binary_insert_last_other_assoc v q hq (linearπ (C:=C) q hq)
  exact eq_of_boundary hd zeroFace middleFace (lastFace.trans zero_comp)

lemma translate_linearπ (r p s:Skeleton C) (h:r*p=s) (q:ℕ) (hq:q≠0) :
    SSet.homologyMap (nerveMap (translate r p s h)) Z q ≫ ComponentStable.inclusion s q ≫ linearπ q hq =
      ComponentStable.inclusion p q ≫ linearπ q hq := by
  subst s
  exact binary_linearπ ![r,p] q hq
noncomputable def cocone (q:ℕ) (hq:q≠0) : Cocone (homologyDiagram (C:=C) q) where
  pt := (homologyRow (C:=C) q).homology 1
  ι := {app p:=ComponentStable.inclusion p.back q ≫ linearπ q hq
        naturality {p s} f:=by
          change SSet.homologyMap (nerveMap (translate f.val p.back s.back f.property)) Z q ≫
            ComponentStable.inclusion s.back q ≫ linearπ q hq = _
          erw [translate_linearπ,Category.comp_id]
          rfl}
noncomputable def fromStable (q:ℕ) (hq:q≠0) : ComponentStable.object (C:=C) q ⟶
    (homologyRow (C:=C) q).homology 1 := colimit.desc (homologyDiagram q) (cocone q hq)
@[reassoc (attr:=simp)] lemma toStable_fromStable (q:ℕ) (hq:q≠0) :
    ComponentStable.toStable (C:=C) q ≫ fromStable q hq=linearπ q hq := by
  apply (ComponentCoproduct.homologyIsColimit C q).hom_ext
  intro p
  change ComponentStable.inclusion p.as q ≫ (ComponentStable.toStable q ≫ fromStable q hq)=_
  rw [←Category.assoc,ComponentStable.inclusion_toStable]
  exact colimit.ι_desc (cocone (C:=C) q hq) ((ActionCategory.objEquiv _ _) p.as)
end StableBarOne

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_BarBinaryBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open FreeChains ComponentStable

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def binaryMap : nerve (Diagram C (Fin 3)) ⟶ nerve C⊗nerve C :=
  nerveMap (eval 2) ≫ (PiSSet.nervePiIso (fun _:Fin 2=>C)).hom ≫
    (PiSSet.binaryIso (fun _:Fin 2=>nerve C)).hom
end IntervalBar.Diagram

end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Simplicial_FirstBarForwardLow
attribute [-instance] _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def lowOneHomologyIso :
    ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).homology 1 ≅
      (homologyRow (C:=C) 1).homology 2 := by
  let K := (RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c
  let L := homologyRow (C:=C) 1
  let e : K.sc' 2 1 0 ≅ L.sc' 3 2 1 :=
    ShortComplex.isoMk (gradedIso 2) (gradedIso 1) (gradedIso 0)
      (differential2 (C:=C)).symm (differential1 (C:=C)).symm
  exact (ShortComplex.homologyFunctor A).mapIso
    (K.isoSc' 2 1 0 (c.prev_eq' rfl) (c.next_eq' rfl) ≪≫ e ≪≫
      (L.isoSc' 3 2 1 (c.prev_eq' rfl) (c.next_eq' rfl)).symm)
end MarkedH1

end

end OAI
end


