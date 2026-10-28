-- Prove2me | Definitions.Def_OAIQ076M015
-- name    : OAIQ076M015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:08:58.767733+00:00
-- url     : https://prove2.me/theorems/aa18c0b4-247a-4910-ab59-a620690b8404
-- title:
--   Definitions bundle OAIQ076M015 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 257 declarations of OpenAI's Lean: 139 definitions, 3 inductive types or structures, 3 instances and 112 theorems. The definitions and types are `OAI.MinUncut.Costed.GraphRegisters.adjacencyProgram`, `OAI.MinUncut.Costed.GraphRegisters.initProgram`, `OAI.MinUncut.Costed.GraphRegisters.rawRenderer`, `OAI.MinUncut.Costed.GraphRegisters.renderLoop`, `OAI.MinUncut.Costed.GraphRegisters.tickProgram`, `OAI.MinUncut.Costed.SourceWords.demandExpressions`, `OAI.MinUncut.Costed.SourceWords.demandStageProgram`, `OAI.MinUncut.Costed.SourceWords.generatedDemands`, `OAI.MinUncut.Costed.SourceWords.generatedGraph`, `OAI.MinUncut.Costed.SourceWords.graphStageWords`, `OAI.MinUncut.Costed.SourceWords.inputTuple`, `OAI.MinUncut.Costed.SourceWords.leftExpr`, `OAI.MinUncut.Costed.SourceWords.localExpressions`, `OAI.MinUncut.Costed.SourceWords.queryWords`, `OAI.MinUncut.Costed.SourceWords.rightExpr`, `OAI.MinUncut.Costed.SourceWords.signExpr`, `OAI.MinUncut.Costed.SourceWords.signatureLookup`, `OAI.MinUncut.Costed.SourceWords.tupleDemands`, `OAI.MinUncut.Costed.SourceWords.tupleList`, `OAI.MinUncut.Enumeration.function`, `OAI.MinUncut.Enumeration.ofEncoding`, `OAI.MinUncut.Enumeration.pair`, `OAI.MinUncut.Outer.AllElementary`, `OAI.MinUncut.Outer.EdgeStatistic`, `OAI.MinUncut.Outer.Elementary`, `OAI.MinUncut.Outer.FamilyAlphabet`, `OAI.MinUncut.Outer.FamilyQuestion`, `OAI.MinUncut.Outer.FamilyVariable`, `OAI.MinUncut.Outer.LocalSample`, `OAI.MinUncut.Outer.LocalTemplate.Alphabet`, `OAI.MinUncut.Outer.LocalTemplate.Index`, `OAI.MinUncut.Outer.LocalTemplate.Query`, `OAI.MinUncut.Outer.LocalTemplate.Query.leftBase`, `OAI.MinUncut.Outer.LocalTemplate.Query.leftNumber`, `OAI.MinUncut.Outer.LocalTemplate.Query.leftTable`, `OAI.MinUncut.Outer.LocalTemplate.Query.localSign`, `OAI.MinUncut.Outer.LocalTemplate.Query.realize`, `OAI.MinUncut.Outer.LocalTemplate.Query.rightNumber`, `OAI.MinUncut.Outer.LocalTemplate.Query.rightTable`, `OAI.MinUncut.Outer.LocalTemplate.Signature` and 102 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FiniteGaussianLaw`, `MinUncut_Analysis_GaussianRows`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Encoding_QuestionEncoding`, `MinUncut_Encoding_SignatureEncoding`, `MinUncut_Estimates_AnalyticOuter`, `MinUncut_Estimates_Bridge`, `MinUncut_Estimates_ComparisonSoundness`, `MinUncut_Estimates_LiteralLocalTemplates`, `MinUncut_Estimates_LiteralTestQueries`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_SamplerAssembly`, `MinUncut_Estimates_SamplerCost`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_UniformGrid`, `MinUncut_Estimates_WeightedTestLaw`, `MinUncut_Games_OuterQuestions`, `MinUncut_Games_QuestionArithmetic`, `MinUncut_Games_QuestionExpressions`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_CanonicalSamplerGraph`, `MinUncut_Graphs_CompleteGraphProgram`, `MinUncut_Graphs_DemandExpressions`, `MinUncut_Graphs_DemandOrder`, `MinUncut_Graphs_EdgeMean`, `MinUncut_Graphs_GeneratedGraph`, `MinUncut_Graphs_GraphSize`, `MinUncut_Machines_ArenaMachineProgram`, `MinUncut_Machines_FiniteAlphabetBounds`, `MinUncut_PCP_HeaderAccumulate`, `MinUncut_PCP_RawInitialTables`, `MinUncut_Search_FiniteEnumeration`, `MinUncut_Search_FiniteQueryFamily`, `MinUncut_Search_RationalDenominatorArithmetic`, `MinUncut_Search_RationalInner`, `MinUncut_Search_SampleEnumeration`, `MinUncut_Search_TemplateArithmetic`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M006`, `OAIQ076M007` and `OAIQ076M008` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M022`, `OAIQ076M023`, `OAIQ076M024`, `OAIQ076M026` and `OAIQ076M027`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M006
import Definitions.Def_OAIQ076M007
import Definitions.Def_OAIQ076M008

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSmallBall
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

open scoped BigOperators
open MeasureTheory

lemma cellWeight_pos {T : ℚ} (hT : 0 < T) {L : ℕ} (hL : 0 < L) (r : ℕ) (i : Fin L) :
    0 < cellWeight r T L i := by
  exact div_pos (qIntegral_pos r (endpoint_lt hT hL i)) (qIntegral_pos r (by linarith))

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FiniteGaussianLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.alphabetNonempty _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

attribute [local instance] OAI.MinUncut.FiniteGaussian.coordsDecEq
lemma gridWeight_pos (g : GridData) (hT : 0<g.T) (hL : 0<g.L)
    (j : TestCoordinates m n → Fin g.L) : 0<gridWeight g j := by
  exact Finset.prod_pos (fun _ _ => cellWeight_pos (by exact_mod_cast hT) hL g.r _)

attribute [local irreducible] tableGrid scoreFamily

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_OuterQuestions
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {Name I : Type*}

def evaluatedTriple (s : Name → F₂) (E : Equation Name) : Triple := fun p => s (E.names p)
def Satisfied (s : Name → F₂) (E : Equation Name) : Prop := parity (evaluatedTriple s E)=E.rhs

open MinUncut.Inner
attribute [local instance] Classical.propDecidable

attribute [local instance] BinaryFourier.dualFintype

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient

structure ProofFamily (Name I : Type*) [Fintype I] where
  first : (U : I → Equation Name) → FoldedProof (FirstAlphabet U)
  second : (V : I → SecondQuestion Name) → FoldedProof (SecondAlphabet V)

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteQueryFamily
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

abbrev FamilyQuestion (Name I : Type*) := (I → Equation Name) ⊕ (I → SecondQuestion Name)

def FamilyAlphabet : FamilyQuestion Name I → Type _
  | .inl U => FirstAlphabet U
  | .inr Q => SecondAlphabet Q

def familyBase : (q : FamilyQuestion Name I) → FamilyAlphabet q
  | .inl U => fun j => origin (U j)
  | .inr _ => fun _ _ => 0

abbrev FamilyVariable (Name I : Type*) [Fintype I] := Variable (familyBase (Name := Name) (I := I))

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_QuestionEncoding
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences

def equationPair (N : ℕ) : Equation (Fin N) ≃ ((Fin 3 → Fin N) × F₂) where
  toFun E := (E.names,E.rhs)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def fieldEncoding : Encoding F₂ := ⟨2,Equiv.refl _⟩

def equationEncoding (N : ℕ) : Encoding (Equation (Fin N)) :=
  let a := ((Encoding.fin 3).function (Encoding.fin N)).prod fieldEncoding
  ⟨a.size,(equationPair N).trans a.code⟩

def secondQuestionEncoding (N : ℕ) : Encoding (SecondQuestion (Fin N)) :=
  (Encoding.fin N).sum (equationEncoding N)

def questionEncoding (N t : ℕ) : Encoding (FamilyQuestion (Fin N) (Fin t)) :=
  ((Encoding.fin t).function (equationEncoding N)).sum
    ((Encoding.fin t).function (secondQuestionEncoding N))

def ambientEncoding (t : ℕ) : Encoding (Fin t → Triple) :=
  (Encoding.fin t).function ((Encoding.fin 3).function fieldEncoding)

instance validDecidable {N : ℕ} (E : Equation (Fin N)) (a : Triple) : Decidable (Valid E a) :=
  inferInstanceAs (Decidable (parity a=E.rhs ∧ ∀p p', E.names p=E.names p' → a p=a p'))

def encodeFirst {N t : ℕ} (U : Fin t → Equation (Fin N)) (a : FirstAlphabet U) : Fin t → Triple :=
  fun j => (a j).val

def decodeFirst {N t : ℕ} (U : Fin t → Equation (Fin N)) (x : Fin t → Triple) :
    Option (FirstAlphabet U) :=
  if h : ∀j, Valid (U j) (x j) then some (fun j => ⟨x j,h j⟩) else none

lemma secondSlotCount_le {N : ℕ} (q : SecondQuestion (Fin N)) : secondSlotCount q≤3 := by
  cases q <;> norm_num [secondSlotCount]

def encodeSecond {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (a : SecondAlphabet Q) : Fin t → Triple :=
  fun j k => if h : k.val < secondSlotCount (Q j) then a j ⟨k.val,h⟩ else 0

def decodeSecond {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (x : Fin t → Triple) : SecondAlphabet Q :=
  fun j k => x j ⟨k.val,k.isLt.trans_le (secondSlotCount_le (Q j))⟩

def encodeAlphabet {N t : ℕ} : (q : FamilyQuestion (Fin N) (Fin t)) → FamilyAlphabet q → (Fin t → Triple)
  | .inl U => encodeFirst U
  | .inr Q => encodeSecond Q

def decodeAlphabet {N t : ℕ} : (q : FamilyQuestion (Fin N) (Fin t)) → (Fin t → Triple) → Option (FamilyAlphabet q)
  | .inl U => decodeFirst U
  | .inr Q => fun x => some (decodeSecond Q x)

def extendTable {N t : ℕ} (q : FamilyQuestion (Fin N) (Fin t)) (R : FamilyAlphabet q → Bool) :
    (Fin t → Triple) → Bool := fun x => ((decodeAlphabet q x).map R).getD false

def paddedVariableEncoding (N t : ℕ) :
    Encoding (FamilyQuestion (Fin N) (Fin t) × ((Fin t → Triple) → Bool)) :=
  (questionEncoding N t).prod ((ambientEncoding t).function Encoding.bool)

def variableCode {N t : ℕ} (v : FamilyVariable (Fin N) (Fin t)) : Fin (paddedVariableEncoding N t).size :=
  (paddedVariableEncoding N t).code (v.1,extendTable v.1 v.2.val)

lemma paddedVariableEncoding_size (N t : ℕ) :
    (paddedVariableEncoding N t).size=
      ((N^3*2)^t+(N+N^3*2)^t)*2^((2^3)^t) := rfl

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_EdgeMean
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
variable {Name I S : Type*} [Fintype I] [Fintype S]

abbrev EdgeStatistic (Name I : Type*) [Fintype I] :=
  (U : I → Equation Name) → (hidden : I → Bool) → (pos : I → Fin 3) → ℝ

def edgeMean (equations : S → Equation Name) (k : ℕ) (F : EdgeStatistic Name I) : ℝ :=
  𝔼 H : FixedSets I k, 𝔼 a : I → S, 𝔼 pos : I → Fin 3,
    F (fun i => equations (a i)) (hiddenSet H.val) pos

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_AnalyticOuter
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner OuterSmoothness MinUncut.Composition RowNoise GaussianHermite MeasureTheory
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] MinUncut.Inner.gradient
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n : ℕ}

def ProofFamily.atomTotal (f : ProofFamily Name I) (σ η θ : ℝ) : EdgeStatistic Name I :=
  fun U h pos => atomProbability (m := m) (n := n) (f.second (secondQuestion U h pos)) σ η θ

def ProofFamily.fourthTotal (f : ProofFamily Name I) (σ η : ℝ) : EdgeStatistic Name I :=
  fun U h pos => fourthError (m := m) (n := n) (projection U h pos)
    (f.first U) (f.second (secondQuestion U h pos)) σ η

end MinUncut.Outer

open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ComparisonSoundness
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner
attribute [local instance] Classical.propDecidable BinaryFourier.dualFintype
attribute [local irreducible] firstError secondError thirdError fourthError atomProbability
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

def ProofFamily.testErrors {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P)
    (f : ProofFamily Name I) (equations : S → Equation Name) : Test → ℝ
  | .first =>
  edgeMean equations O.k (fun U h pos => firstError (m := P.m) (n := P.n)
    (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))
  | .second => edgeMean equations O.k (fun U h pos => secondError (m := P.m) (n := P.n)
    (f.second (secondQuestion U h pos)) ((sourceEta J)^2/P.m) (sourceSigma J) (sourceEta J))
  | .third => edgeMean equations O.k (fun U h pos => thirdError (m := P.m) (n := P.n)
    (f.second (secondQuestion U h pos)) (sourceSigma J) (sourceEta J))
  | .fourth => edgeMean equations O.k (f.fourthTotal (m := P.m) (n := P.n) (sourceSigma J) (sourceEta J))

def budgets {J : ℝ} (P : InnerParameters J) (O : OuterParameters J P) : Test → ℝ
  | .first => 10*sourceSigma J
  | .second => 10*(sourceEta J+sourceEta J)
  | .third => (Fintype.card (Code P.m P.n):ℝ)⁻¹
  | .fourth => O.b4

lemma budgets_pos {J : ℝ} (hJ : 1 ≤ J) (P : InnerParameters J) (O : OuterParameters J P)
    (j : Test) : 0 < budgets P O j := by
  have hσ := sourceSigma_pos hJ
  have hη := sourceEta_pos hJ
  have hb := O.hb4
  cases j
  · exact mul_pos (by norm_num) hσ
  · exact mul_pos (by norm_num) (add_pos hη hη)
  · exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  · exact hb

attribute [local irreducible] edgeMean

attribute [local irreducible] ProofFamily.fourthTotal ProofFamily.atomTotal

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiteralTestQueries
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I] {m n : ℕ}

def comparison (q q' : FamilyQuestion Name I) (P : FamilyAlphabet q → Bool)
    (P' : FamilyAlphabet q' → Bool) : QueryDemand (A := FamilyAlphabet (Name := Name) (I := I)) :=
  ⟨⟨q,P⟩,⟨q',P'⟩,true⟩

def testQuery (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n) (z : Code m n)
    (t : ScoreIndex m n → Bool) : Test → QueryDemand (A := FamilyAlphabet (Name := Name) (I := I))
  | .first => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => t (false,labelCode B a)) (fun a => t (true,labelCode B a))
  | .second => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => t (true,labelCode B a)) (fun a => t (true,labelCode C a))
  | .third => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => Function.update (fun z => t (true,z)) z true (labelCode B a))
    (fun a => Function.update (fun z => t (true,z)) z false (labelCode B a))
  | .fourth => comparison (.inl U) (.inr (secondQuestion U h pos))
    (fun a => t (true,labelCode (pullbackFaces (projection U h pos) C) a))
    (fun a => t (true,labelCode C a))

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_WeightedTestLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I : Type*} [Fintype I] {m n : ℕ}

abbrev LocalSample (A : Type*) {V : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] (m n : ℕ) (g : GridData) :=
  FaceArray A m n × FaceArray A m n × Code m n × (TestCoordinates m n → Fin g.L)

def noiseWeight {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (a : ℚ) (B C : FaceArray A m n) : Test → ℚ
  | .second => RowNoise.rationalDensity a B C
  | _ => 1

def localWeight {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (a b : ℚ) (j : Test) (p : LocalSample A m n g) : ℚ :=
  (Fintype.card (FaceArray A m n):ℚ)⁻¹ * (Fintype.card (FaceArray A m n):ℚ)⁻¹ *
  (Fintype.card (Code m n):ℚ)⁻¹ * gridWeight g p.2.2.2 * noiseWeight a p.1 p.2.1 j / b

lemma localWeight_nonneg {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (g : GridData) (hT : 0<g.T) (hL : 0<g.L) {a b : ℚ} (ha : 0≤a) (ha1 : a≤1)
    (hb : 0<b) (j : Test) (p : LocalSample A m n g) : 0≤localWeight g a b j p := by
  have hg := (gridWeight_pos g hT hL p.2.2.2).le
  have hn : 0≤noiseWeight a p.1 p.2.1 j := by
    cases j with
    | second => exact RowNoise.rationalDensity_nonneg ha ha1 _ _
    | first => exact zero_le_one
    | third => exact zero_le_one
    | fourth => exact zero_le_one
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (inv_nonneg.mpr (Nat.cast_nonneg _))) hg) hn) hb.le

end MinUncut.Outer

namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

instance localSampleFintype {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (m n : ℕ) (g : GridData) : Fintype (LocalSample A m n g) := by
  unfold LocalSample
  infer_instance

def sampleFirst (equations : S → Equation Name) (o : OuterSample I S k) : I → Equation Name :=
  fun i => equations (o.2.1 i)

abbrev sampleSecond (equations : S → Equation Name) (o : OuterSample I S k) : I → SecondQuestion Name :=
  secondQuestion (sampleFirst equations o) (sampleHidden o) o.2.2

abbrev Elementary (equations : S → Equation Name) (k m n : ℕ) (g : GridData) :=
  Σ o : OuterSample I S k, LocalSample (SecondAlphabet (sampleSecond equations o)) m n g

def elementaryWeight (equations : S → Equation Name) (g : GridData) (a b : ℚ) (j : Test)
    (e : Elementary (I := I) equations k m n g) : ℚ :=
  (Fintype.card (OuterSample I S k):ℚ)⁻¹*localWeight g a b j e.2

def elementaryQuery (equations : S → Equation Name) (g : GridData) (σ η : ℚ) (j : Test)
    (e : Elementary (I := I) equations k m n g) : QueryDemand (A := FamilyAlphabet (Name := Name) (I := I)) :=
  testQuery (sampleFirst equations e.1) (sampleHidden e.1) e.1.2.2 e.2.1 e.2.2.1 e.2.2.2.1
    (rationalScoreTable σ η (fun i => midpoint g.T g.L (e.2.2.2.2 i))) j

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalInner
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian

def rationalBudgets (J : ℕ) (d : InnerData) (o : OuterData) : Test → ℚ
  | .first => 10*rationalSigma J
  | .second => 10*(rationalEta J+rationalEta J)
  | .third => (Fintype.card (Code d.m d.n):ℚ)⁻¹
  | .fourth => o.b4

lemma rationalBudgets_cast {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (j : Test) :
    (rationalBudgets J d o j:ℝ)=budgets (d.realize hJ hd) (o.realize hJ d hd ho) j := by
  cases j <;> simp only [rationalBudgets,budgets,Rat.cast_mul,Rat.cast_ofNat,
    Rat.cast_add,Rat.cast_inv,Rat.cast_natCast,rationalSigma_cast,rationalEta_cast] <;> rfl

lemma rationalBudgets_pos {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) (j : Test) : 0 < rationalBudgets J d o j := by
  apply (Rat.cast_pos (K := ℝ)).mp
  rw [rationalBudgets_cast hJ d hd o ho]
  exact budgets_pos (by exact_mod_cast hJ) _ _ j

def rationalWeight (J : ℕ) (d : InnerData) (o : OuterData) : ℚ :=
  ∑ j, (rationalBudgets J d o j)⁻¹

def tableAccuracy (J : ℕ) (d : InnerData) (o : OuterData) : ℚ :=
  1/(8*(1+rationalWeight J d o))

lemma rationalWeight_nonneg {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : 0 ≤ rationalWeight J d o :=
  Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (rationalBudgets_pos hJ d hd o ho j).le)

lemma tableAccuracy_pos {J : ℕ} (hJ : 1≤J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : 0<tableAccuracy J d o := by
  have := rationalWeight_nonneg hJ d hd o ho
  unfold tableAccuracy
  positivity

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerCost
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S]

abbrev AllElementary (equations : S → Equation Name) (k m n : ℕ) (g : GridData) :=
  Test × Elementary (I := I) equations k m n g

def allWeight (equations : S → Equation Name) {k m n : ℕ} (g : GridData) (a : ℚ) (b : Test → ℚ)
    (e : AllElementary (I := I) equations k m n g) : ℚ :=
  elementaryWeight equations g a (b e.1) e.1 e.2

def allDemand (equations : S → Equation Name) {k m n : ℕ} (g : GridData) (σ η : ℚ)
    (e : AllElementary (I := I) equations k m n g) : PathRealization.Demand (FamilyVariable Name I) :=
  (elementaryQuery equations g σ η e.1 e.2).signed familyBase

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_FiniteAlphabetBounds
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.localSampleFintype _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

lemma secondSlot_card_le (q : SecondQuestion Name) : Fintype.card (secondSlot q)≤8 := by
  cases q <;> norm_num [secondSlot,secondSlotCount,Fintype.card_fun,F₂,ZMod.card]

lemma secondAlphabet_card_le (Q : I → SecondQuestion Name) :
    Fintype.card (SecondAlphabet Q)≤2^(3*Fintype.card I) := by
  calc
    Fintype.card (SecondAlphabet Q)=∏ i, Fintype.card (secondSlot (Q i)) := Fintype.card_pi
    _ ≤ ∏ _i : I, 8 := Finset.prod_le_prod' (fun i _ => secondSlot_card_le (Q i))
    _ = 2^(3*Fintype.card I) := by rw [Finset.prod_const,Finset.card_univ,pow_mul]; norm_num

lemma forms_card_le {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A] :
    Fintype.card (Forms A)≤2^Fintype.card A := by
  have hh := Fintype.card_le_of_injective (fun f : Forms A => (f : A → F₂)) AffineMap.coeFn_injective
  simpa only [Fintype.card_fun,F₂,ZMod.card] using hh

lemma faceArray_card_le (Q : I → SecondQuestion Name) (m n : ℕ) :
    Fintype.card (FaceArray (SecondAlphabet Q) m n)≤faceCardBound (Fintype.card I) m n := by
  simp only [FaceArray,Fintype.card_fun,faceCardBound]
  exact Nat.pow_le_pow_left ((forms_card_le).trans (Nat.pow_le_pow_right (by omega) (secondAlphabet_card_le Q))) _

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalDenominatorArithmetic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof RationalDenominator OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

lemma noiseWeight_den {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
    (a : ℚ) (B C : FaceArray A m n) (j : Test) :
    (noiseWeight a B C j).den∣a.den^Fintype.card (Row m n) := by
  cases j with
  | second => exact rationalDensity_den a B C
  | first => exact one_dvd _
  | third => exact one_dvd _
  | fourth => exact one_dvd _

def gridDenominator (m n : ℕ) (g : GridData) : ℕ :=
  ∏ q : TestCoordinates m n → Fin g.L, (gridWeight g q).den

def budgetDenominator (b : Test → ℚ) : ℕ := ∏ j, (b j)⁻¹.den

def innerDenominator (t m n : ℕ) (g : GridData) (a : ℚ) (b : Test → ℚ) : ℕ :=
  (faceCardBound t m n).factorial*(faceCardBound t m n).factorial*
  Fintype.card (Code m n)*gridDenominator m n g*a.den^Fintype.card (Row m n)*budgetDenominator b

def samplerDenominator (I S : Type*) [Fintype I] [Fintype S] (k m n : ℕ)
    (g : GridData) (a : ℚ) (b : Test → ℚ) : ℕ :=
  Fintype.card (OuterSample I S k)*innerDenominator (Fintype.card I) m n g a b

lemma innerDenominator_pos (t m n : ℕ) (g : GridData) (a : ℚ) (b : Test → ℚ) :
    0 < innerDenominator t m n g a b := by
  have hC := Fintype.card_pos (α := Code m n)
  have hg : 0<gridDenominator m n g := denominatorProduct_pos _
  have hb : 0<budgetDenominator b := denominatorProduct_pos _
  unfold innerDenominator
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (Nat.factorial_pos _)
    (Nat.factorial_pos _)) hC) hg) (pow_pos (Rat.den_pos a) _)) hb

lemma localWeight_den (Q : I → SecondQuestion Name) (g : GridData) (a : ℚ) (b : Test → ℚ)
    (j : Test) (p : LocalSample (SecondAlphabet Q) m n g) :
    (localWeight g a (b j) j p).den∣innerDenominator (Fintype.card I) m n g a b := by
  have hf : ((Fintype.card (FaceArray (SecondAlphabet Q) m n):ℚ)⁻¹).den ∣
      (faceCardBound (Fintype.card I) m n).factorial := by
    rw [inv_nat Fintype.card_pos]
    exact Nat.dvd_factorial Fintype.card_pos (faceArray_card_le Q m n)
  unfold localWeight innerDenominator
  rw [div_eq_mul_inv]
  exact mul_dvd (mul_dvd (mul_dvd (mul_dvd (mul_dvd hf hf)
    (by rw [inv_nat Fintype.card_pos])) (denominator_dvd_product _ p.2.2.2))
    (noiseWeight_den a p.1 p.2.1 j)) (denominator_dvd_product _ j)

variable [Nonempty S]
lemma samplerDenominator_pos (hk : k≤Fintype.card I) (g : GridData) (a : ℚ) (b : Test → ℚ) :
    0 < samplerDenominator I S k m n g a b := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  exact mul_pos Fintype.card_pos (innerDenominator_pos _ _ _ _ _ _)

lemma elementaryWeight_den (equations : S → Equation Name) (hk : k≤Fintype.card I)
    (g : GridData) (a : ℚ) (b : Test → ℚ) (j : Test) (e : Elementary (I := I) equations k m n g) :
    (elementaryWeight equations g a (b j) j e).den∣samplerDenominator I S k m n g a b := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  exact mul_dvd (by rw [inv_nat Fintype.card_pos]) (localWeight_den _ g a b j e.2)

omit [Nonempty S] in
lemma samplerDenominator_polynomial (g : GridData) (a : ℚ) (b : Test → ℚ) :
    samplerDenominator I S k m n g a b=
      (Fintype.card (FixedSets I k)*3^Fintype.card I*innerDenominator (Fintype.card I) m n g a b)*
        Fintype.card S^Fintype.card I := by
  simp only [samplerDenominator,OuterSample,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
  ring
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Outer.validDecidable _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.innerDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.outerDataPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

namespace Parameters

def grid {J : ℕ} (P : Parameters J) : GridData :=
  tableGrid P.d.m P.d.n (tableAccuracy J P.d P.o) (tableAccuracy_pos P.hJ P.d P.hd P.o P.ho)

lemma k_le {J : ℕ} (P : Parameters J) : P.o.k≤P.o.t := P.ho.2.2.2.2.1

def denominator {J : ℕ} (P : Parameters J) (S : Type*) [Fintype S] : ℕ :=
  samplerDenominator (Fin P.o.t) S P.o.k P.d.m P.d.n P.grid
    (rationalRate J P.d) (rationalBudgets J P.d P.o)

lemma denominator_pos {J : ℕ} (P : Parameters J) : 0<P.denominator S :=
  samplerDenominator_pos (by simpa only [Fintype.card_fin] using P.k_le) _ _ _

abbrev Sample {J : ℕ} (P : Parameters J) (equations : S → Equation Name) :=
  AllElementary (I := Fin P.o.t) equations P.o.k P.d.m P.d.n P.grid

def weight {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) : ℚ :=
  allWeight equations P.grid (rationalRate J P.d) (rationalBudgets J P.d P.o) e

def demand {J : ℕ} (P : Parameters J) (equations : S → Equation Name) (e : P.Sample equations) :
    PathRealization.Demand (FamilyVariable Name (Fin P.o.t)) :=
  allDemand equations P.grid (rationalSigma J) (rationalEta J) e

end Parameters
end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena

open Turing.ToPartrec

lemma small_succ_get (a : Expr) (j : Fin 4) : Small (.add (g a j) (c 1)) := fun v=>by
  have h := get_le_maximum v a j
  change (g a j).eval v+1≤_
  omega
lemma small_pred_get (a : Expr) (j : Fin 4) : Small (.sub (g a j) (c 1)) := fun v=>by
  have h := get_le_maximum v a j
  change (g a j).eval v-1≤_
  omega

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_HeaderAccumulate
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceBasePhase

open _root_.Turing Complexity
open Target SourceContexts SourceOccurrences
open MinUncutGames.Reduction.MachineSubstitution

abbrev Layout := MachineHorner.Layout 2

end MinUncutGames.Foundations.Hastad.SourceBasePhase

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

open Target

def mismatchBits {q : Nat} (V : FiniteVerifier q) (A : Fin V.«variables» → Bool)
    (e : Fin V.events) (p : PatternIndex q) : List Bool :=
  List.ofFn (fun i => (forbiddenLiteral V e p i).eval A)

@[simp] theorem mismatchBits_length {q : Nat} (V : FiniteVerifier q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (mismatchBits V A e p).length = q := by simp [mismatchBits]

theorem mismatchFill_length {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q) :
    (fillBits (mismatchBits V A e p)).length = q - 3 := by
  have h := fillBits_length (mismatchBits V A e p) (by simpa using hq)
  rw [mismatchBits_length] at h
  omega

def mismatchFill {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) : Bool :=
  (fillBits (mismatchBits V A e p))[j.val]'(by
    rw [mismatchFill_length V hq A e p]
    exact j.isLt)

def extendAssignment {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : Fin (outputVariables V) → Bool :=
  Fin.addCases A (fun k : Fin (auxiliaryCount V) =>
    let pair : Fin (V.events * (patterns q).length) × Fin (q - 3) := finProdFinEquiv.symm k
    let ep : Fin V.events × PatternIndex q := finProdFinEquiv.symm pair.1
    mismatchFill V hq A ep.1 ep.2 pair.2)

@[simp] theorem extend_old {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (v : Fin V.«variables») :
    extendAssignment V hq A (oldIndex V v) = A v := by
  simp [extendAssignment, oldIndex]

@[simp] theorem extend_fresh {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) (e : Fin V.events) (p : PatternIndex q)
    (j : Fin (q - 3)) :
    extendAssignment V hq A (freshIndex V e p j) = mismatchFill V hq A e p j := by
  unfold extendAssignment freshIndex auxiliaryCount
  rw [Fin.addCases_right]
  simp only [Equiv.symm_apply_apply]

@[simp] theorem restrict_extend {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q)
    (A : Fin V.«variables» → Bool) : restrictAssignment V (extendAssignment V hq A) = A := by
  funext v
  exact extend_old V hq A v

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_FiniteEnumeration
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut
open MinUncutGames.Foundations.Hastad.SourceOccurrences

namespace Enumeration
variable {A B : Type}

def ofEncoding (e : Encoding A) : Enumeration A where
  values := e.enumerate
  nodup := e.nodup_enumerate
  complete := e.mem_enumerate

def pair [DecidableEq A] [DecidableEq B] (E : Enumeration A) (F : Enumeration B) : Enumeration (A × B) :=
  ofEncoding (E.encoding.prod F.encoding)

def function [DecidableEq A] [DecidableEq B] (E : Enumeration A) (F : Enumeration B) : Enumeration (A → B) :=
  ofEncoding (E.encoding.function F.encoding)

end Enumeration
end MinUncut

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_SampleEnumeration
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
open MinUncutGames.Foundations.Hastad.SourceOccurrences

namespace SampleEnumeration

def fin (n : ℕ) : Enumeration (Fin n) := Enumeration.ofEncoding (Encoding.fin n)
def field : Enumeration F₂ := Enumeration.ofEncoding fieldEncoding

def point (m n : ℕ) : Enumeration (Point m n) := (fin m).function (fin n)
def row (m n : ℕ) : Enumeration (Row m n) :=
  (fin m).sigma (fun i => ((fin m).subtype (fun j => j≠i)).function (fin n))

local instance codeEq (m n : ℕ) : DecidableEq (Code m n) :=
  Subtype.instDecidableEq

def code (m n : ℕ) : Enumeration (Code m n) :=
  ((row m n).function field).image (faceSum m n).rangeRestrict (by
    intro z
    obtain ⟨f,hf⟩ := z.property
    exact ⟨f,Subtype.ext hf⟩)

local instance codeType (m n : ℕ) : Fintype (Code m n) :=
  Fintype.ofList (code m n).values (code m n).complete

abbrev Slots {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) :=
  Σ j, Fin (secondSlotCount (Q j))

def slots {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) : Enumeration (Slots Q) :=
  (fin t).sigma (fun j => fin (secondSlotCount (Q j)))

def formsPiEquiv (A : Type) [Fintype A] [DecidableEq A] :
    Forms (A → F₂) ≃ F₂ × (A → F₂) :=
  (AffineMap.toConstProdLinearMap F₂).toEquiv.trans
    (Equiv.prodCongr (Equiv.refl F₂) (LinearEquiv.piRing F₂ F₂ A F₂).toEquiv)

def formsCurryEquiv (A : Type) (B : A → Type) :
    Forms (∀a, B a → F₂) ≃ Forms ((Σa, B a) → F₂) :=
  AffineEquiv.arrowCongrEquiv
    (LinearEquiv.piCurry F₂ (fun (_ : A) (_ : B _) => F₂)).symm.toAffineEquiv
    (AffineEquiv.refl F₂ F₂)

def formsEquiv {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) :
    Forms (SecondAlphabet Q) ≃ F₂ × (Slots Q → F₂) :=
  (formsCurryEquiv (Fin t) (fun j => Fin (secondSlotCount (Q j)))).trans (formsPiEquiv (Slots Q))

local instance formEq {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) :
    DecidableEq (Forms (SecondAlphabet Q)) :=
  fun f g => decidable_of_iff (formsEquiv Q f=formsEquiv Q g) (formsEquiv Q).injective.eq_iff

def forms {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) : Enumeration (Forms (SecondAlphabet Q)) :=
  (field.pair ((slots Q).function field)).image (formsEquiv Q).symm (formsEquiv Q).symm.surjective

def arrays {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) :
    Enumeration (FaceArray (SecondAlphabet Q) m n) := (row m n).function (forms Q)

def coordinates (m n : ℕ) : Enumeration (TestCoordinates m n) :=
  Enumeration.ofEncoding ((point m n).encoding.sum ((point m n).encoding.sum (code m n).encoding))

def localSample {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) (g : GridData) :
    Enumeration (LocalSample (SecondAlphabet Q) m n g) := by
  letI : DecidableEq (Forms (SecondAlphabet Q)) := formEq Q
  letI : DecidableEq (FaceArray (SecondAlphabet Q) m n) := inferInstanceAs (DecidableEq (Row m n → Forms (SecondAlphabet Q)))
  exact (arrays Q m n).pair ((arrays Q m n).pair ((code m n).pair ((coordinates m n).function (fin g.L))))

def finsets (t : ℕ) : Enumeration (Finset (Fin t)) :=
  ((fin t).function (Enumeration.ofEncoding Encoding.bool)).image
    (fun f => Finset.univ.filter (fun j => f j=true)) (by
      intro S
      refine ⟨fun j => decide (j∈S),?_⟩
      ext j
      simp)

def fixedSets (t k : ℕ) : Enumeration (FixedSets (Fin t) k) :=
  (finsets t).subtype (fun H => H.card=k)

def outerSample (t s k : ℕ) : Enumeration (OuterSample (Fin t) (Fin s) k) :=
  (fixedSets t k).pair (((fin t).function (fin s)).pair ((fin t).function (fin 3)))

local instance localEq_rc0bedc_1 {N t : ℕ} (Q : Fin t → SecondQuestion (Fin N)) (m n : ℕ) (g : GridData) :
    DecidableEq (LocalSample (SecondAlphabet Q) m n g) := by
  letI : DecidableEq (Forms (SecondAlphabet Q)) := formEq Q
  letI : DecidableEq (FaceArray (SecondAlphabet Q) m n) :=
    inferInstanceAs (DecidableEq (Row m n → Forms (SecondAlphabet Q)))
  exact fun f h => decidable_of_iff
    (f.1=h.1 ∧ f.2.1=h.2.1 ∧ f.2.2.1=h.2.2.1 ∧ f.2.2.2=h.2.2.2)
    (by constructor <;> intro he <;> aesop)
def second {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) : Fin t → SecondQuestion (Fin N) :=
  fun j => if j∈o.1.val then Sum.inl ((eqs (o.2.1 j)).names (o.2.2 j)) else Sum.inr (eqs (o.2.1 j))

lemma second_eq {N s t : ℕ} (eqs : Fin s → Equation (Fin N)) {k : ℕ}
    (o : OuterSample (Fin t) (Fin s) k) : second eqs o=sampleSecond eqs o := by
  funext j
  simp [second,sampleSecond,secondQuestion,sampleFirst,sampleHidden,hiddenSet,slotQuestion]

end SampleEnumeration
end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Bridge
attribute [-instance] _root_.OAI.MinUncut.Preprocess.gridDataPrimcodable _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.SourceBridge
open MinUncut.Inner MinUncut.Outer
open MinUncutGames.Reduction
attribute [local instance] Classical.propDecidable

def boolField (b : Bool) : F₂ := if b then 1 else 0

def equation {N : Type} (e : CloneGap.Equation N) : Equation N :=
  ⟨![e.first,e.second,e.third],boolField e.rhs⟩

def equations (input : SourceEncoding.Input) (i : Fin input.equations.length) :
    Equation (Fin input.«variables») := equation input.equations[i]

end MinUncut.SourceBridge

end
namespace MinUncut.Costed.SourceWords
open MinUncutGames.Reduction MinUncut.SourceBridge

lemma flatMap_word {N : ℕ} (xs : List (CloneGap.Equation (Fin N))) (i : ℕ) (hi : i<xs.length) (p : Fin 4) :
    ((xs.flatMap SourceEncoding.equationWords).drop (4*i+p.val)).headI=
      ((SourceEncoding.equationWords xs[i]).drop p.val).headI := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons e xs ih =>
    cases i with
    | zero =>
      fin_cases p <;> simp [SourceEncoding.equationWords]
    | succ i =>
      have hh : i<xs.length := by simpa using hi
      have he : 4*(i+1)+p.val=(((4*i+p.val)+1)+1)+1+1 := by omega
      rw [he]
      simpa only [List.flatMap_cons,SourceEncoding.equationWords,List.cons_append,
        List.nil_append,List.drop_succ_cons,List.getElem_cons_succ] using ih i hh

lemma input_word (input : SourceEncoding.Input) (i : Fin input.equations.length) (p : Fin 4) :
    ((SourceEncoding.inputWords input).drop (2+4*i.val+p.val)).headI=
      ((SourceEncoding.equationWords input.equations[i]).drop p.val).headI := by
  have he : 2+4*i.val+p.val=(4*i.val+p.val)+1+1 := by omega
  rw [he]
  simpa only [SourceEncoding.inputWords,List.cons_append,List.nil_append,List.drop_succ_cons,Fin.getElem_fin] using
    flatMap_word input.equations i.val i.isLt p

lemma input_name (input : SourceEncoding.Input) (i : Fin input.equations.length) (p : Fin 3) :
    ((SourceEncoding.inputWords input).drop (2+4*i.val+p.val)).headI=
      ((equations input i).names p).val := by
  rw [input_word input i ⟨p.val,by omega⟩]
  fin_cases p <;> rfl

lemma input_rhs (input : SourceEncoding.Input) (i : Fin input.equations.length) :
    ((SourceEncoding.inputWords input).drop (2+4*i.val+3)).headI=(equations input i).rhs.val := by
  rw [input_word input i ⟨3,by decide⟩]
  simp only [SourceEncoding.equationWords,List.drop_succ_cons,List.drop_zero,List.headI_cons,
    equations,equation,boolField,Fin.getElem_fin]
  cases input.equations[i.val].rhs <;> norm_num [ZMod.val_one_eq_one_mod]

end MinUncut.Costed.SourceWords

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable

variable {I Name : Type*}

abbrev Alphabet (h : I → Bool) := (j : I) → Fin (width (h j)) → F₂

lemma slot_width (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) (j : I) :
    secondSlotCount (secondQuestion U h pos j)=width (h j) := by
  cases hh : h j <;> simp [secondQuestion,slotQuestion,hh,secondSlotCount,width]

def alphabetEquiv (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) :
    SecondAlphabet (secondQuestion U h pos) ≃ₗ[F₂] Alphabet h where
  toFun a j k := a j (Fin.cast (slot_width U h pos j).symm k)
  invFun a j k := a j (Fin.cast (slot_width U h pos j) k)
  left_inv a := by funext j k; simp
  right_inv a := by funext j k; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

section Transport
variable {V A W B : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
  [AddCommGroup W] [Module F₂ W] [AddTorsor W B] {m n : ℕ}

def formsPull (e : A ≃ᵃ[F₂] B) : Forms B ≃ Forms A :=
  e.symm.arrowCongrEquiv (AffineEquiv.refl F₂ F₂)

@[simp] lemma formsPull_apply (e : A ≃ᵃ[F₂] B) (f : Forms B) (a : A) :
    formsPull e f a=f (e a) := rfl

def facesPull (e : A ≃ᵃ[F₂] B) : FaceArray B m n ≃ FaceArray A m n :=
  Equiv.piCongrRight (fun _=>formsPull e)

variable [Fintype A] [Fintype B]

def samplePull (e : A ≃ᵃ[F₂] B) (g : GridData) :
    LocalSample B m n g ≃ LocalSample A m n g :=
  (facesPull e).prodCongr ((facesPull e).prodCongr (Equiv.refl _))

lemma noiseWeight_pull (e : A ≃ᵃ[F₂] B) (a : ℚ) (C D : FaceArray B m n) (j : Test) :
    noiseWeight a (facesPull e C) (facesPull e D) j=noiseWeight a C D j := by
  cases j <;> try rfl
  simp only [noiseWeight,RowNoise.rationalDensity]
  apply Finset.prod_congr rfl
  intro r _
  have hc : Fintype.card (Forms A)=Fintype.card (Forms B) := (Fintype.card_congr (formsPull e)).symm
  have he : facesPull e D r=facesPull e C r ↔ D r=C r := (formsPull e).injective.eq_iff
  simp only [RowNoise.rationalRowDensity,hc,he]

lemma localWeight_pull (e : A ≃ᵃ[F₂] B) (g : GridData) (a b : ℚ) (j : Test)
    (p : LocalSample B m n g) : localWeight g a b j (samplePull e g p)=localWeight g a b j p := by
  have hc : Fintype.card (FaceArray A m n)=Fintype.card (FaceArray B m n) :=
    (Fintype.card_congr (facesPull (m:=m) (n:=n) e)).symm
  simp only [localWeight,samplePull,Equiv.prodCongr_apply,Prod.map,Equiv.refl_apply,hc,noiseWeight_pull]
end Transport

variable [Fintype I] {m n : ℕ}

def localSampleEquiv (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) (g : GridData) :
    LocalSample (Alphabet h) m n g ≃ LocalSample (SecondAlphabet (secondQuestion U h pos)) m n g :=
  samplePull (alphabetEquiv U h pos).toAffineEquiv g

lemma localSample_weight (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (g : GridData) (a b : ℚ) (j : Test) (p : LocalSample (Alphabet h) m n g) :
    localWeight g a b j (localSampleEquiv U h pos g p)=localWeight g a b j p :=
  localWeight_pull _ _ _ _ _ _

end MinUncut.Outer.LocalTemplate

end
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
namespace SampleEnumeration

local instance bridgeCodeDecidableEq (m n : ℕ) : DecidableEq (Code m n) := codeEq m n

def testQuery {N t m n : ℕ} (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (B C : FaceArray (SecondAlphabet (secondQuestion U h pos)) m n) (z : Code m n)
    (s : ScoreIndex m n → Bool) : Test → QueryDemand (A := FamilyAlphabet (Name := Fin N) (I := Fin t))
  | .first => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => s (false,labelCode B a)) (fun a => s (true,labelCode B a))
  | .second => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => s (true,labelCode B a)) (fun a => s (true,labelCode C a))
  | .third => comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
    (fun a => Function.update (fun z => s (true,z)) z true (labelCode B a))
    (fun a => Function.update (fun z => s (true,z)) z false (labelCode B a))
  | .fourth => comparison (.inl U) (.inr (secondQuestion U h pos))
    (fun a => s (true,labelCode (pullbackFaces (projection U h pos) C) a))
    (fun a => s (true,labelCode C a))

end SampleEnumeration
end MinUncut.Outer

noncomputable section
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*}

def projectSlot : (h : Bool) → Fin 3 → Triple → (Fin (width h) → F₂)
  | false,_,x => x
  | true,p,x => fun _=>x p

def project (h : I → Bool) (pos : I → Fin 3) (x : I → Triple) : Alphabet h :=
  fun j=>projectSlot (h j) (pos j) (x j)

def decode (h : I → Bool) (x : I → Triple) : Alphabet h :=
  project h (fun _=>0) x

def originTable (U : I → Equation Name) : I → Triple := fun j _=>(U j).rhs

lemma slotCount_width (E : Equation Name) (b : Bool) (p : Fin 3) :
    secondSlotCount (slotQuestion E b p)=width b := by cases b <;> rfl

lemma slotProjection_cast (E : Equation Name) (b : Bool) (p : Fin 3) (a : alphabet E)
    (k : Fin (width b)) :
    slotProjection E b p a (Fin.cast (slotCount_width E b p).symm k)=projectSlot b p a.val k := by
  cases b <;> rfl

lemma alphabetEquiv_projection (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (a : FirstAlphabet U) :
    alphabetEquiv U h pos (projection U h pos a)=project h pos (fun j=>(a j).val) := by
  funext j k
  exact slotProjection_cast (U j) (h j) (pos j) (a j) k

lemma alphabetEquiv_zero (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3) :
    alphabetEquiv U h pos 0=0 := map_zero _

variable {N t : ℕ}

lemma decodeSlot (b : Bool) (x : Triple) (k : Fin (width b))
    (hk : k.val<3) : x ⟨k.val,hk⟩=projectSlot b 0 x k := by
  cases b
  · rfl
  · have he : k.val=0 := by have hi:=k.isLt; change k.val<1 at hi; omega
    change x ⟨k.val,hk⟩=x 0
    congr 1
    exact Fin.ext he

lemma alphabetEquiv_decode (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (x : Fin t → Triple) :
    alphabetEquiv U h pos (decodeSecond (secondQuestion U h pos) x)=decode h x := by
  funext j k
  exact decodeSlot (h j) (x j) k _

lemma extend_second_rep (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    extendTable (.inr (secondQuestion U h pos))
      (rep (familyBase (.inr (secondQuestion U h pos))) (fun a=>P (alphabetEquiv U h pos a))).val =
      (fun x=>P 0 == P (decode h x)) := by
  funext x
  simp only [extendTable,decodeAlphabet,rep,familyBase]
  change (P (alphabetEquiv U h pos 0) ==
    P (alphabetEquiv U h pos (decodeSecond (secondQuestion U h pos) x)))=_
  rw [alphabetEquiv_zero,alphabetEquiv_decode]

lemma extend_first_rep (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    extendTable (.inl U)
      (rep (familyBase (.inl U)) (fun a=>P (alphabetEquiv U h pos (projection U h pos a)))).val =
      (fun x=>if ∀j,Valid (U j) (x j) then
        P (project h pos (originTable U)) == P (project h pos x) else false) := by
  funext x
  simp only [extendTable,decodeAlphabet]
  by_cases hx : ∀j,Valid (U j) (x j)
  · simp only [decodeFirst,dite_eq_left hx,ite_eq_left hx,
      rep,familyBase,alphabetEquiv_projection]
    exact congrArg (fun a => P (project h pos (originTable U)) == P a)
      (alphabetEquiv_projection U h pos (fun j => ⟨x j,hx j⟩))
  · simp only [decodeFirst,dite_eq_right hx,ite_eq_right hx]
    rfl

lemma first_base (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    P (alphabetEquiv U h pos (projection U h pos (familyBase (.inl U))))=
      P (project h pos (originTable U)) := by
  exact congrArg P (alphabetEquiv_projection U h pos (familyBase (.inl U)))

lemma second_base (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3)
    (P : Alphabet h → Bool) :
    P (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos))))=P 0 := by
  exact congrArg P (alphabetEquiv_zero U h pos)

open scoped BigOperators
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable
variable {Name I S : Type} [Fintype I] [Fintype S] {k m n : ℕ} {g : GridData}

abbrev Index (I : Type) [Fintype I] (k m n : ℕ) (g : GridData) :=
  Test × Σ H : FixedSets I k, (I → Fin 3) × LocalSample (Alphabet (hiddenSet H.val)) m n g

instance indexFintype : Fintype (Index I k m n g) := by unfold Index; infer_instance

def occurrence (eqs : S → Equation Name) : ((I → S) × Index I k m n g) ≃ AllElementary (I := I) eqs k m n g where
  toFun p := (p.2.1,⟨(p.2.2.1,p.1,p.2.2.2.1),
    localSampleEquiv (fun i=>eqs (p.1 i)) (hiddenSet p.2.2.1.val) p.2.2.2.1 g p.2.2.2.2⟩)
  invFun p := (p.2.1.2.1,p.1,⟨p.2.1.1,p.2.1.2.2,
    (localSampleEquiv (sampleFirst eqs p.2.1) (sampleHidden p.2.1) p.2.1.2.2 g).symm p.2.2⟩)
  left_inv p := by
    rcases p with ⟨u,j,H,pos,p⟩
    simp only [localSampleEquiv]
    rfl
  right_inv p := by
    rcases p with ⟨j,⟨⟨H,u,pos⟩,p⟩⟩
    simp only [localSampleEquiv]
    rfl

def weight (a : ℚ) (b : Test → ℚ) (e : Index I k m n g) : ℚ :=
  localWeight g a (b e.1) e.1 e.2.2.2

def repetitions (a : ℚ) (b : Test → ℚ) (e : Index I k m n g) : ℕ :=
  multiplicity (innerDenominator (Fintype.card I) m n g a b) (weight a b e)

lemma occurrence_weight (eqs : S → Equation Name) (a : ℚ) (b : Test → ℚ)
    (u : I → S) (e : Index I k m n g) :
    allWeight eqs g a b (occurrence eqs (u,e))=
      (Fintype.card (OuterSample I S k):ℚ)⁻¹*weight a b e := by
  change _*localWeight g a (b e.1) e.1
    (localSampleEquiv (fun i=>eqs (u i)) (hiddenSet e.2.1.val) e.2.2.1 g e.2.2.2)=_
  rw [localSample_weight]
  rfl

lemma weight_nonneg (hT : 0<g.T) (hL : 0<g.L) {a : ℚ} (ha : 0≤a) (ha1 : a≤1)
    (b : Test → ℚ) (hb : ∀j,0<b j) (e : Index I k m n g) : 0≤weight a b e :=
  localWeight_nonneg g hT hL ha ha1 (hb e.1) e.1 e.2.2.2

omit [Fintype S] in
lemma weight_den (eqs : S → Equation Name) (u : I → S) (a : ℚ) (b : Test → ℚ)
    (e : Index I k m n g) : (weight a b e).den ∣ innerDenominator (Fintype.card I) m n g a b := by
  have hh := localWeight_den (secondQuestion (fun i=>eqs (u i)) (hiddenSet e.2.1.val) e.2.2.1)
    g a b e.1 (localSampleEquiv (fun i=>eqs (u i)) (hiddenSet e.2.1.val) e.2.2.1 g e.2.2.2)
  rw [localSample_weight] at hh
  exact hh

lemma occurrence_multiplicity [Nonempty S] (eqs : S → Equation Name) (hk : k≤Fintype.card I)
    (hT : 0<g.T) (hL : 0<g.L) {a : ℚ} (ha : 0≤a) (ha1 : a≤1)
    (b : Test → ℚ) (hb : ∀j,0<b j) (u : I → S) (e : Index I k m n g) :
    multiplicity (samplerDenominator I S k m n g a b)
      (allWeight eqs g a b (occurrence eqs (u,e)))=repetitions a b e := by
  let : Nonempty (FixedSets I k) := fixedSets_nonempty hk
  have hc : (0:ℚ)<Fintype.card (OuterSample I S k) := by exact_mod_cast Fintype.card_pos
  have hw := weight_nonneg hT hL ha ha1 b hb e
  have he := occurrence_weight eqs a b u e
  have hd := elementaryWeight_den eqs hk g a b e.1 (occurrence eqs (u,e)).2
  change (allWeight eqs g a b (occurrence eqs (u,e))).den ∣ _ at hd
  apply Nat.cast_injective (R := ℚ)
  rw [multiplicity_cast (by rw [he]; positivity) hd, repetitions,
    multiplicity_cast hw (weight_den eqs u a b e),he]
  simp only [samplerDenominator,Nat.cast_mul]
  field_simp

open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {I Name : Type*} [Fintype I] {m n : ℕ}

structure Query (h : I → Bool) where
  first : Bool
  left : Alphabet h → Bool
  right : Alphabet h → Bool

def query (h : I → Bool) (B C : FaceArray (Alphabet h) m n) (z : Code m n)
    (s : ScoreIndex m n → Bool) : Test → Query h
  | .first => ⟨false,(fun a=>s (false,labelCode B a)),(fun a=>s (true,labelCode B a))⟩
  | .second => ⟨false,(fun a=>s (true,labelCode B a)),(fun a=>s (true,labelCode C a))⟩
  | .third => ⟨false,(fun a=>Function.update (fun z=>s (true,z)) z true (labelCode B a)),
                     (fun a=>Function.update (fun z=>s (true,z)) z false (labelCode B a))⟩
  | .fourth => ⟨true,(fun a=>s (true,labelCode C a)),(fun a=>s (true,labelCode C a))⟩

def Query.realize {h : I → Bool} (T : Query h) (U : I → Equation Name) (pos : I → Fin 3) :
    QueryDemand (A := FamilyAlphabet (Name := Name) (I := I)) :=
  if T.first then
    comparison (.inl U) (.inr (secondQuestion U h pos))
      (fun a=>T.left (alphabetEquiv U h pos (projection U h pos a)))
      (fun a=>T.right (alphabetEquiv U h pos a))
  else
    comparison (.inr (secondQuestion U h pos)) (.inr (secondQuestion U h pos))
      (fun a=>T.left (alphabetEquiv U h pos a))
      (fun a=>T.right (alphabetEquiv U h pos a))

omit [Fintype I] in
lemma query_realize (U : I → Equation Name) (h : I → Bool) (pos : I → Fin 3)
    (B C : FaceArray (Alphabet h) m n) (z : Code m n) (s : ScoreIndex m n → Bool) (j : Test) :
    (query h B C z s j).realize U pos =
      testQuery U h pos (facesPull (alphabetEquiv U h pos).toAffineEquiv B)
        (facesPull (alphabetEquiv U h pos).toAffineEquiv C) z s j := by
  cases j <;> simp only [query,Query.realize,Bool.false_eq_true,ite_false,ite_true,testQuery]
  all_goals apply congrArg₂ (comparison _ _)
  all_goals funext a
  all_goals rfl

structure Signature (I : Type*) where
  rhs : I → F₂
  same : I → Fin 3 → Fin 3 → Bool

def signature (U : I → Equation Name) : Signature I :=
  ⟨fun i=>(U i).rhs,fun i p q=>decide ((U i).names p=(U i).names q)⟩

def Signature.Valid (s : Signature I) (x : I → Triple) : Prop :=
  ∀i, parity (x i)=s.rhs i ∧ ∀p q,s.same i p q=true → x i p=x i q

def Signature.origin (s : Signature I) : I → Triple := fun i _=>s.rhs i

omit [Fintype I] in
lemma signature_valid (U : I → Equation Name) (x : I → Triple) :
    (signature U).Valid x ↔ ∀i,Valid (U i) (x i) := by
  simp only [Signature.Valid,signature,Valid,decide_eq_true_eq]
omit [Fintype I] in
lemma signature_origin (U : I → Equation Name) : (signature U).origin=originTable U := rfl

variable {N t : ℕ}

def Query.leftBase {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3) (s : Signature (Fin t)) : Bool :=
  if T.first then T.left (project h pos s.origin) else T.left 0

def Query.leftTable {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3)
    (s : Signature (Fin t)) : (Fin t → Triple) → Bool :=
  if T.first then fun x=>if s.Valid x then T.leftBase pos s == T.left (project h pos x) else false
    else fun x=>T.left 0 == T.left (decode h x)

def Query.rightTable {h : Fin t → Bool} (T : Query h) : (Fin t → Triple) → Bool :=
  fun x=>T.right 0 == T.right (decode h x)

def Query.localSign {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3) (s : Signature (Fin t)) : Bool :=
  T.leftBase pos s == T.right 0

lemma Query.left_extended {h : Fin t → Bool} (T : Query h) (U : Fin t → Equation (Fin N))
    (pos : Fin t → Fin 3) :
    extendTable (T.realize U pos).left.1 (rep (familyBase (T.realize U pos).left.1)
      (T.realize U pos).left.2).val = T.leftTable pos (signature U) := by
  rcases T with ⟨first,left,right⟩
  cases first
  · exact extend_second_rep U h pos left
  · change extendTable (.inl U) (rep (familyBase (.inl U))
        (fun a=>left (alphabetEquiv U h pos (projection U h pos a)))).val =
        (fun x=>if (signature U).Valid x then
          left (project h pos (signature U).origin) == left (project h pos x) else false)
    simp_rw [signature_valid]
    exact extend_first_rep U h pos left

lemma Query.right_extended {h : Fin t → Bool} (T : Query h) (U : Fin t → Equation (Fin N))
    (pos : Fin t → Fin 3) :
    extendTable (T.realize U pos).right.1 (rep (familyBase (T.realize U pos).right.1)
      (T.realize U pos).right.2).val = T.rightTable := by
  rcases T with ⟨first,left,right⟩
  cases first <;> exact extend_second_rep U h pos right

lemma Query.signed_equal {h : Fin t → Bool} (T : Query h) (U : Fin t → Equation (Fin N))
    (pos : Fin t → Fin 3) :
    ((T.realize U pos).signed familyBase).equal=T.localSign pos (signature U) := by
  rcases T with ⟨first,left,right⟩
  cases first
  · change (left (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos)))) ==
      right (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos))))) = (left 0 == right 0)
    rw [second_base U h pos left,second_base U h pos right]
  · change (left (alphabetEquiv U h pos (projection U h pos (familyBase (.inl U)))) ==
      right (alphabetEquiv U h pos (familyBase (.inr (secondQuestion U h pos))))) =
      (left (project h pos (signature U).origin) == right 0)
    rw [first_base U h pos left,second_base U h pos right,signature_origin]

end MinUncut.Outer.LocalTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_SignatureEncoding
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.Costed
open MinUncutGames.Foundations.Hastad.SourceOccurrences

def signatureEquiv (t : ℕ) : Signature (Fin t) ≃
    ((Fin t → F₂) × (Fin t → Fin 3 → Fin 3 → Bool)) where
  toFun s := (s.rhs,s.same)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def signatureEncoding (t : ℕ) : Encoding (Signature (Fin t)) :=
  let a := ((Encoding.fin t).function fieldEncoding).prod
    ((Encoding.fin t).function ((Encoding.fin 3).function ((Encoding.fin 3).function Encoding.bool)))
  ⟨a.size,(signatureEquiv t).trans a.code⟩

def signatureNumber {t : ℕ} (s : Signature (Fin t)) : ℕ :=
  (∑i : Fin t,(∑p : Fin 3,(∑q : Fin 3,(s.same i p q).toNat*2^q.val)*(2^3)^p.val)*((2^3)^3)^i.val)+
    ((2^3)^3)^t*(∑i : Fin t,(s.rhs i).val*2^i.val)

lemma signature_code {t : ℕ} (s : Signature (Fin t)) :
    ((signatureEncoding t).code s).val=signatureNumber s := by
  change (∑i : Fin t,(∑p : Fin 3,(∑q : Fin 3,(Encoding.bool.code (s.same i p q)).val*2^q.val)*(2^3)^p.val)*((2^3)^3)^i.val)+_=_
  simp only [bool_code,signatureNumber]
  rfl

lemma constantTable_lookup {α : Type} (e : Encoding α) (f : α → ℕ) (a : α) :
    AExpr.lookupValue ((e.code a).val) (constantTable e f)=f a := by
  apply lookupValue_mem
  · simp only [constantTable,List.map_map,Function.comp_def]
    exact List.Nodup.map (fun x y h=>e.code.injective (Fin.ext h)) e.nodup_enumerate
  · exact List.mem_map.mpr ⟨a,e.mem_enumerate a,rfl⟩

lemma constantTable_eval {α : Type} (e : Encoding α) (f : α → ℕ) (a : α)
    (x : AExpr) (v : List ℕ) (hx : x.eval v=(e.code a).val) :
    (x.lookup (constantTable e f)).eval v=f a := by
  rw [AExpr.eval_lookup,hx,constantTable_lookup]

end MinUncut.Outer.LocalTemplate

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_TemplateArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncutGames.Foundations.PCP.InitialGraph.slotFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

lemma tupleDigit_eval (F : Formula) {u : ℕ} (c : ClauseContext F u) (i : Fin u) :
    (tupleDigit i.val).eval (inputTuple F c)=(c i).val := by
  have h := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply c) i)
  have he : (clauseEncoding F u).code c=finFunctionFinEquiv c := by
    apply congrArg finFunctionFinEquiv
    funext j
    rfl
  simp only [tupleDigit,AExpr.eval,AExpr.eval_pow,inputTuple,Complexity.formulaWords,
    List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.headI_cons,he]
  exact h

lemma slotWord_name (F : Formula) {u : ℕ} (c : ClauseContext F u) (i : Fin u) (s : Slot) :
    (slotWord i.val s 0).eval (inputTuple F c)=(nameAt (clauseAt F (c i)) s).val := by
  simp only [slotWord,AExpr.eval,tupleDigit_eval,Nat.add_zero]
  have he : 3+6*(c i).val+2*(slotEncoding.code s).val=
      (2+6*(c i).val+2*(slotEncoding.code s).val)+1 := by omega
  rw [he]
  exact formula_name_word F (c i) s

lemma slotWord_positive (F : Formula) {u : ℕ} (c : ClauseContext F u) (i : Fin u) (s : Slot) :
    (slotWord i.val s 1).eval (inputTuple F c)=(positiveAt (clauseAt F (c i)) s).toNat := by
  simp only [slotWord,AExpr.eval,tupleDigit_eval]
  have he : 3+6*(c i).val+(2*(slotEncoding.code s).val+1)=
      (2+6*(c i).val+(2*(slotEncoding.code s).val+1))+1 := by omega
  rw [he]
  exact formula_positive_word F (c i) s

end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_QuestionArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteProof
open MinUncutGames.Foundations.Hastad.SourceOccurrences
variable {N t : ℕ}

def equationNumber (E : Equation (Fin N)) : ℕ :=
  E.rhs.val+2*∑p : Fin 3, (E.names p).val*N^p.val

def firstNumber (U : Fin t → Equation (Fin N)) : ℕ :=
  ∑i : Fin t,equationNumber (U i)*(N^3*2)^i.val

def secondNumber (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3) : ℕ :=
  ∑i : Fin t,(if h i then ((U i).names (pos i)).val else N+equationNumber (U i))*(N+N^3*2)^i.val

lemma first_code (U : Fin t → Equation (Fin N)) :
    ((questionEncoding N t).code (.inl U)).val=firstNumber U := rfl
lemma second_code (U : Fin t → Equation (Fin N)) (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    ((questionEncoding N t).code (.inr (secondQuestion U h pos))).val=
      (N^3*2)^t+secondNumber U h pos := by
  change (N^3*2)^t+(∑i : Fin t, ((secondQuestionEncoding N).code (slotQuestion (U i) (h i) (pos i))).val*(N+N^3*2)^i.val)=_
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases h i <;> rfl

def tableNumber (f : (Fin t → Triple) → Bool) : ℕ :=
  (((ambientEncoding t).function Encoding.bool).code f).val

lemma variable_number (v : FamilyVariable (Fin N) (Fin t)) :
    (variableCode v).val= tableNumber (extendTable v.1 v.2.val)+
      2^((2^3)^t)*((questionEncoding N t).code v.1).val := rfl

variable {h : Fin t → Bool}
def Query.leftNumber (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) : ℕ :=
  tableNumber (T.leftTable pos (signature U))+
    2^((2^3)^t)*(if T.first then firstNumber U else (N^3*2)^t+secondNumber U h pos)

def Query.rightNumber (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) : ℕ :=
  tableNumber T.rightTable+2^((2^3)^t)*((N^3*2)^t+secondNumber U h pos)

lemma Query.left_number (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) :
    (variableCode ((T.realize U pos).signed familyBase).left).val=T.leftNumber U pos := by
  rw [variable_number]
  change tableNumber (extendTable _ (rep (familyBase _) (T.realize U pos).left.2).val)+_= _
  rw [T.left_extended]
  unfold Query.leftNumber Query.realize
  by_cases hf : T.first=true
  · simp only [ite_eq_left hf,comparison,QueryDemand.signed,vertex,first_code]
  · simp only [ite_eq_right hf,comparison,QueryDemand.signed,vertex,second_code]

lemma Query.right_number (T : Query h) (U : Fin t → Equation (Fin N)) (pos : Fin t → Fin 3) :
    (variableCode ((T.realize U pos).signed familyBase).right).val=T.rightNumber U pos := by
  rw [variable_number]
  change tableNumber (extendTable _ (rep (familyBase _) (T.realize U pos).right.2).val)+_= _
  rw [T.right_extended]
  unfold Query.rightNumber Query.realize
  by_cases hf : T.first=true
  · simp only [ite_eq_left hf,comparison,QueryDemand.signed,vertex,second_code]
  · simp only [ite_eq_right hf,comparison,QueryDemand.signed,vertex,second_code]

end MinUncut.Outer.LocalTemplate

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_QuestionExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction MinUncut.SourceBridge

variable {t : ℕ}

def inputTuple (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) : List ℕ :=
  (finFunctionFinEquiv u).val::SourceEncoding.inputWords input

lemma tupleDigit_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) :
    (tupleDigit j.val).eval (inputTuple input u)=(u j).val := by
  have hh := congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply u) j)
  change (finFunctionFinEquiv u).val/input.equations.length^j.val%input.equations.length=(u j).val at hh
  simpa only [tupleDigit,AExpr.eval,AExpr.eval_pow,inputTuple,SourceEncoding.inputWords,
    List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero,List.headI_cons] using hh

lemma slotExpr_name (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) (p : Fin 3) :
    (slotExpr j.val p.val).eval (inputTuple input u)=((equations input (u j)).names p).val := by
  simp only [slotExpr,AExpr.eval,tupleDigit_eval]
  have he : 3+4*(u j).val+p.val=(2+4*(u j).val+p.val)+1 := by omega
  rw [he]
  exact input_name input (u j) p

lemma slotExpr_rhs (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) :
    (slotExpr j.val 3).eval (inputTuple input u)=(equations input (u j)).rhs.val := by
  simp only [slotExpr,AExpr.eval,tupleDigit_eval]
  have he : 3+4*(u j).val+3=(2+4*(u j).val+3)+1 := by omega
  rw [he]
  exact input_rhs input (u j)

lemma inputTuple_reg1 (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    ((inputTuple input u).drop 1).headI=input.«variables» := rfl

lemma equationExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) (j : Fin t) :
    (equationExpr j.val).eval (inputTuple input u)=equationNumber (equations input (u j)) := by
  simp only [equationExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_rhs,slotExpr_name,AExpr.eval_pow,inputTuple_reg1,equationNumber]

lemma firstExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    (firstExpr t).eval (inputTuple input u)=firstNumber (fun j=>equations input (u j)) := by
  simp only [firstExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,
    equationExpr_eval,AExpr.eval_pow,inputTuple_reg1,firstNumber]

lemma secondExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondExpr h pos).eval (inputTuple input u)=secondNumber (fun j=>equations input (u j)) h pos := by
  simp only [secondExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,AExpr.eval_pow,
    inputTuple_reg1,secondNumber]
  apply Finset.sum_congr rfl
  intro j _
  cases h j <;> simp only [Bool.false_eq_true,ite_false,ite_true,AExpr.eval,equationExpr_eval,slotExpr_name,inputTuple_reg1]

end MinUncut.Costed.SourceWords

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformGrid
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction MinUncut.SourceBridge

lemma signatureExpr_eval {t : ℕ} (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length) :
    (signatureExpr t).eval (inputTuple input u)=
      ((signatureEncoding t).code (signature (fun j=>equations input (u j)))).val := by
  rw [signature_code]
  simp only [signatureExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_name,slotExpr_rhs,signatureNumber,signature]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  by_cases h : (equations input (u i)).names p=(equations input (u i)).names q
  · simp only [h,decide_true,Bool.toNat_true,ite_true]
  · have h' : ((equations input (u i)).names p).val≠((equations input (u i)).names q).val :=
      fun e=>h (Fin.ext e)
    simp only [h,h',decide_false,Bool.toNat_false,ite_false]

def signatureLookup {t : ℕ} (f : Signature (Fin t) → ℕ) : AExpr :=
  (signatureExpr t).lookup (constantTable (signatureEncoding t) f)
lemma signatureLookup_eval {t : ℕ} (input : SourceEncoding.Input)
    (u : Fin t → Fin input.equations.length) (f : Signature (Fin t) → ℕ) :
    (signatureLookup f).eval (inputTuple input u)=f (signature (fun j=>equations input (u j))) := by
  exact constantTable_eval _ _ _ _ _ (signatureExpr_eval input u)

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction MinUncut.SourceBridge

variable {t : ℕ} {h : Fin t → Bool}

def leftExpr (T : Query h) (pos : Fin t → Fin 3) : AExpr :=
  .add (signatureLookup (fun s=>tableNumber (T.leftTable pos s)))
    (.mul (.const (2^((2^3)^t))) (if T.first then firstExpr t else secondAddress h pos))
def rightExpr (T : Query h) (pos : Fin t → Fin 3) : AExpr :=
  .add (.const (tableNumber T.rightTable)) (.mul (.const (2^((2^3)^t))) (secondAddress h pos))
def signExpr (T : Query h) (pos : Fin t → Fin 3) : AExpr :=
  signatureLookup (fun s=>(T.localSign pos s).toNat)

lemma secondAddress_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondAddress h pos).eval (inputTuple input u)=
      (input.«variables»^3*2)^t+secondNumber (fun j=>equations input (u j)) h pos := by
  simp only [secondAddress,AExpr.eval,AExpr.eval_pow,inputTuple_reg1,secondExpr_eval]
lemma leftExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    (leftExpr T pos).eval (inputTuple input u)=T.leftNumber (fun j=>equations input (u j)) pos := by
  simp only [leftExpr,AExpr.eval,signatureLookup_eval,Query.leftNumber]
  cases T.first <;> simp only [Bool.false_eq_true,ite_false,ite_true,firstExpr_eval,secondAddress_eval]
lemma rightExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    (rightExpr T pos).eval (inputTuple input u)=T.rightNumber (fun j=>equations input (u j)) pos := by
  simp only [rightExpr,AExpr.eval,secondAddress_eval,Query.rightNumber]
lemma signExpr_eval (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    (signExpr T pos).eval (inputTuple input u)=
      ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).equal.toNat := by
  rw [Query.signed_equal]
  exact signatureLookup_eval input u _

def queryWords (T : Query h) (pos : Fin t → Fin 3) (v : List ℕ) : List ℕ :=
  [(leftExpr T pos).eval v,(rightExpr T pos).eval v,(signExpr T pos).eval v]

lemma queryWords_eq (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (T : Query h) (pos : Fin t → Fin 3) :
    queryWords T pos (inputTuple input u)=
      [(variableCode ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).left).val,
       (variableCode ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).right).val,
       ((T.realize (fun j=>equations input (u j)) pos).signed familyBase).equal.toNat] := by
  simp only [queryWords,leftExpr_eval,rightExpr_eval,signExpr_eval,Query.left_number,Query.right_number]

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_LiteralLocalTemplates
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.FiniteProof MinUncut.FiniteGaussian
attribute [local instance] Classical.propDecidable
variable {I Name S : Type} [Fintype I] {k m n : ℕ} {g : GridData}

def indexQuery (σ η : ℚ) (e : Index I k m n g) : Query (hiddenSet e.2.1.val) :=
  query _ e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1
    (rationalScoreTable σ η (fun i=>midpoint g.T g.L (e.2.2.2.2.2.2 i))) e.1

lemma occurrence_query (eqs : S → Equation Name) (σ η : ℚ) (u : I → S) (e : Index I k m n g) :
    elementaryQuery eqs g σ η (occurrence eqs (u,e)).1 (occurrence eqs (u,e)).2=
      (indexQuery σ η e).realize (fun i=>eqs (u i)) e.2.2.1 := by
  rcases e with ⟨j,H,pos,B,C,z,q⟩
  dsimp only [occurrence,indexQuery,elementaryQuery,localSampleEquiv,samplePull,
    Equiv.prodCongr_apply,Prod.map,Equiv.refl_apply]
  exact (query_realize _ _ _ _ _ _ _ _).symm

lemma occurrence_demand (eqs : S → Equation Name) (σ η : ℚ) (u : I → S) (e : Index I k m n g) :
    allDemand eqs g σ η (occurrence eqs (u,e))=
      ((indexQuery σ η e).realize (fun i=>eqs (u i)) e.2.2.1).signed familyBase := by
  unfold allDemand
  rw [occurrence_query]

end MinUncut.Outer.LocalTemplate

end
namespace MinUncut.Costed

namespace SourceWords
open MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate

variable {t : ℕ}

lemma tuple_reg_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (i : ℕ) (hi : i<3) :
    ((inputTuple input u++rest).drop i).headI=((inputTuple input u).drop i).headI := by
  apply drop_head_append
  simp only [inputTuple,List.length_cons,SourceEncoding.inputWords_length]
  omega
lemma tupleDigit_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (j : ℕ) :
    (tupleDigit j).eval (inputTuple input u++rest)=(tupleDigit j).eval (inputTuple input u) := by
  simp only [tupleDigit,AExpr.eval,AExpr.eval_pow,tuple_reg_append input u rest 0 (by decide),
    tuple_reg_append input u rest 2 (by decide)]
lemma slotExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (j : Fin t) (p : ℕ) (hp : p<4) :
    (slotExpr j.val p).eval (inputTuple input u++rest)=(slotExpr j.val p).eval (inputTuple input u) := by
  simp only [slotExpr,AExpr.eval,tupleDigit_append,tupleDigit_eval]
  apply drop_head_append
  simp only [inputTuple,List.length_cons,SourceEncoding.inputWords_length]
  have h := (u j).isLt
  omega
lemma equationExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (j : Fin t) :
    (equationExpr j.val).eval (inputTuple input u++rest)=(equationExpr j.val).eval (inputTuple input u) := by
  simp (discharger := omega) only [equationExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_append input u rest j 3 (by decide),
    slotExpr_append,AExpr.eval_pow,tuple_reg_append input u rest 1 (by decide)]
lemma firstExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) :
    (firstExpr t).eval (inputTuple input u++rest)=(firstExpr t).eval (inputTuple input u) := by
  simp only [firstExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,
    equationExpr_append,AExpr.eval_pow,tuple_reg_append input u rest 1 (by decide)]
lemma secondExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondExpr h pos).eval (inputTuple input u++rest)=(secondExpr h pos).eval (inputTuple input u) := by
  simp only [secondExpr,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,AExpr.eval,AExpr.eval_pow,
    tuple_reg_append input u rest 1 (by decide)]
  apply Finset.sum_congr rfl
  intro j _
  cases h j <;> simp only [Bool.false_eq_true,ite_false,ite_true,AExpr.eval,equationExpr_append,
    slotExpr_append input u rest j (pos j).val (by omega),tuple_reg_append input u rest 1 (by decide)]
lemma signatureExpr_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) :
    (signatureExpr t).eval (inputTuple input u++rest)=(signatureExpr t).eval (inputTuple input u) := by
  simp (discharger := omega) only [signatureExpr,AExpr.eval,AExpr.eval_sum,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    slotExpr_append]
lemma signatureLookup_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (f : Signature (Fin t) → ℕ) :
    (signatureLookup f).eval (inputTuple input u++rest)=(signatureLookup f).eval (inputTuple input u) := by
  simp only [signatureLookup,AExpr.eval_lookup,signatureExpr_append]
lemma secondAddress_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) (h : Fin t → Bool) (pos : Fin t → Fin 3) :
    (secondAddress h pos).eval (inputTuple input u++rest)=(secondAddress h pos).eval (inputTuple input u) := by
  simp only [secondAddress,AExpr.eval,AExpr.eval_pow,tuple_reg_append input u rest 1 (by decide),secondExpr_append]
lemma queryWords_append (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (rest : List ℕ) {h : Fin t → Bool} (T : Query h) (pos : Fin t → Fin 3) :
    queryWords T pos (inputTuple input u++rest)=queryWords T pos (inputTuple input u) := by
  simp only [queryWords,leftExpr,rightExpr,signExpr,AExpr.eval,signatureLookup_append,secondAddress_append]
  cases T.first <;> simp only [Bool.false_eq_true,ite_false,ite_true,firstExpr_append,secondAddress_append]
end SourceWords
end MinUncut.Costed

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalPathGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open MinUncut.Costed.Expr

open PolyProgram Polynomial

noncomputable def adjacencyProgram : PolyProgram (fun v=>[cumulative v (v.drop 1).headI]) :=
  (prec (const 0) accumulatedEdge.program 1 (by
    intro n v i hi
    simpa only [eval_one,cumulative] using cumulative_le_one v i)).comp
      ((projection 1).cons id)

open PolyProgram Polynomial

noncomputable def tickProgram : PolyProgram renderTick :=
  (((projection 0).cons ((projection 1).cons ((projection 2).cons ((projection 3).cons
    (nextRow.program.cons (nextCol.program.cons (nextCount.program.cons
      (adjacencyProgram.cons (drop 7))))))))).comp normalizeProgram).ofEq (by
        intro v
        rfl)

noncomputable def renderLoop : PolyProgram (fun v=>renderTick^[v.headI] v.tail) :=
  iterate tickProgram (C 20*(X+1)^2) renderTick_iter_bound

open MinUncut.PathRealization
open PolyProgram

end MinUncut.Costed.GraphRegisters

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma failure_map {V W : Type*} (f : V → W) (d : Demand V) (s : W → Bool) :
    failure (d.map f) s=failure d (s ∘ f) := rfl

def listFailure {V : Type*} (ds : List (Demand V)) (s : V → Bool) : ℕ :=
  (ds.map (fun d => failure d s)).sum

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalSamplerGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences

variable {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}

def demandExpressions (σ η : ℚ) (e : Index (Fin t) k m n g) : List AExpr :=
  let T := indexQuery σ η e
  [leftExpr T e.2.2.1,rightExpr T e.2.2.1,signExpr T e.2.2.1]

def localExpressions (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ)
    (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) : List AExpr :=
  E.values.flatMap (fun e=>(List.replicate (repetitions a b e) (demandExpressions σ η e)).flatten)

def tupleDemands (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ)
    (σ η : ℚ) : List (Demand (Fin (paddedVariableEncoding input.«variables» t).size)) :=
  E.values.flatMap (fun e=>List.replicate (repetitions a b e)
    ((allDemand (equations input) g σ η (occurrence (equations input) (u,e))).map variableCode))

lemma demandExpressions_eval (input : SourceEncoding.Input)
    (u : Fin t → Fin input.equations.length) (e : Index (Fin t) k m n g) (σ η : ℚ) (rest : List ℕ) :
    (demandExpressions σ η e).map (fun x=>x.eval (inputTuple input u++rest))=
      GraphRegisters.packDemand ((allDemand (equations input) g σ η
        (occurrence (equations input) (u,e))).map variableCode) := by
  change queryWords (indexQuery σ η e) e.2.2.1 (inputTuple input u++rest)=_
  rw [queryWords_append,queryWords_eq,occurrence_demand]
  rfl

lemma localExpressions_eval (input : SourceEncoding.Input)
    (u : Fin t → Fin input.equations.length) (E : Enumeration (Index (Fin t) k m n g))
    (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) (rest : List ℕ) :
    (localExpressions E a b σ η).map (fun x=>x.eval (inputTuple input u++rest))=
      GraphRegisters.packDemands (tupleDemands input u E a b σ η) := by
  simp only [localExpressions,tupleDemands,GraphRegisters.packDemands,List.map_flatMap,
    List.map_flatten,List.flatMap_assoc]
  apply congrArg (List.flatMap · E.values)
  funext e
  simp only [List.map_replicate, demandExpressions_eval,List.flatMap_replicate]

def tupleList (input : SourceEncoding.Input) (t : ℕ) : List (Fin t → Fin input.equations.length) :=
  (List.finRange (input.equations.length^t)).map finFunctionFinEquiv.symm

def generatedDemands (input : SourceEncoding.Input) (E : Enumeration (Index (Fin t) k m n g))
    (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) :
    List (Demand (Fin (paddedVariableEncoding input.«variables» t).size)) :=
  (tupleList input t).flatMap (fun u=>tupleDemands input u E a b σ η)

lemma emitted_demands (input : SourceEncoding.Input) (E : Enumeration (Index (Fin t) k m n g))
    (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) (rest : List ℕ) :
    Blocks.emitted (localExpressions E a b σ η) (input.equations.length^t)
      (SourceEncoding.inputWords input++rest)=
      GraphRegisters.packDemands (generatedDemands input E a b σ η) := by
  rw [Blocks.emitted,←GraphRegisters.finRange_vals]
  simp only [generatedDemands,tupleList,List.flatMap_map,GraphRegisters.packDemands,
    List.flatMap_assoc]
  apply congrArg (List.flatMap · (List.finRange (input.equations.length^t)))
  funext z
  have h := localExpressions_eval input (finFunctionFinEquiv.symm z) E a b σ η rest
  simpa only [Blocks.block,inputTuple,Equiv.apply_symm_apply,List.cons_append,GraphRegisters.packDemands] using h

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
attribute [local instance] Classical.propDecidable

variable {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}

lemma tupleList_sum (input : SourceEncoding.Input) (f : (Fin t → Fin input.equations.length) → ℕ) :
    ((tupleList input t).map f).sum=∑u,f u := by
  simp only [tupleList,←List.ofFn_eq_map,List.map_ofFn,List.sum_ofFn]
  exact Equiv.sum_comp finFunctionFinEquiv.symm f

lemma tupleDemands_failure (input : SourceEncoding.Input) (u : Fin t → Fin input.equations.length)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ)
    (σ η : ℚ) (y : Fin (paddedVariableEncoding input.«variables» t).size → Bool) :
    listFailure (tupleDemands input u E a b σ η) y=
      ∑e : Index (Fin t) k m n g,repetitions a b e*failure
        (allDemand (equations input) g σ η (occurrence (equations input) (u,e))) (y ∘ variableCode) := by
  unfold tupleDemands listFailure
  simp only [List.map_flatMap,sum_flatMap_nat,List.map_replicate,List.sum_replicate,
    nsmul_eq_mul,Nat.cast_id,failure_map]
  exact E.sum_values _

lemma generatedDemands_failure (input : SourceEncoding.Input)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ)
    (σ η : ℚ) (y : Fin (paddedVariableEncoding input.«variables» t).size → Bool) :
    listFailure (generatedDemands input E a b σ η) y=
      ∑u,∑e : Index (Fin t) k m n g,repetitions a b e*failure
        (allDemand (equations input) g σ η (occurrence (equations input) (u,e))) (y ∘ variableCode) := by
  unfold generatedDemands listFailure
  rw [List.map_flatMap,sum_flatMap_nat]
  change ((tupleList input t).map (fun u=>listFailure (tupleDemands input u E a b σ η) y)).sum=_
  simp only [tupleDemands_failure]
  exact tupleList_sum input _

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandOrder
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open PolyProgram

noncomputable def initProgram : PolyProgram initRender :=
  ((vertexExpr.mul vertexExpr).program.cons ((projection 0).cons ((projection 1).cons
    ((projection 2).cons (vertexExpr.program.cons (lastVertexExpr.program.cons
      (lastVertexExpr.program.cons ((const 0).cons ((const 2).cons ((projection 2).cons (drop 3))))))))))).ofEq (by
        intro v
        simp only [Expr.eval,vertexExpr,lastVertexExpr,initRender,queryState,RenderState.encode,
          List.headI_cons,List.length_nil,List.nil_append,List.drop_zero,pow_two])

noncomputable def rawRenderer : PolyProgram renderRaw :=
  (((projection 3).cons (drop 7)).comp (renderLoop.comp initProgram)).ofEq (by
    intro v
    simp only [Function.comp_apply,initRender,List.headI_cons,List.tail_cons]
    rw [renderTick_iter_encode]
    change (RenderState.tick^[(_+_*3)^2] _).V::(RenderState.tick^[(_+_*3)^2] _).tape=_
    rw [tick_iter_V,tick_table]
    rfl)

open MinUncut.PathRealization

end MinUncut.Costed.GraphRegisters

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphSize
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.Parameters
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness Polynomial
attribute [local instance] Classical.propDecidable

def denominatorCoefficient {J : ℕ} (P : Parameters J) : ℕ :=
  Fintype.card (FixedSets (Fin P.o.t) P.o.k)*3^P.o.t*
    innerDenominator P.o.t P.d.m P.d.n P.grid (rationalRate J P.d) (rationalBudgets J P.d P.o)

variable {Name S : Type*} [Fintype Name] [Fintype S] [Nonempty S]

omit [Fintype Name] [Nonempty S] in
lemma denominator_eq {J : ℕ} (P : Parameters J) :
    P.denominator S=P.denominatorCoefficient*Fintype.card S^P.o.t := by
  rw [denominator,samplerDenominator_polynomial]
  simp only [Fintype.card_fin,denominatorCoefficient]

end MinUncut.Outer.Parameters

end
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
noncomputable section

def demandStageProgram (es : List AExpr) (t D : ℕ) : PolyProgram (demandStageWords es t D) :=
  ((variableCountExpr t).program.cons ((unitCountExpr es t).program.cons
    ((thresholdExpr t D).program.cons (Blocks.forward es (tupleCountExpr t))))).ofEq (by
      intro v; rfl)

lemma input_regs (input : SourceEncoding.Input) (rest : List ℕ) :
    (SourceEncoding.inputWords input++rest).headI=input.«variables» ∧
    ((SourceEncoding.inputWords input++rest).drop 1).headI=input.equations.length := by
  constructor <;> rfl

lemma tupleCountExpr_eval (input : SourceEncoding.Input) (rest : List ℕ) (t : ℕ) :
    (tupleCountExpr t).eval (SourceEncoding.inputWords input++rest)=input.equations.length^t := by
  simp only [tupleCountExpr,AExpr.eval_pow,AExpr.eval,(input_regs input rest).2]

lemma variableCountExpr_eval (input : SourceEncoding.Input) (rest : List ℕ) (t : ℕ) :
    (variableCountExpr t).eval (SourceEncoding.inputWords input++rest)=
      (paddedVariableEncoding input.«variables» t).size := by
  simp only [variableCountExpr,AExpr.eval,AExpr.eval_pow,List.drop_zero,(input_regs input rest).1,
      paddedVariableEncoding_size]

lemma unitCountExpr_eval {t k m n : ℕ} {g : MinUncut.FiniteGaussian.GridData}
    (input : SourceEncoding.Input) (rest : List ℕ)
    (E : Enumeration (Index (Fin t) k m n g)) (a : ℚ) (b : MinUncut.Outer.Test → ℚ) (σ η : ℚ) :
    (unitCountExpr (localExpressions E a b σ η) t).eval (SourceEncoding.inputWords input++rest)=
      (generatedDemands input E a b σ η).length := by
  have h := congrArg List.length (emitted_demands input E a b σ η rest)
  rw [Blocks.length_emitted,GraphRegisters.length_packDemands] at h
  simp only [unitCountExpr,AExpr.eval,tupleCountExpr_eval,h]
  omega

lemma thresholdExpr_eval {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input) (rest : List ℕ) :
    (thresholdExpr P.o.t P.denominatorCoefficient).eval (SourceEncoding.inputWords input++rest)=
      5*P.denominator (Fin input.equations.length) := by
  simp only [thresholdExpr,AExpr.eval,tupleCountExpr_eval,P.denominator_eq,Fintype.card_fin,mul_assoc]

lemma demandStageWords_spec {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
    (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid)) (rest : List ℕ) :
    ∃junk, demandStageWords (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) P.o.t P.denominatorCoefficient
      (SourceEncoding.inputWords input++rest)=
       (paddedVariableEncoding input.«variables» P.o.t).size::
       (generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
         (rationalSigma J) (rationalEta J)).length::(5*P.denominator (Fin input.equations.length))::
       (GraphRegisters.packDemands (generatedDemands input E (rationalRate J P.d)
         (rationalBudgets J P.d P.o) (rationalSigma J) (rationalEta J))++junk) := by
  refine ⟨Blocks.retained (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
    (rationalSigma J) (rationalEta J)) (input.equations.length^P.o.t)
    (SourceEncoding.inputWords input++rest),?_⟩
  simp only [demandStageWords,variableCountExpr_eval,unitCountExpr_eval,thresholdExpr_eval,
    tupleCountExpr_eval,emitted_demands]

end
end MinUncut.Costed.SourceWords

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CompleteGraphProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
open MinUncutGames.Foundations.Target MinUncut.SourceTemplate GraphRegisters

variable {J : ℕ} (P : Parameters J)
  (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))

def graphStageWords (v : List ℕ) : List ℕ :=
  GraphRegisters.renderRaw (demandStageWords
    (localExpressions E (rationalRate J P.d) (rationalBudgets J P.d P.o)
      (rationalSigma J) (rationalEta J)) P.o.t P.denominatorCoefficient v)

lemma graphStageWords_spec (input : SourceEncoding.Input) (rest : List ℕ) :
    ∃junk,graphStageWords P E (SourceEncoding.inputWords input++rest)=
      let ds := generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
        (rationalSigma J) (rationalEta J)
      ((paddedVariableEncoding input.«variables» P.o.t).size+ds.length*3)::
        ((canonicalTable ds).map Bool.toNat++2::(5*P.denominator (Fin input.equations.length))::junk) := by
  obtain ⟨junk,hj⟩:=demandStageWords_spec P input E rest
  simp only [graphStageWords,hj,GraphRegisters.renderer_pack]
  exact ⟨_,rfl⟩

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GeneratedGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncut.FiniteProof MinUncutGames.Reduction MinUncut.SourceBridge
open MinUncutGames.Foundations.Hastad.SourceOccurrences
attribute [local instance] Classical.propDecidable
variable {J : ℕ} (P : Parameters J) (input : SourceEncoding.Input)
  [Nonempty (Fin input.equations.length)]
  (E : Enumeration (Index (Fin P.o.t) P.o.k P.d.m P.d.n P.grid))

def generatedGraph : MinUncut.Output :=
  listOutput (generatedDemands input E (rationalRate J P.d) (rationalBudgets J P.d P.o)
    (rationalSigma J) (rationalEta J)) (5*P.denominator (Fin input.equations.length))
    (threshold_positive P.denominator_pos)

end MinUncut.Costed.SourceWords

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_ArenaMachineProgram
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.Arena

lemma outputStep_safe (v : List ℕ) :
    (outputStep v).length≤v.length+4 ∧ maximum (outputStep v)≤ maximum v+1 := by
  have hr (j : Fin 4) : (outRead j).eval v≤ maximum v := by
    change (v.drop _).headI≤_
    exact (head_le_maximum _).trans (maximum_drop v _)
  have h1 := reg_le_maximum v 1
  have h2 := reg_le_maximum v 2
  have h0 := hr 0
  have h3 := hr 1
  have ht := maximum_drop v 3
  simp only [outputStep]
  split_ifs
  · constructor <;> omega
  · simp only [List.cons_append,List.nil_append,List.length_cons,List.length_drop,maximum_cons]
    constructor
    · omega
    · exact max_le (by omega) (max_le (by omega) (max_le (by omega) (max_le (by omega) (by omega))))

end MinUncut.Costed.Arena

end

end OAI
end


