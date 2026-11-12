-- Prove2me | Definitions.Def_OAIQ252P000
-- name    : OAIQ252P000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-11T07:29:24.341692+00:00
-- url     : https://prove2.me/theorems/6744a717-cda9-48f8-a2e8-b8e050a224a4
-- title:
--   Definitions bundle OAIQ252P000 of the split of OpenAI, Perfect completeness for 2-to-1 games
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PerfectCompleteness.Theorem11.exists_reduction`, carved from OpenAI's openai/math development (OpenAI, *Perfect completeness for 2-to-1 games*, OpenAI Math Release, September 23, 2026, result family 105, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 957 declarations of OpenAI's Lean: 409 definitions, 19 inductive types or structures, 4 instances and 525 theorems. The definitions and types are `OAI.PerfectCompleteness.AffineDecoderMeeting.nativeCenter`, `OAI.PerfectCompleteness.AffineDecoderMeeting.nativeQ`, `OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum`, `OAI.PerfectCompleteness.AffineLinearHeavyWitness.badMasks`, `OAI.PerfectCompleteness.AffineLinearHeavyWitness.conditionalMatch`, `OAI.PerfectCompleteness.AscendingBranching.CubeErrors`, `OAI.PerfectCompleteness.BilinearCollisionTransfer.Form`, `OAI.PerfectCompleteness.BilinearCollisionTransfer.fullCollision`, `OAI.PerfectCompleteness.BilinearCollisionTransfer.restrictedCollision`, `OAI.PerfectCompleteness.BilinearGramCompression.combinations`, `OAI.PerfectCompleteness.BilinearGramCompression.crossGram`, `OAI.PerfectCompleteness.BilinearGramCompression.gram`, `OAI.PerfectCompleteness.BilinearRestrictionRank.restrictForm`, `OAI.PerfectCompleteness.BilinearWitness.Witness`, `OAI.PerfectCompleteness.BilinearWitness.assemble`, `OAI.PerfectCompleteness.BilinearWitness.chooseWitness`, `OAI.PerfectCompleteness.BilinearWitness.selected`, `OAI.PerfectCompleteness.BinaryDualCoordinates.character`, `OAI.PerfectCompleteness.BinaryDualCoordinates.coordinates`, `OAI.PerfectCompleteness.BinaryDualCoordinates.equationRows`, `OAI.PerfectCompleteness.BinaryDualCoordinates.equations`, `OAI.PerfectCompleteness.BinaryDualCoordinates.frequency`, `OAI.PerfectCompleteness.BinaryDualCoordinates.frequencyEquiv`, `OAI.PerfectCompleteness.BinaryDualCoordinates.ofBool`, `OAI.PerfectCompleteness.BinaryDualCoordinates.toBool`, `OAI.PerfectCompleteness.BinaryEncoding.clauseBits`, `OAI.PerfectCompleteness.BinaryEncoding.clauseNameSize`, `OAI.PerfectCompleteness.BinaryEncoding.clausesBits`, `OAI.PerfectCompleteness.BinaryEncoding.formulaBits`, `OAI.PerfectCompleteness.BinaryEncoding.frame`, `OAI.PerfectCompleteness.BinaryEncoding.literalBits`, `OAI.PerfectCompleteness.BinaryEncoding.nameBits`, `OAI.PerfectCompleteness.BinaryEncoding.namesBitSize`, `OAI.PerfectCompleteness.BinaryFormula.activeNames`, `OAI.PerfectCompleteness.BinaryFormula.clauseNames`, `OAI.PerfectCompleteness.BinaryFormula.compactIndex`, `OAI.PerfectCompleteness.BinaryFormula.compactLiteral`, `OAI.PerfectCompleteness.BinaryFormula.sourceNames`, `OAI.PerfectCompleteness.BinaryHeaderMachine.Alphabet`, `OAI.PerfectCompleteness.BinaryHeaderMachine.State` and 388 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `PerfectCompleteness_Algebra_AffineDecoderMeeting`, `PerfectCompleteness_Algebra_AffineFunctionalDependence`, `PerfectCompleteness_Algebra_AffineLinearHeavyWitness`, `PerfectCompleteness_Algebra_BilinearGramCompressionLemmas`, `PerfectCompleteness_Algebra_BilinearWitnessLemmas`, `PerfectCompleteness_Construction_AscendingBranchingLemmas`, `PerfectCompleteness_Construction_TreeSourceSpaces`, `PerfectCompleteness_Foundations_DualQuotientRowsLemmas`, `PerfectCompleteness_Foundations_GlobalityLemmas`, `PerfectCompleteness_Foundations_PartitionsLemmas`, `PerfectCompleteness_Foundations_QuarterBalanceLemmas`, `PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas`, `PerfectCompleteness_Foundations_RecursiveSpaces`, `PerfectCompleteness_Machines_BinaryDualCoordinates`, `PerfectCompleteness_Machines_BinaryFormulaLemmas`, `PerfectCompleteness_Machines_BinaryHeaderMachine`, `PerfectCompleteness_Machines_BinaryLiteralMachine`, `PerfectCompleteness_Machines_BinaryNameCompare`, `PerfectCompleteness_Machines_BinaryNameMachine`, `PerfectCompleteness_Machines_BinaryNameSearch`, `PerfectCompleteness_Machines_BinaryOccurrenceRename`, `PerfectCompleteness_Machines_BinaryParsingLemmas`, `PerfectCompleteness_Machines_BinaryRenameLoop`, `PerfectCompleteness_Machines_BinaryRenameMachine`, `PerfectCompleteness_Machines_BinaryRenameWords`, `PerfectCompleteness_Machines_BinaryTokenMachine`, `PerfectCompleteness_Machines_BinaryTotalInputMachine`, `PerfectCompleteness_Machines_BinaryValidatorMachine`, `UniqueGames_Analysis_A13IndexLemmas`, `UniqueGames_Analysis_A5FrequencyTransportLemmas`, `UniqueGames_Analysis_AntecedentCountLemmas`, `UniqueGames_Analysis_CompressionCountLemmas`, `UniqueGames_Analysis_DerivativeInduction`, `UniqueGames_Analysis_HybridCompositionLemmas`, `UniqueGames_Analysis_Identities`, `UniqueGames_Analysis_MatrixCharactersLemmas`, `UniqueGames_Analysis_MatrixNoiseLemmas`, `UniqueGames_Analysis_MatrixRestrictions`, `UniqueGames_Analysis_OperatorPartitions`, `UniqueGames_Analysis_RestrictionLemmas`, `UniqueGames_Analysis_SubspaceCountingLemmas`, `UniqueGames_Analysis_WeightedFourthMoment`, `UniqueGames_Foundations_FiniteTrialsLemmas`, `UniqueGames_Foundations_PinskerLemmas`, `UniqueGames_Machines_GraphCounterStartLemmas`, `UniqueGames_Machines_MachineCompare`, `UniqueGames_Machines_MachineCompositionLemmas`, `UniqueGames_Machines_MachineControlLemmas`, `UniqueGames_Machines_MachineCopy`, `UniqueGames_Machines_MachineDrain`, `UniqueGames_Machines_MachineLemmas`, `UniqueGames_Machines_MachineSubroutineLemmas`, `UniqueGames_Machines_Runtime`, `UniqueGames_Model`, `UniqueGames_PCP_ClauseVerifierLemmas`, `UniqueGames_Reduction_ActualSourceLemmas`, `UniqueGames_Reduction_BinaryLinear`, `UniqueGames_Reduction_GapSemanticsLemmas`, `UniqueGames_Reduction_MachineSubstitution`, `UniqueGames_Reduction_MachineTransfer`, `UniqueGames_Reduction_RealTargetLemmas`.
--
--   **Imports.** It imports the published bundle `Def_PerfectCompleteness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ252P003`, `OAIQ252P004`, `OAIQ252P005` and `OAIQ252P006`.
-- source:
--   OpenAI, Perfect completeness for 2-to-1 games, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 105; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Perfect-completeness-for-2-to-1-games-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit 7ef5c0c

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_PerfectCompleteness

section
-- module Solutions.OAIQ252_PC.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_SubspaceCountingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Subspace classification by one additional coordinate and the finite-field
subspace Möbius identity. All spaces, quotients and dimensions are genuine. -/
namespace UniqueGamesTheorem.Appendix.SubspaceExtensions
open scoped BigOperators
open LinearMap Submodule
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

local instance subspaceFintype [Finite V] : Fintype (Submodule K V) := by
  classical
  letI := Fintype.ofFinite V
  exact Fintype.ofInjective (fun B : Submodule K V => (B : Set V)) SetLike.coe_injective

end
end UniqueGamesTheorem.Appendix.SubspaceExtensions

end

section

namespace UniqueGamesTheorem.Appendix.SubmoduleInterval
open Module
variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def lowerIntervalSpaceEquiv (I : Submodule 𝕜 V)
    (A : {A : Submodule 𝕜 V // A ≤ I}) :
    A.val ≃ₗ[𝕜] A.val.comap I.subtype where
  toFun a := ⟨⟨a.val, A.property a.property⟩, a.property⟩
  invFun b := ⟨b.val.val, b.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

open scoped BigOperators
attribute [local instance] Classical.propDecidable

end UniqueGamesTheorem.Appendix.SubmoduleInterval

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UniqueGamesTheorem.Foundations.Target

/-- Finite forward and inverse tables make totality and invertibility explicit.
An eventual external encoding only needs to serialize the forward table. -/
structure PermutationTable (alphabet : Nat) where
  images : Vector (Fin alphabet) alphabet
  inverseImages : Vector (Fin alphabet) alphabet
  leftInverse : ∀ label : Fin alphabet, inverseImages[images[label]] = label
  rightInverse : ∀ label : Fin alphabet, images[inverseImages[label]] = label

structure Constraint (vertices alphabet : Nat) where
  source : Fin vertices
  target : Fin vertices
  permutation : PermutationTable alphabet

def Constraint.satisfied {n q : Nat} (constraint : Constraint n q)
    (labeling : Fin n → Fin q) : Bool :=
  decide (constraint.permutation.images[labeling constraint.source] = labeling constraint.target)

/-- Constraint occurrences are list entries, so repeated parallel edges retain
their multiplicity. No weights are hidden in this representation. -/
structure Instance (alphabet : Nat) where
  vertices : Nat
  constraints : List (Constraint vertices alphabet)
  nonempty : constraints ≠ []

end UniqueGamesTheorem.Foundations.Target

namespace UniqueGamesTheorem.Integration.BinaryLinear

abbrev F2 := ZMod 2

abbrev Vector (n : Nat) := Fin n → F2

end UniqueGamesTheorem.Integration.BinaryLinear

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_BinaryLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact transport from XOR bit vectors to vector spaces over `ZMod 2`. -/
namespace UniqueGamesTheorem.Integration.BinaryLinear

theorem scalar_cases : ∀ a : F2, a = 0 ∨ a = 1 := by decide

end UniqueGamesTheorem.Integration.BinaryLinear

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixRestrictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Fourier.MatrixRestrictions

open UniqueGamesTheorem.Integration.BinaryLinear
open scoped BigOperators

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
    [AddCommGroup C] [Module F2 C]

abbrev Parameter (W : Submodule F2 E)
    (C' : Submodule F2 C) := (E ⧸ W) →ₗ[F2] C'

/-- The canonical inclusion of `L(E/W,C')` into `L(E,C)`. -/
def embed (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') : (E →ₗ[F2] C) :=
  C'.subtype.comp (A.comp W.mkQ)

@[simp] theorem embed_apply (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') (x : E) :
    embed W C' A x = (A (W.mkQ x) : C) := rfl

theorem embed_injective (W : Submodule F2 E)
    (C' : Submodule F2 C) : Function.Injective (embed W C') := by
  intro A B h
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := W.mkQ_surjective x
  apply Subtype.ext
  exact congrArg (fun f : (E →ₗ[F2] C) => f y) h

theorem embed_vanishes (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    W ≤ LinearMap.ker (embed W C' A) := by
  intro x hx
  change (A (W.mkQ x) : C) = 0
  have hzero : W.mkQ x = 0 := by simpa using hx
  simp [hzero]

theorem embed_range (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    LinearMap.range (embed W C' A) ≤ C' := by
  rintro x ⟨y, rfl⟩
  exact (A (W.mkQ y)).property

/-- These are exactly the maps vanishing on `W` with image in `C'`. -/
theorem exists_embed_iff (W : Submodule F2 E)
    (C' : Submodule F2 C) (B : (E →ₗ[F2] C)) :
    (∃ A : Parameter W C', embed W C' A = B) ↔
      W ≤ LinearMap.ker B ∧ LinearMap.range B ≤ C' := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨embed_vanishes W C' A, embed_range W C' A⟩
  · rintro ⟨hW, hC⟩
    let B' : E →ₗ[F2] C' :=
      B.codRestrict C' (fun x => hC ⟨x, rfl⟩)
    have hker : W ≤ LinearMap.ker B' := by
      intro x hx
      apply Subtype.ext
      exact hW hx
    refine ⟨W.liftQ B' hker, ?_⟩
    apply LinearMap.ext
    intro x
    rfl

/-- Quotient rows are unchanged by every admissible restriction perturbation. -/
theorem quotient_embed_zero (W : Submodule F2 E)
    (C' : Submodule F2 C) (A : Parameter W C') :
    C'.mkQ.comp (embed W C' A) = 0 := by
  apply LinearMap.ext
  intro x
  change C'.mkQ (embed W C' A x) = 0
  exact (Submodule.Quotient.mk_eq_zero C').mpr (A (W.mkQ x)).property

def translate (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C))
    (A : Parameter W C') : (E →ₗ[F2] C) := X + embed W C' A

theorem translate_injective (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C)) :
    Function.Injective (translate W C' X) := by
  intro A B h
  exact embed_injective W C' (add_left_cancel h)

theorem quotient_translate (W : Submodule F2 E)
    (C' : Submodule F2 C) (X : (E →ₗ[F2] C))
    (A : Parameter W C') :
    C'.mkQ.comp (translate W C' X A) = C'.mkQ.comp X := by
  apply LinearMap.ext
  intro x
  change C'.mkQ (X x + embed W C' A x) = C'.mkQ (X x)
  rw [map_add]
  have h : C'.mkQ (embed W C' A x) = 0 :=
    congrArg (fun f : E →ₗ[F2] (C ⧸ C') => f x)
    (quotient_embed_zero W C' A)
  rw [h, add_zero]

noncomputable def order (W : Submodule F2 E) (C' : Submodule F2 C) : Nat :=
  Module.finrank F2 W + Module.finrank F2 (C ⧸ C')

end UniqueGamesTheorem.Fourier.MatrixRestrictions

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BilinearGramCompression

open scoped BigOperators

noncomputable section

variable {K H R I J : Type*} [Field K] [AddCommGroup H] [Module K H]
  [Fintype R] [Fintype I] [Fintype J]

def combinations (rows : R → H) (T : Matrix I R K) : I → H :=
  fun i => ∑ r, T i r • rows r

def crossGram (F : H →ₗ[K] Module.Dual K H) (left : I → H) (right : J → H) :
    Matrix I J K :=
  fun i j => F (left i) (right j)

def gram (F : H →ₗ[K] Module.Dual K H) (rows : R → H) : Matrix R R K :=
  crossGram F rows rows

end
end PerfectCompleteness.BilinearGramCompression

end

section

namespace PerfectCompleteness.BilinearRestrictionRank

noncomputable section

open Module

variable {𝕜 H V U : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup U] [Module 𝕜 U]

def restrictForm (F : H →ₗ[𝕜] Module.Dual 𝕜 H) (N : Submodule 𝕜 H) :
    N →ₗ[𝕜] Module.Dual 𝕜 N :=
  N.dualRestrict.comp (F.domRestrict N)

@[simp]
theorem restrictForm_apply (F : H →ₗ[𝕜] Module.Dual 𝕜 H)
    (N : Submodule 𝕜 H) (x y : N) :
    restrictForm F N x y = F (x : H) (y : H) := rfl

end
end PerfectCompleteness.BilinearRestrictionRank

end

section

namespace PerfectCompleteness.MatrixRowQuotient

noncomputable section

variable {𝕜 H K : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]

def projectMatrix (W : Submodule 𝕜 H) (X : Module.Dual 𝕜 H →ₗ[𝕜] K) :
    Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K :=
  X.comp W.mkQ.dualMap

def liftMatrix (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) : Module.Dual 𝕜 H →ₗ[𝕜] K :=
  X.comp s.dualMap

@[simp] theorem projectMatrix_apply (W : Submodule 𝕜 H)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) (q : Module.Dual 𝕜 (H ⧸ W)) :
    projectMatrix W X q = X (q.comp W.mkQ) := rfl

@[simp] theorem liftMatrix_apply (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (X : Module.Dual 𝕜 (H ⧸ W) →ₗ[𝕜] K) (q : Module.Dual 𝕜 H) :
    liftMatrix W s X q = X (q.comp s) := rfl

def residualVector (W : Submodule 𝕜 H) (s : (H ⧸ W) →ₗ[𝕜] H)
    (hs : W.mkQ.comp s = LinearMap.id) : H →ₗ[𝕜] W :=
  (LinearMap.id - s.comp W.mkQ).codRestrict W (by
    intro h
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change W.mkQ (h - s (W.mkQ h)) = 0
    rw [map_sub]
    have hh := LinearMap.congr_fun hs (W.mkQ h)
    change W.mkQ (s (W.mkQ h)) = W.mkQ h at hh
    rw [hh, sub_self])

@[simp] theorem residualVector_val (W : Submodule 𝕜 H)
    (s : (H ⧸ W) →ₗ[𝕜] H) (hs : W.mkQ.comp s = LinearMap.id) (h : H) :
    (residualVector W s hs h : H) = h - s (W.mkQ h) := rfl

end
end PerfectCompleteness.MatrixRowQuotient

end

section

namespace PerfectCompleteness.MatrixSlice

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

variable {E C : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C]

def Slice (W : Submodule F2 E) (C' : Submodule F2 C) (T : E →ₗ[F2] C) :=
  {X : E →ₗ[F2] C //
    X.domRestrict W = T.domRestrict W ∧ C'.mkQ.comp X = C'.mkQ.comp T}

theorem domRestrict_translate (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) (A : Parameter W C') :
    (translate W C' T A).domRestrict W = T.domRestrict W := by
  apply LinearMap.ext
  intro w
  change T w + embed W C' A w = T w
  have hw : embed W C' A w = 0 := embed_vanishes W C' A w.property
  rw [hw, add_zero]

theorem exists_translate_iff (W : Submodule F2 E) (C' : Submodule F2 C)
    (T X : E →ₗ[F2] C) :
    (∃ A : Parameter W C', translate W C' T A = X) ↔
      X.domRestrict W = T.domRestrict W ∧ C'.mkQ.comp X = C'.mkQ.comp T := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨domRestrict_translate W C' T A, quotient_translate W C' T A⟩
  · rintro ⟨hW, hC⟩
    have hker : W ≤ LinearMap.ker (X - T) := by
      intro w hw
      change X w - T w = 0
      exact sub_eq_zero.mpr (LinearMap.congr_fun hW ⟨w, hw⟩)
    have hrange : LinearMap.range (X - T) ≤ C' := by
      rintro y ⟨x, rfl⟩
      apply (Submodule.Quotient.mk_eq_zero C').mp
      change C'.mkQ (X x - T x) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hC x)
    obtain ⟨A, hA⟩ := (exists_embed_iff W C' (X - T)).mpr ⟨hker, hrange⟩
    refine ⟨A, ?_⟩
    change T + embed W C' A = X
    rw [hA, add_comm T, sub_add_cancel]

def parameterEquivSlice (W : Submodule F2 E) (C' : Submodule F2 C)
    (T : E →ₗ[F2] C) : Parameter W C' ≃ Slice W C' T :=
  Equiv.ofBijective
    (fun A => ⟨translate W C' T A,
      domRestrict_translate W C' T A, quotient_translate W C' T A⟩)
    ⟨by
      intro A B h
      exact translate_injective W C' T (congrArg Subtype.val h), by
      intro X
      obtain ⟨A, hA⟩ := (exists_translate_iff W C' T X.val).mpr X.property
      exact ⟨A, Subtype.ext hA⟩⟩

@[simp] theorem parameterEquivSlice_val (W : Submodule F2 E)
    (C' : Submodule F2 C) (T : E →ₗ[F2] C) (A : Parameter W C') :
    (parameterEquivSlice W C' T A).val = translate W C' T A := rfl

end
end PerfectCompleteness.MatrixSlice

end

section

namespace PerfectCompleteness.TensorCosetEvaluation

noncomputable section

open scoped TensorProduct

section GeneralField

variable {𝕜 U H : Type*} [Field 𝕜]
  [AddCommGroup U] [Module 𝕜 U] [AddCommGroup H] [Module 𝕜 H]

def scalarRestriction (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H)) (u : U) :
    Module.Dual 𝕜 H :=
  Φ.comp (TensorProduct.mk 𝕜 U H u)

@[simp] theorem scalarRestriction_apply (Φ : Module.Dual 𝕜 (U ⊗[𝕜] H))
    (u : U) (h : H) : scalarRestriction Φ u h = Φ (u ⊗ₜ[𝕜] h) := rfl

end GeneralField

end
end PerfectCompleteness.TensorCosetEvaluation

end

section

namespace PerfectCompleteness.TensorRestriction

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {W H : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]

def tensorEquivHom : (W ⊗[F2] H) ≃ₗ[F2] (Module.Dual F2 H →ₗ[F2] W) :=
  (TensorProduct.comm F2 W H).trans
    ((TensorProduct.congr (Module.evalEquiv F2 H) (LinearEquiv.refl F2 W)).trans
      (dualTensorHomEquiv F2 (Module.Dual F2 H) W))

@[simp] theorem tensorEquivHom_tmul (w : W) (h : H) (q : Module.Dual F2 H) :
    tensorEquivHom (w ⊗ₜ[F2] h) q = q h • w := rfl

def restrictionMap (Q : Submodule F2 (Module.Dual F2 H)) :
    (W ⊗[F2] H) →ₗ[F2] (Q →ₗ[F2] W) :=
  (LinearMap.domRestrict' Q).comp tensorEquivHom.toLinearMap

@[simp] theorem restrictionMap_apply (Q : Submodule F2 (Module.Dual F2 H))
    (X : W ⊗[F2] H) (q : Q) :
    restrictionMap Q X q = tensorEquivHom X q.val := rfl

@[simp] theorem restrictionMap_tmul (Q : Submodule F2 (Module.Dual F2 H))
    (w : W) (h : H) (q : Q) :
    restrictionMap Q (w ⊗ₜ[F2] h) q = q.val h • w := rfl

end
end PerfectCompleteness.TensorRestriction

end

section

namespace PerfectCompleteness.TensorEquationSpace

noncomputable section

open scoped BigOperators TensorProduct
open TensorCosetEvaluation

section Binary

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {W H : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]

def pureFactor (Q : Submodule F2 (Module.Dual F2 H))
    (a : Module.Dual F2 W) (q : Q) : Module.Dual F2 (Q →ₗ[F2] W) where
  toFun T := a (T q)
  map_add' T S := by simp only [LinearMap.add_apply, map_add]
  map_smul' c T := by simp only [LinearMap.smul_apply, map_smul, RingHom.id_apply]

omit [FiniteDimensional F2 H] in
@[simp] theorem pureFactor_apply (Q : Submodule F2 (Module.Dual F2 H))
    (a : Module.Dual F2 W) (q : Q) (T : Q →ₗ[F2] W) :
    pureFactor Q a q T = a (T q) := rfl

end Binary
end
end PerfectCompleteness.TensorEquationSpace

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_Identities
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.LinearIdentities

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

variable [FiniteDimensional K W]

/-! ## The unique selector in (A.4) -/

abbrev A4Index := Σ A₀ : Submodule K V, Σ B₀ : Submodule K W, B₀ →ₗ[K] (V ⧸ A₀)

end UniqueGamesTheorem.Appendix.LinearIdentities

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_CompressionCountLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.CompressionCount

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

/-- Canonical rank-`dim U` map. -/
def base : (U × K) →ₗ[F2] (U × C) :=
  (LinearMap.inl F2 U C).comp (LinearMap.fst F2 U K)

@[simp] theorem base_apply (p : U × K) : base U K C p = (p.1, 0) := rfl

variable {U K C}

/-- Compress by restricting to the second domain factor and taking the second
codomain coordinate. -/
def compress (Y : (U × K) →ₗ[F2] (U × C)) : K →ₗ[F2] C :=
  (LinearMap.snd F2 U C).comp (Y.comp (LinearMap.inr F2 U K))

@[simp] theorem compress_apply (Y : (U × K) →ₗ[F2] (U × C)) (k : K) :
    compress Y k = (Y (0, k)).2 := rfl

abbrev Parameters (Z : K →ₗ[F2] C) :=
  (Z.range →ₗ[F2] U) × (U →ₗ[F2] Z.range)

def graph (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Z.range →ₗ[F2] (U × C) := F.prod Z.range.subtype

def lower (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    (U × K) →ₗ[F2] Z.range := H.coprod Z.rangeRestrict

/-- The block matrix `[I+FH,FZ;H,Z]`. -/
def lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (U × K) →ₗ[F2] (U × C) :=
  base U K C + (graph Z P.1).comp (lower Z P.2)

@[simp] theorem lift_apply (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z)
    (p : U × K) :
    lift Z P p = (p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      ((P.2 p.1 : Z.range) : C) + Z p.2) := by
  simp [lift, graph, lower]

@[simp] theorem compress_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    compress (lift Z P) = Z := by
  ext k
  simp

end UniqueGamesTheorem.Appendix.CompressionCount

end

section

/-! The actual Appendix A.4 index encoding. Its kernel and range recover the
two subspaces, and its quotient relation recovers the linear map. The final
count follows from this injection into a genuine binary linear-map space. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A4IndexCount

section Generic

variable {K : Type*} [Field K]

variable {V W : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def quotientRestriction (B B0 : Submodule K W) : B0 →ₗ[K] (W ⧸ B) :=
  B.mkQ.comp B0.subtype

theorem ker_quotientRestriction (B B0 : Submodule K W) :
    (quotientRestriction B B0).ker = B.comap B0.subtype := by
  ext b
  change B.mkQ (b : W) = 0 ↔ (b : W) ∈ B
  exact Submodule.Quotient.mk_eq_zero B

def Valid (A : Submodule K V) (B : Submodule K W)
    (p : LinearIdentities.A4Index (K := K) (W := W) (V := V)) : Prop :=
  p.1 ≤ A ∧ B ≤ p.2.1 ∧ p.2.2.ker = B.comap p.2.1.subtype ∧
    p.2.2.range = A.map p.1.mkQ

abbrev Index (A : Submodule K V) (B : Submodule K W) :=
  {p : LinearIdentities.A4Index (K := K) (W := W) (V := V) // Valid A B p}

end Generic

end UniqueGamesTheorem.Appendix.A4IndexCount

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixCharactersLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Trace characters on actual finite binary matrix spaces. -/

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixCharacters

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear

abbrev F2 := UniqueGamesTheorem.Integration.BinaryLinear.F2

/-- The binary trace pairing between oppositely oriented matrices. -/
def tracePair {n m : Nat} (X : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) : F2 := Matrix.trace (X * S)

@[simp] theorem tracePair_zero_left {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    tracePair (0 : Matrix (Fin n) (Fin m) F2) S = 0 := by simp [tracePair]

@[simp] theorem tracePair_zero_right {n m : Nat} (X : Matrix (Fin n) (Fin m) F2) :
    tracePair X (0 : Matrix (Fin m) (Fin n) F2) = 0 := by simp [tracePair]

theorem tracePair_add_left {n m : Nat} (X Y : Matrix (Fin n) (Fin m) F2)
    (S : Matrix (Fin m) (Fin n) F2) :
    tracePair (X + Y) S = tracePair X S + tracePair Y S := by
  simp [tracePair, Matrix.add_mul]

/-- The unique nontrivial complex-valued character of the binary field. -/
def binarySign (a : F2) : ℂ := if a = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by simp [binarySign]
@[simp] theorem binarySign_one : binarySign 1 = -1 := by simp [binarySign]

theorem binarySign_add (a b : F2) : binarySign (a + b) = binarySign a * binarySign b := by
  have htwo : (1 : F2) + 1 = 0 := by decide
  rcases scalar_cases a with rfl | rfl <;>
    rcases scalar_cases b with rfl | rfl <;> simp [htwo]

@[simp] theorem binarySign_im (a : F2) : (binarySign a).im = 0 := by
  unfold binarySign
  split <;> simp

@[simp] theorem binarySign_mul_self (a : F2) : binarySign a * binarySign a = 1 := by
  unfold binarySign
  split <;> simp

section LinearFunctionals

variable {E : Type*} [AddCommGroup E] [Module F2 E]

/-- A binary linear functional determines a complex additive character. -/
def linearFunctionalCharacter (φ : E →ₗ[F2] F2) : AddChar E ℂ where
  toFun x := binarySign (φ x)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [map_add, binarySign_add]

@[simp] theorem linearFunctionalCharacter_apply (φ : E →ₗ[F2] F2) (x : E) :
    linearFunctionalCharacter φ x = binarySign (φ x) := rfl

@[simp] theorem linearFunctionalCharacter_zero :
    linearFunctionalCharacter (0 : E →ₗ[F2] F2) = 0 := by
  ext x
  simp

end LinearFunctionals

def traceCharacter {n m : Nat} (S : Matrix (Fin m) (Fin n) F2) :
    AddChar (Matrix (Fin n) (Fin m) F2) ℂ where
  toFun X := binarySign (tracePair X S)
  map_zero_eq_one' := by simp
  map_add_eq_mul' X Y := by rw [tracePair_add_left, binarySign_add]

@[simp] theorem traceCharacter_apply {n m : Nat} (S : Matrix (Fin m) (Fin n) F2)
    (X : Matrix (Fin n) (Fin m) F2) :
    traceCharacter S X = binarySign (tracePair X S) := rfl

@[simp] theorem traceCharacter_zero {n m : Nat} :
    traceCharacter (0 : Matrix (Fin m) (Fin n) F2) = 0 := by
  ext X
  simp

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- The basis-independent trace pairing in the statement of Lemma 2.1. -/
def linearTracePair (X : E →ₗ[F2] F) (S : F →ₗ[F2] E) : F2 :=
  LinearMap.trace F2 F (X.comp S)

@[simp] theorem linearTracePair_zero_left (S : F →ₗ[F2] E) :
    linearTracePair (0 : E →ₗ[F2] F) S = 0 := by simp [linearTracePair]

@[simp] theorem linearTracePair_zero_right (X : E →ₗ[F2] F) :
    linearTracePair X (0 : F →ₗ[F2] E) = 0 := by simp [linearTracePair]

theorem linearTracePair_add_left (X Y : E →ₗ[F2] F) (S : F →ₗ[F2] E) :
    linearTracePair (X + Y) S = linearTracePair X S + linearTracePair Y S := by
  simp [linearTracePair, LinearMap.add_comp]

/-- The trace character on actual linear maps, with no choice of basis. -/
def linearTraceCharacter (S : F →ₗ[F2] E) : AddChar (E →ₗ[F2] F) ℂ where
  toFun X := binarySign (linearTracePair X S)
  map_zero_eq_one' := by simp
  map_add_eq_mul' X Y := by rw [linearTracePair_add_left, binarySign_add]

@[simp] theorem linearTraceCharacter_apply (S : F →ₗ[F2] E) (X : E →ₗ[F2] F) :
    linearTraceCharacter S X = binarySign (linearTracePair X S) := rfl

@[simp] theorem linearTraceCharacter_zero :
    linearTraceCharacter (0 : F →ₗ[F2] E) = 0 := by
  ext X
  simp

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixCharacters

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual reindexing of Appendix A.4 geometric witnesses by their raw triples.
The original nonzero weak-pair condition is equivalent to positive total
restriction order plus frequency rank. -/

noncomputable section

namespace UniqueGamesTheorem.Appendix.A13Index

open Module
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions (order)

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev Triple := LinearIdentities.A4Index (K := F2) (W := F) (V := E)

def weakA (q : Triple (E := E) (F := F)) : Submodule F2 E :=
  q.2.2.range.comap q.1.mkQ

def weakB (q : Triple (E := E) (F := F)) : Submodule F2 F :=
  q.2.2.ker.map q.2.1.subtype

theorem recover_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakA p.val = A := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.range.comap A0.mkQ = A
  rw [hR]
  ext a
  change A0.mkQ a ∈ A.map A0.mkQ ↔ a ∈ A
  constructor
  · intro ha
    rcases Submodule.mem_map.mp ha with ⟨v, hv, he⟩
    have hm : a - v ∈ A0 := by
      apply (Submodule.Quotient.mk_eq_zero A0).mp
      change A0.mkQ (a - v) = 0
      rw [map_sub, he, sub_self]
    simpa only [sub_add_cancel] using A.add_mem (hA hm) hv
  · intro ha
    exact Submodule.mem_map.mpr ⟨a, ha, rfl⟩

theorem recover_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) : weakB p.val = B := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change X.ker.map B0.subtype = B
  rw [hK]
  ext b
  constructor
  · intro hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact hv
  · intro hb
    exact Submodule.mem_map.mpr ⟨⟨b, hB hb⟩, hb, rfl⟩

theorem canonicalValid (q : Triple (E := E) (F := F)) :
    A4IndexCount.Valid (weakA q) (weakB q) q := by
  rcases q with ⟨A0, B0, X⟩
  change A0 ≤ X.range.comap A0.mkQ ∧ X.ker.map B0.subtype ≤ B0 ∧
    X.ker = (X.ker.map B0.subtype).comap B0.subtype ∧
    X.range = (X.range.comap A0.mkQ).map A0.mkQ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    change A0.mkQ a ∈ X.range
    have hz : A0.mkQ a = 0 := (Submodule.Quotient.mk_eq_zero A0).mpr ha
    rw [hz]
    exact X.range.zero_mem
  · intro b hb
    rcases Submodule.mem_map.mp hb with ⟨v, hv, rfl⟩
    exact v.property
  · ext b
    constructor
    · intro hb
      exact Submodule.mem_map.mpr ⟨b, hb, rfl⟩
    · intro hb
      change (b : F) ∈ X.ker.map B0.subtype at hb
      rcases Submodule.mem_map.mp hb with ⟨v, hv, he⟩
      have h : v = b := Subtype.ext he
      simpa only [h] using hv
  · ext z
    constructor
    · intro hz
      obtain ⟨v, rfl⟩ := A0.mkQ_surjective z
      exact Submodule.mem_map.mpr ⟨v, hz, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨v, hv, rfl⟩
      exact hv

variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]

omit [FiniteDimensional F2 F] in
theorem dim_weakA {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 A = finrank F2 p.val.1 + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 A = finrank F2 A0 + finrank F2 X.range
  let Q := A4IndexCount.quotientRestriction A0 A
  have hQR : Q.range = X.range := by
    rw [hR]
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.mem_map.mpr ⟨a.val, a.property, rfl⟩
    · intro hz
      rcases Submodule.mem_map.mp hz with ⟨a, ha, he⟩
      exact ⟨⟨a, ha⟩, he⟩
  have hQK : finrank F2 Q.ker = finrank F2 A0 := by
    rw [A4IndexCount.ker_quotientRestriction]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv A ⟨A0, hA⟩).finrank_eq.symm
  have h := Q.finrank_range_add_finrank_ker
  rw [hQR, hQK] at h
  omega

omit [FiniteDimensional F2 E] in
theorem codim_weakB {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    finrank F2 (F ⧸ B) =
      finrank F2 (F ⧸ p.val.2.1) + finrank F2 p.val.2.2.range := by
  rcases p with ⟨⟨A0, B0, X⟩, hA, hB, hK, hR⟩
  change finrank F2 (F ⧸ B) = finrank F2 (F ⧸ B0) + finrank F2 X.range
  have hKB : finrank F2 X.ker = finrank F2 B := by
    rw [hK]
    exact (SubmoduleInterval.lowerIntervalSpaceEquiv B0 ⟨B, hB⟩).finrank_eq.symm
  have h := X.finrank_range_add_finrank_ker
  rw [hKB] at h
  have hBdim := B.finrank_quotient_add_finrank
  have hB0dim := B0.finrank_quotient_add_finrank
  omega

def size (q : Triple (E := E) (F := F)) : Nat :=
  order q.1 q.2.1 + finrank F2 q.2.2.range

theorem weak_order {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    order A B = order p.val.1 p.val.2.1 + 2 * finrank F2 p.val.2.2.range := by
  have ha := dim_weakA p
  have hb := codim_weakB p
  dsimp only [order]
  omega

theorem order_eq_zero_iff (A : Submodule F2 E) (B : Submodule F2 F) :
    order A B = 0 ↔ A = ⊥ ∧ B = ⊤ := by
  constructor
  · intro h
    change finrank F2 A + finrank F2 (F ⧸ B) = 0 at h
    have ha : finrank F2 A = 0 := by omega
    have hb : finrank F2 (F ⧸ B) = 0 := by omega
    refine ⟨Submodule.finrank_eq_zero.mp ha, ?_⟩
    apply Submodule.eq_top_iff_finrank_eq.mpr
    have hq := B.finrank_quotient_add_finrank
    omega
  · rintro ⟨rfl, rfl⟩
    simpa [order] using
      (Module.finrank_eq_zero_of_subsingleton F2 (F ⧸ (⊤ : Submodule F2 F)))

theorem valid_positive_iff {A : Submodule F2 E} {B : Submodule F2 F}
    (p : A4IndexCount.Index A B) :
    (A, B) ≠ (⊥, ⊤) ↔ 0 < size p.val := by
  have h := weak_order p
  constructor
  · intro hp
    by_contra ht
    have hz : order A B = 0 := by
      dsimp only [size] at ht
      omega
    rcases (order_eq_zero_iff A B).mp hz with ⟨hA, hB⟩
    exact hp (Prod.ext hA hB)
  · intro ht hp
    have hAB : A = ⊥ ∧ B = ⊤ := Prod.mk.inj hp
    have hz := (order_eq_zero_iff A B).mpr hAB
    dsimp only [size] at ht
    omega

abbrev WeakPositive :=
  {p : Submodule F2 E × Submodule F2 F // p ≠ (⊥, ⊤)}

abbrev PositiveWitness :=
  Σ p : WeakPositive (E := E) (F := F), A4IndexCount.Index p.val.1 p.val.2

abbrev PositiveTriple := {q : Triple (E := E) (F := F) // 0 < size q}

abbrev BoundedPositiveTriple (d : Nat) :=
  {q : Triple (E := E) (F := F) // 0 < size q ∧ size q ≤ d}

def positiveMap (p : PositiveWitness (E := E) (F := F)) :
    PositiveTriple (E := E) (F := F) :=
  ⟨p.2.val, (valid_positive_iff p.2).mp p.1.property⟩

theorem positiveMap_injective :
    Function.Injective (positiveMap (E := E) (F := F)) := by
  rintro ⟨⟨⟨A, B⟩, hp⟩, p⟩ ⟨⟨⟨A', B'⟩, hp'⟩, p'⟩ he
  have hraw : p.val = p'.val := congrArg Subtype.val he
  have hA : A = A' := by
    calc
      A = weakA p.val := (recover_weakA p).symm
      _ = weakA p'.val := congrArg weakA hraw
      _ = A' := recover_weakA p'
  have hB : B = B' := by
    calc
      B = weakB p.val := (recover_weakB p).symm
      _ = weakB p'.val := congrArg weakB hraw
      _ = B' := recover_weakB p'
  cases hA
  cases hB
  have hpp : p = p' := Subtype.ext hraw
  cases hpp
  rfl

def positiveInverse (q : PositiveTriple (E := E) (F := F)) :
    PositiveWitness (E := E) (F := F) :=
  ⟨⟨(weakA q.val, weakB q.val),
      (valid_positive_iff ⟨q.val, canonicalValid q.val⟩).mpr q.property⟩,
    ⟨q.val, canonicalValid q.val⟩⟩

def positiveEquiv : PositiveWitness (E := E) (F := F) ≃
    PositiveTriple (E := E) (F := F) :=
  Equiv.ofBijective positiveMap ⟨positiveMap_injective, by
    intro q
    refine ⟨positiveInverse q, ?_⟩
    exact Subtype.ext rfl⟩

@[simp] theorem positiveMap_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveMap p).val = p.2.val := rfl

@[simp] theorem positiveEquiv_val (p : PositiveWitness (E := E) (F := F)) :
    (positiveEquiv p).val = p.2.val := rfl

@[instance_reducible]
def tripleFintype [Finite E] [Finite F] :
    Fintype (Triple (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  letI (A : Submodule F2 E) : Finite (E ⧸ A) :=
    Finite.of_surjective A.mkQ A.mkQ_surjective
  letI (A : Submodule F2 E) (B : Submodule F2 F) :
      Fintype (B →ₗ[F2] (E ⧸ A)) := by
    letI : Fintype B := Fintype.ofFinite _
    letI : Fintype (E ⧸ A) := Fintype.ofFinite _
    exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) =>
      (L : B → E ⧸ A)) DFunLike.coe_injective
  exact inferInstance

@[instance_reducible]
def weakPositiveFintype [Finite E] [Finite F] :
    Fintype (WeakPositive (E := E) (F := F)) := by
  classical
  letI : Fintype (Submodule F2 E) := SubspaceExtensions.subspaceFintype
  letI : Fintype (Submodule F2 F) := SubspaceExtensions.subspaceFintype
  exact inferInstance

@[instance_reducible]
def geometricIndexFintype [Finite E] [Finite F]
    (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (A4IndexCount.Index A B) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def positiveWitnessFintype [Finite E] [Finite F] :
    Fintype (PositiveWitness (E := E) (F := F)) := by
  classical
  letI := weakPositiveFintype (E := E) (F := F)
  letI (A : Submodule F2 E) (B : Submodule F2 F) := geometricIndexFintype A B
  exact inferInstance

@[instance_reducible]
def positiveTripleFintype [Finite E] [Finite F] :
    Fintype (PositiveTriple (E := E) (F := F)) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

@[instance_reducible]
def boundedPositiveTripleFintype [Finite E] [Finite F] (d : Nat) :
    Fintype (BoundedPositiveTriple (E := E) (F := F) d) := by
  classical
  letI := tripleFintype (E := E) (F := F)
  exact inferInstance

end UniqueGamesTheorem.Appendix.A13Index

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_DerivativeInduction
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Appendix.DerivativeInduction

open UniqueGamesTheorem.Integration.BinaryLinear
open LinearMap

variable {B U A C : Type*}
variable [AddCommGroup B] [Module F2 B] [AddCommGroup U] [Module F2 U]
variable [AddCommGroup A] [Module F2 A] [AddCommGroup C] [Module F2 C]

/-- The actual complement conditions after choosing domain/codomain splittings. -/
def IsAntecedent (Z : B →ₗ[F2] C) (X : (B × U) →ₗ[F2] (A × C)) : Prop :=
  (∀ b, (X (b, 0)).2 = Z b) ∧
  Disjoint X.range (LinearMap.inl F2 A C).range ∧
  (LinearMap.inl F2 B U).range ⊔ X.ker = ⊤

abbrev Antecedent (Z : B →ₗ[F2] C) :=
  { X : (B × U) →ₗ[F2] (A × C) // IsAntecedent Z X }

theorem antecedent_image_from_left (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    ∃ b : B, X p = X (b, 0) := by
  have hp : p ∈ (LinearMap.inl F2 B U).range ⊔ X.ker := by
    rw [hX.2.2]
    trivial
  obtain ⟨q, hq, r, hr, he⟩ := Submodule.mem_sup.mp hp
  obtain ⟨b, rfl⟩ := hq
  refine ⟨b, ?_⟩
  rw [← he, map_add]
  have hz : X r = 0 := hr
  simp only [hz, add_zero, LinearMap.inl_apply]

theorem antecedent_bottom_mem_range (Z : B →ₗ[F2] C)
    (X : (B × U) →ₗ[F2] (A × C)) (hX : IsAntecedent Z X) (p : B × U) :
    (X p).2 ∈ Z.range := by
  obtain ⟨b, hb⟩ := antecedent_image_from_left Z X hX p
  exact ⟨b, (hX.1 b).symm.trans (congrArg Prod.snd hb).symm⟩

/-- Values on the omitted domain complement, compressed into `range Z`. -/
noncomputable def complementParameter (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) : U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 A C).comp (X.val.comp (LinearMap.inr F2 B U))).codRestrict
    Z.range (fun u => antecedent_bottom_mem_range Z X.val X.property (0, u))

@[simp] theorem complementParameter_val (Z : B →ₗ[F2] C)
    (X : Antecedent (U := U) (A := A) Z) (u : U) :
    (complementParameter Z X u : C) = (X.val (0, u)).2 := rfl

/-- The block matrix `[F Z, F H; Z, H]`. -/
def lift (Z : B →ₗ[F2] C) (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) :
    (B × U) →ₗ[F2] (A × C) :=
  (F.comp (Z.rangeRestrict.coprod H)).prod
    (Z.range.subtype.comp (Z.rangeRestrict.coprod H))

@[simp] theorem lift_apply (Z : B →ₗ[F2] C)
    (F : Z.range →ₗ[F2] A) (H : U →ₗ[F2] Z.range) (p : B × U) :
    lift Z F H p = (F (Z.rangeRestrict p.1 + H p.2),
      ((Z.rangeRestrict p.1 + H p.2 : Z.range) : C)) := rfl

section Subspaces

variable {W V : Type*} [AddCommGroup W] [Module F2 W]
  [AddCommGroup V] [Module F2 V]

noncomputable def coordinateEquiv (P E : Submodule F2 W) (Q D : Submodule F2 V)
    (hP : IsCompl P E) (hQ : IsCompl Q D) :
    (W →ₗ[F2] V) ≃ₗ[F2] ((P × E) →ₗ[F2] (Q × D)) :=
  LinearEquiv.arrowCongr (P.prodEquivOfIsCompl E hP).symm
    (Q.prodEquivOfIsCompl D hQ).symm

@[simp] theorem coordinateEquiv_apply (P E : Submodule F2 W)
    (Q D : Submodule F2 V) (hP : IsCompl P E) (hQ : IsCompl Q D)
    (X : W →ₗ[F2] V) (p : P × E) :
    coordinateEquiv P E Q D hP hQ X p =
      (Q.prodEquivOfIsCompl D hQ).symm (X ((p.1 : W) + p.2)) := rfl

end Subspaces

end UniqueGamesTheorem.Appendix.DerivativeInduction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_AntecedentCountLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Exact compression fibers for arbitrary binary linear maps

This is the general cardinality assertion in Lemma A.2, with the actual kernel
restriction and range quotient. The map X is arbitrary; no chosen-coordinate
or fixed-dimension hypothesis occurs in `card_fiber`.
-/

namespace UniqueGamesTheorem.Appendix.FullCompression

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open Module

noncomputable section

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]

/-- Restrict a dual map to `ker X` and then quotient by `range X`. -/
def compression (X Y : E →ₗ[F2] F) : X.ker →ₗ[F2] (F ⧸ X.range) :=
  X.range.mkQ.comp (Y.comp X.ker.subtype)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] in
@[simp] theorem compression_apply (X Y : E →ₗ[F2] F) (k : X.ker) :
    compression X Y k = X.range.mkQ (Y k) := rfl

end

end UniqueGamesTheorem.Appendix.FullCompression

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_MatrixNoiseLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The actual rank-one averaging operator on finite binary matrix spaces.
The outer weights describe any finite law for `v`; the functional `ℓ` is
uniform. Normalization is needed for eigenvalue bounds, not diagonalization. -/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace UniqueGamesTheorem.Fourier.MatrixNoise

open scoped BigOperators Matrix
open UniqueGamesTheorem.Integration.BinaryLinear (Vector)
open UniqueGamesTheorem.Fourier.MatrixCharacters

/-- The additive character obtained by pairing against a binary vector. -/
def dotCharacter {m : Nat} (w : Vector m) : AddChar (Vector m) ℂ where
  toFun ℓ := binarySign (ℓ ⬝ᵥ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [add_dotProduct, binarySign_add]

@[simp] theorem dotCharacter_apply {m : Nat} (w ℓ : Vector m) :
    dotCharacter w ℓ = binarySign (ℓ ⬝ᵥ w) := rfl

section LinearMaps

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

/-- Evaluation of a uniformly chosen linear functional is a binary character. -/
def evaluationCharacter (w : E) : AddChar (E →ₗ[F2] F2) ℂ where
  toFun ℓ := binarySign (ℓ w)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp only [LinearMap.add_apply, binarySign_add]

@[simp] theorem evaluationCharacter_apply (w : E) (ℓ : E →ₗ[F2] F2) :
    evaluationCharacter w ℓ = binarySign (ℓ w) := rfl

end LinearMaps

end UniqueGamesTheorem.Fourier.MatrixNoise

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_WeightedFourthMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The corrected weighted fourth coefficient-energy estimate of Appendix A.4.
The proof uses the actual compression-fiber energy theorem and the actual
rank-additive predecessor count, not hypotheses replacing either result.
The remaining Fourier interpretation is separate: `energy a X` is the sum of
squares of coefficients after the actual derivative compression.
-/

noncomputable section
namespace UniqueGamesTheorem.Appendix.WeightedFourthMoment

open Module
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
attribute [local instance] Classical.propDecidable

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)]

@[instance_reducible] def vectorFintype (V : Type*) [AddCommGroup V] [Module F2 V]
    [FiniteDimensional F2 V] : Fintype V :=
  Fintype.ofEquiv (Fin (finrank F2 V) → F2) (Module.finBasis F2 V).equivFun.symm.toEquiv

@[instance_reducible] def compressedFintype (X : E →ₗ[F2] F) : Fintype (X.ker →ₗ[F2] (F ⧸ X.range)) := by
  classical
  letI := vectorFintype X.ker
  letI := vectorFintype (F ⧸ X.range)
  exact Fintype.ofInjective DFunLike.coe DFunLike.coe_injective

end UniqueGamesTheorem.Appendix.WeightedFourthMoment

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_RestrictionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace UniqueGamesTheorem.Appendix.Derivatives
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters
attribute [local instance] Classical.propDecidable

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

def HybridIndex (d : ℕ) :=
  {p : Submodule F2 E × Submodule F2 F //
    UniqueGamesTheorem.Fourier.MatrixRestrictions.order p.1 p.2 ≤ d}

end UniqueGamesTheorem.Appendix.Derivatives

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_OperatorPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Actual Fourier-projector partitions for Appendix A.4 and A.5

The partitions use the proved unique geometric selectors on each actual
Fourier index. Their finite index types are the canonical counting types.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives

namespace UniqueGamesTheorem.Appendix.OperatorPartitions

attribute [local instance] Classical.propDecidable

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

open UniqueGamesTheorem.Appendix.LinearIdentities

def A5Geometry (X : F →ₗ[F2] E) (A : Submodule F2 E) (B : Submodule F2 F)
    (p : Submodule F2 E × Submodule F2 F) : Prop :=
  Disjoint p.1 X.range ∧ p.1 ⊔ X.range = A ∧
    p.2 ⊔ X.ker = ⊤ ∧ p.2 ⊓ X.ker = B

abbrev A5GeometricIndex (X : F →ₗ[F2] E)
    (A : Submodule F2 E) (B : Submodule F2 F) :=
  {p : Submodule F2 E × Submodule F2 F // A5Geometry X A B p}

end UniqueGamesTheorem.Appendix.OperatorPartitions

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_HybridCompositionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Native derivative norm decompositions for Appendix A.4 and A.5

The finite projector partitions and exact affine restriction transport yield
norm bounds for the actual derivative operators. The cardinality factors are
explicit: numerical estimates on the geometric index sets are separate lemmas.
-/

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier
open UniqueGamesTheorem.Appendix.Derivatives
open UniqueGamesTheorem.Appendix.OperatorPartitions
open UniqueGamesTheorem.Appendix.LinearIdentities

namespace UniqueGamesTheorem.Appendix.OperatorNorm

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]
  [Finite E] [Finite F]

local instance quotientFinite (A : Submodule F2 E) : Finite (E ⧸ A) :=
  Finite.of_surjective A.mkQ A.mkQ_surjective

local instance compressedDualFintype (A : Submodule F2 E) (B : Submodule F2 F) :
    Fintype (B →ₗ[F2] (E ⧸ A)) := by
  classical
  letI : Fintype B := Fintype.ofFinite _
  letI : Fintype (E ⧸ A) := Fintype.ofFinite _
  exact Fintype.ofInjective (fun L : B →ₗ[F2] (E ⧸ A) => (L : B → E ⧸ A))
    DFunLike.coe_injective

end UniqueGamesTheorem.Appendix.OperatorNorm

end

end

section

/-! Natural changes of domain and codomain preserve rank, Fourier projectors,
and map-derivative energies. The quotient/subtype specialization transports
the actual labels occurring in nested hybrid derivatives. -/

noncomputable section
namespace UniqueGamesTheorem.Appendix.NaturalTransport
open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable

section Nested
variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Finite F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

local instance hybridCompositionQuotientFinite_r6089fa_1 {V : Type*}
    [AddCommGroup V] [Module F2 V] [Finite V]
    (P : Submodule F2 V) : Finite (V ⧸ P) :=
  Finite.of_surjective P.mkQ P.mkQ_surjective
local instance hybridCompositionCompressedDualFintype_r6089fa_1 {U V : Type*}
    [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V]
    (A : Submodule F2 U) (B : Submodule F2 V) : Fintype (B →ₗ[F2] (U ⧸ A)) :=
  OperatorNorm.compressedDualFintype A B
def quotientFactor (A : Submodule F2 E) (C : Submodule F2 (E ⧸ A)) :
    (E ⧸ C.comap A.mkQ) ≃ₗ[F2] ((E ⧸ A) ⧸ C) :=
  (Submodule.quotEquivOfEq (C.comap A.mkQ) (C.mkQ.comp A.mkQ).ker
    (by rw [LinearMap.ker_comp, Submodule.ker_mkQ])).trans
      ((C.mkQ.comp A.mkQ).quotKerEquivOfSurjective
        (C.mkQ_surjective.comp A.mkQ_surjective))

omit [FiniteDimensional F2 E] [Finite E] in
@[simp] theorem quotientFactor_mkQ (A : Submodule F2 E)
    (C : Submodule F2 (E ⧸ A)) (x : E) :
    quotientFactor A C ((C.comap A.mkQ).mkQ x) = C.mkQ (A.mkQ x) := by
  simp [quotientFactor]

def outputFactor (B : Submodule F2 F) (D : Submodule F2 B) :
    D ≃ₗ[F2] (D.map B.subtype) :=
  Submodule.equivMapOfInjective B.subtype Subtype.val_injective D

omit [FiniteDimensional F2 F] [Finite F] in
@[simp] theorem outputFactor_val (B : Submodule F2 F) (D : Submodule F2 B) (x : D) :
    ((outputFactor B D x : D.map B.subtype) : F) = ((x : B) : F) := rfl

end Nested
end UniqueGamesTheorem.Appendix.NaturalTransport

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A5FrequencyTransportLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace UniqueGamesTheorem

/-! Pointwise identification of the natural frequency transport with the
relative frequency used by the actual reverse compression fibers. -/

/-! Canonical indices for the Appendix A.5 induction passage. The outer
hybrid index is recovered from its actual geometric pair, so forgetting it
does not increase multiplicity. -/

namespace Appendix.A5Passage

open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.Derivatives
attribute [local instance] Classical.propDecidable
attribute [local instance] OperatorNorm.quotientFinite OperatorNorm.compressedDualFintype

variable {E F : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup F] [Module F2 F]

abbrev OuterIndex (X : F →ₗ[F2] E) (e : Nat) :=
  HybridIndex (E := E ⧸ X.range) (F := X.ker) e

def LiftedA (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 E :=
  s.val.1.comap X.range.mkQ

def LiftedB (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) : Submodule F2 F :=
  s.val.2.map X.ker.subtype

abbrev Pair (X : F →ₗ[F2] E) {e : Nat} (s : OuterIndex X e) :=
  OperatorPartitions.A5GeometricIndex X (LiftedA X s) (LiftedB X s)

abbrev Passage (X : F →ₗ[F2] E) (e : Nat) :=
  Σ s : OuterIndex X e, Pair X s

def forget (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    Submodule F2 E × Submodule F2 F := q.2.val

@[simp] theorem forget_val (X : F →ₗ[F2] E) (e : Nat) (q : Passage X e) :
    forget X e q = q.2.val := rfl

end Appendix.A5Passage

/-!
# The actual weighted reversal in Appendix A.5

The forward index records an original positive triple and an actual A.5
passage. Its checked reverse-fiber bound permits finite weighted grouping.
The resulting weights are the moments of the actual transported derivatives.
No degree hypothesis or analytic induction hypothesis is used here.
-/

/-! Actual norm and induction steps for Proposition A.5. The universal degree
property below is the motive for strong induction on the degree; defining
that property does not assert its truth. -/

end UniqueGamesTheorem

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions

namespace UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] Classical.propDecidable

@[instance_reducible] def linearMapFintype {U V : Type*} [AddCommGroup U] [Module F2 U]
    [AddCommGroup V] [Module F2 V] [Finite U] [Finite V] : Fintype (U →ₗ[F2] V) := by
  classical
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype V := Fintype.ofFinite V
  exact Fintype.ofInjective (fun φ : U →ₗ[F2] V => (φ : U → V)) DFunLike.coe_injective

end UniqueGamesTheorem.Appendix.RankLevelFilter

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartitionsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PointwiseSpaces

variable {X Y Z : Type*}

def pullback (𝕜 : Type*) [Field 𝕜] (r : X → Y) :
    (Y → 𝕜) →ₗ[𝕜] (X → 𝕜) where
  toFun f := fun x => f (r x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {𝕜 : Type*} [Field 𝕜]

@[simp] theorem pullback_apply (r : X → Y) (f : Y → 𝕜) (x : X) :
    pullback 𝕜 r f x = f (r x) := rfl

@[simp] theorem pullback_one (r : X → Y) :
    pullback 𝕜 r (1 : Y → 𝕜) = (1 : X → 𝕜) := rfl

@[simp] theorem pullback_mul (r : X → Y) (f g : Y → 𝕜) :
    pullback 𝕜 r (f * g) = pullback 𝕜 r f * pullback 𝕜 r g := rfl

def squareSpace (H : Submodule 𝕜 (X → 𝕜)) : Submodule 𝕜 (X → 𝕜) :=
  Submodule.span 𝕜 {u | ∃ f ∈ H, ∃ g ∈ H, f * g = u}

theorem mul_mem_squareSpace (H : Submodule 𝕜 (X → 𝕜))
    {f g : X → 𝕜} (hf : f ∈ H) (hg : g ∈ H) :
    f * g ∈ squareSpace H :=
  Submodule.subset_span ⟨f, hf, g, hg, rfl⟩

theorem squareSpace_pullback_le (r : X → Y)
    (H : Submodule 𝕜 (Y → 𝕜)) (K : Submodule 𝕜 (X → 𝕜))
    (h : H.map (pullback 𝕜 r) ≤ K) :
    (squareSpace H).map (pullback 𝕜 r) ≤ squareSpace K := by
  apply (Submodule.map_span_le _ _ _).2
  rintro u ⟨f, hf, g, hg, rfl⟩
  simpa only [pullback_mul] using mul_mem_squareSpace K
    (h (Submodule.mem_map_of_mem hf)) (h (Submodule.mem_map_of_mem hg))

section Children

variable {J : Type*} {D E : J → Type*}

def childSpace (r : ∀ i, X → D i) (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) :
    Submodule 𝕜 (X → 𝕜) :=
  ⨆ i, (squareSpace (H i)).map (pullback 𝕜 (r i))

theorem childSpace_pullback_le (p : X → Y)
    (rY : ∀ i, Y → D i) (rX : ∀ i, X → E i) (q : ∀ i, E i → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) (K : ∀ i, Submodule 𝕜 (E i → 𝕜))
    (hcomm : ∀ i x, q i (rX i x) = rY i (p x))
    (hchild : ∀ i, (H i).map (pullback 𝕜 (q i)) ≤ K i) :
    (childSpace rY H).map (pullback 𝕜 p) ≤ childSpace rX K := by
  simp only [childSpace, Submodule.map_iSup]
  apply iSup_mono
  intro i
  have hcomp : (pullback 𝕜 p).comp (pullback 𝕜 (rY i)) =
      (pullback 𝕜 (rX i)).comp (pullback 𝕜 (q i)) := by
    ext f x
    exact congrArg f (hcomm i x).symm
  calc
    ((squareSpace (H i)).map (pullback 𝕜 (rY i))).map (pullback 𝕜 p) =
        ((squareSpace (H i)).map (pullback 𝕜 (q i))).map (pullback 𝕜 (rX i)) := by
      rw [← Submodule.map_comp, ← Submodule.map_comp, hcomp]
    _ ≤ (squareSpace (K i)).map (pullback 𝕜 (rX i)) :=
      Submodule.map_mono (squareSpace_pullback_le (q i) (H i) (K i) (hchild i))

end Children

end PerfectCompleteness.PointwiseSpaces

end

section

namespace PerfectCompleteness.ProductReduction

variable {I : Type*} {X R W : I → Type*} {Y : Type*}

def productMap (r : ∀ i, X i → R i) (x : ∀ i, X i) : ∀ i, R i :=
  fun i => r i (x i)

@[simp] theorem productMap_apply (r : ∀ i, X i → R i)
    (x : ∀ i, X i) (i : I) : productMap r x i = r i (x i) := rfl

end PerfectCompleteness.ProductReduction

end

section

namespace PerfectCompleteness.ProjectedColumnSlice

noncomputable section

variable {𝕜 H H' W : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup H'] [Module 𝕜 H']
  [AddCommGroup W] [Module 𝕜 W]
  (i : H' →ₗ[𝕜] H) (Z : Submodule 𝕜 (Module.Dual 𝕜 H))

def projectedColumns : Submodule 𝕜 (Module.Dual 𝕜 H') := Z.map i.dualMap

def restrictionZ : Z →ₗ[𝕜] projectedColumns i Z :=
  (i.dualMap.comp Z.subtype).codRestrict (projectedColumns i Z) (by
    intro z
    exact Submodule.mem_map.mpr ⟨z.val, z.property, rfl⟩)

@[simp] theorem restrictionZ_val (z : Z) :
    (restrictionZ i Z z : Module.Dual 𝕜 H') = i.dualMap z := rfl

@[simp] theorem restrictionZ_apply (z : Z) (h : H') :
    (restrictionZ i Z z : Module.Dual 𝕜 H') h = z.val (i h) := rfl

def targetQ (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W) : projectedColumns i Z →ₗ[𝕜] W :=
  X₀.domRestrict (projectedColumns i Z)

@[simp] theorem targetQ_apply (X₀ : Module.Dual 𝕜 H' →ₗ[𝕜] W)
    (q : projectedColumns i Z) : targetQ i Z X₀ q = X₀ q.val := rfl

end
end PerfectCompleteness.ProjectedColumnSlice

end

section

namespace PerfectCompleteness.PulledColumnSpace

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {H : Type*} [AddCommGroup H] [Module F2 H]

def pulled (W : Submodule F2 H) (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    Submodule F2 (Module.Dual F2 H) :=
  C.map W.mkQ.dualMap

theorem quotientDual_injective (W : Submodule F2 H) :
    Function.Injective W.mkQ.dualMap :=
  LinearMap.dualMap_injective_of_surjective W.mkQ_surjective

def pulledEquiv (W : Submodule F2 H) (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    C ≃ₗ[F2] pulled W C :=
  Submodule.equivMapOfInjective W.mkQ.dualMap (quotientDual_injective W) C

@[simp] theorem pulledEquiv_val (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (q : C) :
    (pulledEquiv W C q : Module.Dual F2 H) = q.val.comp W.mkQ := rfl

def Candidates (W : Submodule F2 H) (C : Submodule F2 (Module.Dual F2 (H ⧸ W)))
    (center : Module.Dual F2 H) :=
  {q : Module.Dual F2 H // q - center ∈ pulled W C}

def candidateEquiv (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    pulled W C ≃ Candidates W C center where
  toFun q := ⟨center + q.val, by
    have he : center + q.val - center = q.val := by abel
    rw [he]
    exact q.property⟩
  invFun q := ⟨q.val - center, q.property⟩
  left_inv q := by
    apply Subtype.ext
    change center + q.val - center = q.val
    abel
  right_inv q := by
    apply Subtype.ext
    change center + (q.val - center) = q.val
    abel

@[simp] theorem candidateEquiv_val (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H)
    (q : pulled W C) :
    (candidateEquiv W C center q).val = center + q.val := rfl

end
end PerfectCompleteness.PulledColumnSpace

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RecursiveSpaces

open PointwiseSpaces

universe u v w

def Slots (branch : Nat → Nat) : Nat → Type
  | 0 => Unit
  | n + 1 => Fin (branch n) × Slots branch n

variable {branch : Nat → Nat} {n : Nat}

abbrev Assignment (A : Slots branch n → Type u) := ∀ s, A s

abbrev childFamily (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    Slots branch n → Type u := fun s => A (i, s)

def childRestriction (A : Slots branch (n + 1) → Type u) (i : Fin (branch n)) :
    Assignment A → Assignment (childFamily A i) := fun x s => x (i, s)

def space (𝕜 : Type w) [Field 𝕜] (branch : Nat → Nat) :
    (n : Nat) → (A : Slots branch n → Type u) →
      Submodule 𝕜 (Assignment A → 𝕜)
  | 0, _ => ⊤
  | n + 1, A => childSpace (childRestriction A)
      (fun i => space 𝕜 branch n (childFamily A i))

variable {𝕜 : Type w} [Field 𝕜]

@[simp] theorem space_zero (A : Slots branch 0 → Type u) :
    space 𝕜 branch 0 A = ⊤ := rfl

def project {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s → B s) : Assignment A → Assignment B :=
  fun x s => e s (x s)

@[simp] theorem project_apply {A : Slots branch n → Type u} {B : Slots branch n → Type v}
    (e : ∀ s, A s → B s) (x : Assignment A) (s : Slots branch n) :
    project e x s = e s (x s) := rfl

theorem project_child {A : Slots branch (n + 1) → Type u}
    {B : Slots branch (n + 1) → Type v} (e : ∀ s, A s → B s)
    (i : Fin (branch n)) (x : Assignment A) :
    project (fun s => e (i, s)) (childRestriction A i x) =
      childRestriction B i (project e x) := rfl

theorem space_project_le (branch : Nat → Nat) :
    ∀ (n : Nat) (A : Slots branch n → Type u) (B : Slots branch n → Type v)
      (e : ∀ s, A s → B s),
      (space 𝕜 branch n B).map (pullback 𝕜 (project e)) ≤ space 𝕜 branch n A := by
  intro n
  induction n with
  | zero =>
      intro A B e
      exact le_top
  | succ n ih =>
      intro A B e
      apply childSpace_pullback_le (project e) (childRestriction B) (childRestriction A)
        (fun i => project (fun s => e (i, s)))
        (fun i => space 𝕜 branch n (childFamily B i))
        (fun i => space 𝕜 branch n (childFamily A i))
      · intro i x
        exact project_child e i x
      · intro i
        exact ih (childFamily A i) (childFamily B i) (fun s => e (i, s))

theorem squareSpace_project_le (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) :
    (squareSpace (space 𝕜 branch n B)).map (pullback 𝕜 (project e)) ≤
      squareSpace (space 𝕜 branch n A) :=
  squareSpace_pullback_le _ _ _ (space_project_le branch n A B e)

def spacePullback (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) : space 𝕜 branch n B →ₗ[𝕜] space 𝕜 branch n A where
  toFun f := ⟨pullback 𝕜 (project e) f,
    space_project_le branch n A B e (Submodule.mem_map_of_mem f.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem spacePullback_apply (A : Slots branch n → Type u) (B : Slots branch n → Type v)
    (e : ∀ s, A s → B s) (f : space 𝕜 branch n B) (x : Assignment A) :
    (spacePullback A B e f).val x = f.val (project e x) := rfl

end PerfectCompleteness.RecursiveSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_FiniteTrialsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite two-player games with actual joint question distributions.

An answer function receives only its own player's question. In a repeated game,
that question is the entire tuple, so a repeated strategy need not act separately
on coordinates. The predicate may reject invalid answers depending on questions.
All probabilities below are actual finite sums of real weights.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

structure FiniteDistribution (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ x, 0 ≤ weight x
  normalized : ∑ x, weight x = 1

namespace FiniteDistribution

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

def expectation (μ : FiniteDistribution Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x, μ.weight x * f x

def probability (μ : FiniteDistribution Ω) (event : Ω → Bool) : ℝ :=
  ∑ x, if event x then μ.weight x else 0

@[simp] theorem probability_true (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => true) = 1 := by
  simpa [probability] using μ.normalized

@[simp] theorem probability_false (μ : FiniteDistribution Ω) :
    μ.probability (fun _ => false) = 0 := by
  simp [probability]

def transport (μ : FiniteDistribution Ω) (equiv : Ω ≃ Γ) : FiniteDistribution Γ where
  weight y := μ.weight (equiv.symm y)
  nonnegative y := μ.nonnegative (equiv.symm y)
  normalized := by rw [equiv.symm.sum_comp, μ.normalized]

/-- Independent repeated sampling, including the single empty tuple at n=0. -/
def iid (μ : FiniteDistribution Ω) (n : Nat) : FiniteDistribution (Fin n → Ω) where
  weight x := ∏ i, μ.weight (x i)
  nonnegative x := Finset.prod_nonneg fun i _ => μ.nonnegative (x i)
  normalized := by rw [← Fintype.sum_pow, μ.normalized, one_pow]

end FiniteDistribution

structure Game (Q₁ Q₂ A₁ A₂ : Type*) [Fintype Q₁] [Fintype Q₂]
    [Fintype A₁] [Fintype A₂] where
  questions : FiniteDistribution (Q₁ × Q₂)
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool

namespace Game

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def tupleQuestionEquiv (n : Nat) :
    (Fin n → Q₁ × Q₂) ≃ (Fin n → Q₁) × (Fin n → Q₂) where
  toFun questions := (fun i => (questions i).1, fun i => (questions i).2)
  invFun questions := fun i => (questions.1 i, questions.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Parallel repetition retains arbitrary dependence on each full local tuple. -/
def repetition (G : Game Q₁ Q₂ A₁ A₂) (n : Nat) :
    Game (Fin n → Q₁) (Fin n → Q₂) (Fin n → A₁) (Fin n → A₂) := by
  classical
  exact
    { questions := (G.questions.iid n).transport (tupleQuestionEquiv n)
      accepts := fun x y a b => decide (∀ i, G.accepts (x i) (y i) (a i) (b i) = true) }

@[simp] theorem repetition_question_weight (G : Game Q₁ Q₂ A₁ A₂) (n : Nat)
    (questions : (Fin n → Q₁) × (Fin n → Q₂)) :
    (G.repetition n).questions.weight questions =
      ∏ i, G.questions.weight (questions.1 i, questions.2 i) := rfl

end Game

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RecursiveSpaceEquiv

open PointwiseSpaces RecursiveSpaces

universe u v w

variable {𝕜 : Type w} [Field 𝕜] {branch : Nat → Nat} {n : Nat}
  {A : Slots branch n → Type u} {B : Slots branch n → Type v}

def spaceEquiv (e : ∀ s, A s ≃ B s) :
    space 𝕜 branch n B ≃ₗ[𝕜] space 𝕜 branch n A where
  toLinearMap := spacePullback A B (fun s => e s)
  invFun := spacePullback B A (fun s => (e s).symm)
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => e s) (project (fun s => (e s).symm) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).apply_symm_apply (x s)
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => (e s).symm) (project (fun s => e s) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).symm_apply_apply (x s)

@[simp] theorem spaceEquiv_apply (e : ∀ s, A s ≃ B s)
    (f : space 𝕜 branch n B) (x : Assignment A) :
    (spaceEquiv e f).val x = f.val (project (fun s => e s) x) := rfl

def squarePullback (e : ∀ s, A s → B s) :
    squareSpace (space 𝕜 branch n B) →ₗ[𝕜] squareSpace (space 𝕜 branch n A) where
  toFun f := ⟨pullback 𝕜 (project e) f.val,
    squareSpace_project_le A B e (Submodule.mem_map_of_mem f.property)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

def squareEquiv (e : ∀ s, A s ≃ B s) :
    squareSpace (space 𝕜 branch n B) ≃ₗ[𝕜] squareSpace (space 𝕜 branch n A) where
  toLinearMap := squarePullback (fun s => e s)
  invFun := squarePullback (fun s => (e s).symm)
  left_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => e s) (project (fun s => (e s).symm) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).apply_symm_apply (x s)
  right_inv f := by
    apply Subtype.ext
    funext x
    change f.val (project (fun s => (e s).symm) (project (fun s => e s) x)) = f.val x
    apply congrArg f.val
    funext s
    exact (e s).symm_apply_apply (x s)

@[simp] theorem squareEquiv_apply (e : ∀ s, A s ≃ B s)
    (f : squareSpace (space 𝕜 branch n B)) (x : Assignment A) :
    (squareEquiv e f).val x = f.val (project (fun s => e s) x) := rfl

end PerfectCompleteness.RecursiveSpaceEquiv

end

section

namespace PerfectCompleteness.RowAdvice

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

def pad {d r : Nat} (_h : d ≤ r) : (Fin d → F2) →ₗ[F2] (Fin r → F2) where
  toFun v i := if hi : i.val < d then v ⟨i.val, hi⟩ else 0
  map_add' v w := by
    funext i
    by_cases hi : i.val < d <;> simp [hi]
  map_smul' a v := by
    funext i
    by_cases hi : i.val < d <;> simp [hi]

@[simp] theorem pad_low {d r : Nat} (h : d ≤ r) (v : Fin d → F2) (i : Fin d) :
    pad h v ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩ = v i := by
  simp [pad, i.isLt]

end
end PerfectCompleteness.RowAdvice

end

section

namespace PerfectCompleteness.SmallBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

@[simp] theorem expectation_const (μ : FiniteDistribution Ω) (c : ℝ) :
    μ.expectation (fun _ => c) = c := by
  simp only [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]

@[simp] theorem expectation_neg (μ : FiniteDistribution Ω) (a : Ω → ℝ) :
    μ.expectation (fun x => -a x) = -μ.expectation a := by
  simp only [FiniteDistribution.expectation, mul_neg, Finset.sum_neg_distrib]

end

end PerfectCompleteness.SmallBias

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_PinskerLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

/-- A finite conjunction of clauses with exactly three literal slots each.
Repeated variables and repeated literals are allowed. -/
structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

end UniqueGamesTheorem.Foundations.Target

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineControlLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Static renaming of labels and finite internal states. This does not execute
a data-copying phase and preserves every actual transition exactly. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineControl

open Turing.TM2

variable {K Λ Λ' σ σ' : Type} {Γ : K → Type}

def configuration (labels : Λ → Λ') (states : σ ≃ σ') (c : Cfg Γ Λ σ) :
    Cfg Γ Λ' σ' where
  l := c.l.map labels
  var := states c.var
  stk := c.stk

def statement (labels : Λ → Λ') (states : σ ≃ σ') : Stmt Γ Λ σ → Stmt Γ Λ' σ'
  | .push k f next => .push k (fun st => f (states.symm st)) (statement labels states next)
  | .peek k f next => .peek k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .pop k f next => .pop k (fun st v => states (f (states.symm st) v))
      (statement labels states next)
  | .load f next => .load (fun st => states (f (states.symm st)))
      (statement labels states next)
  | .branch f yes no => .branch (fun st => f (states.symm st))
      (statement labels states yes) (statement labels states no)
  | .goto f => .goto (fun st => labels (f (states.symm st)))
  | .halt => .halt

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (states : σ ≃ σ')
    (q : Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    stepAux (statement labels states q) (states state) tapes =
      configuration labels states (stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih =>
    simpa only [statement, stepAux, Equiv.symm_apply_apply] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_false] using
        ihNo state tapes
    | true =>
      simpa only [statement, stepAux, Equiv.symm_apply_apply, h, Bool.cond_true] using
        ihYes state tapes
  | goto f => simp [statement, stepAux, configuration]
  | halt => rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineControl

end

section

/-! Exact embedding of a finite-stack program into disjoint stacks and labels.
An original halt can either halt or enter an explicit continuation label.
The simulation preserves all extra stacks and the second state component. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineEmbedding

open Turing.TM2

variable {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}

abbrev Alphabet (Γ : K → Type) (Δ : E → Type) : K ⊕ E → Type
  | .inl k => Γ k
  | .inr e => Δ e

def tapes (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e)) :
    ∀ j, List (Alphabet Γ Δ j)
  | .inl k => source k
  | .inr e => extra e

@[simp] theorem tapes_inl (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) : tapes source extra (.inl k) = source k := rfl

@[simp] theorem tapes_inr (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (e : E) : tapes source extra (.inr e) = extra e := rfl

def label (haltTarget : Option (Λ ⊕ Λextra)) : Option Λ → Option (Λ ⊕ Λextra)
  | none => haltTarget
  | some l => some (.inl l)

def configuration (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e)) (c : Cfg Γ Λ σ) :
    Cfg (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ) where
  l := label haltTarget c.l
  var := (c.var, extraState)
  stk := tapes c.stk extraTapes

def statement (haltTarget : Option (Λ ⊕ Λextra)) :
    Stmt Γ Λ σ → Stmt (Alphabet Γ Δ) (Λ ⊕ Λextra) (σ × τ)
  | .push k f next => .push (.inl k) (fun st => f st.1) (statement haltTarget next)
  | .peek k f next => .peek (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .pop k f next => .pop (.inl k) (fun st v => (f st.1 v, st.2))
      (statement haltTarget next)
  | .load f next => .load (fun st => (f st.1, st.2)) (statement haltTarget next)
  | .branch f yes no => .branch (fun st => f st.1)
      (statement haltTarget yes) (statement haltTarget no)
  | .goto f => .goto (fun st => .inl (f st.1))
  | .halt => match haltTarget with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K] [DecidableEq E]

theorem tapes_update (source : ∀ k, List (Γ k)) (extra : ∀ e, List (Δ e))
    (k : K) (value : List (Γ k)) :
    tapes (Function.update source k value) extra =
      Function.update (tapes source extra) (.inl k) value := by
  funext j
  cases j with
  | inl j =>
    by_cases h : j = k
    · subst j
      simp [Function.update]
    · simp [Function.update, h]
  | inr e => simp [Function.update]

/-- One finite statement executes identically on the original stacks and state.
The entire statement is simulated in exactly one TM2 transition. -/
theorem stepAux_simulation (haltTarget : Option (Λ ⊕ Λextra))
    (extraState : τ) (extraTapes : ∀ e, List (Δ e))
    (q : Stmt Γ Λ σ) (state : σ) (source : ∀ k, List (Γ k)) :
    stepAux (statement haltTarget q) (state, extraState) (tapes source extraTapes) =
      configuration haltTarget extraState extraTapes (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih state (Function.update source k (f state :: source k))
  | peek k f next ih =>
    simpa only [statement, stepAux, tapes_inl] using
      ih (f state (source k).head?) source
  | pop k f next ih =>
    simp only [statement, stepAux, tapes_inl]
    rw [← tapes_update]
    exact ih (f state (source k).head?) (Function.update source k (source k).tail)
  | load f next ih =>
    simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => cases haltTarget <;> rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineEmbedding

end

section

/-! Static exchange of the first two groups of stacks. Symbol types and stack
contents are retained exactly; no machine transition is spent on this layout
change. This aligns the two component machines in sequential composition. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStackSwap

open Turing.TM2

variable {A B C Λ σ : Type}
  {ΓA : A → Type} {ΓB : B → Type} {ΓC : C → Type}

abbrev Alphabet (ΓA : A → Type) (ΓB : B → Type) (ΓC : C → Type) :=
  MachineEmbedding.Alphabet ΓA (MachineEmbedding.Alphabet ΓB ΓC)

def tapes (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    ∀ j, List (Alphabet ΓB ΓA ΓC j)
  | .inl b => source (.inr (.inl b))
  | .inr (.inl a) => source (.inl a)
  | .inr (.inr c) => source (.inr (.inr c))

@[simp] theorem tapes_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (a : A) :
    tapes source (.inr (.inl a)) = source (.inl a) := rfl
@[simp] theorem tapes_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (b : B) :
    tapes source (.inl b) = source (.inr (.inl b)) := rfl
@[simp] theorem tapes_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) (c : C) :
    tapes source (.inr (.inr c)) = source (.inr (.inr c)) := rfl

def configuration (c : Cfg (Alphabet ΓA ΓB ΓC) Λ σ) :
    Cfg (Alphabet ΓB ΓA ΓC) Λ σ where
  l := c.l
  var := c.var
  stk := tapes c.stk

def statement : Stmt (Alphabet ΓA ΓB ΓC) Λ σ → Stmt (Alphabet ΓB ΓA ΓC) Λ σ
  | .push (.inl a) f next => .push (.inr (.inl a)) f (statement next)
  | .push (.inr (.inl b)) f next => .push (.inl b) f (statement next)
  | .push (.inr (.inr c)) f next => .push (.inr (.inr c)) f (statement next)
  | .peek (.inl a) f next => .peek (.inr (.inl a)) f (statement next)
  | .peek (.inr (.inl b)) f next => .peek (.inl b) f (statement next)
  | .peek (.inr (.inr c)) f next => .peek (.inr (.inr c)) f (statement next)
  | .pop (.inl a) f next => .pop (.inr (.inl a)) f (statement next)
  | .pop (.inr (.inl b)) f next => .pop (.inl b) f (statement next)
  | .pop (.inr (.inr c)) f next => .pop (.inr (.inr c)) f (statement next)
  | .load f next => .load f (statement next)
  | .branch f yes no => .branch f (statement yes) (statement no)
  | .goto f => .goto f
  | .halt => .halt

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem tapes_update_first (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (a : A) (value : List (ΓA a)) :
    tapes (Function.update source (.inl a) value) =
      Function.update (tapes source) (.inr (.inl a)) value := by
  funext j
  rcases j with b | a' | c
  · simp [Function.update]
  · by_cases h : a' = a
    · subst a'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]

theorem tapes_update_second (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (b : B) (value : List (ΓB b)) :
    tapes (Function.update source (.inr (.inl b)) value) =
      Function.update (tapes source) (.inl b) value := by
  funext j
  rcases j with b' | a | c
  · by_cases h : b' = b
    · subst b'; simp [Function.update]
    · simp [Function.update, h]
  · simp [Function.update]
  · simp [Function.update]

theorem tapes_update_third (source : ∀ k, List (Alphabet ΓA ΓB ΓC k))
    (c : C) (value : List (ΓC c)) :
    tapes (Function.update source (.inr (.inr c)) value) =
      Function.update (tapes source) (.inr (.inr c)) value := by
  funext j
  rcases j with b | a | c'
  · simp [Function.update]
  · simp [Function.update]
  · by_cases h : c' = c
    · subst c'; simp [Function.update]
    · simp [Function.update, h]

theorem stepAux_simulation (q : Stmt (Alphabet ΓA ΓB ΓC) Λ σ)
    (state : σ) (source : ∀ k, List (Alphabet ΓA ΓB ΓC k)) :
    stepAux (statement q) state (tapes source) =
      configuration (stepAux q state source) := by
  induction q generalizing state source with
  | push k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih state (Function.update source (.inl a) (f state :: source (.inl a)))
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih state (Function.update source (.inr (.inl b))
        (f state :: source (.inr (.inl b))))
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih state (Function.update source (.inr (.inr c))
        (f state :: source (.inr (.inr c))))
  | peek k f next ih =>
    rcases k with a | b | c
    · simpa only [statement, stepAux, tapes_first] using
        ih (f state (source (.inl a)).head?) source
    · simpa only [statement, stepAux, tapes_second] using
        ih (f state (source (.inr (.inl b))).head?) source
    · simpa only [statement, stepAux, tapes_third] using
        ih (f state (source (.inr (.inr c))).head?) source
  | pop k f next ih =>
    rcases k with a | b | c
    · simp only [statement, stepAux, tapes_first]
      rw [← tapes_update_first]
      exact ih (f state (source (.inl a)).head?)
        (Function.update source (.inl a) (source (.inl a)).tail)
    · simp only [statement, stepAux, tapes_second]
      rw [← tapes_update_second]
      exact ih (f state (source (.inr (.inl b))).head?)
        (Function.update source (.inr (.inl b)) (source (.inr (.inl b))).tail)
    · simp only [statement, stepAux, tapes_third]
      rw [← tapes_update_third]
      exact ih (f state (source (.inr (.inr c))).head?)
        (Function.update source (.inr (.inr c)) (source (.inr (.inr c))).tail)
  | load f next ih => simpa only [statement, stepAux] using ih (f state) source
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [statement, stepAux, h, Bool.cond_false] using ihNo state source
    | true => simpa only [statement, stepAux, h, Bool.cond_true] using ihYes state source
  | goto f => rfl
  | halt => rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineStackSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_Runtime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Stack-length bounds derived from actual machine transitions. A finite program
has a maximum number of pushes in any one statement. Iterating its transitions
therefore bounds output length by input length plus that constant times elapsed
steps. This proves a consequence of a runtime certificate, not its converse.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.Runtime

def statementPushBound {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → Nat
  | .push _ _ next => statementPushBound next + 1
  | .peek _ _ next => statementPushBound next
  | .pop _ _ next => statementPushBound next
  | .load _ next => statementPushBound next
  | .branch _ yes no => max (statementPushBound yes) (statementPushBound no)
  | .goto _ => 0
  | .halt => 0

def maxLabelPushes {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) : List Λ → Nat
  | [] => 0
  | label :: rest => max (statementPushBound (program label)) (maxLabelPushes program rest)

theorem maxLabelPushes_ge {K : Type} {Γ : K → Type} {Λ σ : Type}
    (program : Λ → Turing.TM2.Stmt Γ Λ σ) (labels : List Λ) (label : Λ)
    (member : label ∈ labels) :
    statementPushBound (program label) ≤ maxLabelPushes program labels := by
  induction labels with
  | nil => simp at member
  | cons first rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih member) (Nat.le_max_right _ _)

/-- The finite maximum is a proof-bound constant, not an operation of the
machine being analyzed. -/
noncomputable def programPushBound (tm : Turing.FinTM2) : Nat :=
  maxLabelPushes tm.m tm.ΛFin.elems.toList

theorem statement_le_programPushBound (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushBound (tm.m label) ≤ programPushBound tm := by
  apply maxLabelPushes_ge
  simpa using tm.ΛFin.complete label

theorem stepAuxStackLength {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (stmt : Turing.TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) (k : K) :
    ((Turing.TM2.stepAux stmt state tapes).stk k).length ≤
      (tapes k).length + statementPushBound stmt := by
  induction stmt generalizing state tapes with
  | push j f next ih =>
      have changed : ((Function.update tapes j (f state :: tapes j)) k).length ≤
          (tapes k).length + 1 := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih state (Function.update tapes j (f state :: tapes j))
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | peek j f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using
        ih (f state (tapes j).head?) tapes
  | pop j f next ih =>
      have changed : ((Function.update tapes j (tapes j).tail) k).length ≤
          (tapes k).length := by
        by_cases same : k = j
        · subst k; simp
        · simp [Function.update, same]
      have h := ih (f state (tapes j).head?) (Function.update tapes j (tapes j).tail)
      simp only [Turing.TM2.stepAux, statementPushBound]
      omega
  | load f next ih =>
      simpa only [Turing.TM2.stepAux, statementPushBound] using ih (f state) tapes
  | branch condition yes no ihYes ihNo =>
      cases decision : condition state with
      | false =>
          have h := ihNo state tapes
          have hm := Nat.le_max_right (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_false]
          omega
      | true =>
          have h := ihYes state tapes
          have hm := Nat.le_max_left (statementPushBound yes) (statementPushBound no)
          simp only [Turing.TM2.stepAux, statementPushBound, decision, Bool.cond_true]
          omega
  | goto f => simp [Turing.TM2.stepAux, statementPushBound]
  | halt => simp [Turing.TM2.stepAux, statementPushBound]

theorem iterateSizeBound {α : Type} (f : α → α) (size : α → Nat) (C : Nat)
    (oneStep : ∀ x, size (f x) ≤ size x + C) (n : Nat) (x : α) :
    size ((f^[n]) x) ≤ size x + n * C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hs := oneStep ((f^[n]) x)
      have bound : size (f ((f^[n]) x)) ≤ size x + (n + 1) * C := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      simpa only [Function.iterate_succ_apply'] using bound

/-- Resource growth along the actual iterated transition witness. -/
theorem executionSizeBound {σ : Type} (step : σ → Option σ) (size : σ → Nat) (C : Nat)
    (oneStep : ∀ a b, step a = some b → size b ≤ size a + C)
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime step start (some finish) budget) :
    size finish ≤ size start + budget * C := by
  let liftedSize : Option σ → Nat := fun state => (state.map size).getD 0
  have liftedStep : ∀ state : Option σ,
      liftedSize (state.bind step) ≤ liftedSize state + C := by
    intro state
    cases state with
    | none => simp [liftedSize]
    | some a =>
        cases transition : step a with
        | none => simp [liftedSize, transition]
        | some b => simpa [liftedSize, transition] using oneStep a b transition
  have bound := iterateSizeBound (fun state : Option σ => state.bind step)
    liftedSize C liftedStep execution.steps (some start)
  change liftedSize ((flip bind step)^[execution.steps] (some start)) ≤ _ at bound
  rw [execution.evals_in_steps] at bound
  simp only [liftedSize, Option.map_some, Option.getD_some] at bound
  exact Nat.le_trans bound (Nat.add_le_add_left
    (Nat.mul_le_mul_right C execution.steps_le_m) _)

theorem stepStackLength (tm : Turing.FinTM2) (k : tm.K) (a b : tm.Cfg)
    (transition : tm.step a = some b) :
    (b.stk k).length ≤ (a.stk k).length + programPushBound tm := by
  cases a with
  | mk label state tapes =>
      cases label with
      | none => simp [Turing.FinTM2.step, Turing.TM2.step] at transition
      | some label =>
          have result := Option.some.inj transition
          rw [← result]
          exact Nat.le_trans (stepAuxStackLength _ _ _ _)
            (Nat.add_le_add_left (statement_le_programPushBound tm label) _)

theorem initialStackLength (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (k : tm.K) :
    ((Turing.initList tm input).stk k).length ≤ input.length := by
  simp only [Turing.initList]
  split
  next same => subst k; exact Nat.le_refl _
  next _ => simp

@[simp] theorem haltedOutputLength (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    ((Turing.haltList tm output).stk tm.k₁).length = output.length := by
  simp [Turing.haltList]

theorem outputLength_le (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁)) (budget : Nat)
    (execution : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * programPushBound tm := by
  have bound := executionSizeBound tm.step (fun cfg => (cfg.stk tm.k₁).length)
    (programPushBound tm) (stepStackLength tm tm.k₁) execution
  calc
    output.length = ((Turing.haltList tm output).stk tm.k₁).length := (haltedOutputLength tm output).symm
    _ ≤ ((Turing.initList tm input).stk tm.k₁).length + budget * programPushBound tm := bound
    _ ≤ input.length + budget * programPushBound tm :=
      Nat.add_le_add_right (initialStackLength tm input tm.k₁) _

/-- Polynomial-time computation implies a polynomial bound on serialized
output length. This direction is used for intermediate data in composition. -/
theorem encodedOutputLength {α β αΓ βΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β}
    (certificate : Turing.TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤
      (Polynomial.X + Polynomial.C (programPushBound certificate.tm) * certificate.time).eval
        (ea a).length := by
  have bound := outputLength_le certificate.tm _ _ _ (certificate.outputsFun a)
  simpa only [List.length_map, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.mul_comm] using bound

end UniqueGamesTheorem.Foundations.Complexity.Runtime

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCompositionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Execution transport and polynomial budget arithmetic for genuine TM2 sequential
composition. These lemmas preserve actual transition witnesses. The four-phase
lemma requires all phases to be executions of the same combined program; it is
not a replacement for constructing that program and proving its tape handoffs.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineComposition

def advance {σ : Type} (step : σ → Option σ) (state : Option σ) : Option σ :=
  state.bind step

@[simp] theorem advance_none {σ : Type} (step : σ → Option σ) :
    advance step none = none := rfl

@[simp] theorem advance_some {σ : Type} (step : σ → Option σ) (state : σ) :
    advance step (some state) = step state := rfl

@[simp] theorem advance_iterate_none {σ : Type} (step : σ → Option σ) (n : Nat) :
    (advance step)^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_none]

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

theorem natPolynomial_eval_mono (p : Polynomial Nat) {a b : Nat} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial degree coefficient =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left coefficient (Nat.pow_le_pow_left h degree)

/-- Two reversal transfers each consume `intermediateLength + 1` transitions. -/
noncomputable def compositionPolynomial (first second intermediate : Polynomial Nat) : Polynomial Nat :=
  first + Polynomial.C 2 * (intermediate + 1) + second.comp intermediate

theorem compositionBudget_le (first second intermediate : Polynomial Nat)
    (inputLength intermediateLength : Nat)
    (intermediateBound : intermediateLength ≤ intermediate.eval inputLength) :
    first.eval inputLength + 2 * (intermediateLength + 1) + second.eval intermediateLength ≤
      (compositionPolynomial first second intermediate).eval inputLength := by
  have secondBound := natPolynomial_eval_mono second intermediateBound
  have transferBound := Nat.mul_le_mul_left 2 (Nat.add_le_add_right intermediateBound 1)
  simp only [compositionPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_one, Polynomial.eval_comp]
  omega

end UniqueGamesTheorem.Foundations.Complexity.MachineComposition

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineAlphabetTransport

open Turing.TM2

variable {K Λ σ : Type} {Γ Δ : K → Type}

def tapes (h : Γ = Δ) (source : ∀ k, List (Γ k)) : ∀ k, List (Δ k) := h ▸ source

def statement (h : Γ = Δ) (source : Stmt Γ Λ σ) : Stmt Δ Λ σ := h ▸ source

def configuration (h : Γ = Δ) (source : Cfg Γ Λ σ) : Cfg Δ Λ σ := h ▸ source

def program (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Δ Λ σ :=
  fun label => statement h (source label)

@[simp] theorem tapes_rfl (source : ∀ k, List (Γ k)) : tapes rfl source = source := rfl
@[simp] theorem statement_rfl (source : Stmt Γ Λ σ) : statement rfl source = source := rfl
@[simp] theorem configuration_rfl (source : Cfg Γ Λ σ) : configuration rfl source = source := rfl
@[simp] theorem program_rfl (source : Λ → Stmt Γ Λ σ) : program rfl source = source := rfl

@[simp] theorem program_apply (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) (label : Λ) :
    program h source label = statement h (source label) := rfl

@[simp] theorem configuration_roundtrip (h : Γ = Δ) (source : Cfg Δ Λ σ) :
    configuration h (configuration h.symm source) = source := by cases h; rfl

@[simp] theorem configuration_symm_roundtrip (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    configuration h.symm (configuration h source) = source := by cases h; rfl

@[simp] theorem program_roundtrip (h : Γ = Δ) (source : Λ → Stmt Δ Λ σ) :
    program h (program h.symm source) = source := by cases h; rfl

@[simp] theorem program_symm_roundtrip (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ) :
    program h.symm (program h source) = source := by cases h; rfl

@[simp] theorem tapes_roundtrip (h : Γ = Δ) (source : ∀ k, List (Δ k)) :
    tapes h (tapes h.symm source) = source := by cases h; rfl

@[simp] theorem tapes_symm_roundtrip (h : Γ = Δ) (source : ∀ k, List (Γ k)) :
    tapes h.symm (tapes h source) = source := by cases h; rfl

@[simp] theorem configuration_label (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).l = source.l := by cases h; rfl

@[simp] theorem configuration_state (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).var = source.var := by cases h; rfl

@[simp] theorem configuration_tapes (h : Γ = Δ) (source : Cfg Γ Λ σ) :
    (configuration h source).stk = tapes h source.stk := by cases h; rfl

@[simp] theorem configuration_mk (h : Γ = Δ) (label : Option Λ) (state : σ)
    (source : ∀ k, List (Γ k)) :
    configuration h ⟨label, state, source⟩ = ⟨label, state, tapes h source⟩ := by cases h; rfl

@[simp] theorem map_configuration_rfl (source : Option (Cfg Γ Λ σ)) :
    source.map (configuration (rfl : Γ = Γ)) = source := by cases source <;> rfl

variable [DecidableEq K]

def executionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (finish.map (configuration h)) budget where
  steps := execution.steps
  evals_in_steps := by
    cases h
    simpa only [program_rfl, configuration_rfl, map_configuration_rfl]
      using execution.evals_in_steps
  steps_le_m := execution.steps_le_m

@[simp] theorem executionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start finish budget) :
    (executionInTime h source execution).steps = execution.steps := rfl

def successfulExecutionInTime (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    StateTransition.EvalsToInTime (step (program h source)) (configuration h start)
      (some (configuration h finish)) budget := executionInTime h source execution

@[simp] theorem successfulExecutionInTime_steps (h : Γ = Δ) (source : Λ → Stmt Γ Λ σ)
    {start finish : Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (step source) start (some finish) budget) :
    (successfulExecutionInTime h source execution).steps = execution.steps := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineAlphabetTransport

end

section

/-!
# Exact register-equivalence transport for finite-stack programs

The instruction translation reuses `MachineControl.statement` with unchanged
labels. An explicit register equivalence changes neither tapes nor labels.
The transition function, every iterated trace, and runtime witnesses are
transported in exactly the same number of transitions, including failed or
halted traces. No simulation premise is assumed.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

/-- Translate instructions using the checked recursive translator, keeping
every tape and destination label unchanged. -/
abbrev statement (e : σ ≃ τ) : Stmt Γ Λ σ → Stmt Γ Λ τ :=
  MachineControl.statement (id : Λ → Λ) e

/-- Translating every instruction back restores the original statement,
including its state-dependent instruction functions. -/
@[simp] theorem statement_symm_statement (e : σ ≃ τ) (q : Stmt Γ Λ σ) :
    statement e.symm (statement e q) = q := by
  induction q <;>
    simp_all only [statement, MachineControl.statement, Equiv.symm_symm,
      Equiv.symm_apply_apply, id_eq]

def configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) : Cfg Γ Λ τ :=
  ⟨c.l, e c.var, c.stk⟩

@[simp] theorem configuration_label (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).l = c.l := rfl

@[simp] theorem configuration_state (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).var = e c.var := rfl

@[simp] theorem configuration_tapes (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    (configuration e c).stk = c.stk := rfl

@[simp] theorem configuration_symm_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configuration e.symm (configuration e c) = c := by
  cases c
  simp only [configuration, Equiv.symm_apply_apply]

@[simp] theorem configuration_configuration_symm (e : σ ≃ τ) (c : Cfg Γ Λ τ) :
    configuration e (configuration e.symm c) = c := by
  cases c
  simp only [configuration, Equiv.apply_symm_apply]

/-- This is a bijection on actual machine configurations, not just on states. -/
def configurationEquiv (e : σ ≃ τ) : Cfg Γ Λ σ ≃ Cfg Γ Λ τ where
  toFun := configuration e
  invFun := configuration e.symm
  left_inv := configuration_symm_configuration e
  right_inv := configuration_configuration_symm e

@[simp] theorem configurationEquiv_apply (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    configurationEquiv e c = configuration e c := rfl

@[simp] theorem control_configuration (e : σ ≃ τ) (c : Cfg Γ Λ σ) :
    MachineControl.configuration (id : Λ → Λ) e c = configuration e c := by
  cases c
  simp [MachineControl.configuration, configuration]

def program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) : Λ → Stmt Γ Λ τ :=
  fun l => statement e (source l)

@[simp] theorem program_symm_program (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) :
    program e.symm (program e source) = source := by
  funext l
  exact statement_symm_statement e (source l)

variable [DecidableEq K]

/-- The actual recursively interpreted statement commutes with the register
equivalence, with exactly the same tape updates. -/
theorem stepAux_transport (e : σ ≃ τ) (q : Stmt Γ Λ σ) (state : σ)
    (tapes : ∀ k, List (Γ k)) :
    stepAux (statement e q) (e state) tapes =
      configuration e (stepAux q state tapes) := by
  simpa only [statement, control_configuration] using
    MachineControl.stepAux_simulation (id : Λ → Λ) e q state tapes

/-- Exact conjugacy also covers the halted configuration and the `none` step. -/
theorem step_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) :
    step (program e source) (configuration e c) =
      (step source c).map (configuration e) := by
  cases c with
  | mk l state tapes =>
      cases l with
      | none => rfl
      | some l =>
          change some (stepAux (statement e (source l)) (e state) tapes) = _
          rw [stepAux_transport]
          rfl

theorem advance_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (c : Option (Cfg Γ Λ σ)) :
    MachineComposition.advance (step (program e source)) (c.map (configuration e)) =
      (MachineComposition.advance (step source) c).map (configuration e) := by
  cases c with
  | none => rfl
  | some c => exact step_transport e source c

/-- Every intermediate configuration is transported at its original time
index. This includes traces whose option-valued result is `none`. -/
theorem iterate_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program e source)))^[n]
        (c.map (configuration e)) =
      ((MachineComposition.advance (step source))^[n] c).map (configuration e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

/-- A successful running trace exists for exactly the same number of steps in
the translated and original program. -/
theorem trace_iff (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ) :
    (MachineComposition.advance (step (program e source)))^[n]
        (some (configuration e a)) = some (configuration e b) ↔
      (MachineComposition.advance (step source))^[n] (some a) = some b := by
  change (MachineComposition.advance (step (program e source)))^[n]
      ((some a).map (configuration e)) = (some b).map (configuration e) ↔ _
  rw [iterate_transport]
  constructor
  · intro h
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[n] (some a)).map (configuration e) =
      (some b).map (configuration e)
    exact h
  · exact congrArg (Option.map (configuration e))

theorem trace (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (a b : Cfg Γ Λ σ)
    (run : (MachineComposition.advance (step source))^[n] (some a) = some b) :
    (MachineComposition.advance (step (program e source)))^[n]
      (some (configuration e a)) = some (configuration e b) :=
  (trace_iff e source n a b).2 run

/-- Transport an actual runtime witness without changing its step count or
budget; the final option may be either a configuration or `none`. -/
def execution (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (step (program e source)))^[run.steps]
      ((some start).map (configuration e)) = finish.map (configuration e)
    rw [iterate_transport, h]
  steps_le_m := run.steps_le_m

@[simp] theorem execution_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    (execution e source run).steps = run.steps := rfl

/-- Conversely, a translated runtime witness determines the original witness
at exactly the same number of transitions. -/
def execution_reflect (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    StateTransition.EvalsToInTime (step source) start finish budget where
  steps := run.steps
  evals_in_steps := by
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish
    apply Option.map_injective (configurationEquiv e).injective
    change ((MachineComposition.advance (step source))^[run.steps] (some start)).map
      (configuration e) = finish.map (configuration e)
    rw [← iterate_transport]
    exact run.evals_in_steps
  steps_le_m := run.steps_le_m

@[simp] theorem execution_reflect_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget) :
    (execution_reflect e source run).steps = run.steps := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineStateEquiv

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineSubroutineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

open Turing

variable {K Λ Λ' σ : Type} {Γ : K → Type}

def label (labels : Λ → Λ') (exit : Option Λ') : Option Λ → Option Λ'
  | none => exit
  | some l => some (labels l)

def configuration (labels : Λ → Λ') (exit : Option Λ') (c : TM2.Cfg Γ Λ σ) :
    TM2.Cfg Γ Λ' σ := ⟨label labels exit c.l, c.var, c.stk⟩

def statement (labels : Λ → Λ') (exit : Option Λ') :
    TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f next => .push k f (statement labels exit next)
  | .peek k f next => .peek k f (statement labels exit next)
  | .pop k f next => .pop k f (statement labels exit next)
  | .load f next => .load f (statement labels exit next)
  | .branch f yes no => .branch f (statement labels exit yes) (statement labels exit no)
  | .goto f => .goto (fun s => labels (f s))
  | .halt => match exit with
      | none => .halt
      | some l => .goto (fun _ => l)

variable [DecidableEq K]

theorem stepAux_simulation (labels : Λ → Λ') (exit : Option Λ')
    (q : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (statement labels exit q) state tapes =
      configuration labels exit (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
      simpa only [statement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
      simpa only [statement, TM2.stepAux] using
        ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [statement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
      cases h : f state with
      | false => simpa only [statement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
      | true => simpa only [statement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => cases exit <;> rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ')
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' σ)
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit a) =
      some (configuration labels exit b) := by
  cases a with
  | mk l state tapes =>
      cases l with
      | none => simp [TM2.step] at h
      | some l =>
          have hb : TM2.stepAux (source l) state tapes = b := Option.some.inj h
          rw [← hb]
          change some (TM2.stepAux (target (labels l)) state tapes) = _
          rw [atLabels, stepAux_simulation]

end UniqueGamesTheorem.Foundations.Complexity.MachineSubroutine

end

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineStateFrame

open Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

/-- Same code and stacks, with an untouched caller-register component. -/
def frameStatement : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ (σ × τ)
  | .push k f next => .push k (fun state => f state.1) (frameStatement next)
  | .peek k f next => .peek k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .pop k f next => .pop k (fun state bit => (f state.1 bit, state.2))
      (frameStatement next)
  | .load f next => .load (fun state => (f state.1, state.2)) (frameStatement next)
  | .branch f yes no => .branch (fun state => f state.1)
      (frameStatement yes) (frameStatement no)
  | .goto f => .goto (fun state => f state.1)
  | .halt => .halt

def frameConfiguration (ambient : τ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ (σ × τ) :=
  ⟨c.l, (c.var, ambient), c.stk⟩

def frameProgram (source : Λ → TM2.Stmt Γ Λ σ) : Λ → TM2.Stmt Γ Λ (σ × τ) :=
  fun label => frameStatement (source label)

@[simp] theorem frameConfiguration_state (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.1 = c.var := rfl

@[simp] theorem frameConfiguration_metadata (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).var.2 = ambient := rfl

@[simp] theorem frameConfiguration_tapes (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (frameConfiguration ambient c).stk = c.stk := rfl

/-- Optional continuation and labels use the existing subroutine semantics. -/
def statement (labels : Λ → Λ') (exit : Option Λ') (q : TM2.Stmt Γ Λ σ) :
    TM2.Stmt Γ Λ' (σ × τ) :=
  MachineSubroutine.statement labels exit (frameStatement q)

def configuration (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' (σ × τ) :=
  MachineSubroutine.configuration labels exit (frameConfiguration ambient c)

@[simp] theorem configuration_state (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.1 = c.var := rfl

@[simp] theorem configuration_metadata (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).var.2 = ambient := rfl

@[simp] theorem configuration_tapes (labels : Λ → Λ') (exit : Option Λ')
    (ambient : τ) (c : TM2.Cfg Γ Λ σ) :
    (configuration labels exit ambient c).stk = c.stk := rfl

variable [DecidableEq K]

theorem frame_stepAux (q : TM2.Stmt Γ Λ σ) (state : σ) (ambient : τ)
    (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (frameStatement q) (state, ambient) tapes =
      frameConfiguration ambient (TM2.stepAux q state tapes) := by
  induction q generalizing state tapes with
  | push k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih state (Function.update tapes k (f state :: tapes k))
  | peek k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using ih (f state (tapes k).head?) tapes
  | pop k f next ih =>
    simpa only [frameStatement, TM2.stepAux] using
      ih (f state (tapes k).head?) (Function.update tapes k (tapes k).tail)
  | load f next ih => simpa only [frameStatement, TM2.stepAux] using ih (f state) tapes
  | branch f yes no ihYes ihNo =>
    cases h : f state with
    | false => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_false] using ihNo state tapes
    | true => simpa only [frameStatement, TM2.stepAux, h, Bool.cond_true] using ihYes state tapes
  | goto f => rfl
  | halt => rfl

/-- This identity also covers the final halted configuration. -/
theorem frame_step (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : TM2.Cfg Γ Λ σ) :
    TM2.step (frameProgram source) (frameConfiguration ambient c) =
      (TM2.step source c).map (frameConfiguration ambient) := by
  rcases c with ⟨label, state, tapes⟩
  cases label with
  | none => rfl
  | some label =>
    change some (TM2.stepAux (frameStatement (source label)) (state, ambient) tapes) = _
    rw [frame_stepAux]
    rfl

theorem frame_advance (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    MachineComposition.advance (TM2.step (frameProgram source))
        (c.map (frameConfiguration ambient)) =
      (MachineComposition.advance (TM2.step source) c).map (frameConfiguration ambient) := by
  cases c with
  | none => rfl
  | some c => exact frame_step source ambient c

theorem frame_iterate (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (steps : ℕ) (c : Option (TM2.Cfg Γ Λ σ)) :
    (MachineComposition.advance (TM2.step (frameProgram source)))^[steps]
        (c.map (frameConfiguration ambient)) =
      ((MachineComposition.advance (TM2.step source))^[steps] c).map
        (frameConfiguration ambient) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact frame_advance source ambient _

/-- Actual execution with the same step count, budget, and tapes. -/
def frameExecution (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    StateTransition.EvalsToInTime (TM2.step (frameProgram source))
      (frameConfiguration ambient start) (finish.map (frameConfiguration ambient)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (TM2.step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (TM2.step (frameProgram source)))^[run.steps]
      ((some start).map (frameConfiguration ambient)) = finish.map (frameConfiguration ambient)
    rw [frame_iterate, h]
  steps_le_m := run.steps_le_m

@[simp] theorem frameExecution_steps (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    (frameExecution source ambient run).steps = run.steps := rfl

theorem step_simulation (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    (a b : TM2.Cfg Γ Λ σ) (h : TM2.step source a = some b) :
    TM2.step target (configuration labels exit ambient a) =
      some (configuration labels exit ambient b) := by
  have framed : TM2.step (frameProgram source) (frameConfiguration ambient a) =
      some (frameConfiguration ambient b) := by
    rw [frame_step, h]
    rfl
  exact MachineSubroutine.step_simulation labels exit (frameProgram source) target
    atLabels _ _ framed

def execution (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    StateTransition.EvalsToInTime (TM2.step target)
      (configuration labels exit ambient a) (some (configuration labels exit ambient b)) budget :=
  MachineComposition.liftExecutionInTime (TM2.step source) (TM2.step target)
    (configuration labels exit ambient) (step_simulation labels exit ambient source target atLabels) run

@[simp] theorem execution_steps (labels : Λ → Λ') (exit : Option Λ') (ambient : τ)
    (source : Λ → TM2.Stmt Γ Λ σ) (target : Λ' → TM2.Stmt Γ Λ' (σ × τ))
    (atLabels : ∀ l, target (labels l) = statement labels exit (source l))
    {a b : TM2.Cfg Γ Λ σ} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) a (some b) budget) :
    (execution labels exit ambient source target atLabels run).steps = run.steps := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineStateFrame

end

section

/-!
Concrete finite-alphabet serialization primitives. A natural word `n` is `n`
one-bits followed by a zero delimiter. These are size and decoding theorems, not
running-time certificates. In particular, output length is never called runtime.
-/

namespace UniqueGamesTheorem.Foundations.Complexity

def decodeWordsAux : List Bool → Nat → Option (List Nat)
  | [], 0 => some []
  | [], _ + 1 => none
  | true :: bs, n => decodeWordsAux bs (n + 1)
  | false :: bs, n => (decodeWordsAux bs 0).map (n :: ·)

def decodeWords (bs : List Bool) : Option (List Nat) := decodeWordsAux bs 0

theorem decodeWordsAux_word (n k : Nat) (bs : List Bool) :
    decodeWordsAux (encodeWord n ++ bs) k =
      (decodeWordsAux bs 0).map ((k + n) :: ·) := by
  induction n generalizing k with
  | zero => simp [encodeWord, decodeWordsAux]
  | succ n ih =>
      simp only [encodeWord, List.replicate_succ, List.cons_append, List.append_assoc,
        decodeWordsAux]
      simpa [encodeWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1)

@[simp] theorem decodeWords_encodeWords (ns : List Nat) :
    decodeWords (encodeWords ns) = some ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp only [decodeWords, encodeWords, decodeWordsAux_word, Nat.zero_add]
      simpa [decodeWords] using congrArg (Option.map (n :: ·)) ih

@[simp] theorem encodeWord_length (n : Nat) : (encodeWord n).length = n + 1 := by
  simp [encodeWord]

@[simp] theorem encodeWords_append (xs ys : List Nat) :
    encodeWords (xs ++ ys) = encodeWords xs ++ encodeWords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeWords, ih, List.append_assoc]

@[simp] theorem encodeWords_length (ns : List Nat) :
    (encodeWords ns).length = ns.sum + ns.length := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [encodeWords, ih]; omega

open Target

def literalWords {n : Nat} (literal : Literal n) : List Nat :=
  [literal.variableIndex.val, if literal.positive then 1 else 0]

def clauseWords {n : Nat} (clause : Clause n) : List Nat :=
  literalWords clause[0] ++ literalWords clause[1] ++ literalWords clause[2]

def formulaWords (formula : Formula) : List Nat :=
  [formula.variables, formula.clauses.length] ++ formula.clauses.flatMap clauseWords

def formulaBits (formula : Formula) : List Bool := encodeWords (formulaWords formula)

@[simp] theorem literalWords_length {n : Nat} (literal : Literal n) :
    (literalWords literal).length = 2 := by simp [literalWords]

@[simp] theorem clauseWords_length {n : Nat} (clause : Clause n) :
    (clauseWords clause).length = 6 := by simp [clauseWords]

theorem literalBits_length_le {n : Nat} (literal : Literal n) :
    (encodeWords (literalWords literal)).length ≤ n + 2 := by
  have hindex := literal.variableIndex.isLt
  cases hp : literal.positive <;> simp [literalWords, hp]

theorem clauseBits_length_le {n : Nat} (clause : Clause n) :
    (encodeWords (clauseWords clause)).length ≤ 3 * (n + 2) := by
  have h0 := literalBits_length_le clause[0]
  have h1 := literalBits_length_le clause[1]
  have h2 := literalBits_length_le clause[2]
  simp only [clauseWords, encodeWords_append, List.length_append]
  omega

theorem clausesBits_length_le {n : Nat} (clauses : List (Clause n)) :
    (encodeWords (clauses.flatMap clauseWords)).length ≤ clauses.length * (3 * (n + 2)) := by
  induction clauses with
  | nil => simp [encodeWords]
  | cons clause clauses ih =>
      have hc := clauseBits_length_le clause
      simp only [List.flatMap_cons, encodeWords_append, List.length_append,
        List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem formulaBits_length_le (formula : Formula) :
    (formulaBits formula).length ≤
      formula.variables + formula.clauses.length + 2 +
        formula.clauses.length * (3 * (formula.variables + 2)) := by
  have h := clausesBits_length_le formula.clauses
  simp only [formulaBits, formulaWords, encodeWords_append, List.length_append,
    encodeWords, encodeWord_length, List.length_nil]
  omega

end UniqueGamesTheorem.Foundations.Complexity

end

section

/-! A checked parser for the concrete 3CNF serialization, including finite-index
bounds, Boolean signs, clause count, and absence of trailing garbage. -/

namespace UniqueGamesTheorem.Foundations.Complexity

open Target

def parseLiteral («variables» : Nat) : List Nat → Option (Literal «variables» × List Nat)
  | index :: sign :: rest =>
      if bounded : index < «variables» then
        if sign = 0 then some (⟨⟨index, bounded⟩, false⟩, rest)
        else if sign = 1 then some (⟨⟨index, bounded⟩, true⟩, rest)
        else none
      else none
  | _ => none

@[simp] theorem parseLiteral_encoded {n : Nat} (literal : Literal n) (rest : List Nat) :
    parseLiteral n (literalWords literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk index positive =>
      cases positive <;> simp [literalWords, parseLiteral, index.isLt]

def parseClause («variables» : Nat) (words : List Nat) : Option (Clause «variables» × List Nat) := do
  let (a, words) ← parseLiteral «variables» words
  let (b, words) ← parseLiteral «variables» words
  let (c, words) ← parseLiteral «variables» words
  return (⟨#[a, b, c], rfl⟩, words)

theorem clause_three_entries {n : Nat} (clause : Clause n) :
    (⟨#[clause[0], clause[1], clause[2]], rfl⟩ : Clause n) = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded {n : Nat} (clause : Clause n) (rest : List Nat) :
    parseClause n (clauseWords clause ++ rest) = some (clause, rest) := by
  simp [clauseWords, List.append_assoc, parseClause, parseLiteral_encoded,
    clause_three_entries]

def parseClauses («variables» : Nat) : Nat → List Nat → Option (List (Clause «variables») × List Nat)
  | 0, words => some ([], words)
  | count + 1, words => do
      let (clause, words) ← parseClause «variables» words
      let (clauses, words) ← parseClauses «variables» count words
      return (clause :: clauses, words)

@[simp] theorem parseClauses_encoded {n : Nat} (clauses : List (Clause n)) (rest : List Nat) :
    parseClauses n clauses.length (clauses.flatMap clauseWords ++ rest) = some (clauses, rest) := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp [List.append_assoc, parseClauses, parseClause_encoded, ih]

def decodeFormulaWords : List Nat → Option Formula
  | «variables» :: count :: words => do
      let (clauses, trailing) ← parseClauses «variables» count words
      if trailing = [] then some ⟨«variables», clauses⟩ else none
  | _ => none

@[simp] theorem decodeFormulaWords_encoded (formula : Formula) :
    decodeFormulaWords (formulaWords formula) = some formula := by
  cases formula with
  | mk «variables» clauses =>
      have parsed := parseClauses_encoded clauses []
      simp only [List.append_nil] at parsed
      simp [decodeFormulaWords, formulaWords, parsed]

def decodeFormulaBits (bits : List Bool) : Option Formula :=
  decodeWords bits >>= decodeFormulaWords

@[simp] theorem decodeFormulaBits_encoded (formula : Formula) :
    decodeFormulaBits (formulaBits formula) = some formula := by
  simp [decodeFormulaBits, formulaBits]

end UniqueGamesTheorem.Foundations.Complexity

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Pure list specification for destructive zero-based unary table lookup.
These are serialization identities and bit-count bounds, not TM2 runtime
certificates. The connection to actual transitions is in `MachineLookup`.
-/
namespace UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

@[simp] theorem decodeWords_encodeWord (i : Nat) :
    decodeWords (encodeWord i) = some [i] := by
  simpa [encodeWords] using decodeWords_encodeWords [i]

/-! Bounds on the proposed lookup recurrence. A separate machine proof must
identify these counts with actual transition traces. -/

end UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec

end

section

/-!
One actual TM2 transition tests and decrements a zero-delimited unary counter.
The guard peeks before branching: a true bit is popped, while a false delimiter
is retained. Both branches clear the one-bit register and preserve the ambient
state. There is no assumed execution trace or input-dependent finite program.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

open Turing

variable {K Λ σ : Type} [DecidableEq K]

/-- An arbitrary caller frame with one tape holding the unary counter and
its unread suffix. Only this tape depends on the counter value. -/
def counterTapes (counter : K) (base : K → List Bool) (n : Nat)
    (suffix : List Bool) : K → List Bool :=
  Function.update base counter (encodeWord n ++ suffix)

@[simp] theorem counterTapes_counter (counter : K) (base : K → List Bool)
    (n : Nat) (suffix : List Bool) :
    counterTapes counter base n suffix counter = encodeWord n ++ suffix := by
  simp [counterTapes]

end UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_GapSemanticsLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Changing finite encodings preserves the actual Unique Games instance gaps.
Vertex names may be permuted and constraint occurrences may be reordered. -/

namespace UniqueGamesTheorem.Integration.InstanceEquivalences

open UniqueGamesTheorem.Foundations.Target

def renameConstraint {n m q : Nat} (e : Fin n ≃ Fin m) (c : Constraint n q) :
    Constraint m q where
  source := e c.source
  target := e c.target
  permutation := c.permutation

@[simp] theorem renameConstraint_satisfied {n m q : Nat} (e : Fin n ≃ Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (renameConstraint e c).satisfied labeling = c.satisfied (labeling ∘ e) := rfl

end UniqueGamesTheorem.Integration.InstanceEquivalences

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_RealTargetLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Injective vertex addresses may leave unused output vertices. The actual
instance is obtained by mapping endpoints in the original constraint list;
constraint order, multiplicity, and permutation tables are retained exactly. -/

namespace UniqueGamesTheorem.Integration.VertexEmbedding

open UniqueGamesTheorem.Foundations.Target

def embedConstraint {n m q : Nat} (f : Fin n → Fin m) (c : Constraint n q) :
    Constraint m q where
  source := f c.source
  target := f c.target
  permutation := c.permutation

@[simp] theorem embedConstraint_satisfied {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) (labeling : Fin m → Fin q) :
    (embedConstraint f c).satisfied labeling = c.satisfied (labeling ∘ f) := rfl

@[simp] theorem embedConstraint_permutation {n m q : Nat} (f : Fin n → Fin m)
    (c : Constraint n q) : (embedConstraint f c).permutation = c.permutation := rfl

def embedInstance {q m : Nat} (g : Instance q) (f : Fin g.vertices → Fin m)
    (_hf : Function.Injective f) : Instance q where
  vertices := m
  constraints := g.constraints.map (embedConstraint f)
  nonempty h := g.nonempty (List.map_eq_nil_iff.mp h)

@[simp] theorem embedInstance_vertices {q m : Nat} (g : Instance q)
    (f : Fin g.vertices → Fin m) (hf : Function.Injective f) :
    (embedInstance g f hf).vertices = m := rfl

end UniqueGamesTheorem.Integration.VertexEmbedding

end

section

namespace UniqueGamesTheorem.Reduction.ActualHomogeneous

open Integration.BinaryLinear
open scoped BigOperators

abbrev E (k : Nat) := F2 × (Fin k → F2 × F2)

variable {dimension : Nat}

def tau : E dimension →ₗ[F2] F2 := LinearMap.fst F2 _ _
def hBasis (k : Nat) : E k := (1, 0)
def firstBasis (j : Fin dimension) : E dimension := (0, Pi.single j (1, 0))
def secondBasis (j : Fin dimension) : E dimension := (0, Pi.single j (0, 1))

@[simp] theorem tau_hBasis : tau (hBasis dimension) = 1 := rfl
@[simp] theorem tau_firstBasis (j : Fin dimension) : tau (firstBasis j) = 0 := rfl
@[simp] theorem tau_secondBasis (j : Fin dimension) : tau (secondBasis j) = 0 := rfl

end UniqueGamesTheorem.Reduction.ActualHomogeneous

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_ActualSourceLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.MatrixSlice.parameterEquivSlice_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidateEquiv_val _root_.OAI.PerfectCompleteness.PulledColumnSpace.pulledEquiv_val _root_.OAI.PerfectCompleteness.RowAdvice.pad_low _root_.OAI.PerfectCompleteness.TensorEquationSpace.pureFactor_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_apply _root_.OAI.PerfectCompleteness.TensorRestriction.restrictionMap_tmul _root_.OAI.PerfectCompleteness.TensorRestriction.tensorEquivHom_tmul _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.embed_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Reduction.ActualSource

open UniqueGamesTheorem.Integration.BinaryLinear

abbrev Alphabet (s : Nat) := UniqueGamesTheorem.Integration.BinaryLinear.Vector s
abbrev Ambient (s d : Nat) := Alphabet s × UniqueGamesTheorem.Integration.BinaryLinear.Vector d

def alphabetEmbedding (s d : Nat) : Alphabet s →ₗ[F2] Ambient s d :=
  LinearMap.inl F2 (Alphabet s) (UniqueGamesTheorem.Integration.BinaryLinear.Vector d)

@[simp] theorem alphabetEmbedding_apply (s d : Nat) (c : Alphabet s) :
    alphabetEmbedding s d c = (c, 0) := rfl

end UniqueGamesTheorem.Reduction.ActualSource

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DualQuotientRowsLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DualQuotientRows

noncomputable section

open Module
open UniqueGamesTheorem.Foundations.Games

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

def quotientRowEquiv (W : Submodule 𝕜 E) :
    Module.Dual 𝕜 (E ⧸ W) ≃ₗ[𝕜] W.dualAnnihilator :=
  W.dualQuotEquivDualAnnihilator

@[simp]
theorem quotientRowEquiv_val (W : Submodule 𝕜 E) (row : Module.Dual 𝕜 (E ⧸ W)) :
    (quotientRowEquiv W row : Module.Dual 𝕜 E) = row.comp W.mkQ := rfl


variable {H : Type*} [AddCommGroup H] [Module 𝕜 H] [FiniteDimensional 𝕜 H]

def nativeRowMap (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W) →ₗ[𝕜] H :=
  (Module.evalEquiv 𝕜 H).symm.toLinearMap.comp W.mkQ.dualMap

@[simp]
theorem apply_nativeRowMap (W : Submodule 𝕜 (Module.Dual 𝕜 H))
    (row : Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W)) (q : Module.Dual 𝕜 H) :
    q (nativeRowMap W row) = row (W.mkQ q) := by
  change q ((Module.evalEquiv 𝕜 H).symm (W.mkQ.dualMap row)) = _
  rw [Module.apply_evalEquiv_symm_apply]
  rfl

theorem nativeRowMap_injective (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Function.Injective (nativeRowMap W) := by
  intro row₁ row₂ h
  apply (quotientRowEquiv W).injective
  apply Subtype.ext
  apply (Module.evalEquiv 𝕜 H).symm.injective
  exact h

theorem range_nativeRowMap (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    LinearMap.range (nativeRowMap W) = W.dualCoannihilator := by
  apply le_antisymm
  · rintro x ⟨row, rfl⟩
    apply (Submodule.mem_dualCoannihilator _).mpr
    intro q hq
    rw [apply_nativeRowMap]
    have hzero : W.mkQ q = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hq
    rw [hzero, map_zero]
  · intro x hx
    let v : W.dualAnnihilator := ⟨Module.evalEquiv 𝕜 H x, hx⟩
    obtain ⟨row, hrow⟩ := (quotientRowEquiv W).surjective v
    refine ⟨row, ?_⟩
    have hvalue := congrArg (fun z : W.dualAnnihilator =>
      (z : Module.Dual 𝕜 (Module.Dual 𝕜 H))) hrow
    change W.mkQ.dualMap row = Module.evalEquiv 𝕜 H x at hvalue
    change (Module.evalEquiv 𝕜 H).symm (W.mkQ.dualMap row) = x
    rw [hvalue, LinearEquiv.symm_apply_apply]

def nativeRowLinear (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W) →ₗ[𝕜] W.dualCoannihilator :=
  (nativeRowMap W).codRestrict W.dualCoannihilator (fun row => by
    rw [← range_nativeRowMap W]
    exact LinearMap.mem_range_self (nativeRowMap W) row)

def nativeRowEquiv (W : Submodule 𝕜 (Module.Dual 𝕜 H)) :
    Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W) ≃ₗ[𝕜] W.dualCoannihilator :=
  LinearEquiv.ofBijective (nativeRowLinear W) ⟨by
    intro row₁ row₂ h
    exact nativeRowMap_injective W
      (congrArg (fun x : W.dualCoannihilator => (x : H)) h), by
    intro x
    have hx : (x : H) ∈ LinearMap.range (nativeRowMap W) := by
      rw [range_nativeRowMap]
      exact x.property
    obtain ⟨row, hrow⟩ := hx
    exact ⟨row, Subtype.ext hrow⟩⟩

@[simp]
theorem nativeRowEquiv_val (W : Submodule 𝕜 (Module.Dual 𝕜 H))
    (row : Module.Dual 𝕜 (Module.Dual 𝕜 H ⧸ W)) :
    (nativeRowEquiv W row : H) = nativeRowMap W row := rfl

end
end PerfectCompleteness.DualQuotientRows



namespace PerfectCompleteness.LevelPairCounting

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω : Type*} [Fintype Ω] {d : Nat}

def pairProbability (μ : FiniteDistribution Ω) (win : Fin d → Ω → Bool)
    (i j : Fin d) : ℝ :=
  μ.probability (fun ω => win i ω && win j ω)

@[simp] theorem pairProbability_self (μ : FiniteDistribution Ω)
    (win : Fin d → Ω → Bool) (i : Fin d) :
    pairProbability μ win i i = μ.probability (win i) := by
  apply congrArg μ.probability
  funext ω
  cases win i ω <;> rfl

end
end PerfectCompleteness.LevelPairCounting



namespace PerfectCompleteness.SmallBiasSlice

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

def bitSign (b : Bool) : ℝ := if b then -1 else 1


variable {F : Type*} [AddCommMonoid F]

def rowCombination (rows : I → F) (s : I → Bool) : F :=
  ∑ i, if s i then rows i else 0

omit [DecidableEq I] in
@[simp] theorem rowCombination_zero (rows : I → F) :
    rowCombination rows (fun _ => false) = 0 := by simp [rowCombination]


end

end PerfectCompleteness.SmallBiasSlice

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_MachineTransfer
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified reversal and relabeling between finite alphabets

The actual TM2 machine transfers a list over a finite alphabet `α` to a second
stack over `β`, reverses its order, and applies a fixed map `f : α → β` to each
symbol. The trace has exactly `input.length + 1` transitions. An explicit
fallback symbol makes the push expression total, including the unused branch
where the internal register is empty.

This primitive supports machine composition when intermediate stack alphabets
differ. It does not yet implement the Unique Games reduction.
-/

namespace UniqueGamesTheorem.Reduction.MachineTransfer

open Turing

abbrev alphabet (α β : Type) : Bool → Type
  | false => α
  | true => β

variable {α β : Type} [Fintype α] [Fintype β]

def loop (f : α → β) (fallback : β) :
    TM2.Stmt (alphabet α β) Unit (Option β) :=
  .pop false (fun _ head => head.map f)
    (.branch Option.isSome
      (.push true (fun state => state.getD fallback) (.goto fun _ => ()))
      .halt)

def machine (f : α → β) (fallback : β) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := alphabet α β
  Λ := Unit
  main := ()
  σ := Option β
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype α)
  m _ := loop f fallback

def tapeStacks (input : List α) (output : List β) :
    (side : Bool) → List (alphabet α β side)
  | false => input
  | true => output

def running (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) : (machine f fallback).Cfg :=
  ⟨some (), state, tapeStacks input output⟩

def halted (f : α → β) (fallback : β) (output : List β) : (machine f fallback).Cfg :=
  ⟨none, none, tapeStacks (α := α) [] output⟩

omit [Fintype α] [Fintype β] in
theorem update_input (input replacement : List α) (output : List β) :
    Function.update (tapeStacks input output) false replacement = tapeStacks replacement output := by
  funext side
  cases side <;> rfl

omit [Fintype α] [Fintype β] in
theorem update_output (input : List α) (output replacement : List β) :
    Function.update (tapeStacks input output) true replacement = tapeStacks input replacement := by
  funext side
  cases side <;> rfl

theorem step_empty (f : α → β) (fallback : β) (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback [] output state) =
      some (halted f fallback output) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (α := α) [] output)) = _
  simp [loop, TM2.stepAux, tapeStacks, halted, Function.update]
  rw [update_input]
  rfl

theorem step_cons (f : α → β) (fallback : β) (head : α) (input : List α)
    (output : List β) (state : Option β) :
    (machine f fallback).step (running f fallback (head :: input) output state) =
      some (running f fallback input (f head :: output) (some (f head))) := by
  change some (TM2.stepAux (loop f fallback) state (tapeStacks (head :: input) output)) = _
  simp [loop, TM2.stepAux, tapeStacks, running, Function.update]
  rw [update_input, update_output]
  rfl

def next (f : α → β) (fallback : β) (configuration : Option (machine f fallback).Cfg) :
    Option (machine f fallback).Cfg := configuration.bind (machine f fallback).step

/-- Exact actual-machine trace, for any accumulator and internal register. -/
theorem transfer_steps (f : α → β) (fallback : β) (input : List α) (output : List β)
    (state : Option β) :
    (next f fallback)^[input.length + 1] (some (running f fallback input output state)) =
      some (halted f fallback (input.reverse.map f ++ output)) := by
  induction input generalizing output state with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, next,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using step_empty f fallback output state
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (next f fallback)^[input.length + 1]
      ((machine f fallback).step (running f fallback (head :: input) output state)) = _
    rw [step_cons, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

theorem initList_eq (f : α → β) (fallback : β) (input : List α) :
    initList (machine f fallback) input = running f fallback input [] none := by
  unfold initList running
  congr 1
  funext side
  cases side <;> rfl

theorem haltList_eq (f : α → β) (fallback : β) (output : List β) :
    haltList (machine f fallback) output = halted f fallback output := by
  unfold haltList halted
  congr 1
  funext side
  cases side <;> rfl

theorem transfer_init_steps (f : α → β) (fallback : β) (input : List α) :
    (next f fallback)^[input.length + 1] (some (initList (machine f fallback) input)) =
      some (haltList (machine f fallback) (input.reverse.map f)) := by
  calc
    _ = (next f fallback)^[input.length + 1]
        (some (running f fallback input [] none)) :=
      congrArg (fun c => (next f fallback)^[input.length + 1] (some c))
        (initList_eq f fallback input)
    _ = some (halted f fallback (input.reverse.map f)) := by
      simpa only [List.append_nil] using transfer_steps f fallback input [] none
    _ = _ := congrArg some (haltList_eq f fallback (input.reverse.map f)).symm

def outputsInTime (f : α → β) (fallback : β) (input : List α) :
    TM2OutputsInTime (machine f fallback) input (some (input.reverse.map f))
      (input.length + 1) where
  steps := input.length + 1
  evals_in_steps := transfer_init_steps f fallback input
  steps_le_m := Nat.le_refl _

@[simp] theorem outputsInTime_steps (f : α → β) (fallback : β) (input : List α) :
    (outputsInTime f fallback input).steps = input.length + 1 := rfl

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

def exitAt (dst : K) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def loopAt (src dst : K) (f : Γ src → Γ dst) (fallback : Γ dst)
    (loopLabel : Λ) (exit : Option Λ) : TM2.Stmt Γ Λ (σ × Option (Γ dst)) :=
  .pop src (fun state head => (state.1, head.map f))
    (.branch (fun state => state.2.isSome)
      (.push dst (fun state => state.2.getD fallback) (.goto fun _ => loopLabel))
      (exitAt dst exit))

def tapesAt (src dst : K) (base : (k : K) → List (Γ k))
    (input : List (Γ src)) (output : List (Γ dst)) : (k : K) → List (Γ k) :=
  Function.update (Function.update base src input) dst output

@[simp] theorem tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output src = input := by
  simp [tapesAt, distinct]

@[simp] theorem tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst)) :
    tapesAt src dst base input output dst = output := by
  simp [tapesAt]

@[simp] theorem tapesAt_self (src dst : K) (base : (k : K) → List (Γ k)) :
    tapesAt src dst base (base src) (base dst) = base := by
  simp [tapesAt]

theorem update_tapesAt_src (src dst : K) (distinct : src ≠ dst)
    (base : (k : K) → List (Γ k)) (input replacement : List (Γ src))
    (output : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) src replacement =
      tapesAt src dst base replacement output := by
  funext k
  by_cases hs : k = src
  · subst k
    simp [tapesAt, distinct]
  · by_cases hd : k = dst
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_tapesAt_dst (src dst : K)
    (base : (k : K) → List (Γ k)) (input : List (Γ src))
    (output replacement : List (Γ dst)) :
    Function.update (tapesAt src dst base input output) dst replacement =
      tapesAt src dst base input replacement := by
  funext k
  by_cases hd : k = dst
  · subst k
    simp [tapesAt]
  · simp [tapesAt, hd]

def nextAt (dst : K) (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (configuration : Option (TM2.Cfg Γ Λ (σ × Option (Γ dst)))) :
    Option (TM2.Cfg Γ Λ (σ × Option (Γ dst))) :=
  configuration.bind (TM2.step program)

theorem stepAt_empty (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program ⟨some loopLabel, (ambient, register), tapesAt src dst base [] output⟩ =
      some ⟨exit, (ambient, none), tapesAt src dst base [] output⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base [] output)) = _
  rw [atLoop]
  cases exit <;>
    simp [loopAt, exitAt, TM2.stepAux, tapesAt_src, distinct, update_tapesAt_src]

theorem stepAt_cons (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (head : Γ src) (input : List (Γ src))
    (output : List (Γ dst)) (ambient : σ) (register : Option (Γ dst)) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩ =
      some ⟨some loopLabel, (ambient, some (f head)),
        tapesAt src dst base input (f head :: output)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (tapesAt src dst base (head :: input) output)) = _
  rw [atLoop]
  simp [loopAt, TM2.stepAux, tapesAt_src, tapesAt_dst, distinct,
    update_tapesAt_src, update_tapesAt_dst]

/-- Placement-aware exact transfer, preserving all ambient state and other tapes.
The optional exit label is reached in the same final empty-pop transition. -/
theorem transferAt_steps (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (input : List (Γ src)) (output : List (Γ dst))
    (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register), tapesAt src dst base input output⟩) =
      some ⟨exit, (ambient, none), tapesAt src dst base [] (input.reverse.map f ++ output)⟩ := by
  induction input generalizing output register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, nextAt,
      Option.bind_some, List.reverse_nil, List.map_nil, List.nil_append]
      using stepAt_empty src dst distinct f fallback loopLabel exit program atLoop base output
        ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (nextAt dst program)^[input.length + 1]
      (TM2.step program
        ⟨some loopLabel, (ambient, register), tapesAt src dst base (head :: input) output⟩) = _
    rw [stepAt_cons src dst distinct f fallback loopLabel exit program atLoop, ih]
    simp only [List.reverse_cons, List.map_append, List.map_singleton,
      List.append_assoc, List.singleton_append]

/-- The same trace starting with an arbitrary actual ambient tape family. -/
theorem transferAt_fromTapes (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    (nextAt dst program)^[(base src).length + 1]
      (some ⟨some loopLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩ := by
  simpa only [tapesAt_self] using
    transferAt_steps src dst distinct f fallback loopLabel exit program atLoop base
      (base src) (base dst) ambient register

/-- A timed execution witness suitable for composing this bridge with other
phases of the same actual transition system. -/
def transferAtInTime (src dst : K) (distinct : src ≠ dst)
    (f : Γ src → Γ dst) (fallback : Γ dst) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt Γ Λ (σ × Option (Γ dst)))
    (atLoop : program loopLabel = loopAt src dst f fallback loopLabel exit)
    (base : (k : K) → List (Γ k)) (ambient : σ) (register : Option (Γ dst)) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, register), base⟩
      (some ⟨exit, (ambient, none),
        tapesAt src dst base [] ((base src).reverse.map f ++ base dst)⟩)
      ((base src).length + 1) where
  steps := (base src).length + 1
  evals_in_steps := transferAt_fromTapes src dst distinct f fallback loopLabel exit
    program atLoop base ambient register
  steps_le_m := Nat.le_refl _

end UniqueGamesTheorem.Reduction.MachineTransfer

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCopy

open Turing

variable {K Λ σ β : Type} [DecidableEq K]

abbrev Alphabet (β : Type) (_ : K) := β

/-- Drain one tape into two reverse-order accumulators. -/
def forkLoop (source left right : K) (fallback : β) (loopLabel : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push left (fun state => state.2.getD fallback)
        (.push right (fun state => state.2.getD fallback) (.goto fun _ => loopLabel)))
      (Reduction.MachineTransfer.exitAt right exit))

def forkTapes (source left right : K) (base : K → List β)
    (input leftOutput rightOutput : List β) : K → List β :=
  Function.update (Function.update (Function.update base source input) left leftOutput)
    right rightOutput

@[simp] theorem forkTapes_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput source = input := by
  simp [forkTapes, sourceLeft, sourceRight]

@[simp] theorem forkTapes_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput left = leftOutput := by
  simp [forkTapes, leftRight]

@[simp] theorem forkTapes_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput : List β) :
    forkTapes source left right base input leftOutput rightOutput right = rightOutput := by
  simp [forkTapes]

@[simp] theorem forkTapes_self (source left right : K) (base : K → List β) :
    forkTapes source left right base (base source) (base left) (base right) = base := by
  simp [forkTapes]

theorem update_fork_source (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      source replacement = forkTapes source left right base replacement leftOutput rightOutput := by
  funext k
  by_cases hs : k = source
  · subst k; simp [forkTapes, sourceLeft, sourceRight]
  · by_cases hl : k = left
    · subst k; simp [forkTapes, Ne.symm sourceLeft, leftRight]
    · by_cases hr : k = right
      · subst k; simp [forkTapes, Ne.symm sourceRight]
      · simp [forkTapes, hs, hl, hr]

theorem update_fork_left (source left right : K) (leftRight : left ≠ right)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      left replacement = forkTapes source left right base input replacement rightOutput := by
  funext k
  by_cases hl : k = left
  · subst k; simp [forkTapes, leftRight]
  · by_cases hr : k = right
    · subst k; simp [forkTapes, Ne.symm leftRight]
    · simp [forkTapes, hl, hr]

theorem update_fork_right (source left right : K)
    (base : K → List β) (input leftOutput rightOutput replacement : List β) :
    Function.update (forkTapes source left right base input leftOutput rightOutput)
      right replacement = forkTapes source left right base input leftOutput replacement := by
  simp [forkTapes]

theorem forkStep_empty (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (leftOutput rightOutput : List β) (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register), forkTapes source left right base [] leftOutput rightOutput⟩ =
        some ⟨exit, (ambient, none), forkTapes source left right base [] leftOutput rightOutput⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base [] leftOutput rightOutput)) = _
  rw [atLoop]
  cases exit <;>
    simp [forkLoop, Reduction.MachineTransfer.exitAt, TM2.stepAux, sourceLeft, sourceRight,
      leftRight, update_fork_source]

theorem forkStep_cons (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (head : β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    TM2.step program
      ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩ =
      some ⟨some loopLabel, (ambient, some head),
        forkTapes source left right base input (head :: leftOutput) (head :: rightOutput)⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, register)
    (forkTapes source left right base (head :: input) leftOutput rightOutput)) = _
  rw [atLoop]
  simp [forkLoop, TM2.stepAux, sourceLeft, sourceRight, leftRight,
    update_fork_source, update_fork_left, update_fork_right]

/-- Each symbol and the final empty test take one actual transition. -/
theorem forkTrace (source left right : K)
    (sourceLeft : source ≠ left) (sourceRight : source ≠ right) (leftRight : left ≠ right)
    (fallback : β) (loopLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atLoop : program loopLabel = forkLoop source left right fallback loopLabel exit)
    (base : K → List β) (input leftOutput rightOutput : List β)
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (some ⟨some loopLabel, (ambient, register),
        forkTapes source left right base input leftOutput rightOutput⟩) =
      some ⟨exit, (ambient, none), forkTapes source left right base []
        (input.reverse ++ leftOutput) (input.reverse ++ rightOutput)⟩ := by
  induction input generalizing leftOutput rightOutput register with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, List.reverse_nil, List.nil_append] using
        forkStep_empty source left right sourceLeft sourceRight leftRight fallback loopLabel exit
          program atLoop base leftOutput rightOutput ambient register
  | cons head input ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[input.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, register),
        forkTapes source left right base (head :: input) leftOutput rightOutput⟩) = _
    rw [forkStep_cons source left right sourceLeft sourceRight leftRight fallback loopLabel exit
      program atLoop base head input leftOutput rightOutput ambient register, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

def drainedTapes (source scratch : K) (base : K → List β) : K → List β :=
  Reduction.MachineTransfer.tapesAt source scratch base [] (base source).reverse

theorem restoredTapes (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch) (base : K → List β)
    (scratchEmpty : base scratch = []) :
    forkTapes scratch source destination (drainedTapes source scratch base) []
      (base source) (base source ++ base destination) =
        Function.update base destination (base source ++ base destination) := by
  funext k
  by_cases hs : k = source
  · subst k
    simp [forkTapes, sourceDestination]
  · by_cases hd : k = destination
    · subst k; simp [forkTapes]
    · by_cases ht : k = scratch
      · subst k
        simp [forkTapes, Ne.symm sourceScratch, Ne.symm destinationScratch, scratchEmpty]
      · simp [forkTapes, drainedTapes, Reduction.MachineTransfer.tapesAt, hs, hd, ht]

theorem copyTrace (source destination scratch : K)
    (sourceDestination : source ≠ destination) (sourceScratch : source ≠ scratch)
    (destinationScratch : destination ≠ scratch)
    (fallback : β) (firstLabel secondLabel : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K) β) Λ (σ × Option β))
    (atFirst : program firstLabel =
      Reduction.MachineTransfer.loopAt source scratch id fallback firstLabel (some secondLabel))
    (atSecond : program secondLabel = forkLoop scratch source destination fallback secondLabel exit)
    (base : K → List β) (scratchEmpty : base scratch = [])
    (ambient : σ) (register : Option β) :
    (MachineComposition.advance (TM2.step program))^[2 * ((base source).length + 1)]
      (some ⟨some firstLabel, (ambient, register), base⟩) =
      some ⟨exit, (ambient, none),
        Function.update base destination (base source ++ base destination)⟩ := by
  have first := Reduction.MachineTransfer.transferAt_fromTapes source scratch sourceScratch
    id fallback firstLabel (some secondLabel) program atFirst base ambient register
  change (MachineComposition.advance (TM2.step program))^[(base source).length + 1]
    (some ⟨some firstLabel, (ambient, register), base⟩) = _ at first
  simp only [List.map_id, scratchEmpty, List.append_nil] at first
  have second := forkTrace scratch source destination (Ne.symm sourceScratch)
    (Ne.symm destinationScratch) sourceDestination fallback secondLabel exit program atSecond
    (drainedTapes source scratch base)
    (drainedTapes source scratch base scratch) (drainedTapes source scratch base source)
    (drainedTapes source scratch base destination) ambient none
  simp only [forkTapes_self] at second
  have scratchWord : drainedTapes source scratch base scratch = (base source).reverse := by
    simp [drainedTapes]
  have sourceWord : drainedTapes source scratch base source = [] := by
    simp [drainedTapes, sourceScratch]
  have destinationWord : drainedTapes source scratch base destination = base destination := by
    simp [drainedTapes, Reduction.MachineTransfer.tapesAt, Ne.symm sourceDestination,
      destinationScratch]
  rw [scratchWord, sourceWord, destinationWord] at second
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at second
  rw [restoredTapes source destination scratch sourceDestination sourceScratch destinationScratch
    base scratchEmpty] at second
  rw [show 2 * ((base source).length + 1) =
    ((base source).length + 1) + ((base source).length + 1) by omega,
    Function.iterate_add_apply, first]
  exact second

end UniqueGamesTheorem.Foundations.Complexity.MachineCopy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_AffineDecoderMeeting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.AffineDecoderMeeting

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section Algebra

variable {H H' : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup H'] [Module F2 H']
  (i : H' →ₗ[F2] H) (B : Submodule F2 H)
  (C : Submodule F2 (Module.Dual F2 (H ⧸ B)))
  (center : Module.Dual F2 H)

def nativeQ : Submodule F2 (Module.Dual F2 H') :=
  (PulledColumnSpace.pulled B C).map i.dualMap

def nativeCenter : Module.Dual F2 H' := i.dualMap center

end Algebra


end
end PerfectCompleteness.AffineDecoderMeeting

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_AffineFunctionalDependence
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.AffineFunctionalDependence

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

noncomputable section

variable {N V : Type*} [AddCommGroup N] [Module F2 N]
  [AddCommGroup V] [Module F2 V] [Fintype N] [Fintype V]

variable {m : Nat}

def coefficientSum (c : Fin m → F2) : (Fin m → N) →ₗ[F2] N where
  toFun x := ∑ i, c i • x i
  map_add' x y := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp only [Pi.smul_apply, Finset.smul_sum, smul_smul, mul_comm, RingHom.id_apply]

@[simp] theorem coefficientSum_apply (c : Fin m → F2) (x : Fin m → N) :
    coefficientSum c x = ∑ i, c i • x i := rfl

end
end PerfectCompleteness.AffineFunctionalDependence

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.QuarterBalance

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias

noncomputable section

abbrev F2 := ZMod 2

def sign (b : F2) : ℝ := if b = 0 then 1 else -1

theorem scalar_cases : ∀ b : F2, b = 0 ∨ b = 1 := by decide

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]
@[simp] theorem abs_sign (b : F2) : |sign b| = 1 := by unfold sign; split <;> norm_num

end
end PerfectCompleteness.QuarterBalance



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryDualCoordinates
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryDualCoordinates

open scoped BigOperators
open QuarterBalance (F2)
open SmallBiasSlice

noncomputable section

def toBool (a : F2) : Bool := decide (a ≠ 0)

def ofBool (b : Bool) : F2 := if b then 1 else 0

@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> simp [toBool, ofBool]

@[simp] theorem ofBool_toBool (a : F2) : ofBool (toBool a) = a := by
  rcases QuarterBalance.scalar_cases a with rfl | rfl <;> simp [toBool, ofBool]

@[simp] theorem bitSign_toBool (a : F2) : bitSign (toBool a) =
    QuarterBalance.sign a := by
  rcases QuarterBalance.scalar_cases a with rfl | rfl <;>
    simp [bitSign, toBool]

variable {I V : Type*} [Fintype I] [AddCommGroup V] [Module F2 V]

def coordinates (b : Module.Basis I F2 V) (x : V) : I → Bool :=
  fun i => toBool (b.coord i x)

def frequency (b : Module.Basis I F2 V) (s : I → Bool) : Module.Dual F2 V :=
  rowCombination (fun i => b.coord i) s

theorem frequency_apply (b : Module.Basis I F2 V) (s : I → Bool) (x : V) :
    frequency b s x = ∑ i, if s i then b.coord i x else 0 := by
  classical
  simp only [frequency, rowCombination, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases s i <;> simp

@[simp] theorem frequency_apply_basis (b : Module.Basis I F2 V)
    (s : I → Bool) (j : I) : frequency b s (b j) = ofBool (s j) := by
  classical
  rw [frequency_apply, Finset.sum_eq_single j]
  · simp [Module.Basis.coord_apply, ofBool]
  · intro i _ hij
    simp [Module.Basis.coord_apply, Ne.symm hij]
  · simp

def frequencyEquiv (b : Module.Basis I F2 V) :
    (I → Bool) ≃ Module.Dual F2 V where
  toFun := frequency b
  invFun f i := toBool (f (b i))
  left_inv s := by funext i; simp
  right_inv f := by apply b.ext; intro i; simp

def character (f : Module.Dual F2 V) (x : V) : ℝ :=
  QuarterBalance.sign (f x)

@[simp] theorem character_zero (x : V) : character 0 x = 1 := by
  simp [character]

@[simp] theorem abs_character (f : Module.Dual F2 V) (x : V) :
    |character f x| = 1 := QuarterBalance.abs_sign _

variable {U : Type*} [AddCommGroup U] [Module F2 U]

def equationRows (b : Module.Basis I F2 V) (R : U →ₗ[F2] V) :
    I → Module.Dual F2 U := fun i => (b.coord i).comp R

def equations (b : Module.Basis I F2 V) (R : U →ₗ[F2] V) (x : U) : I → Bool :=
  coordinates b (R x)

end
end PerfectCompleteness.BinaryDualCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_AffineLinearHeavyWitness
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.AffineLinearHeavyWitness

open scoped BigOperators
open QuarterBalance (F2)
open BinaryDualCoordinates
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {U V K I J : Type*}
  [AddCommGroup U] [Module F2 U] [Fintype U]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup K] [Module F2 K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def conditionalMatch (μ : FiniteDistribution U) (R : U →ₗ[F2] V) (target : V)
    (G : U → K) (T : U →ₗ[F2] K) (offset : K) : ℝ := by
  classical
  exact μ.expectation (fun x => if R x = target then
    (if G x = offset + T x then 1 else 0) else 0) /
  μ.expectation (fun x => if R x = target then 1 else 0)

def badMasks (c : Module.Basis J F2 K) (bad : Finset (Module.Dual F2 K)) :
    Finset (J → Bool) :=
  bad.map (frequencyEquiv c).symm.toEmbedding

omit [DecidableEq J] in
@[simp] theorem mem_badMasks (c : Module.Basis J F2 K)
    (bad : Finset (Module.Dual F2 K)) (s : J → Bool) :
    s ∈ badMasks c bad ↔ frequency c s ∈ bad := by
  classical
  constructor
  · rintro h
    obtain ⟨f, hf, heq⟩ := Finset.mem_map.mp h
    have heq' : frequency c s = f := by
      change (frequencyEquiv c) s = f
      rw [← heq]
      exact (frequencyEquiv c).apply_symm_apply f
    simpa only [heq'] using hf
  · intro h
    apply Finset.mem_map.mpr
    refine ⟨frequency c s, h, ?_⟩
    exact (frequencyEquiv c).symm_apply_apply s

omit [DecidableEq J] in
@[simp] theorem card_badMasks (c : Module.Basis J F2 K)
    (bad : Finset (Module.Dual F2 K)) :
    (badMasks c bad).card = bad.card := Finset.card_map _

end
end PerfectCompleteness.AffineLinearHeavyWitness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearWitnessLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BilinearWitness

open scoped BigOperators

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

def assemble (f : (i : I) → V i →ₗ[𝕜] H) (x : (i : I) → V i) : H :=
  ∑ i, f i (x i)

omit [DecidableEq I] in
theorem exists_child_pair (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜)
    (nonzero : B ≠ 0) : ∃ i j, ∃ (x : V i) (y : V j), B (f i x) (f j y) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply nonzero
  ext u v
  obtain ⟨x, rfl⟩ := spans u
  obtain ⟨y, rfl⟩ := spans v
  simp only [assemble, map_sum, LinearMap.sum_apply]
  simp only [h, Finset.sum_const_zero, LinearMap.zero_apply]

def Witness (f : (i : I) → V i →ₗ[𝕜] H) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜) :=
  { w : (Σ i : I, Σ j : I, V i × V j) // B (f w.1 w.2.2.1) (f w.2.1 w.2.2.2) ≠ 0 }

def chooseWitness (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜)
    (nonzero : B ≠ 0) : Witness f B := by
  classical
  apply Classical.choice
  obtain ⟨i, j, x, y, h⟩ := exists_child_pair f spans B nonzero
  exact ⟨⟨⟨i, j, x, y⟩, h⟩⟩

def selected (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜) : Finset I := by
  classical
  exact if h : B = 0 then ∅ else
    { (chooseWitness f spans B h).val.1, (chooseWitness f spans B h).val.2.1 }

end
end PerfectCompleteness.BilinearWitness


namespace PerfectCompleteness.BilinearCollisionTransfer

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness BilinearWitness

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

abbrev Form := H →ₗ[𝕜] H →ₗ[𝕜] 𝕜

def fullCollision (a b : Option (Form (𝕜 := 𝕜) (H := H))) : Bool :=
  decide (∃ F, a = some F ∧ b = some F)

def restrictedCollision (a b : Option (Form (𝕜 := 𝕜) (H := H)))
    (U : Submodule 𝕜 H) : Bool :=
  decide (∃ F G, a = some F ∧ b = some G ∧
    ∀ v ∈ U, ∀ w ∈ U, F v w = G v w)

end
end PerfectCompleteness.BilinearCollisionTransfer

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_AscendingBranchingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.AscendingBranching

open scoped BigOperators Classical

noncomputable section

def CubeErrors (L c ε : ℝ) (m : Nat) : Prop :=
  2 ≤ m ∧
    Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < ε ∧
    Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < ε ∧
    2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < ε ∧
    (1 - c / (m : ℝ) ^ 2) ^ (m ^ 3) < ε

end
end PerfectCompleteness.AscendingBranching



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeSourceSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeSourceSpaces

abbrev F2 := ZMod 2

end PerfectCompleteness.TreeSourceSpaces

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_ClauseVerifierLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.clauseWords_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.decodeFormulaBits_encoded _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.decodeFormulaWords_encoded _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.parseClause_encoded _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.parseClauses_encoded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP

open Target

structure ClauseAnswer where
  first : Bool
  second : Bool
  third : Bool
  deriving DecidableEq

inductive Slot where
  | first
  | second
  | third
  deriving DecidableEq

def answerAt (answer : ClauseAnswer) : Slot → Bool
  | .first => answer.first
  | .second => answer.second
  | .third => answer.third

def nameAt {n : Nat} (clause : Clause n) : Slot → Fin n
  | .first => clause[0].variableIndex
  | .second => clause[1].variableIndex
  | .third => clause[2].variableIndex

def literalValue (positive value : Bool) : Bool :=
  if positive then value else !value

def localSatisfies {n : Nat} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  (literalValue clause[0].positive answer.first ||
   literalValue clause[1].positive answer.second) ||
   literalValue clause[2].positive answer.third

def clauseAt (formula : Formula) (index : Fin formula.clauses.length) :
    Clause formula.variables := formula.clauses[index.val]

end UniqueGamesTheorem.Foundations.PCP

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceContexts

open Target PCP

/-- Executable tuple encoding of the eight clause answers. -/
def clauseAnswerEquiv : ClauseAnswer ≃ Bool × Bool × Bool where
  toFun a := (a.first, a.second, a.third)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩
  left_inv a := by cases a; rfl
  right_inv a := by rcases a with ⟨a, b, c⟩; rfl

def clauseAnswerFinEquiv : ClauseAnswer ≃ Fin 8 :=
  clauseAnswerEquiv.trans
    ((Equiv.prodCongr finTwoEquiv.symm
      (Equiv.prodCongr finTwoEquiv.symm finTwoEquiv.symm)).trans
      ((Equiv.prodCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans finProdFinEquiv))

instance clauseAnswerFintype : Fintype ClauseAnswer :=
  Fintype.ofEquiv (Bool × Bool × Bool) clauseAnswerEquiv.symm

instance slotFintype : Fintype Slot where
  elems := {.first, .second, .third}
  complete s := by cases s <;> simp

@[simp] theorem card_clauseAnswer : Fintype.card ClauseAnswer = 8 := by
  rw [Fintype.card_congr clauseAnswerFinEquiv]
  rfl

@[simp] theorem card_slot : Fintype.card Slot = 3 := by decide

abbrev J (u : ℕ) := Fin u → ClauseAnswer
abbrev ClauseContext (F : Formula) (u : ℕ) := Fin u → Fin F.clauses.length
abbrev VariableContext (F : Formula) (u : ℕ) := Fin u → Fin F.variables
abbrev SlotContext (u : ℕ) := Fin u → Slot

@[simp] theorem card_J (u : ℕ) : Fintype.card (J u) = 8 ^ u := by simp [J]
@[simp] theorem card_ClauseContext (F : Formula) (u : ℕ) :
    Fintype.card (ClauseContext F u) = F.clauses.length ^ u := by simp [ClauseContext]
@[simp] theorem card_VariableContext (F : Formula) (u : ℕ) :
    Fintype.card (VariableContext F u) = F.variables ^ u := by simp [VariableContext]
@[simp] theorem card_SlotContext (u : ℕ) :
    Fintype.card (SlotContext u) = 3 ^ u := by simp [SlotContext]

def localConsistent {n : ℕ} (clause : Clause n) (answer : ClauseAnswer) : Bool :=
  decide (∀ s s' : Slot, nameAt clause s = nameAt clause s' →
    answerAt answer s = answerAt answer s')

@[simp] theorem localConsistent_eq_true_iff {n : ℕ}
    (clause : Clause n) (answer : ClauseAnswer) :
    localConsistent clause answer = true ↔
      ∀ s s' : Slot, nameAt clause s = nameAt clause s' →
        answerAt answer s = answerAt answer s' := by
  simp [localConsistent]

/-- Satisfaction and consistency over all `3*u` occurrence slots. -/
def validJ (F : Formula) {u : ℕ} (c : ClauseContext F u) (j : J u) : Bool :=
  decide ((∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
    ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
      answerAt (j t) s = answerAt (j t') s')

@[simp] theorem validJ_eq_true_iff (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (j : J u) :
    validJ F c j = true ↔
      (∀ t, localSatisfies (clauseAt F (c t)) (j t) = true) ∧
      ∀ t t' s s', nameAt (clauseAt F (c t)) s = nameAt (clauseAt F (c t')) s' →
        answerAt (j t) s = answerAt (j t') s' := by
  simp [validJ]

/-- First matching visible occurrence, with the third slot as an off-support
default. Its inputs contain no hidden incidence choice. -/
def canonicalSlot {n : ℕ} (clause : Clause n) (v : Fin n) : Slot :=
  if nameAt clause .first = v then .first
  else if nameAt clause .second = v then .second else .third

def baseAccepts (F : Formula) (v : Fin F.variables) (c : Fin F.clauses.length)
    (i : Bool) (j : ClauseAnswer) : Bool :=
  decide (localSatisfies (clauseAt F c) j = true ∧
    localConsistent (clauseAt F c) j = true ∧
    answerAt j (canonicalSlot (clauseAt F c) v) = i)

@[simp] theorem baseAccepts_eq_true_iff (F : Formula) (v : Fin F.variables)
    (c : Fin F.clauses.length) (i : Bool) (j : ClauseAnswer) :
    baseAccepts F v c i j = true ↔
      localSatisfies (clauseAt F c) j = true ∧
      localConsistent (clauseAt F c) j = true ∧
      answerAt j (canonicalSlot (clauseAt F c) v) = i := by
  simp [baseAccepts]

end UniqueGamesTheorem.Foundations.Hastad.SourceContexts

end

section

namespace UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

open Target PCP SourceContexts

abbrev Position (u : ℕ) := Fin u × Slot
abbrev NameProfile (u : ℕ) := Position u → Position u → Bool

/-- All local control data have sizes determined solely by the repetition
parameter. Global variable and clause indices are absent. -/
structure Signature (u : ℕ) where
  signs : Position u → Bool
  sameName : NameProfile u
  selected : SlotContext u
  deriving DecidableEq

@[simp] theorem card_position (u : ℕ) : Fintype.card (Position u) = 3 * u := by
  simp [Position, Nat.mul_comm]

def positiveAt {n : ℕ} (clause : Clause n) : Slot → Bool
  | .first => clause[0].positive
  | .second => clause[1].positive
  | .third => clause[2].positive

def occurrenceName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (p : Position u) : Fin F.variables :=
  nameAt (clauseAt F (c p.1)) p.2

/-- The equality matrix can be supplied by a separate field-comparison
procedure after an explicit reindexing of the `3*u` positions. -/
def contextNameProfile (F : Formula) {u : ℕ} (c : ClauseContext F u) : NameProfile u :=
  fun p q => decide (occurrenceName F c p = occurrenceName F c q)

def ofContext (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (selected : SlotContext u) : Signature u where
  signs p := positiveAt (clauseAt F (c p.1)) p.2
  sameName := contextNameProfile F c
  selected := selected

@[simp] theorem ofContext_signs (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p : Position u) :
    (ofContext F c s).signs p = positiveAt (clauseAt F (c p.1)) p.2 := rfl

@[simp] theorem ofContext_sameName (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) (p q : Position u) :
    (ofContext F c s).sameName p q =
      decide (occurrenceName F c p = occurrenceName F c q) := rfl

@[simp] theorem ofContext_selected (F : Formula) {u : ℕ} (c : ClauseContext F u)
    (s : SlotContext u) : (ofContext F c s).selected = s := rfl

/-- Local clause truth is computed from signs and the three answer bits. -/
def signatureSatisfies {u : ℕ} (σ : Signature u) (j : J u) (t : Fin u) : Bool :=
  (literalValue (σ.signs (t, .first)) (j t).first ||
    literalValue (σ.signs (t, .second)) (j t).second) ||
    literalValue (σ.signs (t, .third)) (j t).third

@[simp] theorem signatureSatisfies_ofContext (F : Formula) {u : ℕ}
    (c : ClauseContext F u) (s : SlotContext u) (j : J u) (t : Fin u) :
    signatureSatisfies (ofContext F c s) j t =
      localSatisfies (clauseAt F (c t)) (j t) := rfl

end UniqueGamesTheorem.Foundations.Hastad.SourceLocalSignature

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryFormulaLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryFormula

open UniqueGamesTheorem.Foundations

def clauseNames (c : Clause) : List Nat :=
  [(c)[0].name, (c)[1].name, (c)[2].name]

def sourceNames (F : Formula) : List Nat :=
  F.clauses.flatMap clauseNames

def activeNames (F : Formula) : List Nat :=
  (sourceNames F).eraseDups

def compactIndex (F : Formula) (v : Nat)
    (hv : v ∈ activeNames F) : Fin (activeNames F).length :=
  ⟨(activeNames F).idxOf v, List.idxOf_lt_length_iff.mpr hv⟩

def compactLiteral (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : Target.Literal (activeNames F).length :=
  ⟨compactIndex F l.name hl, l.positive⟩

@[simp] theorem compactLiteral_positive (F : Formula) (l : Literal)
    (hl : l.name ∈ activeNames F) : (compactLiteral F l hl).positive = l.positive := rfl

theorem clauseNames_flat_length (cs : List Clause) :
    (cs.flatMap clauseNames).length = 3 * cs.length := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.flatMap_cons, List.length_append, clauseNames,
      List.length_cons, List.length_nil, ih]
    omega

end PerfectCompleteness.BinaryFormula



namespace PerfectCompleteness.BinaryEncoding

open BinaryFormula

@[simp] theorem bitsValue_bits (n : Nat) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [bitsValue]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      simp only [bitsValue, ih]

def frame : List Bool → List Bool
  | [] => [false]
  | b :: bits => true :: b :: frame bits

@[simp] theorem parseFrame_encoded (bits trailing : List Bool) :
    parseFrame (frame bits ++ trailing) = some (bits, trailing) := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, parseFrame, ih]

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp [frame, ih]; omega

def nameBits (name : Nat) : List Bool := frame name.bits

@[simp] theorem parseName_encoded (name : Nat) (rest : List Bool) :
    parseName (nameBits name ++ rest) = some (name, rest) := by
  simp [parseName, nameBits]

@[simp] theorem nameBits_length (name : Nat) :
    (nameBits name).length = 2 * name.size + 1 := by
  simp [nameBits, Nat.size_eq_bits_len]

def literalBits (literal : Literal) : List Bool :=
  literal.positive :: nameBits literal.name

@[simp] theorem parseLiteral_encoded (literal : Literal) (rest : List Bool) :
    parseLiteral (literalBits literal ++ rest) = some (literal, rest) := by
  cases literal with
  | mk name sign => simp [literalBits, parseLiteral]

@[simp] theorem literalBits_length (literal : Literal) :
    (literalBits literal).length = 2 * literal.name.size + 2 := by
  simp [literalBits]

def clauseBits (clause : Clause) : List Bool :=
  literalBits clause[0] ++ literalBits clause[1] ++ literalBits clause[2]

theorem clause_three_entries (clause : Clause) : #v[clause[0], clause[1], clause[2]] = clause := by
  apply Vector.ext
  intro i hi
  have cases_i : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases cases_i with rfl | rfl | rfl <;> rfl

@[simp] theorem parseClause_encoded (clause : Clause) (rest : List Bool) :
    parseClause (clauseBits clause ++ rest) = some (clause, rest) := by
  simp [clauseBits, List.append_assoc, parseClause, clause_three_entries]

def clauseNameSize (clause : Clause) : Nat :=
  ((clauseNames clause).map Nat.size).sum

@[simp] theorem clauseBits_length (clause : Clause) :
    (clauseBits clause).length = 2 * clauseNameSize clause + 6 := by
  simp [clauseBits, clauseNameSize, clauseNames]
  omega

def clausesBits : List Clause → List Bool
  | [] => [false]
  | clause :: clauses => true :: (clauseBits clause ++ clausesBits clauses)

def formulaBits (formula : Formula) : List Bool := clausesBits formula.clauses

def namesBitSize (clauses : List Clause) : Nat :=
  ((clauses.flatMap clauseNames).map Nat.size).sum

@[simp] theorem namesBitSize_nil : namesBitSize [] = 0 := rfl

@[simp] theorem namesBitSize_cons (clause : Clause) (clauses : List Clause) :
    namesBitSize (clause :: clauses) = clauseNameSize clause + namesBitSize clauses := by
  simp [namesBitSize, clauseNameSize]

theorem clausesBits_length (clauses : List Clause) :
    (clausesBits clauses).length = 7 * clauses.length + 2 * namesBitSize clauses + 1 := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [clausesBits, List.length_cons, List.length_append, clauseBits_length,
        namesBitSize_cons, ih]
      omega

theorem formulaBits_length (formula : Formula) :
    (formulaBits formula).length =
      7 * formula.clauses.length + 2 * namesBitSize formula.clauses + 1 :=
  clausesBits_length formula.clauses

theorem clauses_length_lt_bits (clauses : List Clause) :
    clauses.length < (clausesBits clauses).length := by
  rw [clausesBits_length]
  omega

@[simp] theorem parseClauses_encoded (clauses : List Clause) (rest : List Bool)
    (fuel : Nat) (enough : clauses.length < fuel) :
    parseClauses fuel (clausesBits clauses ++ rest) = some (clauses, rest) := by
  induction clauses generalizing fuel with
  | nil =>
      cases fuel with
      | zero => omega
      | succ fuel => simp [clausesBits, parseClauses]
  | cons clause clauses ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          have hrest : clauses.length < fuel := by simp only [List.length_cons] at enough; omega
          simp [clausesBits, parseClauses, List.append_assoc, ih fuel hrest]

@[simp] theorem decodeFormula_encoded (formula : Formula) :
    decodeFormula (formulaBits formula) = some formula := by
  cases formula with
  | mk clauses =>
      have hlen := clauses_length_lt_bits clauses
      have parsed := parseClauses_encoded clauses [] ((clausesBits clauses).length + 1) (by omega)
      simp only [List.append_nil] at parsed
      simp [formulaBits, decodeFormula, parsed]

end PerfectCompleteness.BinaryEncoding

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryHeaderMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryHeaderMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Alphabet {K : Type} (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool

section Placement

variable {K Λ A : Type} [DecidableEq K]

def delimiter (destination : K) (next : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push destination (fun _ => false)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

def tapes (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update base variableTape variableCounter)
    clauses clauseCounter) destination output

@[simp] theorem tapes_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output variableTape =
      variableCounter := by
  simp [tapes, vc, vd]

@[simp] theorem tapes_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output clauses =
      clauseCounter := by
  simp [tapes, cd]

@[simp] theorem tapes_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output : List Bool) :
    tapes variableTape clauses destination base variableCounter clauseCounter output destination =
      output := by
  simp [tapes]

theorem update_variables (variableTape clauses destination : K)
    (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      variableTape replacement = tapes variableTape clauses destination base replacement clauseCounter output := by
  funext k
  by_cases hv : k = variableTape
  · subst k
    simp [tapes, vc, vd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hv]
    · by_cases hc : k = clauses
      · subst k
        simp [tapes, hv, hd]
      · simp [tapes, hv, hc, hd]

theorem update_clauses (variableTape clauses destination : K)
    (cd : clauses ≠ destination) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      clauses replacement = tapes variableTape clauses destination base variableCounter replacement output := by
  funext k
  by_cases hc : k = clauses
  · subst k
    simp [tapes, cd]
  · by_cases hd : k = destination
    · subst k
      simp [tapes, hc]
    · simp [tapes, hc, hd]

theorem update_destination (variableTape clauses destination : K) (base : K → List Bool)
    (variableCounter clauseCounter output replacement : List Bool) :
    Function.update (tapes variableTape clauses destination base variableCounter clauseCounter output)
      destination replacement = tapes variableTape clauses destination base variableCounter clauseCounter replacement := by
  simp [tapes]

variable (variableTape clauses destination : K)
variable (vc : variableTape ≠ clauses) (vd : variableTape ≠ destination) (cd : clauses ≠ destination)
variable (clauseStart clauseLoop variableStart variableLoop : Λ) (exit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atClauseStart : program clauseStart = delimiter destination clauseLoop)
variable (atClauseLoop : program clauseLoop =
  loopAt clauses destination id false clauseLoop (some variableStart))
variable (atVariableStart : program variableStart = delimiter destination variableLoop)
variable (atVariableLoop : program variableLoop =
  loopAt variableTape destination id false variableLoop exit)
variable (base : K → List Bool) (ambient : A)

include atClauseStart in
theorem clauseDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some clauseLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program clauseStart) _ _) = _
  rw [atClauseStart]
  simp [delimiter, TM2.stepAux, update_destination]

include atVariableStart in
theorem variableDelimiterStep (variableCounter clauseCounter output : List Bool)
    (register : Option Bool) :
    TM2.step program
      ⟨some variableStart, (ambient, register),
        tapes variableTape clauses destination base variableCounter clauseCounter output⟩ =
      some ⟨some variableLoop, (ambient, none),
        tapes variableTape clauses destination base variableCounter clauseCounter (false :: output)⟩ := by
  change some (TM2.stepAux (program variableStart) _ _) = _
  rw [atVariableStart]
  simp [delimiter, TM2.stepAux, update_destination]

include cd atClauseLoop in
theorem clauseCounterTrace (m : Nat) (variableCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[m + 1]
      (some ⟨some clauseLoop, (ambient, register),
        tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) =
      some ⟨some variableStart, (ambient, none),
        tapes variableTape clauses destination base variableCounter [] (List.replicate m true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) clauses destination cd id false
    clauseLoop (some variableStart) program atClauseLoop
    (tapes variableTape clauses destination base variableCounter (List.replicate m true) output)
    ambient register
  change (nextAt destination program)^[m + 1]
    (some ⟨some clauseLoop, (ambient, register),
      tapes variableTape clauses destination base variableCounter (List.replicate m true) output⟩) = _
  simpa only [tapes_clauses variableTape clauses destination cd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_clauses variableTape clauses destination cd, update_destination,
    nextAt, advance] using h

include vc vd atVariableLoop in
theorem variableCounterTrace (n : Nat) (clauseCounter output : List Bool)
    (register : Option Bool) :
    (advance (TM2.step program))^[n + 1]
      (some ⟨some variableLoop, (ambient, register),
        tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] clauseCounter (List.replicate n true ++ output)⟩ := by
  have h := transferAt_fromTapes (Γ := Alphabet) variableTape destination vd id false
    variableLoop exit program atVariableLoop
    (tapes variableTape clauses destination base (List.replicate n true) clauseCounter output)
    ambient register
  change (nextAt destination program)^[n + 1]
    (some ⟨some variableLoop, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) clauseCounter output⟩) = _
  simpa only [tapes_variables variableTape clauses destination vc vd, tapes_destination,
    List.length_replicate, List.reverse_replicate, List.map_id_fun, id_eq,
    tapesAt, update_variables variableTape clauses destination vc vd, update_destination,
    nextAt, advance] using h

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

include vc vd cd atClauseStart atClauseLoop atVariableStart atVariableLoop

theorem headerTrace (n m : Nat) (body : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[n + m + 4]
      (some ⟨some clauseStart, (ambient, register),
        tapes variableTape clauses destination base
          (List.replicate n true) (List.replicate m true) body⟩) =
      some ⟨exit, (ambient, none),
        tapes variableTape clauses destination base [] [] (encodeWord n ++ encodeWord m ++ body)⟩ := by
  have first := clauseDelimiterStep variableTape clauses destination clauseStart clauseLoop program
    atClauseStart base ambient (List.replicate n true) (List.replicate m true) body register
  change (advance (TM2.step program))^[1]
    (some ⟨some clauseStart, (ambient, register),
      tapes variableTape clauses destination base (List.replicate n true) (List.replicate m true) body⟩) = _ at first
  have second := clauseCounterTrace variableTape clauses destination cd clauseLoop variableStart program
    atClauseLoop base ambient m (List.replicate n true) (false :: body) none
  have third := variableDelimiterStep variableTape clauses destination variableStart variableLoop program
    atVariableStart base ambient (List.replicate n true) []
    (List.replicate m true ++ false :: body) none
  change (advance (TM2.step program))^[1]
    (some ⟨some variableStart, (ambient, none),
      tapes variableTape clauses destination base (List.replicate n true) []
        (List.replicate m true ++ false :: body)⟩) = _ at third
  have fourth := variableCounterTrace variableTape clauses destination vc vd variableLoop exit program
    atVariableLoop base ambient n [] (false :: (List.replicate m true ++ false :: body)) none
  have full := joinTrace (joinTrace (joinTrace first second) third) fourth
  have htime : ((1 + (m + 1)) + 1) + (n + 1) = n + m + 4 := by omega
  rw [htime] at full
  simpa only [encodeWord, List.append_assoc, List.singleton_append,
    List.cons_append, List.nil_append] using full

end Placement

end PerfectCompleteness.BinaryHeaderMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# A destructive equality test on two actual Bool stacks

Each loop transition pops both stacks and compares only the two finite head
registers. A sticky mismatch flag makes the loop continue after disagreement.
The final empty/empty test selects an equal or different continuation and resets
all comparison registers. The ambient state and every other tape are preserved.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineCompare

open Turing
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (K : Type) : K → Type := fun _ => Bool
abbrev State (σ : Type) := σ × Bool × Option Bool × Option Bool

/-- An optional continuation, without reading or writing any tape. -/
def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

/-- Clear both head registers and the mismatch flag after choosing the exit. -/
def finish (exit : Option Λ) : TM2.Stmt (Alphabet K) Λ (State σ) :=
  .load (fun state => (state.1, false, none, none)) (exitAt exit)

/-- The only comparison performed by the program is on two `Option Bool` heads.
In particular, no statement is given a whole-list equality oracle. -/
def loop (left right : K) (loopLabel : Λ) (equalExit differentExit : Option Λ) :
    TM2.Stmt (Alphabet K) Λ (State σ) :=
  .pop left (fun state head => (state.1, state.2.1, head, state.2.2.2))
    (.pop right (fun state head => (state.1, state.2.1, state.2.2.1, head))
      (.branch (fun state => state.2.2.1.isNone && state.2.2.2.isNone)
        (.branch (fun state => state.2.1) (finish differentExit) (finish equalExit))
        (.load (fun state =>
          (state.1, state.2.1 || decide (state.2.2.1 ≠ state.2.2.2), none, none))
          (.goto fun _ => loopLabel))))

/-- Specification-only outcome, also recording an earlier mismatch. -/
def mismatch (flag : Bool) (leftWord rightWord : List Bool) : Bool :=
  flag || decide (leftWord ≠ rightWord)

@[simp] theorem mismatch_nil_nil (flag : Bool) : mismatch flag [] [] = flag := by
  simp [mismatch]

@[simp] theorem mismatch_nil_cons (flag head : Bool) (tail : List Bool) :
    mismatch flag [] (head :: tail) = true := by simp [mismatch]

@[simp] theorem mismatch_cons_nil (flag head : Bool) (tail : List Bool) :
    mismatch flag (head :: tail) [] = true := by simp [mismatch]

@[simp] theorem mismatch_true (leftWord rightWord : List Bool) :
    mismatch true leftWord rightWord = true := by simp [mismatch]

theorem mismatch_cons (flag leftHead rightHead : Bool) (leftTail rightTail : List Bool) :
    mismatch (flag || decide (leftHead ≠ rightHead)) leftTail rightTail =
      mismatch flag (leftHead :: leftTail) (rightHead :: rightTail) := by
  cases flag <;> cases leftHead <;> cases rightHead <;> simp [mismatch]

@[simp] theorem stepAux_exitAt (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (exitAt exit) state tapes = ⟨exit, state, tapes⟩ := by
  cases exit <;> rfl

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State σ)
    (tapes : K → List Bool) :
    TM2.stepAux (finish exit) state tapes =
      ⟨exit, (state.1, false, none, none), tapes⟩ := by
  simp [finish, TM2.stepAux]

theorem update_left (left right : K) (distinct : left ≠ right)
    (base : K → List Bool) (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) left replacement =
      tapesAt left right base replacement rightWord := by
  funext k
  by_cases hl : k = left
  · subst k
    simp [tapesAt, distinct]
  · by_cases hr : k = right
    · subst k
      simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hl, hr]

theorem update_right (left right : K) (base : K → List Bool)
    (leftWord rightWord replacement : List Bool) :
    Function.update (tapesAt left right base leftWord rightWord) right replacement =
      tapesAt left right base leftWord replacement := by
  simp [tapesAt]

theorem step_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] []⟩ =
      some ⟨if flag then differentExit else equalExit, (ambient, false, none, none),
        tapesAt left right base [] []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] [])) = _
  rw [atLoop]
  cases flag <;>
    simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_nil_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base [] tail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base [] (head :: tail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_nil (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (head : Bool) (tail : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (head :: tail) []⟩ =
      some ⟨some loopLabel, (ambient, true, none, none), tapesAt left right base tail []⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (head :: tail) [])) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem step_cons_cons (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftHead rightHead : Bool) (leftTail rightTail : List Bool)
    (ambient : σ) (flag : Bool) (leftRegister rightRegister : Option Bool) :
    TM2.step program
      ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail)⟩ =
      some ⟨some loopLabel,
        (ambient, flag || decide (leftHead ≠ rightHead), none, none),
        tapesAt left right base leftTail rightTail⟩ := by
  change some (TM2.stepAux (program loopLabel) (ambient, flag, leftRegister, rightRegister)
    (tapesAt left right base (leftHead :: leftTail) (rightHead :: rightTail))) = _
  rw [atLoop]
  simp [loop, TM2.stepAux, distinct, update_left, update_right]

theorem trace_left_empty (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] rightWord⟩) =
      some ⟨if mismatch flag [] rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction rightWord generalizing flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
      MachineComposition.advance_some, mismatch_nil_nil] using
      step_empty left right distinct loopLabel equalExit differentExit program atLoop base
        ambient flag leftRegister rightRegister
  | cons head tail ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
      (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base [] (head :: tail)⟩) = _
    rw [step_nil_cons left right distinct loopLabel equalExit differentExit program atLoop]
    simpa only [mismatch_true, mismatch_nil_cons] using ih true none none

/-- The exact trace with a possibly pre-existing mismatch. Every input symbol
is consumed even when disagreement has already been detected. -/
theorem compareTrace_flag (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ) (flag : Bool)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if mismatch flag leftWord rightWord then differentExit else equalExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  induction leftWord generalizing rightWord flag leftRegister rightRegister with
  | nil =>
    simpa only [List.length_nil, Nat.zero_max] using
      trace_left_empty left right distinct loopLabel equalExit differentExit program atLoop
        base rightWord ambient flag leftRegister rightRegister
  | cons head tail ih =>
    cases rightWord with
    | nil =>
      rw [List.length_cons, List.length_nil, Nat.max_zero, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[tail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) []⟩) = _
      rw [step_cons_nil left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [List.length_nil, Nat.max_zero, mismatch_true, mismatch_cons_nil] using
        ih [] true none none
    | cons rightHead rightTail =>
      rw [List.length_cons, List.length_cons, Nat.succ_max_succ, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[max tail.length rightTail.length + 1]
        (TM2.step program ⟨some loopLabel, (ambient, flag, leftRegister, rightRegister),
          tapesAt left right base (head :: tail) (rightHead :: rightTail)⟩) = _
      rw [step_cons_cons left right distinct loopLabel equalExit differentExit program atLoop]
      simpa only [mismatch_cons] using
        ih rightTail (flag || decide (head ≠ rightHead)) none none

/-- With a clear initial flag, the final continuation tests equality of the
two complete original words. Both tapes and all comparison registers are empty. -/
theorem compareTrace (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (leftWord rightWord : List Bool) (ambient : σ)
    (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max leftWord.length rightWord.length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister),
        tapesAt left right base leftWord rightWord⟩) =
      some ⟨if leftWord = rightWord then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  have h := compareTrace_flag left right distinct loopLabel equalExit differentExit program
    atLoop base leftWord rightWord ambient false leftRegister rightRegister
  by_cases heq : leftWord = rightWord <;> simpa [mismatch, heq] using h

theorem compareTrace_fromTapes (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[max (base left).length (base right).length + 1]
      (some ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩) =
      some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩ := by
  simpa only [tapesAt_self] using
    compareTrace left right distinct loopLabel equalExit differentExit program atLoop base
      (base left) (base right) ambient leftRegister rightRegister

/-- An actual timed execution witness, with the exact stored transition count. -/
def compareInTime (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some loopLabel, (ambient, false, leftRegister, rightRegister), base⟩
      (some ⟨if base left = base right then equalExit else differentExit,
        (ambient, false, none, none), tapesAt left right base [] []⟩)
      (max (base left).length (base right).length + 1) where
  steps := max (base left).length (base right).length + 1
  evals_in_steps := compareTrace_fromTapes left right distinct loopLabel equalExit differentExit
    program atLoop base ambient leftRegister rightRegister
  steps_le_m := Nat.le_refl _

@[simp] theorem compareInTime_steps (left right : K) (distinct : left ≠ right)
    (loopLabel : Λ) (equalExit differentExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet K) Λ (State σ))
    (atLoop : program loopLabel = loop left right loopLabel equalExit differentExit)
    (base : K → List Bool) (ambient : σ) (leftRegister rightRegister : Option Bool) :
    (compareInTime left right distinct loopLabel equalExit differentExit program atLoop base
      ambient leftRegister rightRegister).steps =
        max (base left).length (base right).length + 1 := rfl

end UniqueGamesTheorem.Foundations.Complexity.MachineCompare

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryNameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryNameMachine

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

def frame : List Bool → List Bool
  | [] => [false]
  | bit :: bits => true :: bit :: frame bits

def finalDigit : List Bool → Option Bool → Option Bool
  | [], previous => previous
  | bit :: bits, _ => finalDigit bits (some bit)

def canonical (bits : List Bool) : Bool := (finalDigit bits none).getD true

structure Result where
  accepted : Bool
  remaining : List Bool
  reversedPayload : List Bool
  deriving DecidableEq

def scanSpec : List Bool → List Bool → Option Bool → Result
  | [], acc, _ => ⟨false, [], acc⟩
  | false :: rest, acc, last => ⟨last.getD true, rest, acc⟩
  | [true], acc, _ => ⟨false, [], acc⟩
  | true :: bit :: rest, acc, _ => scanSpec rest (bit :: acc) (some bit)

def steps : List Bool → Nat
  | true :: _ :: rest => steps rest + 1
  | _ => 1

@[simp] theorem frame_length (bits : List Bool) :
    (frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => simp [frame]
  | cons bit bits ih => simp only [frame, List.length_cons, ih]; omega

theorem scanSpec_frame (bits suffix acc : List Bool) (last : Option Bool) :
    scanSpec (frame bits ++ suffix) acc last =
      ⟨(finalDigit bits last).getD true, suffix, bits.reverse ++ acc⟩ := by
  induction bits generalizing acc last with
  | nil => simp [frame, scanSpec, finalDigit]
  | cons bit bits ih =>
      simpa [frame, scanSpec, finalDigit, List.reverse_cons, List.append_assoc] using
        ih (bit :: acc) (some bit)

@[simp] theorem steps_frame (bits suffix : List Bool) :
    steps (frame bits ++ suffix) = bits.length + 1 := by
  induction bits with
  | nil => simp [frame, steps]
  | cons bit bits ih => simp [frame, steps, ih]

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := A × Option Bool × Option Bool

def clean (ambient : A) : State A := (ambient, none, none)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1) (exitAt exit)

def scan (source destination : K) (again : Λ) (accepted rejected : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .pop source (fun state head => (state.1, state.2.1, head))
    (.branch (fun state => state.2.2.isNone)
      (finish rejected)
      (.branch (fun state => state.2.2.getD false)
        (.pop source (fun state head => (state.1, state.2.1, head))
          (.branch (fun state => state.2.2.isSome)
            (.push destination (fun state => state.2.2.getD false)
              (.load (fun state => (state.1, state.2.2, none))
                (.goto fun _ => again)))
            (finish rejected)))
        (.branch (fun state => state.2.1.getD true)
          (finish accepted) (finish rejected))))

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A)
    (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1, base⟩ := by
  cases exit <;> rfl

theorem update_source (source destination : K) (distinct : source ≠ destination)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) source replacement =
      tapesAt source destination base replacement output := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hd : k = destination
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hd]

theorem update_destination (source destination : K)
    (base : K → List Bool) (input output replacement : List Bool) :
    Function.update (tapesAt source destination base input output) destination replacement =
      tapesAt source destination base input replacement := by
  simp [tapesAt]

variable (source destination : K) (distinct : source ≠ destination)
variable (again : Λ) (accepted rejected : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atScan : program again = scan source destination again accepted rejected)
variable (base : K → List Bool) (ambient : A)

include distinct atScan

theorem step_empty (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_end (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (false :: rest) output⟩ =
      some ⟨if last.getD true then accepted else rejected, clean ambient,
        tapesAt source destination base rest output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  cases h : last.getD true <;>
    simp [scan, TM2.stepAux, distinct, update_source, h]

theorem step_truncated (output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register), tapesAt source destination base [true] output⟩ =
      some ⟨rejected, clean ambient, tapesAt source destination base [] output⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source]

theorem step_digit (bit : Bool) (rest output : List Bool) (last register : Option Bool) :
    TM2.step program
      ⟨some again, (ambient, last, register),
        tapesAt source destination base (true :: bit :: rest) output⟩ =
      some ⟨some again, (ambient, some bit, none),
        tapesAt source destination base rest (bit :: output)⟩ := by
  change some (TM2.stepAux (program again) _ _) = _
  rw [atScan]
  simp [scan, TM2.stepAux, distinct, update_source, update_destination]

theorem scanTrace (input output : List Bool) (last register : Option Bool) :
    (advance (TM2.step program))^[steps input]
      (some ⟨some again, (ambient, last, register),
        tapesAt source destination base input output⟩) =
      some ⟨if (scanSpec input output last).accepted then accepted else rejected,
        clean ambient, tapesAt source destination base
          (scanSpec input output last).remaining (scanSpec input output last).reversedPayload⟩ := by
  induction input using List.twoStepInduction generalizing output last register with
  | nil =>
      simpa only [steps, scanSpec, Bool.false_eq_true, ite_false, if_false,
        Function.iterate_one, advance_some] using
        step_empty source destination distinct again accepted rejected program atScan base ambient
          output last register
  | singleton flag =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient [] output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · simpa only [steps, scanSpec, Bool.false_eq_true, ite_false, if_false,
          Function.iterate_one, advance_some] using
          step_truncated source destination distinct again accepted rejected program atScan base ambient
            output last register
  | cons_cons flag bit rest ih _ =>
      cases flag
      · have h := step_end source destination distinct again accepted rejected program atScan
          base ambient (bit :: rest) output last register
        cases hlast : last.getD true <;>
          simpa [steps, scanSpec, hlast] using h
      · rw [steps, Function.iterate_succ_apply]
        simp only [advance_some]
        rw [step_digit source destination distinct again accepted rejected program atScan]
        exact ih (bit :: output) (some bit) none

theorem framedTrace (bits suffix output : List Bool) (register : Option Bool) :
    (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some again, (ambient, none, register),
        tapesAt source destination base (frame bits ++ suffix) output⟩) =
      some ⟨if canonical bits then accepted else rejected, clean ambient,
        tapesAt source destination base suffix (bits.reverse ++ output)⟩ := by
  have h := scanTrace source destination distinct again accepted rejected program atScan
    base ambient (frame bits ++ suffix) output none register
  cases hlast : (finalDigit bits none).getD true <;>
    simpa [steps_frame, scanSpec_frame, canonical, hlast] using h

end Program

end PerfectCompleteness.BinaryNameMachine

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryNameCompare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryNameCompare


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := (A × Bool × Option Bool) × Option Bool

def clean (ambient : A) : State A := ((ambient, false, none), none)

def scanStateEquiv (A : Type) : BinaryNameMachine.State (A × Bool) ≃ State A where
  toFun s := ((s.1.1, s.1.2, s.2.1), s.2.2)
  invFun s := ((s.1.1, s.1.2.1), s.1.2.2, s.2)
  left_inv := by rintro ⟨⟨a, b⟩, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

inductive Label
  | scan | copyOut | copyBack | compare
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .copyOut, .copyBack, .compare]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

def instruction (tape : Fin 5 → K) (labels : Label → Λ)
    (equalExit differentExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .scan => MachineStateEquiv.statement (scanStateEquiv A)
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
        (some (labels .copyOut)) malformedExit)
  | .copyOut => UniqueGamesTheorem.Reduction.MachineTransfer.loopAt (tape 1) (tape 4) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 4) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels .compare))
  | .compare => MachineStateEquiv.statement (compareStateEquiv A)
      (MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit)

def steps (payloadLength keyLength : Nat) : Nat :=
  (payloadLength + 1) + 2 * (keyLength + 1) + (max payloadLength keyLength + 1)

theorem steps_le (payloadLength keyLength : Nat) :
    steps payloadLength keyLength ≤ 2 * payloadLength + 3 * keyLength + 4 := by
  unfold steps
  omega

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem compareTrace (tape : Fin 5 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (equalExit differentExit malformedExit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) =
      instruction tape labels equalExit differentExit malformedExit l)
    (base : K → List Bool) (bits suffix key : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (sourceWord : base (tape 0) = BinaryNameMachine.frame bits ++ suffix)
    (keyWord : base (tape 1) = key)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) (ambient : A) :
    (advance (TM2.step program))^[steps bits.length key.length]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, Function.update base (tape 0) suffix⟩ := by
  have hd (i j : Fin 5) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let finalBase := Function.update base (tape 0) suffix
  let afterScan := Function.update finalBase (tape 2) bits.reverse
  let afterCopy := Function.update afterScan (tape 3) key
  have scanRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scan), clean ambient, base⟩) =
      some ⟨some (labels .copyOut), clean ambient, afterScan⟩ := by
    let back := MachineStateEquiv.program (scanStateEquiv A).symm program
    have atScan : back (labels .scan) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scan)
          (some (labels .copyOut)) malformedExit := by
      change MachineStateEquiv.statement (scanStateEquiv A).symm
        (program (labels .scan)) = _
      rw [atLabels .scan]
      exact MachineStateEquiv.statement_symm_statement (scanStateEquiv A) _
    have backForward : MachineStateEquiv.program (scanStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (scanStateEquiv A)
        (MachineStateEquiv.statement (scanStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (scanStateEquiv A).symm (program l)
    have initialTapes : UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt (tape 0) (tape 2)
        base (BinaryNameMachine.frame bits ++ suffix) [] = base := by
      rw [← sourceWord, ← candidateEmpty]
      exact UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scan) (some (labels .copyOut)) malformedExit back atScan base (ambient, false)
      bits suffix [] none
    simp only [canonical, ↓reduceIte, initialTapes, List.append_nil] at native
    have transported := MachineStateEquiv.trace (scanStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, scanStateEquiv, Equiv.coe_fn_mk, BinaryNameMachine.clean,
      clean, afterScan, finalBase, UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt] using transported
  have afterScanKey : afterScan (tape 1) = key := by
    simpa [afterScan, finalBase, hd 1 2 (by decide), hd 1 0 (by decide)] using keyWord
  have afterScanCopy : afterScan (tape 3) = [] := by
    simpa [afterScan, finalBase, hd 3 2 (by decide), hd 3 0 (by decide)] using copyEmpty
  have afterScanScratch : afterScan (tape 4) = [] := by
    simpa [afterScan, finalBase, hd 4 2 (by decide), hd 4 0 (by decide)] using scratchEmpty
  have copyRun : (advance (TM2.step program))^[2 * (key.length + 1)]
      (some ⟨some (labels .copyOut), clean ambient, afterScan⟩) =
      some ⟨some (labels .compare), clean ambient, afterCopy⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 4)
      (hd 1 3 (by decide)) (hd 1 4 (by decide)) (hd 3 4 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels .compare)) program
      (atLabels .copyOut) (atLabels .copyBack) afterScan afterScanScratch
      (ambient, false, none) none
    simpa only [afterScanKey, afterScanCopy, List.append_nil, clean, afterCopy] using h
  have candidateWord : afterCopy (tape 2) = bits.reverse := by
    simp [afterCopy, afterScan, hd 2 3 (by decide)]
  have copiedWord : afterCopy (tape 3) = key := by simp [afterCopy]
  have restored : UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt (tape 2) (tape 3)
      afterCopy [] [] = finalBase := by
    funext k
    by_cases hc : k = tape 2
    · subst k
      simp [UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
        hd 2 3 (by decide), hd 2 0 (by decide), candidateEmpty]
    · by_cases hk : k = tape 3
      · subst k
        simp [UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, finalBase,
          hd 3 0 (by decide), copyEmpty]
      · simp [UniqueGamesTheorem.Reduction.MachineTransfer.tapesAt, afterCopy, afterScan, hc, hk]
  have comparisonRun : (advance (TM2.step program))^[max bits.length key.length + 1]
      (some ⟨some (labels .compare), clean ambient, afterCopy⟩) =
      some ⟨if bits.reverse = key then equalExit else differentExit,
        clean ambient, finalBase⟩ := by
    let back := MachineStateEquiv.program (compareStateEquiv A).symm program
    have atCompare : back (labels .compare) =
        MachineCompare.loop (tape 2) (tape 3) (labels .compare) equalExit differentExit := by
      change MachineStateEquiv.statement (compareStateEquiv A).symm
        (program (labels .compare)) = _
      rw [atLabels .compare]
      exact MachineStateEquiv.statement_symm_statement (compareStateEquiv A) _
    have backForward : MachineStateEquiv.program (compareStateEquiv A) back = program := by
      funext l
      change MachineStateEquiv.statement (compareStateEquiv A)
        (MachineStateEquiv.statement (compareStateEquiv A).symm (program l)) = _
      simpa only [Equiv.symm_symm] using
        MachineStateEquiv.statement_symm_statement (compareStateEquiv A).symm (program l)
    have native := MachineCompare.compareTrace_fromTapes (tape 2) (tape 3)
      (hd 2 3 (by decide)) (labels .compare) equalExit differentExit back atCompare afterCopy
      ambient none none
    rw [candidateWord, copiedWord, restored, List.length_reverse] at native
    have transported := MachineStateEquiv.trace (compareStateEquiv A) back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, compareStateEquiv, Equiv.coe_fn_mk, clean] using transported
  exact joinTrace (joinTrace scanRun copyRun) comparisonRun

end PerfectCompleteness.BinaryNameCompare

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryNameSearch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryNameSearch

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Token := Bool × List Bool

def tokenBits (token : Token) : List Bool :=
  token.1 :: BinaryNameMachine.frame token.2

def stream : List Token → List Bool
  | [] => []
  | token :: tokens => tokenBits token ++ stream tokens

def payloads (tokens : List Token) : List (List Bool) := tokens.map Prod.snd

def afterMatch : List Token → List Bool → List Token
  | [], _ => []
  | token :: tokens, key => if token.2 = key then tokens else afterMatch tokens key

def steps : List Token → List Bool → Nat
  | [], _ => 0
  | token :: tokens, key =>
      1 + BinaryNameCompare.steps token.2.length key.length +
        if token.2 = key then 0 else 1 + steps tokens key

def payloadSize (tokens : List Token) : Nat := (payloads tokens |>.map List.length).sum

@[simp] theorem stream_nil : stream [] = [] := rfl

@[simp] theorem stream_cons (token : Token) (tokens : List Token) :
    stream (token :: tokens) = tokenBits token ++ stream tokens := rfl

@[simp] theorem payloads_nil : payloads [] = [] := rfl

@[simp] theorem payloads_cons (token : Token) (tokens : List Token) :
    payloads (token :: tokens) = token.2 :: payloads tokens := rfl

@[simp] theorem payloadSize_nil : payloadSize [] = 0 := rfl

@[simp] theorem payloadSize_cons (token : Token) (tokens : List Token) :
    payloadSize (token :: tokens) = token.2.length + payloadSize tokens := rfl

@[simp] theorem stream_length (tokens : List Token) :
    (stream tokens).length = 2 * payloadSize tokens + 2 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      simp only [stream_cons, List.length_append, tokenBits, List.length_cons,
        BinaryNameMachine.frame_length, ih, payloadSize_cons]
      omega

theorem steps_le (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ 2 * payloadSize tokens + (3 * key.length + 6) * tokens.length := by
  induction tokens with
  | nil => simp [steps]
  | cons token tokens ih =>
      have h := BinaryNameCompare.steps_le token.2.length key.length
      simp only [steps, payloadSize_cons, List.length_cons]
      split <;> nlinarith

theorem steps_le_stream (tokens : List Token) (key : List Bool) :
    steps tokens key ≤ (3 * key.length + 7) * (stream tokens).length := by
  have h := steps_le tokens key
  rw [stream_length]
  nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State A

abbrev clean (ambient : A) : State A := BinaryNameCompare.clean ambient

inductive Label
  | sign
  | comparison (label : BinaryNameCompare.Label)
  | increment
  deriving DecidableEq, Fintype

def compareTapes (tape : Fin 6 → K) : Fin 5 → K := fun i => tape i.castSucc

omit [DecidableEq K] in
theorem compareTapes_injective (tape : Fin 6 → K) (distinct : Function.Injective tape) :
    Function.Injective (compareTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 6 => i.val) (distinct h)

def exitAt (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  match exit with
  | none => .halt
  | some label => .goto fun _ => label

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1) (exitAt exit)

def instruction (tape : Fin 6 → K) (labels : Label → Λ)
    (foundExit missingExit malformedExit : Option Λ) :
    Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .sign =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (finish (some (labels (.comparison .scan)))) (finish missingExit))
  | .comparison l => BinaryNameCompare.instruction (compareTapes tape)
      (fun l => labels (.comparison l)) foundExit (some (labels .increment)) malformedExit l
  | .increment => .push (tape 5) (fun _ => true) (.goto fun _ => labels .sign)

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1, base⟩ := by
  cases exit <;> rfl

theorem update_source (source counter : K) (distinct : source ≠ counter)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) source replacement =
      tapesAt source counter base replacement count := by
  funext k
  by_cases hs : k = source
  · subst k; simp [tapesAt, distinct]
  · by_cases hc : k = counter
    · subst k; simp [tapesAt, Ne.symm distinct]
    · simp [tapesAt, hs, hc]

theorem update_counter (source counter : K)
    (base : K → List Bool) (input count replacement : List Bool) :
    Function.update (tapesAt source counter base input count) counter replacement =
      tapesAt source counter base input replacement := by
  simp [tapesAt]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 6 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (foundExit missingExit malformedExit : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) =
  instruction tape labels foundExit missingExit malformedExit l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem signStep (sign : Bool) (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (sign :: input) counter⟩ =
      some ⟨some (labels (.comparison .scan)), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ := by
  have hd : tape 0 ≠ tape 5 := fun h => (by decide : (0 : Fin 6) ≠ 5) (distinct h)
  change some (TM2.stepAux (program (labels .sign)) _ _) = _
  rw [atLabels .sign]
  simp [instruction, TM2.stepAux, clean, BinaryNameCompare.clean, hd, update_source]

omit distinct in
theorem incrementStep (input counter : List Bool) :
    TM2.step program
      ⟨some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base input counter⟩ =
      some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base input (true :: counter)⟩ := by
  change some (TM2.stepAux (program (labels .increment)) _ _) = _
  rw [atLabels .increment]
  simp [instruction, TM2.stepAux, update_counter]

theorem tokenTrace (token : Token) (key suffix counter : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[1 + BinaryNameCompare.steps token.2.length key.length]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨if token.2 = key then foundExit else some (labels .increment), clean ambient,
        tapesAt (tape 0) (tape 5) base suffix counter⟩ := by
  have hd (i j : Fin 6) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := tapesAt (tape 0) (tape 5) base
    (BinaryNameMachine.frame token.2 ++ suffix) counter
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (tokenBits token ++ suffix) counter⟩) =
      some ⟨some (labels (.comparison .scan)), clean ambient, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, tokenBits, List.cons_append] using
      signStep tape distinct labels foundExit missingExit malformedExit program atLabels
        base ambient token.1 (BinaryNameMachine.frame token.2 ++ suffix) counter
  have second := BinaryNameCompare.compareTrace (compareTapes tape)
    (compareTapes_injective tape distinct) (fun l => labels (.comparison l))
    foundExit (some (labels .increment)) malformedExit program
    (fun l => atLabels (.comparison l)) initial token.2 suffix key.reverse canonical
    (by simp [initial, compareTapes, hd 0 5 (by decide)])
    (by simpa [initial, compareTapes, tapesAt,
      hd 1 0 (by decide), hd 1 5 (by decide)] using keyWord)
    (by simpa [initial, compareTapes, tapesAt, hd 2 0 (by decide), hd 2 5 (by decide)]
      using candidateEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 3 0 (by decide), hd 3 5 (by decide)] using copyEmpty)
    (by simpa [initial, compareTapes, tapesAt,
      hd 4 0 (by decide), hd 4 5 (by decide)] using scratchEmpty)
    ambient
  have heq : token.2.reverse = key.reverse ↔ token.2 = key := by
    constructor
    · intro h
      have := congrArg List.reverse h
      simpa only [List.reverse_reverse] using this
    · intro h; rw [h]
  simp only [List.length_reverse, heq] at second
  rw [show Function.update initial (compareTapes tape 0) suffix =
      tapesAt (tape 0) (tape 5) base suffix counter by
    exact update_source _ _ (hd 0 5 (by decide)) base _ counter suffix] at second
  exact joinTrace first second

theorem searchTrace (tokens : List Token) (key suffix counter : List Bool)
    (canonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : key ∈ payloads tokens)
    (keyWord : base (tape 1) = key.reverse)
    (candidateEmpty : base (tape 2) = []) (copyEmpty : base (tape 3) = [])
    (scratchEmpty : base (tape 4) = []) :
    (advance (TM2.step program))^[steps tokens key]
      (some ⟨some (labels .sign), clean ambient,
        tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
      some ⟨foundExit, clean ambient,
        tapesAt (tape 0) (tape 5) base (stream (afterMatch tokens key) ++ suffix)
          (List.replicate ((payloads tokens).idxOf key) true ++ counter)⟩ := by
  induction tokens generalizing counter with
  | nil => simp at present
  | cons token tokens ih =>
      have headCanonical := canonical token (by simp)
      have tailCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true :=
        fun t ht => canonical t (by simp [ht])
      have first := tokenTrace tape distinct labels foundExit missingExit malformedExit
        program atLabels base ambient token key (stream tokens ++ suffix) counter
        headCanonical keyWord candidateEmpty copyEmpty scratchEmpty
      by_cases same : token.2 = key
      · simpa only [steps, same, ite_true, if_true, Nat.add_zero, stream_cons,
          List.append_assoc, afterMatch, payloads_cons, List.idxOf_cons_self,
          List.replicate_zero, List.nil_append] using first
      · have remaining : key ∈ payloads tokens := by
          rcases List.mem_cons.mp present with equal | remaining
          · exact False.elim (same equal.symm)
          · exact remaining
        have increment : (advance (TM2.step program))^[1]
            (some ⟨some (labels .increment), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) counter⟩) =
            some ⟨some (labels .sign), clean ambient,
              tapesAt (tape 0) (tape 5) base (stream tokens ++ suffix) (true :: counter)⟩ := by
          simpa only [Function.iterate_one, advance_some] using
            incrementStep tape labels foundExit missingExit malformedExit program
              atLabels base ambient (stream tokens ++ suffix) counter
        have rest := ih (true :: counter) tailCanonical remaining
        simp only [same, ite_false, if_false] at first
        have full := joinTrace first (joinTrace increment rest)
        have counterEq : List.replicate ((payloads tokens).idxOf key) true ++
            (true :: counter) =
            List.replicate ((payloads tokens).idxOf key + 1) true ++ counter := by
          rw [List.replicate_succ']
          simp only [List.append_assoc, List.singleton_append]
        have indexEq : (token.2 :: payloads tokens).idxOf key =
            (payloads tokens).idxOf key + 1 := by
          simp only [List.idxOf_cons, beq_false_of_ne same, Bool.false_eq_true, ite_false, if_false, cond_false]
        simpa only [steps, same, ite_false, if_false, stream_cons, List.append_assoc, afterMatch,
          payloads_cons, indexEq, counterEq, cond_false] using full

end Program

end PerfectCompleteness.BinaryNameSearch

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_MachineDrain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Actual complete-stack cleanup, with an arbitrary continuation. Each symbol
costs one transition and the empty-stack branch costs one final transition. -/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineDrain

open Turing

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool

def drain (source : K) (again : Λ) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool) :=
  .pop source (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.goto fun _ => again)
      (.load (fun state => (state.1, none)) (Reduction.MachineTransfer.exitAt source exit)))

theorem drainTrace (source : K) (again : Λ) (exit : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (σ × Option Bool))
    (atDrain : program again = drain source again exit)
    (base : K → List Bool) (word : List Bool) (ambient : σ) (register : Option Bool) :
    (MachineComposition.advance (TM2.step program))^[word.length + 1]
      (some ⟨some again, (ambient, register), Function.update base source word⟩) =
      some ⟨exit, (ambient, none), Function.update base source []⟩ := by
  induction word generalizing register with
  | nil =>
      change some (TM2.stepAux (program again) (ambient, register)
        (Function.update base source [])) = _
      rw [atDrain]
      cases exit <;> simp [drain, TM2.stepAux, Reduction.MachineTransfer.exitAt]
  | cons symbol word ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      change (MachineComposition.advance (TM2.step program))^[word.length + 1]
        (some (TM2.stepAux (program again) (ambient, register)
          (Function.update base source (symbol :: word)))) = _
      rw [atDrain]
      simpa [drain, TM2.stepAux] using ih (some symbol)

end UniqueGamesTheorem.Foundations.Complexity.MachineDrain

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryLiteralMachine
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryLiteralMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryNameCompare.State (A × Bool)
abbrev clean (ambient : A) (sign : Bool := false) : State A :=
  BinaryNameCompare.clean (ambient, sign)

inductive Label
  | readSign | scanKey | copyOut | copyBack
  | search (label : BinaryNameSearch.Label)
  | drainSearch | drainKey | emitIndex | emitSign
  deriving DecidableEq, Fintype

def searchTapes (tape : Fin 9 → K) : Fin 6 → K
  | 0 => tape 3
  | 1 => tape 2
  | 2 => tape 4
  | 3 => tape 5
  | 4 => tape 6
  | 5 => tape 7

omit [DecidableEq K] in
theorem searchTapes_injective (tape : Fin 9 → K) (distinct : Function.Injective tape) :
    Function.Injective (searchTapes tape) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp only [searchTapes] at h
  all_goals first | rfl | have heq := congrArg Fin.val (distinct h); norm_num at heq

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def readSign (tape : Fin 9 → K) (next : Λ) (malformed : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .push (tape 7) (fun _ => false)
    (.pop (tape 0) (fun state head => (state.1, head))
      (.branch (fun state => state.2.isSome)
        (.load (fun state => clean state.1.1.1 (state.2.getD false)) (.goto fun _ => next))
        (finish malformed)))

def emitSign (output : K) (exit : Option Λ) :
    TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .branch (fun state => state.1.1.2)
    (.push output (fun _ => true) (.push output (fun _ => false) (finish exit)))
    (.push output (fun _ => false) (finish exit))

def instruction (tape : Fin 9 → K) (labels : Label → Λ)
    (exit malformed : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .readSign => readSign tape (labels .scanKey) malformed
  | .scanKey => MachineStateEquiv.statement (BinaryNameCompare.scanStateEquiv (A × Bool))
      (BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
        (some (labels .copyOut)) malformed)
  | .copyOut => loopAt (tape 1) (tape 6) id false
      (labels .copyOut) (some (labels .copyBack))
  | .copyBack => MachineCopy.forkLoop (tape 6) (tape 1) (tape 3) false
      (labels .copyBack) (some (labels (.search .sign)))
  | .search l => BinaryNameSearch.instruction (searchTapes tape)
      (fun l => labels (.search l)) (some (labels .drainSearch)) malformed malformed l
  | .drainSearch => MachineDrain.drain (tape 3) (labels .drainSearch)
      (some (labels .drainKey))
  | .drainKey => MachineDrain.drain (tape 2) (labels .drainKey)
      (some (labels .emitIndex))
  | .emitIndex => loopAt (tape 7) (tape 8) id false
      (labels .emitIndex) (some (labels .emitSign))
  | .emitSign => emitSign (tape 8) exit

def signWord (sign : Bool) : List Bool := encodeWord (if sign then 1 else 0)

def index (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  (BinaryNameSearch.payloads tokens).idxOf bits

def outputWord (tokens : List BinaryNameSearch.Token) (bits : List Bool) (sign : Bool) :
    List Bool := encodeWord (index tokens bits) ++ signWord sign

def steps (tokens : List BinaryNameSearch.Token) (bits : List Bool) : Nat :=
  1 + (bits.length + 1) + 2 * ((BinaryNameSearch.stream tokens).length + 1) +
    BinaryNameSearch.steps tokens bits +
    ((BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length + 1) +
    (bits.length + 1) + (index tokens bits + 2) + 1

theorem afterMatch_length_le (tokens : List BinaryNameSearch.Token) (bits : List Bool) :
    (BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)).length ≤
      (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp [BinaryNameSearch.afterMatch]
  | cons token tokens ih =>
      simp only [BinaryNameSearch.afterMatch, BinaryNameSearch.stream_cons, List.length_append]
      split <;> omega

theorem steps_le (tokens : List BinaryNameSearch.Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    steps tokens bits ≤
      3 * ((BinaryNameSearch.stream tokens).length + bits.length) ^ 2 +
        13 * ((BinaryNameSearch.stream tokens).length + bits.length) + 9 := by
  have search := BinaryNameSearch.steps_le_stream tokens bits
  have suffix := afterMatch_length_le tokens bits
  have idx : index tokens bits < tokens.length := by
    have h := List.idxOf_lt_length_iff.mpr present
    simpa [index, BinaryNameSearch.payloads] using h
  have count : tokens.length ≤ (BinaryNameSearch.stream tokens).length := by
    rw [BinaryNameSearch.stream_length]
    omega
  unfold steps
  nlinarith [Nat.zero_le ((BinaryNameSearch.stream tokens).length * bits.length)]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base = ⟨exit, clean state.1.1.1, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem literalTrace (tape : Fin 9 → K) (distinct : Function.Injective tape)
    (labels : Label → Λ) (exit malformed : Option Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction tape labels exit malformed l)
    (base : K → List Bool) (tokens : List BinaryNameSearch.Token)
    (sign : Bool) (bits suffix : List Bool)
    (canonical : BinaryNameMachine.canonical bits = true)
    (tokensCanonical : ∀ token ∈ tokens, BinaryNameMachine.canonical token.2 = true)
    (present : bits ∈ BinaryNameSearch.payloads tokens)
    (cursor : base (tape 0) = sign :: (BinaryNameMachine.frame bits ++ suffix))
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 9, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = [])
    (ambient : A) :
    (advance (TM2.step program))^[steps tokens bits]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨exit, clean ambient,
        Function.update (Function.update base (tape 0) suffix) (tape 8)
          ((outputWord tokens bits sign).reverse ++ base (tape 8))⟩ := by
  have hd (i j : Fin 9) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  have he (i : Fin 9) (hlo : 2 ≤ i.val := by decide) (hhi : i.val ≤ 7 := by decide) :
      base (tape i) = [] := empty i hlo hhi
  let s₁ := Function.update (Function.update base (tape 7) [false]) (tape 0)
    (BinaryNameMachine.frame bits ++ suffix)
  let s₂ := Function.update (Function.update s₁ (tape 0) suffix) (tape 2) bits.reverse
  let s₃ := Function.update s₂ (tape 3) (BinaryNameSearch.stream tokens)
  let tail := BinaryNameSearch.stream (BinaryNameSearch.afterMatch tokens bits)
  let s₄ := tapesAt (tape 3) (tape 7) s₃ tail (encodeWord (index tokens bits))
  let s₅ := Function.update s₄ (tape 3) []
  let s₆ := Function.update s₅ (tape 2) []
  let s₇ := tapesAt (tape 7) (tape 8) s₆ []
    ((encodeWord (index tokens bits)).reverse ++ s₆ (tape 8))
  let s₈ := Function.update s₇ (tape 8) ((signWord sign).reverse ++ s₇ (tape 8))
  have signRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .readSign), clean ambient, base⟩) =
      some ⟨some (labels .scanKey), clean ambient sign, s₁⟩ := by
    change some (TM2.stepAux (program (labels .readSign)) _ _) = _
    rw [atLabels .readSign]
    simp [instruction, readSign, TM2.stepAux, clean, BinaryNameCompare.clean,
      cursor, he 7, hd 0 7 (by decide), s₁]
  have s₁cursor : s₁ (tape 0) = BinaryNameMachine.frame bits ++ suffix := by simp [s₁]
  have s₁key : s₁ (tape 2) = [] := by
    simp [s₁, hd 2 0 (by decide), hd 2 7 (by decide), he 2]
  have keyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .scanKey), clean ambient sign, s₁⟩) =
      some ⟨some (labels .copyOut), clean ambient sign, s₂⟩ := by
    let e := BinaryNameCompare.scanStateEquiv (A × Bool)
    let back := MachineStateEquiv.program e.symm program
    have atScan : back (labels .scanKey) =
        BinaryNameMachine.scan (tape 0) (tape 2) (labels .scanKey)
          (some (labels .copyOut)) malformed := by
      change MachineStateEquiv.statement e.symm (program (labels .scanKey)) = _
      rw [atLabels .scanKey]
      exact MachineStateEquiv.statement_symm_statement e _
    have backForward : MachineStateEquiv.program e back = program := by
      funext l
      change MachineStateEquiv.statement e (MachineStateEquiv.statement e.symm (program l)) = _
      exact MachineStateEquiv.statement_symm_statement e.symm _
    have initial : tapesAt (tape 0) (tape 2) s₁
        (BinaryNameMachine.frame bits ++ suffix) [] = s₁ := by
      rw [← s₁cursor, ← s₁key]
      exact tapesAt_self _ _ _
    have native := BinaryNameMachine.framedTrace (tape 0) (tape 2) (hd 0 2 (by decide))
      (labels .scanKey) (some (labels .copyOut)) malformed back atScan s₁
      ((ambient, sign), false) bits suffix [] none
    simp only [canonical, ↓reduceIte, initial, List.append_nil] at native
    have transported := MachineStateEquiv.trace e back _ _ _ native
    rw [backForward] at transported
    simpa only [MachineStateEquiv.configuration, e, BinaryNameCompare.scanStateEquiv, Equiv.coe_fn_mk,
      BinaryNameMachine.clean, clean, BinaryNameCompare.clean, s₂, tapesAt] using transported
  have s₂permanent : s₂ (tape 1) = BinaryNameSearch.stream tokens := by
    simpa [s₂, s₁, hd 1 0 (by decide), hd 1 2 (by decide), hd 1 7 (by decide)] using permanent
  have s₂empty (i : Fin 9) (hi : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6) : s₂ (tape i) = [] := by
    rcases hi with rfl | rfl | rfl | rfl <;>
      simp [s₂, s₁, hd, he]
  have copyRun : (advance (TM2.step program))^[2 * ((BinaryNameSearch.stream tokens).length + 1)]
      (some ⟨some (labels .copyOut), clean ambient sign, s₂⟩) =
      some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩ := by
    have h := MachineCopy.copyTrace (tape 1) (tape 3) (tape 6)
      (hd 1 3 (by decide)) (hd 1 6 (by decide)) (hd 3 6 (by decide)) false
      (labels .copyOut) (labels .copyBack) (some (labels (.search .sign))) program
      (atLabels .copyOut) (atLabels .copyBack) s₂
      (s₂empty 6 (by simp)) ((ambient, sign), false, none) none
    simpa only [s₂permanent, s₂empty 3 (by simp), List.append_nil,
      clean, BinaryNameCompare.clean, s₃] using h
  have s₃key : s₃ (tape 2) = bits.reverse := by
    simp [s₃, s₂, hd 2 3 (by decide)]
  have s₃counter : s₃ (tape 7) = [false] := by
    simp [s₃, s₂, s₁, hd 7 3 (by decide), hd 7 2 (by decide), hd 7 0 (by decide)]
  have s₃stream : s₃ (tape 3) = BinaryNameSearch.stream tokens := by simp [s₃]
  have searchRun : (advance (TM2.step program))^[BinaryNameSearch.steps tokens bits]
      (some ⟨some (labels (.search .sign)), clean ambient sign, s₃⟩) =
      some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩ := by
    have h := BinaryNameSearch.searchTrace (searchTapes tape)
      (searchTapes_injective tape distinct) (fun l => labels (.search l))
      (some (labels .drainSearch)) malformed malformed program
      (fun l => atLabels (.search l)) s₃ (ambient, sign) tokens bits [] [false]
      tokensCanonical present s₃key
      (by simpa [s₃, searchTapes, hd 4 3 (by decide)] using s₂empty 4 (by simp))
      (by simpa [s₃, searchTapes, hd 5 3 (by decide)] using s₂empty 5 (by simp))
      (by simpa [s₃, searchTapes, hd 6 3 (by decide)] using s₂empty 6 (by simp))
    have initial : tapesAt (tape 3) (tape 7) s₃ (BinaryNameSearch.stream tokens) [false] = s₃ := by
      rw [← s₃stream, ← s₃counter]
      exact tapesAt_self _ _ _
    simpa only [searchTapes, List.append_nil, initial, clean, BinaryNameSearch.clean,
      s₄, tail, encodeWord, index] using h
  have s₄stream : s₄ (tape 3) = tail := by simp [s₄, hd 3 7 (by decide)]
  have drainSearchRun : (advance (TM2.step program))^[tail.length + 1]
      (some ⟨some (labels .drainSearch), clean ambient sign, s₄⟩) =
      some ⟨some (labels .drainKey), clean ambient sign, s₅⟩ := by
    have h := MachineDrain.drainTrace (tape 3) (labels .drainSearch)
      (some (labels .drainKey)) program (atLabels .drainSearch) s₄ tail
      ((ambient, sign), false, none) none
    have initial : Function.update s₄ (tape 3) tail = s₄ := by
      rw [← s₄stream]; exact Function.update_eq_self _ _
    simpa only [initial, clean, BinaryNameCompare.clean, s₅] using h
  have s₅key : s₅ (tape 2) = bits.reverse := by
    simp [s₅, s₄, tapesAt, hd 2 3 (by decide), hd 2 7 (by decide), s₃key]
  have drainKeyRun : (advance (TM2.step program))^[bits.length + 1]
      (some ⟨some (labels .drainKey), clean ambient sign, s₅⟩) =
      some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩ := by
    have h := MachineDrain.drainTrace (tape 2) (labels .drainKey)
      (some (labels .emitIndex)) program (atLabels .drainKey) s₅ bits.reverse
      ((ambient, sign), false, none) none
    have initial : Function.update s₅ (tape 2) bits.reverse = s₅ := by
      rw [← s₅key]; exact Function.update_eq_self _ _
    simpa only [initial, List.length_reverse, clean, BinaryNameCompare.clean, s₆] using h
  have s₆index : s₆ (tape 7) = encodeWord (index tokens bits) := by
    simp [s₆, s₅, s₄, hd 7 2 (by decide), hd 7 3 (by decide)]
  have indexRun : (advance (TM2.step program))^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), clean ambient sign, s₆⟩) =
      some ⟨some (labels .emitSign), clean ambient sign, s₇⟩ := by
    change (nextAt (Γ := Alphabet) (tape 8) program)^[index tokens bits + 2]
      (some ⟨some (labels .emitIndex), (((ambient, sign), false, none), none), s₆⟩) =
      some ⟨some (labels .emitSign), (((ambient, sign), false, none), none), s₇⟩
    have h := transferAt_fromTapes (Γ := Alphabet) (tape 7) (tape 8)
      (hd 7 8 (by decide)) id false (labels .emitIndex) (some (labels .emitSign)) program
      (atLabels .emitIndex) s₆ ((ambient, sign), false, none) none
    have time : index tokens bits + 1 + 1 = index tokens bits + 2 := by omega
    simpa only [s₆index, encodeWord_length, List.map_id_fun, id_eq, time, s₇] using h
  have emitRun : (advance (TM2.step program))^[1]
      (some ⟨some (labels .emitSign), clean ambient sign, s₇⟩) =
      some ⟨exit, clean ambient, s₈⟩ := by
    change some (TM2.stepAux (program (labels .emitSign)) _ _) = _
    rw [atLabels .emitSign]
    cases sign <;> simp [instruction, emitSign, clean, BinaryNameCompare.clean,
      TM2.stepAux, signWord, encodeWord, s₈, Function.update_idem]
  have full := joinTrace (joinTrace (joinTrace (joinTrace (joinTrace (joinTrace
    (joinTrace signRun keyRun) copyRun) searchRun) drainSearchRun) drainKeyRun) indexRun) emitRun
  have finalTapes : s₈ = Function.update (Function.update base (tape 0) suffix) (tape 8)
      ((outputWord tokens bits sign).reverse ++ base (tape 8)) := by
    funext k
    by_cases h8 : k = tape 8
    · subst k
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, outputWord,
        List.reverse_append, List.append_assoc, hd]
    · by_cases h0 : k = tape 0
      · subst k
        simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd]
      · by_cases h2 : k = tape 2
        · subst k
          simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 2]
        · by_cases h3 : k = tape 3
          · subst k
            simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 3]
          · by_cases h7 : k = tape 7
            · subst k
              simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, hd, he 7]
            · simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, tapesAt, h8, h0, h2, h3, h7]
  simpa only [steps, tail, finalTapes] using full

end PerfectCompleteness.BinaryLiteralMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryOccurrenceRename
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryOccurrenceRename

open BinaryFormula UniqueGamesTheorem.Foundations

theorem literal_mem_names (F : Formula) (c : Clause) (hc : c ∈ F.clauses)
    (i : Fin 3) : (c)[i].name ∈ sourceNames F := by
  apply List.mem_flatMap.mpr
  refine ⟨c, hc, ?_⟩
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> simp [clauseNames]

def nameIndex (F : Formula) (name : Nat) (mem : name ∈ sourceNames F) :
    Fin (sourceNames F).length :=
  ⟨(sourceNames F).idxOf name, List.idxOf_lt_length_of_mem mem⟩

def literal (F : Formula) (l : Literal) (mem : l.name ∈ sourceNames F) :
    Target.Literal (sourceNames F).length :=
  ⟨nameIndex F l.name mem, l.positive⟩

def clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Target.Clause (sourceNames F).length :=
  #v[literal F (c)[0] (literal_mem_names F c mem 0),
    literal F (c)[1] (literal_mem_names F c mem 1),
    literal F (c)[2] (literal_mem_names F c mem 2)]

def renamed (F : Formula) : Target.Formula where
  «variables» := (sourceNames F).length
  clauses := F.clauses.attach.map (fun c => clause F c.val c.property)

def restrictAssignment (F : Formula) (A : Nat → Bool) :
    Fin (sourceNames F).length → Bool :=
  fun i => A (sourceNames F)[i.val]

def extendAssignment (F : Formula) (A : Fin (sourceNames F).length → Bool) : Nat → Bool :=
  fun name => if mem : name ∈ sourceNames F then A (nameIndex F name mem) else false

@[simp] theorem nameIndex_reads_name (F : Formula) (name : Nat)
    (mem : name ∈ sourceNames F) : (sourceNames F)[(nameIndex F name mem).val] = name :=
  List.getElem_idxOf _

@[simp] theorem clause_eval_restrict (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Nat → Bool) : (clause F c mem).eval (restrictAssignment F A) = c.eval A := by
  simp [clause, literal, Target.Clause.eval, Target.Literal.eval,
    BinaryFormula.Clause.eval, BinaryFormula.Literal.eval, restrictAssignment]

@[simp] theorem clause_eval_extend (F : Formula) (c : Clause) (mem : c ∈ F.clauses)
    (A : Fin (sourceNames F).length → Bool) :
    (clause F c mem).eval A = c.eval (extendAssignment F A) := by
  have evalLiteral (l : Literal) (hl : l.name ∈ sourceNames F) :
      (literal F l hl).eval A = l.eval (extendAssignment F A) := by
    simp only [literal, Target.Literal.eval, BinaryFormula.Literal.eval,
      extendAssignment, dite_eq_left hl]
    rfl
  simp [clause, Target.Clause.eval, BinaryFormula.Clause.eval, evalLiteral]

@[simp] theorem renamed_clause_count (F : Formula) :
    (renamed F).clauses.length = F.clauses.length := by simp [renamed]

@[simp] theorem renamed_variable_count (F : Formula) :
    (renamed F).variables = 3 * F.clauses.length := by
  exact clauseNames_flat_length F.clauses

theorem nat_bits_injective : Function.Injective Nat.bits := by
  intro a b same
  have decoded := congrArg BinaryEncoding.bitsValue same
  simpa only [BinaryEncoding.bitsValue_bits] using decoded

theorem idxOf_binary_payloads (names : List Nat) (name : Nat) :
    (names.map Nat.bits).idxOf name.bits = names.idxOf name := by
  induction names with
  | nil => rfl
  | cons first names ih =>
      by_cases same : first = name
      · subst first
        simp
      · have different : first.bits ≠ name.bits := fun h => same (nat_bits_injective h)
        simp only [List.map_cons, List.idxOf_cons, beq_false_of_ne same,
          beq_false_of_ne different, ih]

theorem renamed_encoding_bound (F : Formula) :
    (Complexity.formulaBits (renamed F)).length ≤
      9 * F.clauses.length * F.clauses.length + 10 * F.clauses.length + 2 := by
  have h := Complexity.formulaBits_length_le (renamed F)
  simp only [renamed_clause_count, renamed_variable_count] at h
  nlinarith

end PerfectCompleteness.BinaryOccurrenceRename

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryParsingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryParsing

open BinaryEncoding BinaryFormula

theorem frame_eq (bits : List Bool) : BinaryNameMachine.frame bits = frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [BinaryNameMachine.frame, frame, ih]

theorem canonical_cons_cons (a b : Bool) (bits : List Bool) :
    BinaryNameMachine.canonical (a :: b :: bits) = BinaryNameMachine.canonical (b :: bits) := rfl

theorem canonical_iff (bits : List Bool) :
    BinaryNameMachine.canonical bits = true ↔ (bitsValue bits).bits = bits := by
  induction bits with
  | nil => simp [BinaryNameMachine.canonical, BinaryNameMachine.finalDigit, bitsValue]
  | cons bit bits ih =>
      cases bits with
      | nil => cases bit <;> decide
      | cons next bits =>
          rw [canonical_cons_cons, ih]
          constructor
          · intro htail
            have hn : bitsValue (next :: bits) ≠ 0 := by
              intro hz
              rw [hz, Nat.zero_bits] at htail
              contradiction
            rw [bitsValue, Nat.bits_append_bit _ bit (fun h => False.elim (hn h)), htail]
          · intro hfull
            calc
              (bitsValue (next :: bits)).bits =
                  (Nat.bit bit (bitsValue (next :: bits))).div2.bits := by rw [Nat.div2_bit]
              _ = (Nat.bit bit (bitsValue (next :: bits))).bits.tail :=
                Nat.div2_bits_eq_tail _
              _ = (bit :: next :: bits).tail := congrArg List.tail hfull
              _ = next :: bits := rfl

@[simp] theorem canonical_nat_bits (name : Nat) :
    BinaryNameMachine.canonical name.bits = true := by
  apply (canonical_iff _).mpr
  rw [bitsValue_bits]

theorem parseFrame_sound (input digits rest : List Bool)
    (parsed : parseFrame input = some (digits, rest)) : input = frame digits ++ rest := by
  induction input using List.twoStepInduction generalizing digits rest with
  | nil => simp [parseFrame] at parsed
  | singleton flag =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · simp [parseFrame] at parsed
  | cons_cons flag bit input ih _ =>
      cases flag
      · simp only [parseFrame, Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        rfl
      · cases h : parseFrame input with
        | none => simp [parseFrame, h] at parsed
        | some pair =>
            rcases pair with ⟨ds, tail⟩
            have hs := ih ds tail h
            simp [parseFrame, h] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            simp [frame, hs]

theorem parseName_sound (input : List Bool) (name : Nat) (rest : List Bool)
    (parsed : parseName input = some (name, rest)) : input = nameBits name ++ rest := by
  cases h : parseFrame input with
  | none => simp [parseName, h] at parsed
  | some pair =>
      rcases pair with ⟨digits, tail⟩
      by_cases canonical : digits = (bitsValue digits).bits
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some] at parsed
        rw [ite_eq_left canonical] at parsed
        simp only [Option.some.injEq, Prod.mk.injEq] at parsed
        rcases parsed with ⟨rfl, rfl⟩
        have hs := parseFrame_sound input digits tail h
        exact hs.trans (congrArg (fun ds => frame ds ++ tail) canonical)
      · simp only [parseName, h, Option.bind_eq_bind, Option.bind_some, ite_eq_right canonical] at parsed
        cases parsed

theorem parseLiteral_sound (input : List Bool) (literal : Literal) (rest : List Bool)
    (parsed : parseLiteral input = some (literal, rest)) :
    input = literalBits literal ++ rest := by
  cases input with
  | nil => simp [parseLiteral] at parsed
  | cons sign input =>
      cases h : parseName input with
      | none => simp [parseLiteral, h] at parsed
      | some pair =>
          rcases pair with ⟨name, tail⟩
          have hs := parseName_sound input name tail h
          simp [parseLiteral, h] at parsed
          rcases parsed with ⟨rfl, rfl⟩
          simp [literalBits, hs]

theorem parseClause_sound (input : List Bool) (clause : Clause) (rest : List Bool)
    (parsed : parseClause input = some (clause, rest)) : input = clauseBits clause ++ rest := by
  cases ha : parseLiteral input with
  | none => simp [parseClause, ha] at parsed
  | some first =>
      rcases first with ⟨a, afterA⟩
      cases hb : parseLiteral afterA with
      | none => simp [parseClause, ha, hb] at parsed
      | some second =>
          rcases second with ⟨b, afterB⟩
          cases hc : parseLiteral afterB with
          | none => simp [parseClause, ha, hb, hc] at parsed
          | some third =>
              rcases third with ⟨c, afterC⟩
              have hA := parseLiteral_sound input a afterA ha
              have hB := parseLiteral_sound afterA b afterB hb
              have hC := parseLiteral_sound afterB c afterC hc
              have pairEq : (#v[a, b, c], afterC) = (clause, rest) := by
                apply Option.some.inj
                simpa only [parseClause, ha, hb, hc, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def] using parsed
              rcases Prod.mk.inj pairEq with ⟨rfl, rfl⟩
              simp [clauseBits, hA, hB, hC, List.append_assoc]

theorem parseClauses_sound (fuel : Nat) (input : List Bool)
    (clauses : List Clause) (rest : List Bool)
    (parsed : parseClauses fuel input = some (clauses, rest)) :
    input = clausesBits clauses ++ rest := by
  induction fuel generalizing input clauses rest with
  | zero => simp [parseClauses] at parsed
  | succ fuel ih =>
      cases input with
      | nil => simp [parseClauses] at parsed
      | cons flag input =>
          cases flag
          · simp only [parseClauses, Option.some.injEq, Prod.mk.injEq] at parsed
            rcases parsed with ⟨rfl, rfl⟩
            rfl
          · cases hc : parseClause input with
            | none => simp [parseClauses, hc] at parsed
            | some first =>
                rcases first with ⟨clause, afterClause⟩
                cases hs : parseClauses fuel afterClause with
                | none => simp [parseClauses, hc, hs] at parsed
                | some remaining =>
                    rcases remaining with ⟨cs, tail⟩
                    have hC := parseClause_sound input clause afterClause hc
                    have hS := ih afterClause cs tail hs
                    simp [parseClauses, hc, hs] at parsed
                    rcases parsed with ⟨rfl, rfl⟩
                    simp [clausesBits, hC, hS, List.append_assoc]

theorem decodeFormula_sound (input : List Bool) (formula : Formula)
    (parsed : decodeFormula input = some formula) : input = formulaBits formula := by
  cases h : parseClauses (input.length + 1) input with
  | none => simp [decodeFormula, h] at parsed
  | some pair =>
      rcases pair with ⟨clauses, rest⟩
      by_cases empty : rest = []
      · subst rest
        simp [decodeFormula, h] at parsed
        subst formula
        simpa only [formulaBits, List.append_nil] using
          parseClauses_sound (input.length + 1) input clauses [] h
      · simp [decodeFormula, h, empty] at parsed

end PerfectCompleteness.BinaryParsing



namespace PerfectCompleteness.BinaryLanguage

open UniqueGamesTheorem.Foundations

def rejectBinary : BinaryFormula.Formula where
  clauses := [#v[⟨0, true⟩, ⟨0, true⟩, ⟨0, true⟩],
    #v[⟨0, false⟩, ⟨0, false⟩, ⟨0, false⟩]]

def totalParsed (input : List Bool) : BinaryFormula.Formula :=
  (BinaryEncoding.decodeFormula input).getD rejectBinary

def totalRename (input : List Bool) : Target.Formula :=
  BinaryOccurrenceRename.renamed (totalParsed input)

end PerfectCompleteness.BinaryLanguage

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryRenameLoop
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryParsing.canonical_nat_bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryRenameLoop


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

abbrev Token := BinaryNameSearch.Token

def nextSlot (slot : Fin 3) : Fin 3 := if slot = 0 then 1 else if slot = 1 then 2 else 0

def clauseIncrement (slot : Fin 3) : Nat := if slot = 2 then 1 else 0

def finalSlot : Nat → Fin 3 → Fin 3
  | 0, slot => slot
  | n + 1, slot => finalSlot n (nextSlot slot)

def completedClauses : Nat → Fin 3 → Nat
  | 0, _ => 0
  | n + 1, slot => completedClauses n (nextSlot slot) + clauseIncrement slot

theorem finalSlot_three (n : Nat) : finalSlot (n + 3) 0 = finalSlot n 0 := by
  simp [finalSlot, nextSlot]

theorem completedClauses_three (n : Nat) :
    completedClauses (n + 3) 0 = completedClauses n 0 + 1 := by
  simp [completedClauses, nextSlot, clauseIncrement]

@[simp] theorem finalSlot_triples (n : Nat) : finalSlot (3 * n) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, finalSlot_three, ih]

@[simp] theorem completedClauses_triples (n : Nat) : completedClauses (3 * n) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.mul_succ, completedClauses_three, ih]

def outputBody (tokens input : List Token) : List Bool :=
  input.flatMap (fun token => BinaryLiteralMachine.outputWord tokens token.2 token.1)

@[simp] theorem outputBody_nil (tokens : List Token) : outputBody tokens [] = [] := rfl

@[simp] theorem outputBody_cons (tokens : List Token) (token : Token) (input : List Token) :
    outputBody tokens (token :: input) =
      BinaryLiteralMachine.outputWord tokens token.2 token.1 ++ outputBody tokens input := rfl

def steps (tokens : List Token) : List Token → Nat
  | [] => 1
  | token :: input => BinaryLiteralMachine.steps tokens token.2 + 2 + steps tokens input

theorem payload_length_le_stream (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    bits.length ≤ (BinaryNameSearch.stream tokens).length := by
  induction tokens with
  | nil => simp at present
  | cons token tokens ih =>
      rcases List.mem_cons.mp present with equal | remaining
      · rw [equal]
        simp only [BinaryNameSearch.stream_cons, List.length_append,
          BinaryNameSearch.tokenBits, List.length_cons, BinaryNameMachine.frame_length]
        omega
      · have tail := ih remaining
        simp only [BinaryNameSearch.stream_cons, List.length_append]
        omega

def perLiteralBound (streamLength : Nat) : Nat :=
  12 * streamLength ^ 2 + 26 * streamLength + 11

theorem literal_steps_le (tokens : List Token) (bits : List Bool)
    (present : bits ∈ BinaryNameSearch.payloads tokens) :
    BinaryLiteralMachine.steps tokens bits + 2 ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length := by
  have body := BinaryLiteralMachine.steps_le tokens bits present
  have size := payload_length_le_stream tokens bits present
  have sumBound : (BinaryNameSearch.stream tokens).length + bits.length ≤
      2 * (BinaryNameSearch.stream tokens).length := by omega
  have sq := Nat.mul_self_le_mul_self sumBound
  unfold perLiteralBound
  nlinarith

theorem steps_le (tokens input : List Token) (included : ∀ token ∈ input, token ∈ tokens) :
    steps tokens input ≤
      perLiteralBound (BinaryNameSearch.stream tokens).length * input.length + 1 := by
  induction input with
  | nil => simp [steps]
  | cons token input ih =>
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, included token (by simp), rfl⟩
      have head := literal_steps_le tokens token.2 present
      have tail := ih (fun t ht => included t (by simp [ht]))
      simp only [steps, List.length_cons]
      nlinarith

section Program

variable {K Λ A : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (A : Type) := BinaryLiteralMachine.State (A × Fin 3)
abbrev clean (ambient : A) (slot : Fin 3) : State A :=
  BinaryLiteralMachine.clean (ambient, slot)

inductive Label
  | entry
  | literal (label : BinaryLiteralMachine.Label)
  | tally
  deriving DecidableEq, Fintype

def literalTapes (tape : Fin 11 → K) : Fin 9 → K := fun i => tape i.castSucc.castSucc

omit [DecidableEq K] in
theorem literalTapes_injective (tape : Fin 11 → K) (distinct : Function.Injective tape) :
    Function.Injective (literalTapes tape) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 11 => i.val) (distinct h)

def finish (exit : Option Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 state.1.1.1.2)
    (match exit with
      | none => .halt
      | some label => .goto fun _ => label)

def next (again : Λ) : TM2.Stmt (Alphabet (K := K)) Λ (State A) :=
  .load (fun state => clean state.1.1.1.1 (nextSlot state.1.1.1.2))
    (.goto fun _ => again)

def instruction (tape : Fin 11 → K) (labels : Label → Λ)
    (done malformed : Option Λ) : Label → TM2.Stmt (Alphabet (K := K)) Λ (State A)
  | .entry =>
      .pop (tape 0) (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push (tape 0) (fun state => state.2.getD false)
            (finish (some (labels (.literal .readSign)))))
          (finish done))
  | .literal l => BinaryLiteralMachine.instruction (literalTapes tape)
      (fun l => labels (.literal l)) (some (labels .tally)) malformed l
  | .tally =>
      .push (tape 9) (fun _ => true)
        (.branch (fun state => state.1.1.1.2 == (2 : Fin 3))
          (.push (tape 10) (fun _ => true) (next (labels .entry)))
          (next (labels .entry)))

def loopTapes (tape : Fin 11 → K) (base : K → List Bool)
    (cursor output variableCounter clauses : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update base
    (tape 0) cursor) (tape 8) output) (tape 9) variableCounter) (tape 10) clauses

theorem loopTapes_cursor (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 0) = cursor := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_variables (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 9) = variableCounter := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  simp [loopTapes, hd]

theorem loopTapes_clauses (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses : List Bool) :
    loopTapes tape base cursor output variableCounter clauses (tape 10) = clauses := by
  simp [loopTapes]

theorem update_cursor (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 0) replacement =
      loopTapes tape base replacement output variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 0
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_output (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 8) replacement =
      loopTapes tape base cursor replacement variableCounter clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 8
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_variables (tape : Fin 11 → K) (distinct : Function.Injective tape)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 9) replacement =
      loopTapes tape base cursor output replacement clauses := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  funext k
  by_cases h : k = tape 9
  · subst k; simp [loopTapes, hd]
  · simp [loopTapes, h, Function.update_apply]

theorem update_clauses (tape : Fin 11 → K)
    (base : K → List Bool) (cursor output variableCounter clauses replacement : List Bool) :
    Function.update (loopTapes tape base cursor output variableCounter clauses) (tape 10) replacement =
      loopTapes tape base cursor output variableCounter replacement := by
  simp [loopTapes]

@[simp] theorem stepAux_finish (exit : Option Λ) (state : State A) (base : K → List Bool) :
    TM2.stepAux (finish exit) state base =
      ⟨exit, clean state.1.1.1.1 state.1.1.1.2, base⟩ := by
  cases exit <;> rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

variable (tape : Fin 11 → K) (distinct : Function.Injective tape)
variable (labels : Label → Λ) (done malformed : Option Λ)
variable (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
variable (atLabels : ∀ l, program (labels l) = instruction tape labels done malformed l)
variable (base : K → List Bool) (ambient : A)

include distinct atLabels

theorem peekStep (slot : Fin 3) (head : Bool) (tail output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (head :: tail) output variableCounter clauses⟩ =
      some ⟨some (labels (.literal .readSign)), clean ambient slot,
        loopTapes tape base (head :: tail) output variableCounter clauses⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .entry)) _ _) = _
  rw [atLabels .entry]
  simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
    loopTapes_cursor tape distinct, update_cursor tape distinct]

theorem emptyStep (slot : Fin 3) (output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base [] output variableCounter clauses⟩ =
      some ⟨done, clean ambient slot, loopTapes tape base [] output variableCounter clauses⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .entry)) _ _) = _
  rw [atLabels .entry]
  simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
    loopTapes_cursor tape distinct, update_cursor tape distinct]

theorem tallyStep (slot : Fin 3) (cursor output variableCounter clauses : List Bool) :
    TM2.step program
      ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base cursor output variableCounter clauses⟩ =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base cursor output (true :: variableCounter)
          (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  change some (TM2.stepAux (program (labels .tally)) _ _) = _
  rw [atLabels .tally]
  fin_cases slot <;>
    simp [instruction, TM2.stepAux, clean, BinaryLiteralMachine.clean, BinaryNameCompare.clean,
      next, nextSlot, clauseIncrement, loopTapes_variables tape distinct, loopTapes_clauses,
      update_variables tape distinct, update_clauses]

theorem bodyTrace (tokens : List Token) (token : Token) (slot : Fin 3)
    (suffix output variableCounter clauses : List Bool)
    (canonical : BinaryNameMachine.canonical token.2 = true)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (present : token.2 ∈ BinaryNameSearch.payloads tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[BinaryLiteralMachine.steps tokens token.2 + 2]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
  have hd (i j : Fin 11) (hne : i ≠ j) : tape i ≠ tape j := fun h => hne (distinct h)
  let initial := loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix)
    output variableCounter clauses
  have first : (advance (TM2.step program))^[1]
      (some ⟨some (labels .entry), clean ambient slot, initial⟩) =
      some ⟨some (labels (.literal .readSign)), clean ambient slot, initial⟩ := by
    simpa only [Function.iterate_one, advance_some, initial,
      BinaryNameSearch.tokenBits, List.cons_append] using
      peekStep tape distinct labels done malformed program atLabels base ambient slot token.1
        (BinaryNameMachine.frame token.2 ++ suffix) output variableCounter clauses
  have workEmpty (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      initial (tape i) = [] := by
    have h0 : i ≠ 0 := by intro h; subst i; omega
    have h8 : i ≠ 8 := by intro h; subst i; omega
    have h9 : i ≠ 9 := by intro h; subst i; omega
    have h10 : i ≠ 10 := by intro h; subst i; omega
    simpa [initial, loopTapes, hd i 0 h0, hd i 8 h8, hd i 9 h9, hd i 10 h10]
      using empty i lo hi
  have literal := BinaryLiteralMachine.literalTrace (literalTapes tape)
    (literalTapes_injective tape distinct) (fun l => labels (.literal l))
    (some (labels .tally)) malformed program (fun l => atLabels (.literal l))
    initial tokens token.1 token.2 suffix canonical tokensCanonical present
    (by simp [initial, literalTapes, loopTapes, BinaryNameSearch.tokenBits, hd])
    (by simpa [initial, literalTapes, loopTapes, hd] using permanent)
    (fun i lo hi => workEmpty i.castSucc.castSucc lo hi) (ambient, slot)
  have finalTapes :
      Function.update (Function.update initial (literalTapes tape 0) suffix)
        (literalTapes tape 8)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++
          initial (literalTapes tape 8)) =
      loopTapes tape base suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses := by
    have out : initial (literalTapes tape 8) = output := by
      simp [initial, literalTapes, loopTapes, hd]
    rw [out]
    change Function.update (Function.update
      (loopTapes tape base (BinaryNameSearch.tokenBits token ++ suffix) output variableCounter clauses)
      (tape 0) suffix) (tape 8) _ = _
    rw [update_cursor tape distinct, update_output tape distinct]
  rw [finalTapes] at literal
  have tally : (advance (TM2.step program))^[1]
      (some ⟨some (labels .tally), clean ambient slot,
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          variableCounter clauses⟩) =
      some ⟨some (labels .entry), clean ambient (nextSlot slot),
        loopTapes tape base suffix
          ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
          (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)⟩ := by
    simpa only [Function.iterate_one, advance_some] using
      tallyStep tape distinct labels done malformed program atLabels base ambient slot suffix
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        variableCounter clauses
  have full := joinTrace (joinTrace first literal) tally
  simpa only [show 1 + BinaryLiteralMachine.steps tokens token.2 + 1 =
    BinaryLiteralMachine.steps tokens token.2 + 2 by omega] using full

theorem loopTrace (tokens input : List Token) (slot : Fin 3)
    (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient slot,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient (finalSlot input.length slot),
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate input.length true ++ variableCounter)
          (List.replicate (completedClauses input.length slot) true ++ clauses)⟩ := by
  induction input generalizing slot output variableCounter clauses with
  | nil =>
      simpa only [steps, Function.iterate_one, advance_some, BinaryNameSearch.stream_nil,
        List.length_nil, outputBody_nil, List.reverse_nil, List.nil_append,
        finalSlot, completedClauses, List.replicate_zero] using
        emptyStep tape distinct labels done malformed program atLabels base ambient
          slot output variableCounter clauses
  | cons token input ih =>
      have member := included token (by simp)
      have present : token.2 ∈ BinaryNameSearch.payloads tokens :=
        List.mem_map.mpr ⟨token, member, rfl⟩
      have first := bodyTrace tape distinct labels done malformed program atLabels base ambient
        tokens token slot (BinaryNameSearch.stream input) output variableCounter clauses
        (tokensCanonical token member) tokensCanonical present permanent empty
      have rest := ih (nextSlot slot)
        ((BinaryLiteralMachine.outputWord tokens token.2 token.1).reverse ++ output)
        (true :: variableCounter) (List.replicate (clauseIncrement slot) true ++ clauses)
        (fun t ht => included t (by simp [ht]))
      have full := joinTrace first rest
      have variableEq : List.replicate input.length true ++ (true :: variableCounter) =
          List.replicate (input.length + 1) true ++ variableCounter := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      have clauseEq : List.replicate (completedClauses input.length (nextSlot slot)) true ++
          (List.replicate (clauseIncrement slot) true ++ clauses) =
          List.replicate (completedClauses (input.length + 1) slot) true ++ clauses := by
        rw [← List.append_assoc, ← List.replicate_add]
        rfl
      simpa only [steps, BinaryNameSearch.stream_cons, List.length_cons, finalSlot,
        outputBody_cons, List.reverse_append, List.append_assoc, variableEq, clauseEq] using full

theorem triplesTrace (tokens input : List Token) (count : Nat)
    (length_eq : input.length = 3 * count) (output variableCounter clauses : List Bool)
    (tokensCanonical : ∀ t ∈ tokens, BinaryNameMachine.canonical t.2 = true)
    (included : ∀ t ∈ input, t ∈ tokens)
    (permanent : base (tape 1) = BinaryNameSearch.stream tokens)
    (empty : ∀ i : Fin 11, 2 ≤ i.val → i.val ≤ 7 → base (tape i) = []) :
    (advance (TM2.step program))^[steps tokens input]
      (some ⟨some (labels .entry), clean ambient 0,
        loopTapes tape base (BinaryNameSearch.stream input) output variableCounter clauses⟩) =
      some ⟨done, clean ambient 0,
        loopTapes tape base [] ((outputBody tokens input).reverse ++ output)
          (List.replicate (3 * count) true ++ variableCounter)
          (List.replicate count true ++ clauses)⟩ := by
  have h := loopTrace tape distinct labels done malformed program atLabels base ambient
    tokens input 0 output variableCounter clauses tokensCanonical included permanent empty
  simpa only [length_eq, finalSlot_triples, completedClauses_triples] using h

end Program

end PerfectCompleteness.BinaryRenameLoop

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryTokenMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryTokenMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open BinaryFormula BinaryEncoding

abbrev Tape := Fin 3
abbrev Alphabet (_ : Tape) := Bool
abbrev State := Unit × Option Bool

inductive Label where
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3)
  | restore
  | accept
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Label :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

@[simp] theorem afterName_zero : afterName 0 = .sign 1 := rfl
@[simp] theorem afterName_one : afterName 1 = .sign 2 := rfl
@[simp] theorem afterName_two : afterName 2 = .clause := rfl

def jump (label : Label) : TM2.Stmt Alphabet Label State :=
  .load (fun _ => ((), none)) (.goto fun _ => label)

def clauseInstruction : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (jump (.sign 0)) (jump .restore)))

def signInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isSome)
      (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
      (jump .reject))

def nameInstruction (slot : Fin 3) : TM2.Stmt Alphabet Label State :=
  .pop 0 (fun state head => (state.1, head))
    (.branch (fun state => state.2.isNone)
      (jump .reject)
      (.branch (fun state => state.2.getD false)
        (.push 1 (fun _ => true)
          (.pop 0 (fun state head => (state.1, head))
            (.branch (fun state => state.2.isSome)
              (.push 1 (fun state => state.2.getD false) (jump (.name slot)))
              (jump .reject))))
        (.push 1 (fun _ => false) (jump (afterName slot)))))

def program : Label → TM2.Stmt Alphabet Label State
  | .clause => clauseInstruction
  | .sign slot => signInstruction slot
  | .name slot => nameInstruction slot
  | .restore => loopAt 1 2 id false .restore (some .accept)
  | .accept => .halt
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 0
  k₁ := 2
  Γ := Alphabet
  Λ := Label
  main := .clause
  σ := State
  initialState := ((), none)
  m := program

def tapes (input reversed output : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then input else if k = 1 then reversed else output

def cfg (label : Option Label) (input reversed output : List Bool)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, ((), register), tapes input reversed output⟩

@[simp] theorem tapes_zero (input reversed output : List Bool) :
    tapes input reversed output 0 = input := rfl

@[simp] theorem tapes_one (input reversed output : List Bool) :
    tapes input reversed output 1 = reversed := rfl

@[simp] theorem tapes_two (input reversed output : List Bool) :
    tapes input reversed output 2 = output := rfl

theorem update_zero (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 0 replacement =
      tapes replacement reversed output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem update_one (input reversed output replacement : List Bool) :
    Function.update (tapes input reversed output) 1 replacement =
      tapes input replacement output := by
  funext k
  fin_cases k <;> simp [tapes]

theorem clauseStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (true :: input) reversed output register) =
      some (cfg (some (.sign 0)) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]
  rfl

theorem finalStep (input reversed output : List Bool) (register : Option Bool) :
    machine.step (cfg (some .clause) (false :: input) reversed output register) =
      some (cfg (some .restore) input reversed output) := by
  change some (TM2.stepAux (program .clause) _ _) = _
  simp [program, clauseInstruction, jump, cfg, TM2.stepAux, update_zero]
  rfl

theorem signStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.sign slot)) (bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: reversed) output) := by
  change some (TM2.stepAux (program (.sign slot)) _ _) = _
  simp [program, signInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameEndStep (slot : Fin 3) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step (cfg (some (.name slot)) (false :: input) reversed output register) =
      some (cfg (some (afterName slot)) input (false :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameDigitStep (slot : Fin 3) (bit : Bool) (input reversed output : List Bool)
    (register : Option Bool) :
    machine.step
      (cfg (some (.name slot)) (true :: bit :: input) reversed output register) =
      some (cfg (some (.name slot)) input (bit :: true :: reversed) output) := by
  change some (TM2.stepAux (program (.name slot)) _ _) = _
  simp [program, nameInstruction, jump, cfg, TM2.stepAux, update_zero, update_one]
  rfl

theorem nameTrace (slot : Fin 3) (bits suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[bits.length + 1]
      (some (cfg (some (.name slot)) (frame bits ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix ((frame bits).reverse ++ reversed) output) := by
  induction bits generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one, advance_some,
        frame, List.singleton_append, List.reverse_singleton] using
        nameEndStep slot suffix reversed output register
  | cons bit bits ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [frame, List.cons_append, advance_some]
      rw [nameDigitStep, ih]
      simp only [List.reverse_cons, List.append_assoc,
        List.cons_append, List.nil_append]

theorem literalTrace (slot : Fin 3) (literal : Literal)
    (suffix reversed output : List Bool) (register : Option Bool) :
    (advance machine.step)^[literal.name.size + 2]
      (some (cfg (some (.sign slot)) (literalBits literal ++ suffix) reversed output register)) =
      some (cfg (some (afterName slot)) suffix
        ((literalBits literal).reverse ++ reversed) output) := by
  rw [show literal.name.size + 2 = (literal.name.bits.length + 1) + 1 by
    rw [Nat.size_eq_bits_len]]
  rw [Function.iterate_succ_apply]
  simp only [literalBits, List.cons_append, advance_some]
  rw [signStep]
  change (advance machine.step)^[literal.name.bits.length + 1]
    (some (cfg (some (.name slot)) (frame literal.name.bits ++ suffix)
      (literal.positive :: reversed) output)) = _
  rw [nameTrace]
  simp only [nameBits, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem clauseTrace (clause : Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[clauseNameSize clause + 6]
      (some (cfg (some (.sign 0)) (clauseBits clause ++ suffix) reversed output register)) =
      some (cfg (some .clause) suffix ((clauseBits clause).reverse ++ reversed) output) := by
  have first := literalTrace 0 clause[0]
    (literalBits clause[1] ++ literalBits clause[2] ++ suffix) reversed output register
  have second := literalTrace 1 clause[1] (literalBits clause[2] ++ suffix)
    ((literalBits clause[0]).reverse ++ reversed) output none
  have third := literalTrace 2 clause[2] suffix
    ((literalBits clause[1]).reverse ++ ((literalBits clause[0]).reverse ++ reversed)) output none
  simp only [afterName_zero, afterName_one, afterName_two, List.append_assoc]
    at first second third
  have full := joinTrace (joinTrace first second) third
  have htime : (clause[0].name.size + 2 + (clause[1].name.size + 2)) +
      (clause[2].name.size + 2) = clauseNameSize clause + 6 := by
    simp [clauseNameSize, clauseNames]
    omega
  rw [htime] at full
  simpa only [clauseBits, List.append_assoc, List.reverse_append] using full

def tokens (clauses : List Clause) : List Bool := clauses.flatMap clauseBits

@[simp] theorem tokens_nil : tokens [] = [] := rfl

@[simp] theorem tokens_cons (clause : Clause) (clauses : List Clause) :
    tokens (clause :: clauses) = clauseBits clause ++ tokens clauses := by
  simp [tokens]

@[simp] theorem tokens_length (clauses : List Clause) :
    (tokens clauses).length = 6 * clauses.length + 2 * namesBitSize clauses := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      simp only [tokens_cons, List.length_append, clauseBits_length, ih,
        List.length_cons, namesBitSize_cons]
      omega

theorem stripTrace (clauses : List Clause) (suffix reversed output : List Bool)
    (register : Option Bool) :
    (advance machine.step)^[7 * clauses.length + namesBitSize clauses + 1]
      (some (cfg (some .clause) (clausesBits clauses ++ suffix) reversed output register)) =
      some (cfg (some .restore) suffix ((tokens clauses).reverse ++ reversed) output) := by
  induction clauses generalizing reversed register with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, namesBitSize_nil, Nat.add_zero,
        Nat.zero_add, Function.iterate_one, advance_some, clausesBits,
        List.singleton_append, tokens_nil, List.reverse_nil, List.nil_append] using
        finalStep suffix reversed output register
  | cons clause clauses ih =>
      have first : (advance machine.step)^[1]
          (some (cfg (some .clause)
            (true :: (clauseBits clause ++ (clausesBits clauses ++ suffix)))
            reversed output register)) =
          some (cfg (some (.sign 0))
            (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output) := by
        simpa only [Function.iterate_one, advance_some] using
          clauseStep (clauseBits clause ++ (clausesBits clauses ++ suffix)) reversed output register
      have second := clauseTrace clause (clausesBits clauses ++ suffix) reversed output none
      have third := ih ((clauseBits clause).reverse ++ reversed) none
      have full := joinTrace (joinTrace first second) third
      have htime : (1 + (clauseNameSize clause + 6)) +
          (7 * clauses.length + namesBitSize clauses + 1) =
          7 * (clause :: clauses).length + namesBitSize (clause :: clauses) + 1 := by
        simp only [List.length_cons, namesBitSize_cons]
        omega
      rw [htime] at full
      simpa only [clausesBits, List.cons_append, List.append_assoc,
        tokens_cons, List.reverse_append] using full

theorem restoreTrace (input unread output : List Bool) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .restore) unread input.reverse output register)) =
      some (cfg (some .accept) unread [] (input ++ output)) := by
  have h := transferAt_fromTapes (Γ := Alphabet) (σ := Unit) 1 2 (by decide)
    id false .restore (some .accept) program rfl
    (tapes unread input.reverse output) () register
  have ht : tapesAt 1 2 (tapes unread input.reverse output) [] (input ++ output) =
      tapes unread [] (input ++ output) := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  change (nextAt 2 program)^[input.length + 1]
    (some (cfg (some .restore) unread input.reverse output register)) = _
  simpa only [tapes_one, tapes_two, List.length_reverse, List.reverse_reverse,
    List.map_id_fun, id_eq, ht, nextAt, advance, cfg] using! h

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .clause) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem acceptTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 2]
      (some (initList machine (formulaBits formula))) =
      some (cfg (some .accept) [] [] (tokens formula.clauses)) := by
  have first := stripTrace formula.clauses [] [] [] none
  simp only [List.append_nil] at first
  have second := restoreTrace (tokens formula.clauses) [] [] none
  simp only [List.append_nil] at second
  have full := joinTrace first second
  have htime : (7 * formula.clauses.length + namesBitSize formula.clauses + 1) +
      ((tokens formula.clauses).length + 1) =
      13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2 := by
    rw [tokens_length]
    omega
  rw [htime] at full
  simpa only [initList_eq, BinaryEncoding.formulaBits] using full

theorem haltStep (output : List Bool) :
    machine.step (cfg (some .accept) [] [] output) = some (cfg none [] [] output) := by
  change some (TM2.stepAux (program .accept) _ _) = _
  rfl

theorem tokenTrace (formula : Formula) :
    (advance machine.step)^[13 * formula.clauses.length +
        3 * namesBitSize formula.clauses + 3]
      (some (initList machine (formulaBits formula))) =
      some (haltList machine (tokens formula.clauses)) := by
  rw [show 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 =
    (13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 2) + 1 by omega,
    Function.iterate_succ_apply', acceptTrace, advance_some, haltStep, haltList_eq]

theorem tokenSteps_le (formula : Formula) :
    13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3 ≤
      3 * (formulaBits formula).length + 3 := by
  rw [BinaryEncoding.formulaBits_length]
  omega

def outputsInTime (formula : Formula) :
    TM2OutputsInTime machine (formulaBits formula) (some (tokens formula.clauses))
      (3 * (formulaBits formula).length + 3) where
  steps := 13 * formula.clauses.length + 3 * namesBitSize formula.clauses + 3
  evals_in_steps := tokenTrace formula
  steps_le_m := tokenSteps_le formula


noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits (id : List Bool → List Bool)
      (fun formula => tokens formula.clauses) where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
  outputsFun formula := by
    change TM2OutputsInTime machine ((formulaBits formula).map id)
      (some ((tokens formula.clauses).map id))
      ((Polynomial.C 3 * Polynomial.X + Polynomial.C 3 : Polynomial Nat).eval
        (formulaBits formula).length)
    simpa only [List.map_id_fun, id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using outputsInTime formula

theorem machine_finiteAlphabet (k : machine.K) : Finite (machine.Γ k) := by
  change Finite Bool
  infer_instance

end PerfectCompleteness.BinaryTokenMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryRenameWords
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineLookupSpec.decodeWords_encodeWord _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineUnaryCounter.counterTapes_counter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryRenameWords

open BinaryFormula UniqueGamesTheorem.Foundations

def clauseLiterals (c : Clause) : List Literal := [(c)[0], (c)[1], (c)[2]]

def literals (clauses : List Clause) : List Literal := clauses.flatMap clauseLiterals

def token (literal : Literal) : BinaryNameSearch.Token :=
  (literal.positive, literal.name.bits)

def tokens (clauses : List Clause) : List BinaryNameSearch.Token :=
  (literals clauses).map token

@[simp] theorem literals_nil : literals [] = [] := rfl

@[simp] theorem literals_cons (c : Clause) (cs : List Clause) :
    literals (c :: cs) = (c)[0] :: (c)[1] :: (c)[2] :: literals cs := rfl

@[simp] theorem literals_length (cs : List Clause) :
    (literals cs).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [literals_cons, List.length_cons, ih]; omega

@[simp] theorem tokens_length (cs : List Clause) :
    (tokens cs).length = 3 * cs.length := by simp [tokens]

theorem literals_names (F : Formula) :
    (literals F.clauses).map Literal.name = sourceNames F := by
  simp only [literals, sourceNames, List.map_flatMap]
  rfl

theorem tokens_payloads (F : Formula) :
    BinaryNameSearch.payloads (tokens F.clauses) = (sourceNames F).map Nat.bits := by
  rw [← literals_names]
  simp only [BinaryNameSearch.payloads, tokens, List.map_map, token, Function.comp_def]

theorem token_bits (literal : Literal) :
    BinaryNameSearch.tokenBits (token literal) = BinaryEncoding.literalBits literal := by
  simp only [BinaryNameSearch.tokenBits, token, BinaryEncoding.literalBits,
    BinaryEncoding.nameBits, BinaryParsing.frame_eq]

theorem tokens_stream (cs : List Clause) :
    BinaryNameSearch.stream (tokens cs) = BinaryTokenMachine.tokens cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [tokens, literals_cons, List.map_cons, BinaryNameSearch.stream_cons,
        token_bits, BinaryTokenMachine.tokens_cons, BinaryEncoding.clauseBits]
      simpa only [tokens, List.append_assoc] using
        congrArg (fun tail => BinaryEncoding.literalBits (c)[0] ++
          BinaryEncoding.literalBits (c)[1] ++ BinaryEncoding.literalBits (c)[2] ++ tail) ih

theorem tokens_canonical (cs : List Clause) :
    ∀ t ∈ tokens cs, BinaryNameMachine.canonical t.2 = true := by
  intro t mem
  obtain ⟨literal, _, rfl⟩ := List.mem_map.mp mem
  exact BinaryParsing.canonical_nat_bits literal.name

theorem payload_index (F : Formula) (name : Nat) :
    (BinaryNameSearch.payloads (tokens F.clauses)).idxOf name.bits =
      (sourceNames F).idxOf name := by
  rw [tokens_payloads, BinaryOccurrenceRename.idxOf_binary_payloads]

def outputLiteral (names : List Nat) (literal : Literal) : List Bool :=
  Complexity.encodeWord (names.idxOf literal.name) ++
    Complexity.encodeWord (if literal.positive then 1 else 0)

def body (F : Formula) : List Bool :=
  (literals F.clauses).flatMap (outputLiteral (sourceNames F))

theorem encoded_clause (F : Formula) (c : Clause) (mem : c ∈ F.clauses) :
    Complexity.encodeWords (Complexity.clauseWords (BinaryOccurrenceRename.clause F c mem)) =
      (clauseLiterals c).flatMap (outputLiteral (sourceNames F)) := by
  simp [Complexity.clauseWords, Complexity.literalWords, Complexity.encodeWords,
    BinaryOccurrenceRename.clause, BinaryOccurrenceRename.literal,
    BinaryOccurrenceRename.nameIndex, clauseLiterals, outputLiteral, List.append_assoc]
  rfl

theorem encodeWords_flatMap {α : Type} (xs : List α) (f : α → List Nat) :
    Complexity.encodeWords (xs.flatMap f) =
      xs.flatMap (fun x => Complexity.encodeWords (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, Complexity.encodeWords_append, ih]

theorem encoded_body (F : Formula) :
    Complexity.encodeWords ((BinaryOccurrenceRename.renamed F).clauses.flatMap
      Complexity.clauseWords) = body F := by
  rw [encodeWords_flatMap]
  change (F.clauses.attach.map (fun c => BinaryOccurrenceRename.clause F c.val c.property)).flatMap
    (fun c => Complexity.encodeWords (Complexity.clauseWords c)) = body F
  rw [List.flatMap_map]
  simp only [encoded_clause]
  have h := congrArg (fun cs : List Clause =>
    cs.flatMap (fun c => (clauseLiterals c).flatMap (outputLiteral (sourceNames F))))
    (List.attach_map_subtype_val F.clauses)
  simpa only [List.flatMap_map, body, literals, List.flatMap_assoc] using h

theorem encoded_renamed (F : Formula) :
    Complexity.formulaBits (BinaryOccurrenceRename.renamed F) =
      Complexity.encodeWord (3 * F.clauses.length) ++
        Complexity.encodeWord F.clauses.length ++ body F := by
  simp only [Complexity.formulaBits, Complexity.formulaWords, Complexity.encodeWords_append,
    Complexity.encodeWords, List.append_nil,
    BinaryOccurrenceRename.renamed_variable_count,
    BinaryOccurrenceRename.renamed_clause_count, encoded_body, List.append_assoc]

end PerfectCompleteness.BinaryRenameWords

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Reduction_MachineSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A certified machine for fixed symbol substitution

For a fixed table `emit : Bool → List Bool`, this actual finite TM2 machine
produces `(input.flatMap emit).reverse` in exactly `2 * input.length + 1`
transitions. It has one input-pop transition and one literal-emission transition
per input symbol, followed by the final empty pop. Literal emission is a fixed
finite statement; its maximum number of pushes depends only on `emit`.

This is a machine primitive, not a runtime theorem for the Unique Games reduction.
-/

namespace UniqueGamesTheorem.Reduction.MachineSubstitution

open Turing

open UniqueGamesTheorem.Foundations.Complexity

section PushWord

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K]

/-- Push a fixed word in its listed order, then execute the continuation. -/
def pushWord (dst : K) : List (Γ dst) → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | [], continuation => continuation
  | symbol :: word, continuation =>
      .push dst (fun _ => symbol) (pushWord dst word continuation)

/-- Literal pushes preserve the state and every other tape. -/
theorem stepAux_pushWord (dst : K) (word : List (Γ dst))
    (continuation : TM2.Stmt Γ Λ σ) (state : σ) (tapes : ∀ k, List (Γ k)) :
    TM2.stepAux (pushWord dst word continuation) state tapes =
      TM2.stepAux continuation state
        (Function.update tapes dst (word.reverse ++ tapes dst)) := by
  induction word generalizing tapes with
  | nil => simp [pushWord]
  | cons symbol word ih =>
    simp only [pushWord, TM2.stepAux]
    rw [ih]
    simp only [Function.update_self, Function.update_idem, List.reverse_cons,
      List.append_assoc, List.singleton_append]

end PushWord

end UniqueGamesTheorem.Reduction.MachineSubstitution

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Machines_GraphCounterStartLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineCompare.compareInTime_steps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual archive-copy and unary-header addition before the embedded logarithm
machine. The two header values stay on tapes; they never enter finite control. -/

/-! A complete finite machine adding the actual logarithmic graph-round count
as a unary prefix, preserving every bit of the original validated graph table. -/

/-! Generic placement of the odometer-digit initialization used in
`Hastad.SourceLoopInit`. This extracts its seed/copy/trim scheme from the
formula/header parser: the actual checked copy loop preserves the radix and
scratch, and a single positive-unary pop leaves the remaining count.
The finite program depends on the fixed digit width, not on the radix value. -/

/-!
A concrete sequential composition of two finite TM2 programs. The first output
is transferred to a temporary stack and then to the second input. Both loops
execute actual transitions and reset their shared register on exit. Static
renaming changes neither a stack word nor the number of executed transitions.
-/

namespace UniqueGamesTheorem.Foundations.Complexity.MachineSequential

open Turing

abbrev Tape (first second : FinTM2) := first.K ⊕ (second.K ⊕ Unit)
abbrev Symbols (first second : FinTM2) : Tape first second → Type :=
  MachineEmbedding.Alphabet first.Γ
    (MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
abbrev Label (first second : FinTM2) := first.Λ ⊕ (Bool ⊕ second.Λ)
abbrev Register (second : FinTM2) := Option (second.Γ second.k₀)
abbrev State (first second : FinTM2) := (first.σ × second.σ) × Register second

def firstStates (first second : FinTM2) :
    first.σ × (second.σ × Register second) ≃ State first second where
  toFun st := ((st.1, st.2.1), st.2.2)
  invFun st := (st.1.1, (st.1.2, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondStates (first second : FinTM2) :
    second.σ × (first.σ × Register second) ≃ State first second where
  toFun st := ((st.2.1, st.1), st.2.2)
  invFun st := (st.1.2, (st.1.1, st.2))
  left_inv _ := rfl
  right_inv _ := rfl

def secondLabels (first second : FinTM2) :
    second.Λ ⊕ (Bool ⊕ first.Λ) → Label first second
  | .inl label => .inr (.inr label)
  | .inr (.inl bit) => .inr (.inl bit)
  | .inr (.inr label) => .inl label

def bridgeLabel (first second : FinTM2) (bit : Bool) : Label first second :=
  .inr (.inl bit)

def firstStatement (first second : FinTM2) (q : first.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement id (firstStates first second)
    (MachineEmbedding.statement (some (bridgeLabel first second false)) q)

def secondStatement (first second : FinTM2) (q : second.Stmt) :
    TM2.Stmt (Symbols first second) (Label first second) (State first second) :=
  MachineControl.statement (secondLabels first second) (secondStates first second)
    (MachineStackSwap.statement
      (MachineEmbedding.statement
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none q))

def program (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) :
    Label first second → TM2.Stmt (Symbols first second) (Label first second)
      (State first second)
  | .inl label => firstStatement first second (first.m label)
  | .inr (.inr label) => secondStatement first second (second.m label)
  | .inr (.inl false) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inl first.k₁) (.inr (.inr ())) relabel fallback
        (bridgeLabel first second false) (some (bridgeLabel first second true))
  | .inr (.inl true) =>
      Reduction.MachineTransfer.loopAt (Γ := Symbols first second)
        (.inr (.inr ())) (.inr (.inl second.k₀)) id fallback
        (bridgeLabel first second true) (some (.inr (.inr second.main)))

def machine (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) : FinTM2 where
  K := Tape first second
  kFin := by
    letI := first.kFin
    letI := second.kFin
    exact inferInstanceAs (Fintype (first.K ⊕ (second.K ⊕ Unit)))
  k₀ := .inl first.k₀
  k₁ := .inr (.inl second.k₁)
  Γ := Symbols first second
  Λ := Label first second
  ΛFin := by
    letI := first.ΛFin
    letI := second.ΛFin
    exact inferInstanceAs (Fintype (first.Λ ⊕ (Bool ⊕ second.Λ)))
  main := .inl first.main
  σ := State first second
  σFin := by
    letI := first.σFin
    letI := second.σFin
    letI := second.Γk₀Fin
    exact inferInstanceAs (Fintype ((first.σ × second.σ) × Option (second.Γ second.k₀)))
  initialState := ((first.initialState, second.initialState), none)
  Γk₀Fin := first.Γk₀Fin
  m := program first second relabel fallback

def firstConfiguration (first second : FinTM2) (c : first.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration id (firstStates first second)
    (MachineEmbedding.configuration (some (bridgeLabel first second false))
      (second.initialState, (none : Register second)) (fun _ => []) c)

def secondConfiguration (first second : FinTM2) (c : second.Cfg) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  MachineControl.configuration (secondLabels first second) (secondStates first second)
    (MachineStackSwap.configuration
      (MachineEmbedding.configuration
        (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
        (Λextra := Bool ⊕ first.Λ) none
        (first.initialState, (none : Register second)) (fun _ => []) c))

theorem firstStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : first.Cfg)
    (transition : first.step a = some b) :
    (machine first second relabel fallback).step (firstConfiguration first second a) =
      some (firstConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement id (firstStates first second)
          (MachineEmbedding.statement (some (bridgeLabel first second false)) (first.m label)))
        ((firstStates first second) (state, (second.initialState, none)))
        (MachineEmbedding.tapes tapes (fun _ => []))) = _
      have controlled := MachineControl.stepAux_simulation id (firstStates first second)
        (MachineEmbedding.statement
          (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
          (some (bridgeLabel first second false)) (first.m label))
        (state, (second.initialState, none)) (MachineEmbedding.tapes tapes (fun _ => []))
      have embedded := MachineEmbedding.stepAux_simulation
        (Δ := MachineEmbedding.Alphabet second.Γ (fun _ : Unit => second.Γ second.k₀))
        (some (bridgeLabel first second false)) (second.initialState, (none : Register second))
        (fun _ => []) (first.m label) state tapes
      exact congrArg some (controlled.trans
        (congrArg (MachineControl.configuration id (firstStates first second)) embedded))

theorem secondStep (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (a b : second.Cfg)
    (transition : second.step a = some b) :
    (machine first second relabel fallback).step (secondConfiguration first second a) =
      some (secondConfiguration first second b) := by
  cases a with
  | mk label state tapes =>
    cases label with
    | none => cases transition
    | some label =>
      have hb := Option.some.inj transition
      subst b
      change some (TM2.stepAux
        (MachineControl.statement (secondLabels first second) (secondStates first second)
          (MachineStackSwap.statement
            (MachineEmbedding.statement
              (Δ := MachineEmbedding.Alphabet first.Γ (fun _ : Unit => second.Γ second.k₀))
              (Λextra := Bool ⊕ first.Λ) none (second.m label))))
        ((secondStates first second) (state, (first.initialState, none)))
        (MachineStackSwap.tapes (MachineEmbedding.tapes tapes (fun _ => [])))) = _
      rw [MachineControl.stepAux_simulation, MachineStackSwap.stepAux_simulation,
        MachineEmbedding.stepAux_simulation]
      rfl

theorem firstConfiguration_init (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (input : List (first.Γ first.k₀)) :
    firstConfiguration first second (initList first input) =
      initList (machine first second relabel fallback) input := by
  unfold firstConfiguration MachineControl.configuration MachineEmbedding.configuration initList
  congr 1
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₀
    · subst k
      simp [machine, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineEmbedding.tapes, h]
  · simp [machine, MachineEmbedding.tapes]
  · simp [machine, MachineEmbedding.tapes]

theorem secondConfiguration_halt (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (output : List (second.Γ second.k₁)) :
    secondConfiguration first second (haltList second output) =
      haltList (machine first second relabel fallback) output := by
  unfold secondConfiguration MachineControl.configuration MachineStackSwap.configuration
    MachineEmbedding.configuration haltList
  congr 1
  funext k
  rcases k with k | k | k
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
  · by_cases h : k = second.k₁
    · subst k
      simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]
      rfl
    · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes, h]
  · simp [machine, MachineStackSwap.tapes, MachineEmbedding.tapes]

def temporaryTapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    ∀ k, List (Symbols first second k)
  | .inl _ => []
  | .inr (.inl _) => []
  | .inr (.inr _) => word

def temporaryConfiguration (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    TM2.Cfg (Symbols first second) (Label first second) (State first second) :=
  ⟨some (bridgeLabel first second true),
    ((first.initialState, second.initialState), none), temporaryTapes first second word⟩

theorem firstTransfer_tapes (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    Reduction.MachineTransfer.tapesAt (.inl first.k₁) (.inr (.inr ()))
      (firstConfiguration first second (haltList first word)).stk [] (word.reverse.map relabel) =
        temporaryTapes first second (word.reverse.map relabel) := by
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₁
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
        MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes,
        haltList, h]
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
      MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]

theorem secondTransfer_tapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols first second)
      (.inr (.inr ())) (.inr (.inl second.k₀))
      (temporaryTapes first second word) [] word.reverse =
        (secondConfiguration first second (initList second word.reverse)).stk := by
  funext k
  rcases k with k | k | k
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]
  · by_cases h : k = second.k₀
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList, h]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]

def firstTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (first.Γ first.k₁)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (firstConfiguration first second (haltList first word))
      (some (temporaryConfiguration first second (word.reverse.map relabel)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inl first.k₁ : Tape first second) (.inr (.inr ())) (by intro h; cases h)
    relabel fallback (bridgeLabel first second false)
    (some (bridgeLabel first second true)) (program first second relabel fallback) rfl
    (firstConfiguration first second (haltList first word)).stk
    (first.initialState, second.initialState) none
  have inputTape : (firstConfiguration first second (haltList first word)).stk (.inl first.k₁) =
      word := by simp [firstConfiguration, MachineControl.configuration,
        MachineEmbedding.configuration, MachineEmbedding.tapes, haltList]
  have outputTape :
      (firstConfiguration first second (haltList first word)).stk (.inr (.inr ())) = [] := rfl
  rw [inputTape, outputTape, List.append_nil, firstTransfer_tapes] at run
  exact run

def secondTransfer (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀) (word : List (second.Γ second.k₀)) :
    StateTransition.EvalsToInTime (machine first second relabel fallback).step
      (temporaryConfiguration first second word)
      (some (secondConfiguration first second (initList second word.reverse)))
      (word.length + 1) := by
  let run := Reduction.MachineTransfer.transferAtInTime
    (.inr (.inr ()) : Tape first second) (.inr (.inl second.k₀)) (by intro h; cases h)
    id fallback (bridgeLabel first second true) (some (.inr (.inr second.main)))
    (program first second relabel fallback) rfl (temporaryTapes first second word)
    (first.initialState, second.initialState) none
  simp only [temporaryTapes, List.map_id, List.append_nil] at run
  rw [secondTransfer_tapes] at run
  exact run

/-- An execution of each component yields an actual execution of the combined
machine. The two transfer loops add exactly twice the intermediate length plus two. -/
def execute (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (fallback : second.Γ second.k₀)
    (input : List (first.Γ first.k₀)) (middle : List (first.Γ first.k₁))
    (output : List (second.Γ second.k₁)) (firstBudget secondBudget : Nat)
    (runFirst : TM2OutputsInTime first input (some middle) firstBudget)
    (runSecond : TM2OutputsInTime second (middle.map relabel) (some output) secondBudget) :
    TM2OutputsInTime (machine first second relabel fallback) input (some output)
      (firstBudget + 2 * (middle.length + 1) + secondBudget) := by
  let start := MachineComposition.liftExecutionInTime first.step
    (machine first second relabel fallback).step (firstConfiguration first second)
    (firstStep first second relabel fallback) runFirst
  let bridge₁ := firstTransfer first second relabel fallback middle
  have bridge₂ := secondTransfer first second relabel fallback (middle.reverse.map relabel)
  have reversal : (middle.reverse.map relabel).reverse = middle.map relabel := by
    simp only [List.map_reverse, List.reverse_reverse]
  rw [reversal] at bridge₂
  simp only [List.length_map, List.length_reverse] at bridge₂
  let finish := MachineComposition.liftExecutionInTime second.step
    (machine first second relabel fallback).step (secondConfiguration first second)
    (secondStep first second relabel fallback) runSecond
  let phase₁₂ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ start bridge₁
  let phase₁₂₃ := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂ bridge₂
  have full := StateTransition.EvalsToInTime.trans _ _ _ _ _ _ phase₁₂₃ finish
  rw [firstConfiguration_init, secondConfiguration_halt] at full
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by have h := full.steps_le_m; omega
  }

/-- General sequential composition with an explicit symbol of the intermediate
alphabet to totalize the bridge's unused empty-register expression. Its time
polynomial uses the transition-derived output-length bound of the first machine. -/
noncomputable def compose {α β γ αΓ βΓ γΓ : Type}
    {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) (fallback : βΓ) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) := by
  let relabel : first.tm.Γ first.tm.k₁ → second.tm.Γ second.tm.k₀ :=
    fun symbol => second.inputAlphabet.symm (first.outputAlphabet symbol)
  let defaultSymbol := second.inputAlphabet.symm fallback
  let intermediate : Polynomial Nat := Polynomial.X +
    Polynomial.C (Runtime.programPushBound first.tm) * first.time
  refine {
    tm := machine first.tm second.tm relabel defaultSymbol
    inputAlphabet := first.inputAlphabet
    outputAlphabet := second.outputAlphabet
    time := MachineComposition.compositionPolynomial first.time second.time intermediate
    outputsFun := ?_
  }
  intro a
  let input := (ea a).map first.inputAlphabet.invFun
  let middle := (eb (f a)).map first.outputAlphabet.invFun
  let output := (ec (g (f a))).map second.outputAlphabet.invFun
  have handoff : middle.map relabel = (eb (f a)).map second.inputAlphabet.invFun := by
    dsimp only [middle, relabel]
    simp only [List.map_map]
    apply List.map_congr_left
    intro symbol _
    exact congrArg second.inputAlphabet.symm (first.outputAlphabet.apply_symm_apply symbol)
  have runSecond : TM2OutputsInTime second.tm (middle.map relabel) (some output)
      (second.time.eval (eb (f a)).length) := by
    rw [handoff]
    exact second.outputsFun (f a)
  have full := execute first.tm second.tm relabel defaultSymbol input middle output
    (first.time.eval (ea a).length) (second.time.eval (eb (f a)).length)
    (first.outputsFun a) runSecond
  have intermediateBound : (eb (f a)).length ≤ intermediate.eval (ea a).length :=
    Runtime.encodedOutputLength first a
  have totalBound := MachineComposition.compositionBudget_le first.time second.time
    intermediate (ea a).length (eb (f a)).length intermediateBound
  have middleLength : middle.length = (eb (f a)).length := by simp only [middle, List.length_map]
  exact {
    toEvalsTo := full.toEvalsTo
    steps_le_m := by
      apply Nat.le_trans full.steps_le_m
      simpa only [middleLength] using totalBound
  }

noncomputable def composeBits {α β γ : Type}
    {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
    {f : α → β} {g : β → γ}
    (first : TM2ComputableInPolyTime ea eb f)
    (second : TM2ComputableInPolyTime eb ec g) :
    TM2ComputableInPolyTime ea ec (fun a => g (f a)) :=
  compose first second false

end UniqueGamesTheorem.Foundations.Complexity.MachineSequential

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryRenameMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryRenameMachine


open Turing UniqueGamesTheorem.Foundations
open Complexity Complexity.MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer

abbrev Tape := Fin 12
abbrev Alphabet (_ : Tape) := Bool
abbrev State := BinaryRenameLoop.State Unit

inductive Label
  | copyOut | copyBack
  | loop (label : BinaryRenameLoop.Label)
  | restore | clauseStart | clauseLoop | variableStart | variableLoop
  | cleanup | reject
  deriving DecidableEq, Fintype

def loopTapes : Fin 11 → Tape := Fin.castSucc

theorem loopTapes_injective : Function.Injective loopTapes := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Tape => k.val) h

def program : Label → TM2.Stmt Alphabet Label State
  | .copyOut => loopAt 1 6 id false .copyOut (some .copyBack)
  | .copyBack => MachineCopy.forkLoop 6 1 0 false .copyBack (some (.loop .entry))
  | .loop label => BinaryRenameLoop.instruction loopTapes Label.loop
      (some .restore) (some .reject) label
  | .restore => loopAt 8 11 id false .restore (some .clauseStart)
  | .clauseStart => BinaryHeaderMachine.delimiter 11 .clauseLoop
  | .clauseLoop => loopAt 10 11 id false .clauseLoop (some .variableStart)
  | .variableStart => BinaryHeaderMachine.delimiter 11 .variableLoop
  | .variableLoop => loopAt 9 11 id false .variableLoop (some .cleanup)
  | .cleanup => MachineDrain.drain 1 .cleanup none
  | .reject => .halt

abbrev machine : FinTM2 where
  K := Tape
  k₀ := 1
  k₁ := 11
  Γ := Alphabet
  Λ := Label
  main := .copyOut
  σ := State
  initialState := BinaryRenameLoop.clean () 0
  m := program

def tapes (permanent cursor reversed variableCounter clauseCounter output : List Bool) :
    Tape → List Bool := fun k =>
  if k = 0 then cursor
  else if k = 1 then permanent
  else if k = 8 then reversed
  else if k = 9 then variableCounter
  else if k = 10 then clauseCounter
  else if k = 11 then output
  else []

def cfg (label : Option Label)
    (permanent cursor reversed variableCounter clauseCounter output : List Bool) : machine.Cfg :=
  ⟨label, BinaryRenameLoop.clean () 0,
    tapes permanent cursor reversed variableCounter clauseCounter output⟩

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .copyOut) input [] [] [] [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] [] [] [] [] output := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> simp [tapes, machine]

theorem copyTrace (input : List Bool) :
    (advance machine.step)^[2 * (input.length + 1)]
      (some (cfg (some .copyOut) input [] [] [] [] [])) =
      some (cfg (some (.loop .entry)) input input [] [] [] []) := by
  have updated : Function.update (tapes input [] [] [] [] []) 0 input =
      tapes input input [] [] [] [] := by
    funext k
    fin_cases k <;> simp [tapes]
  have h := MachineCopy.copyTrace (1 : Tape) 0 6 (by decide) (by decide) (by decide)
    false .copyOut .copyBack (some (.loop .entry)) program rfl rfl
    (tapes input [] [] [] [] []) (by simp [tapes])
    (BinaryRenameLoop.clean () 0).1 none
  have first : tapes input [] [] [] [] [] 1 = input := rfl
  have second : tapes input [] [] [] [] [] 0 = [] := rfl
  rw [first, second, List.append_nil, updated] at h
  exact h

theorem restoreTrace (input body variableCounter clauseCounter : List Bool) :
    (advance machine.step)^[body.length + 1]
      (some (cfg (some .restore) input [] body.reverse variableCounter clauseCounter [])) =
      some (cfg (some .clauseStart) input [] [] variableCounter clauseCounter body) := by
  change (nextAt (11 : Tape) program)^[body.length + 1]
    (some (cfg (some .restore) input [] body.reverse variableCounter clauseCounter [])) = _
  have updated : tapesAt (8 : Tape) 11
      (tapes input [] body.reverse variableCounter clauseCounter []) [] body =
      tapes input [] [] variableCounter clauseCounter body := by
    funext k
    fin_cases k <;> simp [tapesAt, tapes]
  have h := transferAt_fromTapes (Γ := Alphabet) (8 : Tape) 11 (by decide) id false
    .restore (some .clauseStart) program rfl
    (tapes input [] body.reverse variableCounter clauseCounter [])
    (BinaryRenameLoop.clean () 0).1 none
  have source : tapes input [] body.reverse variableCounter clauseCounter [] 8 = body.reverse := rfl
  have output : tapes input [] body.reverse variableCounter clauseCounter [] 11 = [] := rfl
  rw [source, output, List.length_reverse, List.reverse_reverse, List.map_id_fun,
    List.append_nil, id_eq, updated] at h
  exact h

theorem headerTrace (input body : List Bool) (n m : Nat) :
    (advance machine.step)^[n + m + 4]
      (some (cfg (some .clauseStart) input [] []
        (List.replicate n true) (List.replicate m true) body)) =
      some (cfg (some .cleanup) input [] [] [] []
        (encodeWord n ++ encodeWord m ++ body)) := by
  change (advance (TM2.step program))^[n + m + 4]
    (some ⟨some .clauseStart, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] (List.replicate n true) (List.replicate m true) body⟩) =
    some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] (encodeWord n ++ encodeWord m ++ body)⟩
  have updated (variableWord clauses output : List Bool) :
      BinaryHeaderMachine.tapes (9 : Tape) 10 11 (tapes input [] [] [] [] [])
        variableWord clauses output = tapes input [] [] variableWord clauses output := by
    funext k
    fin_cases k <;> simp [BinaryHeaderMachine.tapes, tapes]
  have h := BinaryHeaderMachine.headerTrace (9 : Tape) 10 11
    (by decide) (by decide) (by decide)
    .clauseStart .clauseLoop .variableStart .variableLoop (some .cleanup) program
    rfl rfl rfl rfl (tapes input [] [] [] [] [])
    (BinaryRenameLoop.clean () 0).1 n m body none
  simp only [updated] at h
  exact h

theorem cleanupTrace (input output : List Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .cleanup) input [] [] [] [] output)) =
      some (cfg none [] [] [] [] [] output) := by
  change (advance (TM2.step program))^[input.length + 1]
    (some ⟨some .cleanup, ((BinaryRenameLoop.clean () 0).1, none),
      tapes input [] [] [] [] output⟩) =
    some ⟨none, ((BinaryRenameLoop.clean () 0).1, none), tapes [] [] [] [] [] output⟩
  have updated (word : List Bool) :
      Function.update (tapes [] [] [] [] [] output) 1 word =
        tapes word [] [] [] [] output := by
    funext k
    fin_cases k <;> simp [tapes]
  have h := MachineDrain.drainTrace (1 : Tape) .cleanup none program rfl
    (tapes [] [] [] [] [] output) input (BinaryRenameLoop.clean () 0).1 none
  simp only [updated] at h
  exact h

theorem outputBody_eq (formula : BinaryFormula.Formula) :
    BinaryRenameLoop.outputBody (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) = BinaryRenameWords.body formula := by
  change ((BinaryRenameWords.literals formula.clauses).map BinaryRenameWords.token).flatMap
    (fun t => BinaryLiteralMachine.outputWord (BinaryRenameWords.tokens formula.clauses)
      t.2 t.1) = (BinaryRenameWords.literals formula.clauses).flatMap
        (BinaryRenameWords.outputLiteral (BinaryFormula.sourceNames formula))
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro literal _
  simp only [BinaryRenameWords.token, BinaryLiteralMachine.outputWord,
    BinaryLiteralMachine.index, BinaryLiteralMachine.signWord,
    BinaryRenameWords.payload_index, BinaryRenameWords.outputLiteral]
  rfl

theorem loopTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
        (BinaryRenameWords.tokens formula.clauses)]
      (some (cfg (some (.loop .entry)) (BinaryTokenMachine.tokens formula.clauses)
        (BinaryTokenMachine.tokens formula.clauses) [] [] [] [])) =
      some (cfg (some .restore) (BinaryTokenMachine.tokens formula.clauses) []
        (BinaryRenameWords.body formula).reverse (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []) := by
  change (advance (TM2.step program))^[BinaryRenameLoop.steps
      (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)]
    (some ⟨some (.loop .entry), BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) (BinaryTokenMachine.tokens formula.clauses)
        [] [] [] []⟩) =
    some ⟨some .restore, BinaryRenameLoop.clean () 0,
      tapes (BinaryTokenMachine.tokens formula.clauses) [] (BinaryRenameWords.body formula).reverse
        (List.replicate (3 * formula.clauses.length) true)
        (List.replicate formula.clauses.length true) []⟩
  let input := BinaryTokenMachine.tokens formula.clauses
  have updated (cursor output variableWord clauseWord : List Bool) :
      BinaryRenameLoop.loopTapes loopTapes (tapes input [] [] [] [] [])
        cursor output variableWord clauseWord =
      tapes input cursor output variableWord clauseWord [] := by
    funext k
    fin_cases k <;> simp [BinaryRenameLoop.loopTapes, loopTapes, tapes]
  have scratch (i : Fin 11) (lo : 2 ≤ i.val) (hi : i.val ≤ 7) :
      tapes input [] [] [] [] [] (loopTapes i) = [] := by
    have n0 : loopTapes i ≠ 0 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n1 : loopTapes i ≠ 1 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n8 : loopTapes i ≠ 8 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n9 : loopTapes i ≠ 9 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n10 : loopTapes i ≠ 10 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    have n11 : loopTapes i ≠ 11 := by intro h; have := congrArg Fin.val h; simp [loopTapes] at this; omega
    simp [tapes, n0, n1, n8, n9, n10, n11]
  have run := BinaryRenameLoop.triplesTrace loopTapes loopTapes_injective Label.loop
    (some .restore) (some .reject) program (fun _ => rfl)
    (tapes input [] [] [] [] []) ()
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    formula.clauses.length (BinaryRenameWords.tokens_length formula.clauses) [] [] []
    (BinaryRenameWords.tokens_canonical formula.clauses) (fun _ h => h)
    (by change input = _; rw [BinaryRenameWords.tokens_stream]) scratch
  simp only [updated, BinaryRenameWords.tokens_stream, outputBody_eq, List.append_nil, input] at run
  exact run

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

def steps (formula : BinaryFormula.Formula) : Nat :=
  2 * ((BinaryTokenMachine.tokens formula.clauses).length + 1) +
    BinaryRenameLoop.steps (BinaryRenameWords.tokens formula.clauses)
      (BinaryRenameWords.tokens formula.clauses) +
    ((BinaryRenameWords.body formula).length + 1) + (4 * formula.clauses.length + 4) +
    ((BinaryTokenMachine.tokens formula.clauses).length + 1)

theorem renameTrace (formula : BinaryFormula.Formula) :
    (advance machine.step)^[steps formula]
      (some (initList machine (BinaryTokenMachine.tokens formula.clauses))) =
      some (haltList machine (formulaBits (BinaryOccurrenceRename.renamed formula))) := by
  have first := copyTrace (BinaryTokenMachine.tokens formula.clauses)
  have second := loopTrace formula
  have third := restoreTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (List.replicate (3 * formula.clauses.length) true)
    (List.replicate formula.clauses.length true)
  have fourth := headerTrace (BinaryTokenMachine.tokens formula.clauses)
    (BinaryRenameWords.body formula) (3 * formula.clauses.length) formula.clauses.length
  have fifth := cleanupTrace (BinaryTokenMachine.tokens formula.clauses)
    (encodeWord (3 * formula.clauses.length) ++ encodeWord formula.clauses.length ++
      BinaryRenameWords.body formula)
  have full := joinTrace (joinTrace (joinTrace (joinTrace first second) third) fourth) fifth
  have count : 3 * formula.clauses.length + formula.clauses.length + 4 =
      4 * formula.clauses.length + 4 := by omega
  simpa only [steps, initList_eq, haltList_eq, BinaryRenameWords.encoded_renamed, count] using full

theorem clause_count_le_stream (formula : BinaryFormula.Formula) :
    formula.clauses.length ≤ (BinaryTokenMachine.tokens formula.clauses).length := by
  rw [BinaryTokenMachine.tokens_length]
  omega

theorem body_length_le (formula : BinaryFormula.Formula) :
    (BinaryRenameWords.body formula).length ≤
      9 * (BinaryTokenMachine.tokens formula.clauses).length ^ 2 +
        10 * (BinaryTokenMachine.tokens formula.clauses).length + 2 := by
  have initial := BinaryOccurrenceRename.renamed_encoding_bound formula
  rw [BinaryRenameWords.encoded_renamed] at initial
  simp only [List.length_append] at initial
  have count := clause_count_le_stream formula
  have square := Nat.mul_self_le_mul_self count
  nlinarith

noncomputable def timePolynomial : Polynomial Nat :=
  Polynomial.C 12 * Polynomial.X ^ 3 + Polynomial.C 35 * Polynomial.X ^ 2 +
    Polynomial.C 28 * Polynomial.X + Polynomial.C 11

theorem steps_le (formula : BinaryFormula.Formula) :
    steps formula ≤ timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length := by
  have loopBound := BinaryRenameLoop.steps_le
    (BinaryRenameWords.tokens formula.clauses) (BinaryRenameWords.tokens formula.clauses)
    (fun _ h => h)
  rw [BinaryRenameWords.tokens_stream, BinaryRenameWords.tokens_length] at loopBound
  have literalCount : 3 * formula.clauses.length ≤
      (BinaryTokenMachine.tokens formula.clauses).length := by
    rw [BinaryTokenMachine.tokens_length]
    omega
  have product := Nat.mul_le_mul_left
    (BinaryRenameLoop.perLiteralBound (BinaryTokenMachine.tokens formula.clauses).length)
    literalCount
  have output := body_length_le formula
  have count := clause_count_le_stream formula
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold steps BinaryRenameLoop.perLiteralBound at *
  nlinarith

def outputsInTime (formula : BinaryFormula.Formula) :
    TM2OutputsInTime machine (BinaryTokenMachine.tokens formula.clauses)
      (some (formulaBits (BinaryOccurrenceRename.renamed formula)))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length) where
  steps := steps formula
  evals_in_steps := renameTrace formula
  steps_le_m := steps_le formula

noncomputable def tokenComputation :
    TM2ComputableInPolyTime (fun formula : BinaryFormula.Formula =>
      BinaryTokenMachine.tokens formula.clauses) formulaBits BinaryOccurrenceRename.renamed where
  tm := machine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := timePolynomial
  outputsFun formula := by
    change TM2OutputsInTime machine ((BinaryTokenMachine.tokens formula.clauses).map id)
      (some ((formulaBits (BinaryOccurrenceRename.renamed formula)).map id))
      (timePolynomial.eval (BinaryTokenMachine.tokens formula.clauses).length)
    simpa only [List.map_id_fun, id_eq] using outputsInTime formula

noncomputable def preprocessing :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits
      (fun formula : BinaryFormula.Formula => BinaryTokenMachine.tokens formula.clauses)
      (id : BinaryFormula.Formula → BinaryFormula.Formula) where
  tm := BinaryTokenMachine.computableInPolyTime.tm
  inputAlphabet := BinaryTokenMachine.computableInPolyTime.inputAlphabet
  outputAlphabet := BinaryTokenMachine.computableInPolyTime.outputAlphabet
  time := BinaryTokenMachine.computableInPolyTime.time
  outputsFun := BinaryTokenMachine.computableInPolyTime.outputsFun

noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime BinaryEncoding.formulaBits formulaBits
      BinaryOccurrenceRename.renamed :=
  MachineSequential.composeBits preprocessing tokenComputation

end PerfectCompleteness.BinaryRenameMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryValidatorMachine
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_cons _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_length _root_.OAI.PerfectCompleteness.BinaryRenameWords.literals_nil _root_.OAI.PerfectCompleteness.BinaryRenameWords.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_cons _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_length _root_.OAI.PerfectCompleteness.BinaryTokenMachine.tokens_nil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryValidatorMachine


open BinaryEncoding BinaryFormula

inductive Mode
  | clause
  | sign (slot : Fin 3)
  | name (slot : Fin 3) (last : Bool)
  | digit (slot : Fin 3)
  | done
  | reject
  deriving DecidableEq, Fintype

def afterName (slot : Fin 3) : Mode :=
  if slot = 0 then .sign 1 else if slot = 1 then .sign 2 else .clause

def nextMode : Mode → Bool → Mode
  | .clause, true => .sign 0
  | .clause, false => .done
  | .sign slot, _ => .name slot true
  | .name slot _, true => .digit slot
  | .name slot last, false => if last then afterName slot else .reject
  | .digit slot, bit => .name slot bit
  | .done, _ => .reject
  | .reject, _ => .reject

def run : Mode → List Bool → Mode
  | mode, [] => mode
  | mode, bit :: rest => run (nextMode mode bit) rest

@[simp] theorem run_reject (input : List Bool) : run .reject input = .reject := by
  induction input with
  | nil => rfl
  | cons bit input ih => simpa only [run, nextMode] using ih

theorem run_done_iff (input : List Bool) : run .done input = .done ↔ input = [] := by
  cases input with
  | nil => simp [run]
  | cons bit rest => simp [run, nextMode]

theorem finalDigit_true_iff (bits : List Bool) :
    BinaryNameMachine.finalDigit bits (some true) = some true ↔
      BinaryNameMachine.canonical bits = true := by
  cases bits with
  | nil => simp [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
  | cons bit bits =>
      simp only [BinaryNameMachine.finalDigit, BinaryNameMachine.canonical]
      have hsome : ∀ (ds : List Bool) (b : Bool),
          ∃ last, BinaryNameMachine.finalDigit ds (some b) = some last := by
        intro ds
        induction ds with
        | nil => intro b; exact ⟨b, rfl⟩
        | cons d ds ih => intro b; exact ih d
      obtain ⟨last, hlast⟩ := hsome bits bit
      rw [hlast]
      simp

theorem run_frame (slot : Fin 3) (bits rest : List Bool) (last : Bool)
    (valid : BinaryNameMachine.finalDigit bits (some last) = some true) :
    run (.name slot last) (frame bits ++ rest) = run (afterName slot) rest := by
  induction bits generalizing last with
  | nil =>
      have hlast : last = true := by simpa [BinaryNameMachine.finalDigit] using valid
      subst last
      simp [frame, run, nextMode]
  | cons bit bits ih =>
      have hvalid : BinaryNameMachine.finalDigit bits (some bit) = some true := valid
      simpa only [frame, List.cons_append, run, nextMode] using ih bit hvalid

theorem run_name (slot : Fin 3) (name : Nat) (rest : List Bool) :
    run (.name slot true) (nameBits name ++ rest) = run (afterName slot) rest := by
  apply run_frame
  exact (finalDigit_true_iff name.bits).mpr (BinaryParsing.canonical_nat_bits name)

theorem run_literal (slot : Fin 3) (literal : Literal) (rest : List Bool) :
    run (.sign slot) (literalBits literal ++ rest) = run (afterName slot) rest := by
  simpa only [literalBits, List.cons_append, run, nextMode] using
    run_name slot literal.name rest

theorem run_clause (clause : Clause) (rest : List Bool) :
    run (.sign 0) (clauseBits clause ++ rest) = run .clause rest := by
  simp [clauseBits, List.append_assoc, run_literal, afterName]

theorem run_clauses (clauses : List Clause) : run .clause (clausesBits clauses) = .done := by
  induction clauses with
  | nil => rfl
  | cons clause clauses ih =>
      change run (.sign 0) (clauseBits clause ++ clausesBits clauses) = .done
      rw [run_clause, ih]

theorem run_formula (formula : Formula) : run .clause (formulaBits formula) = .done :=
  run_clauses formula.clauses

open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition

end PerfectCompleteness.BinaryValidatorMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryTotalInputMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BinaryTotalInputMachine


open Turing
open UniqueGamesTheorem.Foundations.Complexity
open MachineComposition
open UniqueGamesTheorem.Reduction.MachineTransfer
open UniqueGamesTheorem.Reduction.MachineSubstitution
open BinaryValidatorMachine (Mode nextMode run)

inductive Label
  | scan
  | restore
  | drain
  | rejectOutput
  deriving DecidableEq

protected abbrev Label.enumList : List Label := [.scan, .restore, .drain, .rejectOutput]

protected theorem Label.enumList_nodup : Label.enumList.Nodup := by decide

instance instFintypeLabel : Fintype Label where
  elems := ⟨Label.enumList, Label.enumList_nodup⟩
  complete x := by cases x <;> decide

abbrev Alphabet (_ : Fin 3) := Bool
abbrev State := Mode × Option Bool

def rejectedWord : List Bool := BinaryEncoding.formulaBits BinaryLanguage.rejectBinary

def instruction : Label → TM2.Stmt Alphabet Label State
  | .scan =>
      .pop 0 (fun state head => (state.1, head))
        (.branch (fun state => state.2.isSome)
          (.push 2 (fun state => state.2.getD false)
            (.load (fun state => (nextMode state.1 (state.2.getD false), none))
              (.goto fun _ => .scan)))
          (.branch (fun state => decide (state.1 = .done))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .restore))
            (.load (fun _ => (.clause, none)) (.goto fun _ => .drain))))
  | .restore => loopAt 2 1 id false .restore none
  | .drain => MachineDrain.drain 2 .drain (some .rejectOutput)
  | .rejectOutput => pushWord 1 rejectedWord.reverse .halt

abbrev machine : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ := Alphabet
  Λ := Label
  main := .scan
  σ := State
  initialState := (.clause, none)
  m := instruction

def tapes (input output saved : List Bool) : Fin 3 → List Bool
  | 0 => input
  | 1 => output
  | _ => saved

def cfg (label : Option Label) (input output saved : List Bool) (mode : Mode := .clause)
    (register : Option Bool := none) : machine.Cfg :=
  ⟨label, (mode, register), tapes input output saved⟩

@[simp] theorem tapes_input (input output saved : List Bool) :
    tapes input output saved 0 = input := rfl

@[simp] theorem tapes_output (input output saved : List Bool) :
    tapes input output saved 1 = output := rfl

@[simp] theorem tapes_saved (input output saved : List Bool) :
    tapes input output saved 2 = saved := rfl

theorem update_input (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 0 replacement =
      tapes replacement output saved := by
  funext k
  fin_cases k <;> rfl

theorem update_output (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 1 replacement =
      tapes input replacement saved := by
  funext k
  fin_cases k <;> rfl

theorem update_saved (input output saved replacement : List Bool) :
    Function.update (tapes input output saved) 2 replacement =
      tapes input output replacement := by
  funext k
  fin_cases k <;> rfl

def afterScan (mode : Mode) : Label := if mode = .done then .restore else .drain

theorem step_scan_empty (output saved : List Bool) (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) [] output saved mode register) =
      some (cfg (some (afterScan mode)) [] output saved) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  by_cases accepted : mode = .done <;>
    simp [instruction, cfg, TM2.stepAux, update_input, afterScan, accepted] <;> rfl

theorem step_scan_cons (bit : Bool) (input output saved : List Bool)
    (mode : Mode) (register : Option Bool) :
    machine.step (cfg (some .scan) (bit :: input) output saved mode register) =
      some (cfg (some .scan) input output (bit :: saved) (nextMode mode bit)) := by
  change some (TM2.stepAux (instruction .scan) _ _) = _
  simp [instruction, cfg, TM2.stepAux, update_input, update_saved]
  rfl

theorem scanTrace (input output saved : List Bool) (mode : Mode) (register : Option Bool) :
    (advance machine.step)^[input.length + 1]
      (some (cfg (some .scan) input output saved mode register)) =
      some (cfg (some (afterScan (run mode input))) [] output (input.reverse ++ saved)) := by
  induction input generalizing saved mode register with
  | nil =>
      simpa only [List.length_nil, Nat.zero_add, Function.iterate_one,
        advance_some, run, List.reverse_nil, List.nil_append] using
          step_scan_empty output saved mode register
  | cons bit input ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      simp only [advance_some]
      rw [step_scan_cons]
      simpa only [run, List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: saved) (nextMode mode bit) none

theorem restoreTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .restore) [] output saved .clause register)) =
      some (cfg none [] (saved.reverse ++ output) []) := by
  change (nextAt (1 : Fin 3) instruction)^[saved.length + 1]
    (some ⟨some .restore, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨none, (Mode.clause, none), tapes [] (saved.reverse ++ output) []⟩
  have trace := transferAt_steps (2 : Fin 3) 1 (by decide) id false .restore none
    instruction rfl (tapes [] [] []) saved output Mode.clause register
  simpa only [tapesAt, update_saved, update_output,
    List.map_id_fun, id_eq] using trace

theorem drainTrace (saved output : List Bool) (register : Option Bool) :
    (advance machine.step)^[saved.length + 1]
      (some (cfg (some .drain) [] output saved .clause register)) =
      some (cfg (some .rejectOutput) [] output []) := by
  change (advance (TM2.step instruction))^[saved.length + 1]
    (some ⟨some .drain, (Mode.clause, register), tapes [] output saved⟩) =
    some ⟨some .rejectOutput, (Mode.clause, none), tapes [] output []⟩
  have trace := MachineDrain.drainTrace (2 : Fin 3) .drain (some .rejectOutput)
    instruction rfl (tapes [] output []) saved Mode.clause register
  simpa only [update_saved] using trace

theorem step_rejectOutput (output : List Bool) :
    machine.step (cfg (some .rejectOutput) [] output []) =
      some (cfg none [] (rejectedWord ++ output) []) := by
  change some (TM2.stepAux
    (pushWord (Γ := Alphabet) (Λ := Label) (σ := State)
      (1 : Fin 3) rejectedWord.reverse .halt) _ _) = _
  rw [stepAux_pushWord]
  simp only [cfg, List.reverse_reverse, tapes_output, update_output, TM2.stepAux]
  rfl

theorem joinTrace {X : Type*} {f : X → X} {a b c : X} {n m : Nat}
    (first : f^[n] a = b) (second : f^[m] b = c) : f^[n + m] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, first, second]

theorem acceptedTrace (input : List Bool) (accepted : run .clause input = .done) :
    (advance machine.step)^[2 * input.length + 2]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] input []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, accepted, ↓reduceIte, List.append_nil] at first
  have second := restoreTrace input.reverse [] none
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at second
  have time : 2 * input.length + 2 = (input.length + 1) + (input.length + 1) := by omega
  rw [time]
  exact joinTrace first second

theorem rejectedTrace (input : List Bool) (rejected : run .clause input ≠ .done) :
    (advance machine.step)^[2 * input.length + 3]
      (some (cfg (some .scan) input [] [])) = some (cfg none [] rejectedWord []) := by
  have first := scanTrace input [] [] .clause none
  simp only [afterScan, rejected, ↓reduceIte, List.append_nil] at first
  have second := drainTrace input.reverse [] none
  simp only [List.length_reverse] at second
  have third : (advance machine.step)^[1]
      (some (cfg (some .rejectOutput) [] [] [])) = some (cfg none [] rejectedWord []) := by
    simpa only [Function.iterate_one, advance_some, List.append_nil] using
      step_rejectOutput []
  have time : 2 * input.length + 3 = (input.length + 1) + (input.length + 1) + 1 := by omega
  rw [time]
  exact joinTrace (joinTrace first second) third

theorem initList_eq (input : List Bool) :
    initList machine input = cfg (some .scan) input [] [] := by
  unfold initList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem haltList_eq (output : List Bool) :
    haltList machine output = cfg none [] output [] := by
  unfold haltList cfg
  congr 1
  funext k
  fin_cases k <;> rfl

def steps (input : List Bool) : Nat :=
  if run .clause input = .done then 2 * input.length + 2 else 2 * input.length + 3

theorem steps_le (input : List Bool) : steps input ≤ 2 * input.length + 3 := by
  unfold steps
  split <;> omega

end PerfectCompleteness.BinaryTotalInputMachine

end OAI
end


