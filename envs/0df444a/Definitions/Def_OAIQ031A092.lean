-- Prove2me | Definitions.Def_OAIQ031A092
-- name    : OAIQ031A092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:31:14.248924+00:00
-- url     : https://prove2.me/theorems/9c06e753-6123-48bf-a9ae-12a6a24cfb73
-- title:
--   Definitions bundle OAIQ031A092 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 15 definitions, 1 instance and 14 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.twistedEquiv`, `OAI.ArExplicit.CompleteComparison.syzygyInclusion`, `OAI.ArExplicit.Resolution.homERightLinearEquiv`, `OAI.ArExplicit.T.B`, `OAI.ArExplicit.T.barB`, `OAI.ArExplicit.T.barDb`, `OAI.ArExplicit.T.bimoduleTwistedDifferential`, `OAI.ArExplicit.T.bimoduleTwistedTerm`, `OAI.ArExplicit.T.bimoduleTwoConeData`, `OAI.ArExplicit.T.firstTail`, `OAI.ArExplicit.T.fourthSyzygy`, `OAI.ArExplicit.T.pB`, `OAI.ArExplicit.T.tensorHighB`, `OAI.ArExplicit.TwoCone.restrictedHighLift`, `OAI.ArExplicit.TwoCone.tailMap`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Bar_BarCasimir`, `AuslanderReiten_Bar_TBarHomotopies`, `AuslanderReiten_Bar_TBarLift`, `AuslanderReiten_Bar_TwistedBar`, `AuslanderReiten_Cocycles_TwistedBoundary`, `AuslanderReiten_Cocycles_TwistedBoundaryFormula`, `AuslanderReiten_Complete_CompleteStableSourceNaturality`, `AuslanderReiten_Cones_BimoduleTwoCone`, `AuslanderReiten_Cones_TwoConeTail`, `AuslanderReiten_Cones_TwoConeTailRestriction`, `AuslanderReiten_Coordinates_TensorHighLift`, `AuslanderReiten_Coordinates_TensorTailMap`, `AuslanderReiten_Duality_DualResolution`, `AuslanderReiten_Homology_TNullhomotopy`.
--
--   **Imports.** It imports the bundles `OAIQ031A077`, `OAIQ031A078` and `OAIQ031A079` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A105`, `OAIQ031A106`, `OAIQ031A109`, `OAIQ031A115` and `OAIQ031A116`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A077
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A079

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarCasimir
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

variable [CharP k 2]

theorem casimirInsertion_boundary (ξ : object k R 1) (hξ : boundary k R 0 ξ = 0)
    (n : ℕ) (x : object k R (n + 1)) :
    boundary k R (n + 1) (casimirInsertion k R ξ (n + 1) x) +
      casimirInsertion k R ξ n (boundary k R n x) = 0 := by
  induction n with
  | zero =>
    rw [casimirInsertion_boundary_zero k R ξ hξ]
    exact double_zero_p0 k _
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy =>
      simp only [map_add]
      calc
        _ = (boundary k R (n + 1 + 1) (casimirInsertion k R ξ (n + 1 + 1) x) +
          casimirInsertion k R ξ (n + 1) (boundary k R (n + 1) x)) +
          (boundary k R (n + 1 + 1) (casimirInsertion k R ξ (n + 1 + 1) y) +
          casimirInsertion k R ξ (n + 1) (boundary k R (n + 1) y)) := by abel
        _ = 0 := by rw [hx, hy, add_zero]
    | tmul a x =>
      rw [casimirInsertion_tmul, boundary_succ_tmul, boundary_succ_tmul,
        map_add, casimirInsertion_left, casimirInsertion_tmul]
      have hi := congrArg (fun z => a ⊗ₜ[k] z) (ih x)
      rw [TensorProduct.tmul_add, TensorProduct.tmul_zero] at hi
      calc
        _ = (left k R (n + 1 + 1) a (casimirInsertion k R ξ (n + 1) x) +
          left k R (n + 1 + 1) a (casimirInsertion k R ξ (n + 1) x)) +
          (a ⊗ₜ[k] boundary k R (n + 1) (casimirInsertion k R ξ (n + 1) x) +
          a ⊗ₜ[k] casimirInsertion k R ξ n (boundary k R n x)) := by abel
        _ = 0 := by rw [double_zero_p0 k, hi, add_zero]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBar
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.AbsoluteBar
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]

instance twistInvPairSymm (h : R ≃ₐ[k] R) :
    RingHomInvPair (twistEnveloping k R h).symm.toRingHom (twistEnveloping k R h).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (twistEnveloping k R h).toRingEquiv

def twistedEquiv (h : R ≃ₐ[k] R) (n : ℕ) :
    twistedObject k R h n ≃ₛₗ[(twistEnveloping k R h).toRingHom] moduleObject k R n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem twistedFree (h : R ≃ₐ[k] R) (n : ℕ) :
    Module.Free (Enveloping k R) (twistedObject k R h (n + 1)) := by
  let := free k R n
  exact Module.Free.of_equiv (twistedEquiv k R h (n + 1)).symm

theorem twistedProjective (h : R ≃ₐ[k] R) (n : ℕ) :
    Module.Projective (Enveloping k R) (twistedObject k R h (n + 1)) := by
  let := twistedFree k R h n
  exact Module.Projective.of_free

variable [CharP k 2]

theorem casimirInsertionMap_boundary (h : R ≃ₐ[k] R) (ξ : object k R 1)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ)
    (hz : boundary k R 0 ξ = 0) (n : ℕ) :
    (differential k R (n + 1)).comp (casimirInsertionMap k R h ξ hξ (n + 1)) +
      (casimirInsertionMap k R h ξ hξ n).comp (twistedDifferential k R h n) = 0 := by
  apply LinearMap.ext
  exact casimirInsertion_boundary k R ξ hz n

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TBarLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)
local notation "R" => T k q

def B (H : kˣ) (n : ℕ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) n →ₗ[AbsoluteBar.Enveloping k R]
      AbsoluteBar.moduleObject k R (n + 1) :=
  AbsoluteBar.casimirInsertionMap k R (TrivialExtension.twist H) (twistedCasimir q H)
    (twistedCasimir_equivariant q H) n

variable [CharP k 2]

theorem B_differential (H : kˣ) (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (B q H (n + 1)) +
      (B q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) n) = 0 :=
  AbsoluteBar.casimirInsertionMap_boundary k R (TrivialExtension.twist H) (twistedCasimir q H)
    (twistedCasimir_equivariant q H) (twistedCasimir_augmentation q H) n

omit [CharP k 2] in
theorem P_augmentation : (AbsoluteBar.differential k R 0).comp (P q 0) =
    AbsoluteBar.cochain3 k R (CocycleData.p q) :=
  AbsoluteBar.suffixComparison_augmentation k R (CocycleData.p q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_BimoduleTwoCone
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) [CharP k 2]
local notation "R" => T k q

abbrev bimoduleTwoConeData : TwoCone.Data (ExternalTensor.EnvelopingProduct k R R) :=
  (productTwoConeData q).restrict (ExternalTensor.envelopingEquiv k R R).symm.toRingHom

abbrev firstTail := TwoCone.C₁ (bimoduleTwoConeData q)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_TwistedBoundaryFormula
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β : Type*} {k : Type*} [Field k] (q : k)

theorem row_twisted_contraction (H : kˣ) (t : TripleMonomial) (a b : T k q) :
    (∑ i : TIndex, evalTriple q a b (TrivialExtension.twist H (T.vector q i)) t *
      T.vector q i.star) =
    ((multiplication.flatMap (boundaryLeftContribution t)).map (evalPair q H a b)).sum := by
  rw [Finset.sum_eq_single t.third]
  · simp only [evalTriple, coefficient_twist, T.coefficient_vector]
    rw [Algebra.smul_mul_assoc, multiplication_eq]
    rw [list_sum_flatMap_p1]
    simp only [List.smul_sum, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro m hm
    simp only [evalMul, T.coefficient_vector, boundaryLeftContribution]
    split_ifs <;> simp_all [evalPair, pow_add, smul_smul]
    all_goals module
  · intro i _ hi
    simp only [evalTriple, coefficient_twist, T.coefficient_vector, ite_eq_right (Ne.symm hi),
      mul_zero, zero_smul, zero_mul]
  · simp

theorem twisted_contraction_formula (H : kˣ) (a b : T k q) :
    (∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) * T.vector q i.star) =
      ((cochain.flatMap fun t => multiplication.flatMap (boundaryLeftContribution t)).map
        (evalPair q H a b)).sum := by
  simp only [p_apply, list_right_mul_p1]
  rw [sum_list_comm]
  simp_rw [row_twisted_contraction]
  exact (list_sum_flatMap_p1 cochain _ (evalPair q H a b)).symm

theorem twisted_boundary_formula (H : kˣ) (a b : T k q) :
    a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b =
      ((multiplication.flatMap boundaryRightContributions).map (evalPair q H a b)).sum := by
  rw [multiplication_eq q a (z q H b), multiplication_eq q a b,
    multiplication_eq q (z q H a) (TrivialExtension.twist H⁻¹ b), map_list_sum]
  simp only [List.map_map, Function.comp_def, evalMul, map_smul, z_vector]
  rw [list_sum_flatMap_p1]
  simp only [list_sum_map_add_p1]
  congr 1
  apply List.map_congr_left
  intro m hm
  simp only [boundaryRightContributions, ← selected_eq, List.map_append, List.sum_append]
  simp only [evalMul, coefficient_z, coefficient_twist]
  have hinv := mul_inverse_weight H m.second
  have he : q ^ m.degree * ((H : k) * q * T.coefficient q m.first a) *
      (((H⁻¹ : kˣ) : k) ^ m.second.weight * T.coefficient q m.second b) =
      q ^ (m.degree + 1) * (H : k) ^ (if m.second.1 then 0 else 1) *
        T.coefficient q m.first a * T.coefficient q m.second b := by
    calc
      _ = ((H : k) * ((H⁻¹ : kˣ) : k) ^ m.second.weight) *
          (q ^ m.degree * q * T.coefficient q m.first a * T.coefficient q m.second b) := by ring
      _ = _ := by rw [hinv, pow_succ]; ring
  split_ifs <;> simp_all [evalPair, pow_succ, smul_smul] <;> module

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_TwistedBoundary
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

variable [CharP k 2]

theorem twisted_boundary (H : kˣ) (a b : T k q) :
    (∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) *
      T.vector q i.star) =
      a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b := by
  have hz : (∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) *
      T.vector q i.star) +
      (a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b) = 0 := by
    rw [twisted_contraction_formula, twisted_boundary_formula]
    have hc := boundaryTerms_sum_zero (SparseParity.module_add_self_eq_zero (k := k))
      (evalPair q H a b)
    rw [boundaryTerms, List.map_append, List.sum_append] at hc
    convert! hc using 1
    all_goals try with_reducible_and_instances rfl
  have hd := SparseParity.module_add_self_eq_zero (k := k)
    (a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b)
  exact add_right_cancel (hz.trans hd.symm)

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TNullhomotopy
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] [CharP k 2] (q : k)
local notation "R" => T k q
local notation "Ae" => AbsoluteBar.Enveloping k R

def pB (H : kˣ) (n : ℕ) :
    AbsoluteBar.twistedObject k R (TrivialExtension.twist H) (n + 3) →ₗ[Ae]
      AbsoluteBar.moduleObject k R (n + 1) :=
  (P q n).comp (B q H (n + 3))

theorem B_comm (H : kˣ) (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (B q H (n + 1)) =
      (B q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) n) := by
  apply LinearMap.ext
  intro x
  have hh := LinearMap.congr_fun (B_differential q H n) x
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.zero_apply] at hh
  exact add_right_cancel (hh.trans
    (SparseParity.module_add_self_eq_zero (k := k) (B q H n
      (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) n x))).symm)

theorem P_comm (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (P q (n + 1)) =
      (P q n).comp (AbsoluteBar.differential k R (n + 4)) := by
  apply LinearMap.ext
  intro x
  exact P_differential q (n + 1) x

theorem pB_comm (H : kˣ) (n : ℕ) :
    (AbsoluteBar.differential k R (n + 1)).comp (pB q H (n + 1)) =
      (pB q H n).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) (n + 3)) := by
  unfold pB
  rw [← LinearMap.comp_assoc, P_comm, LinearMap.comp_assoc, B_comm, ← LinearMap.comp_assoc]

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TBarHomotopies
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "R" => T k q
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def barB (n : ℕ) : (Q₀).X n ⟶ (P₀).X (n+1) :=
  ModuleCat.ofHom (X := (Q₀).X n) (Y := (P₀).X (n+1)) (B q H (n+1))

def barDb : (Q₀).X 0 ⟶ (P₀).X 0 :=
  ModuleCat.ofHom (X := (Q₀).X 0) (Y := (P₀).X 0)
    ((B q H 0).comp (AbsoluteBar.twistedDifferential k R (TrivialExtension.twist H) 0))

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteStableSourceNaturality
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {R : Type u} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{u} R) ℤ}

def syzygyInclusion (hP : ExactProjectiveComplex P) (n : ℤ) :
    Cokernel P (n+1) →ₗ[R] P.X n :=
  (LinearMap.ker (P.d n (n-1)).hom).subtype.comp (cokernelSyzygyEquiv hP n).toLinearMap

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeTail
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)
variable (g : (n : ℕ) → Q (n+3) →ₗ[R] D.term (n+2))
variable (b : (n : ℕ) → Q (n+3) →ₗ[R] D.term (n+4))

def tailMap (φ₄ : Q 4 →ₗ[R] term D 1) (φ₅ : Q 5 →ₗ[R] term D 2)
    (hφ : (d D 1).comp φ₅ = φ₄.comp (δ 4)) :
    FourthCokernel Q δ →ₗ[R] C₁ D :=
  (LinearMap.range (δ 4)).liftQ (((LinearMap.range (d D 1)).mkQ).comp φ₄) (by
    rintro x ⟨y,rfl⟩
    change (LinearMap.range (d D 1)).mkQ (φ₄ (δ 4 y)) = 0
    rw [← show d D 1 (φ₅ y) = φ₄ (δ 4 y) from DFunLike.congr_fun hφ y]
    exact DFunLike.congr_fun (LinearMap.range_mkQ_comp (d D 1)) (φ₅ y))

@[simp] theorem tailMap_mk (φ₄ : Q 4 →ₗ[R] term D 1) (φ₅ : Q 5 →ₗ[R] term D 2)
    (hφ : (d D 1).comp φ₅ = φ₄.comp (δ 4)) (x : Q 4) :
    tailMap D Q δ φ₄ φ₅ hφ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ₄ x) := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeTailRestriction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)
variable (φ : (n : ℕ) → Q (n+3) →ₗ[R] term D n)

def restrictedHighLift (n : ℕ) : restrictedSource j Q (n+3) →ₗ[S] term (D.restrict j) n :=
  (termRestrictionEquiv j D n).toLinearMap.comp
    ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (φ n))).hom

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorHighLift
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R
local notation "P₀" => AbsoluteBar.complex k R
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

def tensorHighB (n : ℕ) :=
  ExternalTensor.bottomMap k Te Te P₀ P₀ Q₀ Q₀ (n+3) (n+4) (barB q H (n+3)) (barDb q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_TensorTailMap
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
local notation "R" => T k q
local notation "Q₀" => productTwistedTotal q H

local notation "F" => ExternalTensor.envelopingFunctor k R R

abbrev bimoduleTwistedTerm (n : ℕ) := (F).obj ((Q₀).X n)

def bimoduleTwistedDifferential (n : ℕ) := ((F).map ((Q₀).d (n+1) n)).hom

abbrev fourthSyzygy := TwoCone.FourthCokernel (bimoduleTwistedTerm q H) (bimoduleTwistedDifferential q H)

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Duality_DualResolution
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

def homERightLinearEquiv : (E q →ₗ[C] C) ≃ₗ[Cᵐᵒᵖ] rightE q where
  __ := homEEquiv q
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

end ArExplicit.Resolution

end

end OAI
end


