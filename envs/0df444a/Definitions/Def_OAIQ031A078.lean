-- Prove2me | Definitions.Def_OAIQ031A078
-- name    : OAIQ031A078
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:21:10.618781+00:00
-- url     : https://prove2.me/theorems/48c6ba4d-b453-43ab-b1be-62455ef897f0
-- title:
--   Definitions bundle OAIQ031A078 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 13 definitions, 1 instance and 17 theorems. The definitions and types are `OAI.ArExplicit.AbsoluteBar.casimirInsertionMap`, `OAI.ArExplicit.AbsoluteBar.twistedAugmentation`, `OAI.ArExplicit.AbsoluteBar.twistedComplex`, `OAI.ArExplicit.AbsoluteBar.twistedDifferential`, `OAI.ArExplicit.AbsoluteBar.twistedModule`, `OAI.ArExplicit.AbsoluteBar.twistedObject`, `OAI.ArExplicit.AbsoluteBar.twistedToOrdinary`, `OAI.ArExplicit.Resolution.homEEquiv`, `OAI.ArExplicit.T.P`, `OAI.ArExplicit.T.barComparison`, `OAI.ArExplicit.T.productTwistedTotal`, `OAI.ArExplicit.T.productTwoConeData`, `OAI.ArExplicit.TwoCone.C₁`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Algebras_TMultiplication`, `AuslanderReiten_Bar_BarCasimir`, `AuslanderReiten_Bar_TBarLift`, `AuslanderReiten_Bar_TCasimir`, `AuslanderReiten_Bar_TwistedBar`, `AuslanderReiten_Cocycles_CocycleClosure`, `AuslanderReiten_Cocycles_CocycleExt`, `AuslanderReiten_Cocycles_CocycleFormula`, `AuslanderReiten_Cocycles_SparseCocycle`, `AuslanderReiten_Complete_CompleteShift`, `AuslanderReiten_Complete_CompleteShiftDual`, `AuslanderReiten_Cones_BimoduleTwoCone`, `AuslanderReiten_Cones_TwoCone`, `AuslanderReiten_Coordinates_TensorHighLift`, `AuslanderReiten_Duality_DualResolution`.
--
--   **Imports.** It imports the bundles `OAIQ031A061`, `OAIQ031A062`, `OAIQ031A063` and `OAIQ031A065` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A091`, `OAIQ031A092`, `OAIQ031A093`, `OAIQ031A094`, `OAIQ031A095`, `OAIQ031A096`, `OAIQ031A098`, `OAIQ031A102` and `OAIQ031A104`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A061
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A063
import Definitions.Def_OAIQ031A065

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TMultiplication
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

namespace CocycleData

open BaseAlgebra TrivialExtension

variable {k : Type*} [Field k] (q : k)

theorem multiplication_coefficient (a b : T k q) (i : TIndex) :
    T.coefficient q i (a * b) = multiplicationCoefficient q a b i := by
  obtain ⟨upper, i⟩ := i
  cases upper <;> cases i
  · exact multiplication_false_e q a b
  · exact multiplication_false_x q a b
  · exact multiplication_false_y q a b
  · exact multiplication_false_z q a b
  · exact multiplication_false_u q a b
  · exact multiplication_false_v q a b
  · exact multiplication_false_t q a b
  · exact multiplication_false_j q a b
  · exact multiplication_false_f q a b
  · exact multiplication_false_n q a b
  · exact multiplication_true_e q a b
  · exact multiplication_true_x q a b
  · exact multiplication_true_y q a b
  · exact multiplication_true_z q a b
  · exact multiplication_true_u q a b
  · exact multiplication_true_v q a b
  · exact multiplication_true_t q a b
  · exact multiplication_true_j q a b
  · exact multiplication_true_f q a b
  · exact multiplication_true_n q a b

end CocycleData
end ArExplicit

end

end OAI
end

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

theorem casimirInsertion_left (ξ : object k R 1) (n : ℕ) (a : R) (x : object k R n) :
    casimirInsertion k R ξ n (left k R n a x) =
      left k R (n + 1) a (casimirInsertion k R ξ n x) := by
  cases n with
  | zero => exact casimirMap_left k R ξ a x
  | succ n =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x => rfl

theorem casimirInsertion_right (ξ : object k R 1) (h : R ≃ₐ[k] R)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ)
    (n : ℕ) (a : R) (x : object k R n) :
    casimirInsertion k R ξ n (right k R n (MulOpposite.op (h a)) x) =
      right k R (n + 1) (MulOpposite.op a) (casimirInsertion k R ξ n x) := by
  induction n with
  | zero =>
    change left k R 1 (x * h a) ξ = right k R 1 (MulOpposite.op a) (left k R 1 x ξ)
    rw [left_mul, hξ, left_right]
  | succ n ih =>
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b x =>
      change b ⊗ₜ[k] casimirInsertion k R ξ n (right k R n (MulOpposite.op (h a)) x) =
        b ⊗ₜ[k] right k R (n + 1) (MulOpposite.op a) (casimirInsertion k R ξ n x)
      rw [ih]

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_SparseCocycle
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

theorem multiplication_eq (a b : T k q) :
    a * b = (multiplication.map (evalMul q a b)).sum := by
  apply T.coordinate_ext q
  intro i
  rw [multiplication_coefficient]
  rw [map_list_sum]
  simp [multiplicationCoefficient, evalMul, List.map_map, Function.comp_def, mul_ite, eq_comm]

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TCasimir
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

theorem twistedCasimir_coordinates (H : kˣ) (i : TIndex) :
    tensorRightCoordinates q (twistedCasimir q H) i =
      TrivialExtension.twist H (vector q i.star) := by
  simp only [twistedCasimir, map_sum, Finset.sum_apply, tensorRightCoordinates_tmul,
    coefficient_vector]
  rw [Finset.sum_eq_single i.star]
  · simp
  · intro j _ hj
    have hn : i ≠ j.star := by
      intro h
      have := congrArg TIndex.star h
      simp only [star_star] at this
      exact hj this.symm
    simp [hn]
  · simp

theorem tensorRightCoordinates_left (a : R) (x : R ⊗[k] R) (i : TIndex) :
    tensorRightCoordinates q (AbsoluteBar.left k R 1 a x) i =
      a * tensorRightCoordinates q x i := by
  induction x using OAI.tensorInductionOn with
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, mul_add, hx, hy]
  | tmul b c =>
    change tensorRightCoordinates q ((a * b) ⊗ₜ[k] c) i = _
    simp only [tensorRightCoordinates_tmul, Algebra.mul_smul_comm]

theorem twistedCasimir_equivariant (H : kˣ) (a : R) :
    AbsoluteBar.left k R 1 (TrivialExtension.twist H a) (twistedCasimir q H) =
      AbsoluteBar.right k R 1 (MulOpposite.op a) (twistedCasimir q H) := by
  apply (tensorRightCoordinates q).injective
  funext i
  rw [tensorRightCoordinates_left, twistedCasimir_coordinates, ← map_mul]
  simp only [twistedCasimir, map_sum, AbsoluteBar.right_tmul k R 0, AbsoluteBar.right_zero k R, MulOpposite.unop_op, Finset.sum_apply,
    tensorRightCoordinates_tmul, coefficient_right_product]
  have he := congrArg (TrivialExtension.twist H) (expand q (a * vector q i.star))
  simpa only [map_sum, map_smul] using he

end ArExplicit.T

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

@[instance_reducible] def twistedModule (h : R ≃ₐ[k] R) (n : ℕ) :
    Module (Enveloping k R) (object k R n) :=
  Module.compHom (object k R n) ((representation k R n).comp (twistEnveloping k R h).toAlgHom).toRingHom

def twistedObject (h : R ≃ₐ[k] R) (n : ℕ) : ModuleCat.{u} (Enveloping k R) :=
  letI := twistedModule k R h n
  ModuleCat.of (Enveloping k R) (object k R n)

instance twistInvPair (h : R ≃ₐ[k] R) :
    RingHomInvPair (twistEnveloping k R h).toRingHom (twistEnveloping k R h).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (twistEnveloping k R h).toRingEquiv

def twistedToOrdinary (h : R ≃ₐ[k] R) {n m : ℕ}
    (f : object k R n →ₗ[k] object k R m)
    (hl : ∀ a x, f (left k R n a x) = left k R m a (f x))
    (hr : ∀ a x, f (right k R n (MulOpposite.op (h a)) x) =
      right k R m (MulOpposite.op a) (f x)) :
    twistedObject k R h n →ₗ[Enveloping k R] moduleObject k R m where
  toAddHom := f.toAddHom
  map_smul' a x := by
    let y : object k R n := x
    change f (representation k R n (twistEnveloping k R h a) y) = representation k R m a (f y)
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      change f (left k R n a (right k R n (MulOpposite.op (h b.unop)) y)) =
        left k R m a (right k R m b (f y))
      rw [hl, hr, MulOpposite.op_unop]

def casimirInsertionMap (h : R ≃ₐ[k] R) (ξ : object k R 1)
    (hξ : ∀ a : R, left k R 1 (h a) ξ = right k R 1 (MulOpposite.op a) ξ) (n : ℕ) :
    twistedObject k R h n →ₗ[Enveloping k R] moduleObject k R (n + 1) :=
  twistedToOrdinary k R h (casimirInsertion k R ξ n)
    (casimirInsertion_left k R ξ n) (fun a x => casimirInsertion_right k R ξ h hξ n a x)

def twistedDifferential (h : R ≃ₐ[k] R) (n : ℕ) :
    twistedObject k R h (n + 1) →ₗ[Enveloping k R] twistedObject k R h n where
  toAddHom := (boundary k R n).toAddHom
  map_smul' a x := (differential k R n).map_smul (twistEnveloping k R h a) x

variable [CharP k 2]

def twistedComplex (h : R ≃ₐ[k] R) : ChainComplex (ModuleCat.{u} (Enveloping k R)) ℕ :=
  ChainComplex.of (fun n => twistedObject k R h (n + 1))
    (fun n => ModuleCat.ofHom (X := twistedObject k R h (n + 2))
      (Y := twistedObject k R h (n + 1)) (twistedDifferential k R h (n + 1)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R (n + 1))

@[simp] theorem twistedComplex_d (h : R ≃ₐ[k] R) (n : ℕ) :
    (twistedComplex k R h).d (n + 1) n = ModuleCat.ofHom
      (X := twistedObject k R h (n + 2)) (Y := twistedObject k R h (n + 1))
        (twistedDifferential k R h (n + 1)) := by
  simp only [twistedComplex, ChainComplex.of.d]
  apply Category.id_comp

def twistedAugmentation (h : R ≃ₐ[k] R) : twistedComplex k R h ⟶
    (ChainComplex.single₀ (ModuleCat.{u} (Enveloping k R))).obj (twistedObject k R h 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (X := twistedObject k R h 1) (Y := twistedObject k R h 0)
      (twistedDifferential k R h 0), by
      rw [twistedComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact boundary_squared k R 0⟩

@[simp] theorem twistedAugmentation_zero (h : R ≃ₐ[k] R) :
    (twistedAugmentation k R h).f 0 = ModuleCat.ofHom (X := twistedObject k R h 1)
      (Y := twistedObject k R h 0) (twistedDifferential k R h 0) :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

end ArExplicit.AbsoluteBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleFormula
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {α β k : Type*} [Field k] (q : k)

theorem row_differential (p : TripleMonomial) (a b c d : T k q) :
    a * evalTriple q b c d p + evalTriple q (a * b) c d p +
      evalTriple q a (b * c) d p + evalTriple q a b (c * d) p +
      evalTriple q a b c p * d =
        ((multiplication.flatMap (contributions p)).map (evalQuad q a b c d)).sum := by
  rw [list_sum_flatMap_p0]
  simp only [evalTriple, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  rw [multiplication_eq q a (T.vector q p.output),
    multiplication_eq q (T.vector q p.output) d]
  simp only [multiplication_coefficient, multiplicationCoefficient,
    List.smul_sum, List.sum_smul, list_mul_sum, list_sum_mul, List.map_map, Function.comp_def]
  simp only [list_sum_map_add_p0]
  congr 1
  apply List.map_congr_left
  intro m hm
  simp only [contributions, List.map_append, List.sum_append, evalMul, T.coefficient_vector, smul_smul]
  split_ifs <;> simp_all [evalQuad, pow_add] <;> module

theorem p_differential_formula (a b c d : T k q) :
    a * p q b c d + p q (a * b) c d + p q a (b * c) d +
      p q a b (c * d) + p q a b c * d =
        (differentialTerms.map (evalQuad q a b c d)).sum := by
  simp only [p_apply, list_left_mul, list_right_mul_p0, list_sum_map_add_p0]
  simp_rw [row_differential]
  exact (list_sum_flatMap_p0 cochain (fun p => multiplication.flatMap (contributions p))
    (evalQuad q a b c d)).symm

end ArExplicit.CocycleData

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleClosure
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] [CharP k 2] (q : k)

theorem p_cocycle (a b c d : T k q) :
    a * p q b c d + p q (a * b) c d + p q a (b * c) d +
      p q a b (c * d) + p q a b c * d = 0 := by
  rw [p_differential_formula]
  exact differentialTerms_sum_zero (SparseParity.module_add_self_eq_zero (k := k)) _

end ArExplicit.CocycleData

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleExt
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] [CharP k 2] (q : k)

theorem p_isCocycle3 : AbsoluteBar.IsCocycle3 k (T k q) (p q) := by
  intro a b c d
  have h := @p_cocycle k inferInstance inferInstance q a b c d
  convert! h using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.CocycleData

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

variable [CharP k 2]

omit [CharP k 2] in

def P (n : ℕ) : AbsoluteBar.moduleObject k R (n + 4) →ₗ[AbsoluteBar.Enveloping k R]
    AbsoluteBar.moduleObject k R (n + 1) :=
  AbsoluteBar.suffixComparisonMap k R (CocycleData.p q) n

theorem P_differential (n : ℕ) (x : AbsoluteBar.object k R (n + 4)) :
    AbsoluteBar.boundary k R n (AbsoluteBar.suffixComparison k R (CocycleData.p q) (n + 1) x) =
      AbsoluteBar.suffixComparison k R (CocycleData.p q) n (AbsoluteBar.boundary k R (n + 3) x) :=
  AbsoluteBar.suffixComparison_boundary k R (CocycleData.p q) (CocycleData.p_isCocycle3 q) n x

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShift
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace ExactProjectiveCochain

open CompleteComparison

theorem to_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : ExactProjectiveCochain K) : ExactProjectiveComplex (chainOfCochain K) where
  finite i := by
    let := hK.finite (-i)
    exact Module.Finite.equiv (CategoryTheory.Iso.toLinearEquiv
      (K.extendXIso negIndexEmbedding (show negIndexEmbedding.f (-i) = i from neg_neg i))).symm
  projective i := by
    let := hK.projective (-i)
    exact Module.Projective.of_equiv (CategoryTheory.Iso.toLinearEquiv
      (K.extendXIso negIndexEmbedding (show negIndexEmbedding.f (-i) = i from neg_neg i))).symm
  exactAt i := (chain_exactAt_iff (chainOfCochain K) i).mp
    ((K.extend_exactAt_iff negIndexEmbedding (j := -i) (j' := i) (neg_neg i)).mpr
      (hK.exactAt (-i)))

end ExactProjectiveCochain

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteShiftDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

namespace TotallyAcyclicCochain

open CompleteComparison

theorem to_chain {K : CochainComplex (ModuleCat.{u} R) ℤ}
    (hK : TotallyAcyclicCochain K) : TotallyAcyclicComplex (chainOfCochain K) where
  toExactProjectiveComplex := hK.toExactProjectiveCochain.to_chain
  dualExact := hK.dualExact.to_chain

end TotallyAcyclicCochain

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R]

variable (D : Data R)

abbrev C₁ := Cokernel D 1

end ArExplicit.TwoCone

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
local notation "Te" => AbsoluteBar.Enveloping k R

def barComparison (n : ℕ) : (AbsoluteBar.complex k R).X (n+3) ⟶
    (AbsoluteBar.complex k R).X n :=
  ModuleCat.ofHom (X := (AbsoluteBar.complex k R).X (n+3))
    (Y := (AbsoluteBar.complex k R).X n) (P q n)

theorem barComparison_chain (n : ℕ) :
    barComparison q (n+1) ≫ (AbsoluteBar.complex k R).d (n+1) n =
      (AbsoluteBar.complex k R).d (n+4) (n+3) ≫ barComparison q n := by
  simp only [AbsoluteBar.complex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact P_differential q (n+1) x

abbrev productTwoConeData : TwoCone.Data (Te ⊗[k] Te) :=
  ExternalTensor.twoConeData k Te Te (AbsoluteBar.complex k R) (AbsoluteBar.complex k R)
    (barComparison q) (barComparison q) (barComparison_chain q) (barComparison_chain q)

end ArExplicit.T

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
local notation "Q₀" => AbsoluteBar.twistedComplex k R (TrivialExtension.twist H)

abbrev productTwistedTotal := ExternalTensor.complex k Te Te Q₀ Q₀

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

def homEEquiv : (E q →ₗ[C] C) ≃ rightE q where
  toFun := evaluateE q
  invFun := fromRightE q
  left_inv := fromRightE_evaluateE q
  right_inv := evaluateE_fromRightE q

end ArExplicit.Resolution

end

end OAI
end


