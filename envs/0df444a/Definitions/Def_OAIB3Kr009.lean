-- Prove2me | Definitions.Def_OAIB3Kr009
-- name    : OAIB3Kr009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T16:59:30.708435+00:00
-- url     : https://prove2.me/theorems/5f4afee3-57dd-447c-945b-30e5317a7d32
-- title:
--   Definitions bundle OAIB3Kr009 of the split of OpenAI, The Kirchberg–Rørdam character criterion
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KirchbergRordam.character_criterion`, carved from OpenAI's openai/math development (OpenAI, *The Kirchberg–Rørdam character criterion*, OpenAI Math Release, September 25, 2026, result family 299, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 41 definitions, 8 instances and 11 theorems. The definitions and types are `OAI.KirchbergRordam.GenericRW.ConeCube.point`, `OAI.KirchbergRordam.GenericRW.ConeCube.post`, `OAI.KirchbergRordam.GenericRW.ConeCut.coeff`, `OAI.KirchbergRordam.GenericRW.CubeCalculus.coord`, `OAI.KirchbergRordam.GenericRW.CubeFrame.expansion`, `OAI.KirchbergRordam.GenericRW.CubeFrame.scalarSection`, `OAI.KirchbergRordam.GenericRW.CubeWeights.Cube`, `OAI.KirchbergRordam.GenericRW.CubeWeights.H`, `OAI.KirchbergRordam.GenericRW.CubeWeights.Punctured`, `OAI.KirchbergRordam.GenericRW.CubeWeights.g`, `OAI.KirchbergRordam.GenericRW.CubeWeights.radius`, `OAI.KirchbergRordam.GenericRW.CubeWeights.total`, `OAI.KirchbergRordam.GenericRW.CubeWeights.weight`, `OAI.KirchbergRordam.GenericRW.CuntzBelow`, `OAI.KirchbergRordam.GenericRW.DetectingSpace.CommutativeQuotient`, `OAI.KirchbergRordam.GenericRW.DetectingSpace.closedCommutatorIdeal`, `OAI.KirchbergRordam.GenericRW.DetectingSpace.commutatorIdeal`, `OAI.KirchbergRordam.GenericRW.DetectingSpace.finiteCommutators`, `OAI.KirchbergRordam.GenericRW.Domination.invReg`, `OAI.KirchbergRordam.GenericRW.Domination.remReg`, `OAI.KirchbergRordam.GenericRW.DoubleCommutator.bracket`, `OAI.KirchbergRordam.GenericRW.DoubleCommutator.orbit`, `OAI.KirchbergRordam.GenericRW.DoubleCommutator.quadratic`, `OAI.KirchbergRordam.GenericRW.DropSections.Scalar`, `OAI.KirchbergRordam.GenericRW.ExactCut.cut`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.IsFactor`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.SumHilbert`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.column`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.columnSpace`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.diagonal`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.entry`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.injection`, `OAI.KirchbergRordam.GenericRW.FactorIndependence.row`, `OAI.KirchbergRordam.GenericRW.FlipPath.angle`, `OAI.KirchbergRordam.GenericRW.FlipPath.phase`, `OAI.KirchbergRordam.GenericRW.Intertwining.algebra`, `OAI.KirchbergRordam.GenericRW.MatrixMix.Mat`, `OAI.KirchbergRordam.GenericRW.MatrixMix.e`, `OAI.KirchbergRordam.GenericRW.MatrixMix.linear`, `OAI.KirchbergRordam.GenericRW.MatrixMix.x` and 1 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`CharacterCriterion_AmplifiedComparison`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/AmplifiedComparison.lean), [`CharacterCriterion_ConeCube`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/ConeCube.lean), [`CharacterCriterion_CubeCalculus`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/CubeCalculus.lean), [`CharacterCriterion_DetectingSpaces`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/DetectingSpaces.lean), [`CharacterCriterion_DropSections`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/DropSections.lean), [`CharacterCriterion_FactorIndependence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/FactorIndependence.lean), [`CharacterCriterion_FlipPath`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/FlipPath.lean), [`CharacterCriterion_Fullness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/Fullness.lean), [`CharacterCriterion_FunctionalCalculus`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/FunctionalCalculus.lean), [`CharacterCriterion_MatrixSimplex`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/MatrixSimplex.lean), [`CharacterCriterion_SignObstruction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/SignObstruction.lean), [`CharacterCriterion_SquareZeroCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CharacterCriterion/SquareZeroCone.lean).
--
--   **Imports.** It imports the published bundle `Def_CharacterCriterion`.
--
--   **Imported by** (directly, in this split): the bundles `OAIB3Kr011` and `OAIB3Kr012`; the proofs of `OAI_KirchbergRordam_PrimeDropPresentation_to_central` and `OAI_KirchbergRordam_PrimeTensorSections_sectionMap_isometry`.
-- source:
--   OpenAI, The Kirchberg–Rørdam character criterion, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 299; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Kirchberg-Rordam-character-criterion-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib
import Definitions.Def_CharacterCriterion

section
-- module Solutions.OAIB3_Krc.Compat
attribute [-instance] _root_.OAI.KirchbergRordam.NormUltrapower.quotientNormedRing _root_.OAI.KirchbergRordam.StarCompletion.completionNormedAlgebra _root_.OAI.KirchbergRordam.StarCompletion.completionStar _root_.OAI.KirchbergRordam.StarCompletion.completionStarRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FactorIndependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct


open scoped InnerProductSpace
namespace KirchbergRordam.GenericRW
namespace FactorIndependence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  ∀ T : H →L[ℂ] H, T ∈ M → T ∈ M.commutant → ∃ z : ℂ, T = z • 1

abbrev SumHilbert (ι : Type*) (H : Type*) := PiLp 2 (fun _ : ι => H)

def diagonal (T : H →L[ℂ] H) : SumHilbert ι H →L[ℂ] SumHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => T.comp (PiLp.proj 2 (fun _ : ι => H) i))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma diagonal_apply (T : H →L[ℂ] H) (x : SumHilbert ι H) (i : ι) :
    diagonal T x i = T (x i) := rfl

variable [DecidableEq ι]

def injection (i : ι) : H →L[ℂ] SumHilbert ι H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℂ (fun _ : ι => H) i)

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma injection_apply (i j : ι) (x : H) :
    injection i x j = if j = i then x else 0 := by
  simp [injection]

def entry (P : SumHilbert ι H →L[ℂ] SumHilbert ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (P.comp (injection j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] lemma entry_apply (P : SumHilbert ι H →L[ℂ] SumHilbert ι H)
    (i j : ι) (x : H) : entry P i j x = P (injection j x) i := rfl

def column (b : ι → H →L[ℂ] H) (ξ : H) : SumHilbert ι H :=
  WithLp.toLp 2 (fun i => b i ξ)

omit [CompleteSpace H] [Fintype ι] [DecidableEq ι] in
@[simp] lemma column_apply (b : ι → H →L[ℂ] H) (ξ : H) (i : ι) : column b ξ i = b i ξ := rfl

def columnSpace (M : VonNeumannAlgebra H) (b : ι → H →L[ℂ] H) :
    Submodule ℂ (SumHilbert ι H) :=
  (Submodule.span ℂ {v | ∃ c : H →L[ℂ] H, c ∈ M.commutant ∧
    ∃ ξ : H, v = diagonal c (column b ξ)}).topologicalClosure

def row (a : ι → H →L[ℂ] H) : SumHilbert ι H →L[ℂ] H :=
  ∑ i, (a i).comp (PiLp.proj 2 (fun _ : ι => H) i)

omit [CompleteSpace H] [DecidableEq ι] in
@[simp] lemma row_apply (a : ι → H →L[ℂ] H) (x : SumHilbert ι H) :
    row a x = ∑ i, a i (x i) := by simp [row]

end FactorIndependence
end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DetectingSpaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace


open scoped BigOperators
open Set Module

universe uQuot


open Topology
namespace KirchbergRordam.GenericRW
namespace DetectingSpace


noncomputable instance quotientNormedRing {R : Type uQuot} [NormedRing R] (I : Ideal R)
    [I.IsTwoSided] [IsClosed (I : Set R)] : NormedRing (R ⧸ I) :=
  KirchbergRordam.QuotientNormSupport.normedRing I

variable {D : Type*} [CStarAlgebra D]


def commutatorIdeal : TwoSidedIdeal D :=
  TwoSidedIdeal.span {z | ∃ a b : selfAdjoint D, z = (a : D) * b - b * a}

def closedCommutatorIdeal : Ideal D :=
  (commutatorIdeal (D := D)).asIdeal.topologicalClosure

instance instIsTwoSidedClosedCommutatorIdeal : (closedCommutatorIdeal (D := D)).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    exact (show Set.MapsTo (fun x : D => x * b)
      (commutatorIdeal (D := D) : Set D) (commutatorIdeal (D := D) : Set D) from
      fun x hx => TwoSidedIdeal.mul_mem_right _ _ _ hx).closure
        (continuous_mul_const b) ha

instance instIsClosedCoeIdealClosedCommutatorIdeal : IsClosed (closedCommutatorIdeal (D := D) : Set D) := isClosed_closure

lemma commutator_mem (a b : selfAdjoint D) :
    (a : D) * b - b * a ∈ closedCommutatorIdeal :=
  subset_closure (TwoSidedIdeal.subset_span ⟨a, b, rfl⟩)

abbrev CommutativeQuotient (D : Type*) [CStarAlgebra D] := D ⧸ closedCommutatorIdeal (D := D)

instance instNormedAlgebraComplexCommutativeQuotient : NormedAlgebra ℂ (CommutativeQuotient D) where
  norm_smul_le := norm_smul_le

lemma quotient_sa_commute (a b : selfAdjoint D) :
    Commute (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) (a : D))
      (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) (b : D)) := by
  change Ideal.Quotient.mk _ ((a : D) * b) = Ideal.Quotient.mk _ ((b : D) * a)
  exact Ideal.Quotient.eq.mpr (commutator_mem a b)

lemma quotient_commute (a b : D) :
    Commute (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) a)
      (Ideal.Quotient.mkₐ ℂ (closedCommutatorIdeal (D := D)) b) := by
  rw [← realPart_add_I_smul_imaginaryPart a, ← realPart_add_I_smul_imaginaryPart b]
  simp only [map_add, map_smul]
  exact ((quotient_sa_commute _ _).add_right ((quotient_sa_commute _ _).smul_right _)).add_left
    (((quotient_sa_commute _ _).smul_left _).add_right
      (((quotient_sa_commute _ _).smul_left _).smul_right _))

instance instCommRingCommutativeQuotient : CommRing (CommutativeQuotient D) :=
  { (inferInstance : Ring (CommutativeQuotient D)) with
    mul_comm := by
      intro a b
      induction a using Quotient.inductionOn with | _ a =>
        induction b using Quotient.inductionOn with | _ b =>
          exact quotient_commute a b }

instance instNormedCommRingCommutativeQuotient : NormedCommRing (CommutativeQuotient D) where


def finiteCommutators (s : Finset (selfAdjoint D)) : Set D :=
  {z | ∃ a ∈ s, ∃ b ∈ s, z = (a : D) * b - b * a}

end DetectingSpace


end KirchbergRordam.GenericRW
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_Fullness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


namespace KirchbergRordam.GenericRW
namespace PrimitiveSeparation
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (I : Ideal A) [I.IsTwoSided] [IsClosed (I : Set A)]

instance quotientNormedAlgebra : NormedAlgebra ℂ (A ⧸ I) where
  norm_smul_le := norm_smul_le

def quotientCLM : A →L[ℂ] (A ⧸ I) :=
  (Ideal.Quotient.mkₐ ℂ I).toLinearMap.mkContinuous 1 fun a => by
    change ‖(Submodule.Quotient.mk a : A ⧸ I)‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le I a

omit [Nontrivial A] in
@[simp] lemma quotientCLM_apply (a : A) : quotientCLM I a = Ideal.Quotient.mk I a := rfl

end PrimitiveSeparation
end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SignObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


open scoped InnerProductSpace
open NormedSpace
namespace KirchbergRordam.GenericRW
namespace DoubleCommutator

section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

def bracket (X T : A) : A := X * T - T * X

def orbit (X T : A) (t : ℝ) : A := exp (t • X) * T * exp (t • (-X))

end BanachAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]


def quadratic (ξ : H) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp
    (((innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ H ξ)).restrictScalars ℝ)

end DoubleCommutator

open DoubleCommutator


end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_SquareZeroCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


namespace KirchbergRordam.GenericRW
namespace Intertwining
variable {A : Type*} [CStarAlgebra A]


def algebra (v : A) : StarSubalgebra ℂ (A × A) where
  carrier := {p | v * p.1 = p.2 * v ∧ star v * p.2 = p.1 * star v}
  mul_mem' := by
    intro p q hp hq
    constructor
    · change v * (p.1 * q.1) = (p.2 * q.2) * v
      rw [← mul_assoc, hp.1, mul_assoc, hq.1, mul_assoc]
    · change star v * (p.2 * q.2) = (p.1 * q.1) * star v
      rw [← mul_assoc, hp.2, mul_assoc, hq.2, mul_assoc]
  one_mem' := by simp
  add_mem' := by
    intro p q hp hq
    constructor <;> change _ * (_ + _) = (_ + _) * _
    · rw [mul_add, add_mul, hp.1, hq.1]
    · rw [mul_add, add_mul, hp.2, hq.2]
  zero_mem' := by simp
  algebraMap_mem' := by
    intro z
    constructor
    · exact Algebra.commutes z v |>.symm
    · exact Algebra.commutes z (star v) |>.symm
  star_mem' := by
    intro p hp
    constructor
    · simpa only [star_mul, star_star, Prod.fst_star, Prod.snd_star] using (congrArg star hp.2).symm
    · simpa only [star_mul, star_star, Prod.fst_star, Prod.snd_star] using (congrArg star hp.1).symm

instance closed (v : A) : IsClosed ((algebra v : StarSubalgebra ℂ (A × A)) : Set (A × A)) :=
  (isClosed_eq (by fun_prop) (by fun_prop)).inter (isClosed_eq (by fun_prop) (by fun_prop))

end Intertwining

end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FlipPath
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


namespace KirchbergRordam.GenericRW.FlipPath
open scoped BigOperators


def angle : C(unitInterval,ℝ) := ⟨fun t => min (max (3*(t:ℝ)-1) 0) 1,by fun_prop⟩

def phase : C(unitInterval,ℂ) :=
  ⟨fun t => Complex.exp (((Real.pi*angle t : ℝ):ℂ)*Complex.I),by fun_prop⟩

end KirchbergRordam.GenericRW.FlipPath

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_DropSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


namespace KirchbergRordam.GenericRW.DropSections
open scoped Matrix Kronecker BigOperators ComplexOrder
abbrev Scalar := C(unitInterval,ℂ)

end KirchbergRordam.GenericRW.DropSections
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_FunctionalCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


namespace KirchbergRordam.GenericRW
namespace Domination
section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def invReg (τ : ℝ) (t : ℝ) : ℝ := (max t 0 + τ)⁻¹
def remReg (τ : ℝ) (t : ℝ) : ℝ := 1 - t * invReg τ t

end

end Domination


section
variable {A : Type*} [CStarAlgebra A]


def CuntzBelow (a b : A) : Prop :=
  a ∈ closure (Set.range (fun x : A => star x * b * x))

end

namespace ExactCut
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


def cut (a : A) (δ : ℝ) : A := (a - algebraMap ℝ A δ)⁺

end ExactCut
end KirchbergRordam.GenericRW

end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_CubeCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.CubeCalculus
open scoped CStarAlgebra
variable {I A : Type*} [CStarAlgebra A]
def coord (i : I) : C(I→unitInterval,ℂ) :=
  ⟨fun t => ((t i:ℝ):ℂ),by fun_prop⟩
end KirchbergRordam.GenericRW.CubeCalculus


namespace KirchbergRordam.GenericRW.CubeFrame
open scoped BigOperators CStarAlgebra
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X]
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]
variable (κ : C(X,ℂ) →⋆ₐ[ℂ] B) (ρ : B →⋆ₐ[ℂ] C(X,T))
variable (p : I→C(X,ℂ)) (u : I→B) (e : I→T)
variable (hc : ∀ f a,Commute (κ f) a)
variable (hu : ∀ i,star (u i)*u i=κ (star (p i)*p i))

def expansion (f : I→C(X,ℂ)) : B := ∑ i,κ (f i)*u i
end KirchbergRordam.GenericRW.CubeFrame

namespace KirchbergRordam.GenericRW.CubeFrame
open scoped BigOperators
variable {X B T I : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [CStarAlgebra B] [CStarAlgebra T] [Fintype I] [DecidableEq I]

def scalarSection (a : T) : C(X,ℂ) →ₗ[ℂ] C(X,T) where
  toFun f := ⟨fun t => f t • a,by fun_prop⟩
  map_add' f g := by ext t; simp [add_smul]
  map_smul' c f := by ext t; simp [smul_smul]

end KirchbergRordam.GenericRW.CubeFrame
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_ConeCube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


namespace KirchbergRordam.GenericRW.ConeCube
open scoped CStarAlgebra BigOperators ComplexOrder

def post {X A B : Type*} [TopologicalSpace X] [CStarAlgebra A] [CStarAlgebra B]
    (φ : A→⋆ₐ[ℂ] B) : C(X,A)→⋆ₐ[ℂ] C(X,B) where
  toFun f := ⟨φ∘f,(map_continuous φ).comp f.continuous⟩
  map_zero' := by ext t; exact map_zero φ
  map_one' := by ext t; exact map_one φ
  map_add' f g := by ext t; exact map_add φ _ _
  map_mul' f g := by ext t; exact map_mul φ _ _
  commutes' c := by ext t; exact φ.commutes c
  map_star' f := by ext t; exact map_star φ _

def point {X A : Type*} [TopologicalSpace X] [CStarAlgebra A] (t : X) : C(X,A)→⋆ₐ[ℂ] A where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

end KirchbergRordam.GenericRW.ConeCube


end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_MatrixSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace


namespace KirchbergRordam.GenericRW.MatrixMix
open scoped BigOperators
variable {A : Type*} [CStarAlgebra A]
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
abbrev Mat (ι : Type*) := Matrix ι ι ℂ
def e (i j : ι) : Mat ι := Matrix.single i j 1

variable (φ : Mat ι →⋆ₐ[ℂ] A) (ψ : Mat κ →⋆ₐ[ℂ] A)
variable (hc : ∀ a b,Commute (φ a) (ψ b))
def x (i j : ι×κ) : A := φ (e i.1 j.1)*ψ (e i.2 j.2)

def linear : Mat (ι×κ) →ₗ[ℂ] A where
  toFun a := ∑ i,∑ j,a i j • x φ ψ i j
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum,smul_smul]
end KirchbergRordam.GenericRW.MatrixMix


namespace KirchbergRordam.GenericRW.CubeWeights
open scoped BigOperators
abbrev Cube (n : ℕ) := Fin (n+1) → unitInterval
abbrev Punctured (n : ℕ) := {t : Cube n // t≠0}
variable {n : ℕ}
def radius (t : Cube n) : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => (t i:ℝ))

def weight (t : Punctured n) (i : Fin (n+1)) : ℝ := max ((t.1 i:ℝ)/radius t.1-1/2) 0
def total (t : Punctured n) : ℝ := ∑ i,weight t i

def g (δ : ℝ) (t : unitInterval) : ℝ := max (1-2*(t:ℝ)/δ) 0

def H (δ : ℝ) (t : Cube n) : ℝ := 1-∏ i,g δ (t i)
end KirchbergRordam.GenericRW.CubeWeights
end

end OAI
end

section
-- module Solutions.OAIB3_Krc.CharacterCriterion_AmplifiedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GenericRW.ConeCut
open scoped CStarAlgebra ComplexOrder BigOperators
open MatrixMix

def coeff (δ : ℝ) (t : unitInterval) : ℝ := max ((t:ℝ)-δ) 0
end KirchbergRordam.GenericRW.ConeCut

end

end OAI
end


