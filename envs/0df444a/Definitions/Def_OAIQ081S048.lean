-- Prove2me | Definitions.Def_OAIQ081S048
-- name    : OAIQ081S048
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:39:13.432228+00:00
-- url     : https://prove2.me/theorems/47221039-e86d-4db9-96c4-59849ce9d437
-- title:
--   Definitions bundle OAIQ081S048 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 113 declarations of OpenAI's Lean: 91 definitions, 1 inductive type or structure and 21 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixPeek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preReversePeek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signaturePeek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureSeed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.AddService.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.addCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell.updateCell`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.accumulate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.addCmd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.addProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.callAt`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingBasis.R`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingBasis.basis`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingBasis.coordinates`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.E`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.coordinates`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldCoordinates`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.readBase`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.reducedEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.rho`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.sectionValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.WordTriple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadHead`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadWordProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.loadY`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.scalarAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceClear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceExpand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.serviceRoute` and 52 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramAddService`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramCell`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramPair`, `SubexponentialSAT_SqrtLog_IrreducibleSearchCompanion`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_RingBasis`, `SubexponentialSAT_SqrtLog_RingModel`, `SubexponentialSAT_SqrtLog_RingProgramBounds`, `SubexponentialSAT_SqrtLog_RingProgramCompanion`, `SubexponentialSAT_SqrtLog_RingProgramWords`, `SubexponentialSAT_SqrtLog_RingScanAdd`, `SubexponentialSAT_SqrtLog_RingScanLoad`, `SubexponentialSAT_SqrtLog_RingScanService`, `SubexponentialSAT_SqrtLog_RingScanServiceBasic`, `SubexponentialSAT_SqrtLog_RingScanServiceLifts`, `SubexponentialSAT_SqrtLog_RingScanTriple`, `SubexponentialSAT_SqrtLog_RingScanTripleLoop`, `SubexponentialSAT_SqrtLog_RingTripleBasic`, `SubexponentialSAT_SqrtLog_RingTripleExpand`, `SubexponentialSAT_SqrtLog_RingTripleMatrix`, `SubexponentialSAT_SqrtLog_RingTripleProgram`, `SubexponentialSAT_SqrtLog_RingTripleRowStep`, `SubexponentialSAT_SqrtLog_RingTripleRows`, `SubexponentialSAT_SubexpActualRing`, `SubexponentialSAT_SubexpConvolutionControl`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpJetCellProgram`, `SubexponentialSAT_SubexpJetInitProgram`, `SubexponentialSAT_SubexpLinearFactorCall`, `SubexponentialSAT_SubexpLinearFactorProgram`, `SubexponentialSAT_SubexpLocalCRTSetup`, `SubexponentialSAT_SubexpNodeScanControl`, `SubexponentialSAT_SubexpPolynomialAddService`, `SubexponentialSAT_SubexpPolynomialConstructor`, `SubexponentialSAT_SubexpPolynomialServiceControl`, `SubexponentialSAT_SubexpPreparedQuartic`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S027` and `OAIQ081S028` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S067`, `OAIQ081S068`, `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S080` and `OAIQ081S081`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S027
import Definitions.Def_OAIQ081S028

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessReverse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed EOF-controlled reversal of a raw list of framed words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

abbrev preReversePeek : PreReverseCode := .base (.atom (.peek 0 0 1))

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def preMatrixPeek : PreMatrixCode := .base (.atom (.peek 14 0 1))

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def signatureSeed : SignatureCode := .base
  (.seq (.atom (.set 0 true)) (.atom (.push 2 0)))

def signaturePeek : SignatureCode := .base (.atom (.peek 13 0 1))

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPreparedQuartic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Quartic operations with a stored modulus

The modulus is input data. None of the operations in this file computes
`p^mu`, its bit expansion, or an irreducible polynomial. Setup is separate.
-/

namespace SubexponentialSAT.SubexpPreparedQuartic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p μ : ℕ) [Fact p.Prime]

variable (M : Modulus p μ)

/-- A stored zero word avoids computing any residue representation inside
the negation callback. -/
def zeroWord : Word (baseWidth p μ) :=
  ⟨List.replicate (baseWidth p μ) false, by simp⟩

omit [Fact (Nat.Prime p)] in
@[simp] theorem zeroWord_value : wordValue p μ (zeroWord p μ) = 0 := by
  have hz (n : ℕ) : BinaryArithmetic.toNat (List.replicate n false) = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, toNat_cons, bitVal_false, ih]
  simp [wordValue, zeroWord, hz]

end SubexponentialSAT.SubexpPreparedQuartic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpActualRing
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The counting ring from the executable quartic search

Both the residue field and the prime-power ring use the coefficients returned
by QuarticSearch. No separately chosen minimum polynomial enters this file.
The polynomial quotient is the semantic interpretation of those coefficients;
the executable four-coordinate arithmetic is implemented separately.
-/

noncomputable section
namespace SubexponentialSAT.SubexpActualRing

open Polynomial

/-- Reindex the linear remainder coordinates by a proved exact degree. -/
def coordinatesOfDegree {A : Type*} [CommRing A] {d : ℕ}
    (f : A[X]) (hf : f.Monic) (hd : f.natDegree = d) :
    LiftRing.Extension f ≃ₗ[A] (Fin d → A) :=
  hd ▸ LiftRing.coordinates hf

@[simp] theorem coordinatesOfDegree_apply {A : Type*} [CommRing A] {d : ℕ}
    (f : A[X]) (hf : f.Monic) (hd : f.natDegree = d)
    (x : LiftRing.Extension f) (i : Fin d) :
    coordinatesOfDegree f hf hd x i = (LiftRing.remainder hf x).coeff i := by
  subst d
  rfl

@[simp] theorem coordinatesOfDegree_symm_apply {A : Type*} [CommRing A] {d : ℕ}
    (f : A[X]) (hf : f.Monic) (hd : f.natDegree = d) (a : Fin d → A) :
    (coordinatesOfDegree f hf hd).symm a =
      LiftRing.mk f (∑ i : Fin d, monomial i (a i)) := by
  subst d
  rfl

end SubexponentialSAT.SubexpActualRing

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

abbrev E := LiftRing.Extension a.residuePolynomial
abbrev O := LiftRing.Extension (a.F t)

def reducedEquiv (ht : 0 < t) :
    LiftRing.Extension ((a.F t).map (LiftRing.baseReduction 3 t ht)) ≃+* a.E :=
  Ideal.quotEquivOfEq
    (congrArg (fun f : (ZMod 3)[X] => Ideal.span ({f} : Set (ZMod 3)[X])) (a.F_map t ht))

def rho (ht : 0 < t) : a.O t →+* a.E :=
  (a.reducedEquiv t ht).toRingHom.comp (LiftRing.residue 3 t ht (a.F t))

@[simp] theorem rho_mk (ht : 0 < t) (q : (Base t)[X]) :
    a.rho t ht (LiftRing.mk (a.F t) q) =
      LiftRing.mk a.residuePolynomial (q.map (LiftRing.baseReduction 3 t ht)) := rfl

def fieldCoordinates : a.E ≃ₗ[ZMod 3] (Fin d → ZMod 3) :=
  SubexpActualRing.coordinatesOfDegree a.residuePolynomial a.residuePolynomial_monic
    a.residuePolynomial_degree

@[simp] theorem fieldCoordinates_symm_apply (c : Fin d → ZMod 3) :
    a.fieldCoordinates.symm c =
      LiftRing.mk a.residuePolynomial (∑ i : Fin d, monomial i (c i)) :=
  SubexpActualRing.coordinatesOfDegree_symm_apply _ _ _ c

def coordinates (ht : 0 < t) : a.O t ≃ₗ[Base t] (Fin d → Base t) :=
  SubexpActualRing.coordinatesOfDegree (a.F t) (a.F_monic t ht) (a.F_degree t ht)

@[simp] theorem coordinates_apply (ht : 0 < t) (x : a.O t) (i : Fin d) :
    a.coordinates t ht x i = (LiftRing.remainder (a.F_monic t ht) x).coeff i :=
  SubexpActualRing.coordinatesOfDegree_apply _ _ _ x i

@[simp] theorem coordinates_symm_apply (ht : 0 < t) (c : Fin d → Base t) :
    (a.coordinates t ht).symm c = LiftRing.mk (a.F t) (∑ i : Fin d, monomial i (c i)) :=
  SubexpActualRing.coordinatesOfDegree_symm_apply _ _ _ c

/-- No preimage choice is used: lift every residue coefficient separately. -/
def sectionValue (ht : 0 < t) (z : a.E) : a.O t :=
  (a.coordinates t ht).symm (fun i => ((a.fieldCoordinates z i).val : Base t))

@[simp] theorem rho_sectionValue (ht : 0 < t) (z : a.E) :
    a.rho t ht (a.sectionValue t ht z) = z := by
  rw [sectionValue, coordinates_symm_apply, rho_mk]
  simp only [Polynomial.map_sum, Polynomial.map_monomial, map_natCast, ZMod.natCast_zmod_val]
  rw [← fieldCoordinates_symm_apply]
  exact a.fieldCoordinates.symm_apply_apply z

def base : Base t →+* a.O t := LiftRing.of (a.F t)

def readBase (ht : 0 < t) (x : a.O t) : Base t :=
  (LiftRing.remainder (a.F_monic t ht) x).coeff 0

@[simp] theorem readBase_base (ht : 0 < t) (hd : d ≠ 0) (c : Base t) :
    a.readBase t ht (a.base t c) = c := by
  unfold readBase base
  rw [LiftRing.remainder_of _ (by rw [a.F_degree t ht]; omega)]
  simp

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingBasis
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Finite multiplication tables for any monic polynomial quotient. -/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingBasis

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A] {d : ℕ}
variable (F : A[X]) (hF : F.Monic) (hdegree : F.natDegree = d)

abbrev R := LiftRing.Extension F

def coordinates : R F ≃ₗ[A] (Fin d → A) :=
  SubexpActualRing.coordinatesOfDegree F hF hdegree

def basis (i : Fin d) : R F := LiftRing.mk F (X ^ (i : ℕ))

@[simp] theorem coordinates_apply (x : R F) (i : Fin d) :
    coordinates F hF hdegree x i = (LiftRing.remainder hF x).coeff i :=
  SubexpActualRing.coordinatesOfDegree_apply _ _ _ x i

/-- Reconstruction from d coordinates uses the ordinary quotient power basis. -/
theorem reconstruct (x : R F) :
    (∑ i : Fin d, LiftRing.of F (coordinates F hF hdegree x i) * basis F i) = x := by
  have hx := (coordinates F hF hdegree).symm_apply_apply x
  rw [coordinates, SubexpActualRing.coordinatesOfDegree_symm_apply] at hx
  calc
    _ = LiftRing.mk F (∑ i : Fin d, monomial i (coordinates F hF hdegree x i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← C_mul_X_pow_eq_monomial]
      simp only [basis, LiftRing.of, RingHom.comp_apply, map_mul]
    _ = x := hx

/-- A coefficient vector is reconstructed as this same finite linear sum. -/
theorem coordinates_symm (c : Fin d → A) :
    (coordinates F hF hdegree).symm c =
      ∑ i : Fin d, LiftRing.of F (c i) * basis F i := by
  rw [coordinates, SubexpActualRing.coordinatesOfDegree_symm_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial]
  simp only [basis, LiftRing.of, RingHom.comp_apply, map_mul]

theorem basis_mul_coordinates (i j k : Fin d) :
    coordinates F hF hdegree (basis F i * basis F j) k = structureConstant F i j k := by
  rw [coordinates_apply]
  simp only [basis, ← map_mul, ← pow_add, LiftRing.remainder_mk, structureConstant]

include hF hdegree in
/-- The d^3 multiplication entries suffice for arbitrary quotient arithmetic. -/
theorem basis_mul (i j : Fin d) :
    basis F i * basis F j =
      ∑ k : Fin d, LiftRing.of F (structureConstant F i j k) * basis F k := by
  calc
    _ = ∑ k : Fin d, LiftRing.of F (coordinates F hF hdegree (basis F i * basis F j) k) * basis F k :=
      (reconstruct F hF hdegree _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [basis_mul_coordinates]

/-- The constant one has the unit vector at index zero. -/
theorem one_coordinates (hd : 0 < d) (i : Fin d) :
    coordinates F hF hdegree 1 i = if i.val = 0 then 1 else 0 := by
  rw [coordinates_apply]
  have hpos : 0 < F.natDegree := by omega
  have hone : (1 : R F) = LiftRing.of F 1 := (map_one _).symm
  rw [hone, LiftRing.remainder_of hF hpos]
  simp only [Polynomial.C_1, Polynomial.coeff_one]

end SubexponentialSAT.SqrtLog.RingBasis

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramWords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-width base-ring words for arbitrary extension degree. The arithmetic
programs below are the audited fixed scalar programs; the degree does not occur
in their instruction tables. Extension-vector scanning is a separate layer. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.BitProgram SubexponentialSAT.ModularRingPrograms SubexponentialSAT.ModularDivisionPrograms

variable (p t : ℕ) [Fact p.Prime]

abbrev ScalarCode := Word (baseWidth p t)

structure ScalarCache where
  zero : ScalarCode p t
  one : ScalarCode p t
  minusOne : ScalarCode p t
  zero_correct : wordValue p t zero = 0
  one_correct : wordValue p t one = 1
  minusOne_correct : wordValue p t minusOne = -1

variable (M : SubexpPreparedQuartic.Modulus p t)

/-- Flat coefficient-vector ABI: coefficient zero first, each word little endian. -/
def flat {d B : ℕ} (x : Code (Word B) d) : List Bool :=
  (List.ofFn fun i => (x i).val).flatten

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem ternary_baseWidth (t : ℕ) : baseWidth 3 t = 2 * t := by
  have hlog : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp [baseWidth, hlog, Nat.mul_comm]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchCompanion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit companion recurrence for the supplied monic polynomial

This module supplies the structure constants needed by the dynamic ring
program. It executes only coefficient-vector operations; polynomial
remainder is used solely to state and prove its meaning.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

section Correctness

variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]
variable {d : ℕ} (hd : 0 < d) (c a : Fin d → R)
include hd

omit [Nontrivial R] in
theorem ofFn_mulX :
    Polynomial.ofFn d (mulX c a) = X * Polynomial.ofFn d a -
      C (entry a (d - 1)) * QuarticSearch.poly c := by
  apply Polynomial.ext
  intro j
  rw [coeff_sub, coeff_C_mul]
  cases j with
  | zero =>
      rw [coeff_X_mul_zero, ← candidateEntry_eq_coeff]
      simp [ entry, mulX, candidateEntry, hd,
        show (0 : ℕ) ≠ d by omega]
  | succ j =>
      rw [coeff_X_mul, ← candidateEntry_eq_coeff]
      by_cases hj : j + 1 < d
      · have hj0 : j < d := by omega
        simp [ entry, mulX, candidateEntry, hj, hj0,
          show j + 1 ≠ d by omega]
      · by_cases he : j + 1 = d
        · have hj0 : j < d := by omega
          have hsub : d - 1 = j := by omega
          simp [ entry, candidateEntry, he, hsub, hj0]
        · have hj0 : ¬j < d := by omega
          simp [ofFn_coeff_entry, entry, candidateEntry, hj, hj0, he]

omit [Nontrivial R] in
theorem polynomial_dvd_power_sub_ofFn (n : ℕ) :
    QuarticSearch.poly c ∣ X ^ n - Polynomial.ofFn d (powerVector c n) := by
  induction n with
  | zero => simp [powerVector, ofFn_oneVector hd]
  | succ n ih =>
      rw [powerVector, cacheVector_eq, ofFn_mulX hd c]
      have he : X ^ (n + 1) - (X * Polynomial.ofFn d (powerVector c n) -
          C (entry (powerVector c n) (d - 1)) * QuarticSearch.poly c) =
          X * (X ^ n - Polynomial.ofFn d (powerVector c n)) +
            C (entry (powerVector c n) (d - 1)) * QuarticSearch.poly c := by
        rw [pow_succ]
        ring
      rw [he]
      exact dvd_add (dvd_mul_of_dvd_right ih X) (dvd_mul_left _ _)

theorem ofFn_powerVector (n : ℕ) :
    Polynomial.ofFn d (powerVector c n) = X ^ n %ₘ QuarticSearch.poly c := by
  have he := Polynomial.modByMonic_eq_of_dvd_sub (QuarticSearch.poly_monic c)
    (polynomial_dvd_power_sub_ofFn hd c n)
  have hlt : (Polynomial.ofFn d (powerVector c n)).degree < (QuarticSearch.poly c).degree := by
    rw [degree_eq_natDegree (QuarticSearch.poly_monic c).ne_zero, QuarticSearch.poly_natDegree]
    exact Polynomial.ofFn_degree_lt _
  rw [(Polynomial.modByMonic_eq_self_iff (QuarticSearch.poly_monic c)).mpr hlt] at he
  exact he.symm

theorem structureTable_eq_coeff (i j k : Fin d) :
    structureTable c i j k = (X ^ (i.val + j.val) %ₘ QuarticSearch.poly c).coeff k.val := by
  rw [← ofFn_powerVector hd c]
  exact (Polynomial.ofFn_coeff_eq_val_of_lt _ k.isLt).symm

end Correctness

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramCompanion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable measured generation of dynamic monic-quotient multiplication
constants. Polynomial remainder occurs only in the correctness theorem. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

theorem structureTableRun_remainder [Nontrivial A] [DecidableEq A]
    (ops : RepresentedRing C A) {d : ℕ} (hd : 0 < d)
    (c : Code C d) (i j k : Fin d) :
    ops.decode ((structureTableRun ops.program c).1 i j k) =
      (Polynomial.X ^ (i.val + j.val) %ₘ
        SubexponentialSAT.QuarticSearch.poly (fun i => ops.decode (c i))).coeff k.val := by
  rw [structureTableRun_correct, IrreducibleSearch.structureTable_eq_coeff hd]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native addition of dense polynomial arrays whose coefficients have an
arbitrary runtime extension degree. The fixed scanner visits base words;
there is no quartet assumption and no generated instruction table. -/

namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

/-- This code is the same fixed scalar-word scanner for every extension degree,
polynomial length, modulus, and coefficient width. -/
abbrev addCmd : Cmd 8 20 := SubexponentialSAT.DensePolynomialPrograms.addCmd

abbrev addProgram : Program 8 20 (size addCmd + 1) := compiled addCmd 8 8

end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite control for triangular, truncated convolution

Polynomial coefficients occupy equal-width flat cells. Both input arrays have
D cells. The left array is consumed; the right array is retained. The output
array is preallocated with D zero cells. Unary loop counters and indices are
runtime stacks, so changing D does not change this control program.

The scalar product-and-accumulate command is inserted as a fixed command. Its
concrete implementation uses the quartic multiplier and the persistent cell
updater; it is never a semantic-function instruction.
-/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

/-- Order-preserving copy; stack 120 is reserved scratch. -/
def copy (src dst : Fin 256) : Code := .call (StackRoutines.copyProgram src dst 120 0 1)

def clear (src : Fin 256) : Code := .call (StackRoutines.clearProgram src 0 1)

def appendIndex (index : Fin 256) : Code :=
  (.base (.atom (.set 0 false))) ;; (.base (.atom (.push index 0)))

def popToken (counter : Fin 256) : Code := .base (.atom (.pop counter 0 1))

def test (counter : Fin 256) (flag : Fin 16) : Code := .base (.atom (.peek counter 0 flag))

/-- Stack 104 holds the unary coefficient width, and 121--122 are scratch. -/
def takeCell (src dst : Fin 256) : Code := takeWord 104 121 122 src dst 0 1

/-- One actual (i,j) iteration. The inserted fixed command consumes operands
198/199 and accumulates into output cell indexed by unary stack 103. -/
def innerStep (pair : Code) : Code :=
  popToken 109 ;; takeCell 108 199 ;; copy 110 198 ;; pair ;; appendIndex 103

def innerLoop (pair : Code) : Code :=
  test 109 15 ;; .while 15 (innerStep pair ;; test 109 15)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialAddService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cached dense addition for the local CRT controller. The fixed service
copies operands 240/241, invokes the actual dense-add instruction table, and
moves its output to 244. All native workspace is restored. -/

namespace SubexponentialSAT.SubexpPolynomialAddService

open BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

def transfer (src dst : Fin 256) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)
def finish : Code := .seq (transfer 8 245) (transfer 245 244)

end SubexponentialSAT.SubexpPolynomialAddService

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramAddService
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The arbitrary-degree native adder relocated into a caller, with all
untouched stacks preserved. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.DensePolynomialLoop
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t)

/-- Relocate the fixed addition program into a caller's physical workspace. -/
abbrev callAt {r s : ℕ} (registers : Fin 8 ↪ Fin r) (ports : Fin 20 ↪ Fin s) : Cmd r s :=
  .call (ProgramLinking.liftProgram addProgram registers ports)


namespace AddService
open SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpPolynomialAddService

def command : Code := .seq (copy 240 8) (.seq (copy 241 9)
  (.seq (DensePolynomialProgram.callAt registers ports) finish))

end AddService
end SubexponentialSAT.SqrtLog.DensePolynomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetCellProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Concrete addition into one packed jet cell

The persistent jet, unary index, and cell width are on stacks 102, 103, and
104. The array subprogram uses 112--117, and order-preserving moves use 118.
All instruction tables are fixed independently of widths and indices. The
full service reads the old cell, invokes the actual flattened quartic adder,
and writes the sum back. Its endpoint changes only the contribution and jet
stacks; all other caller stacks and registers 8--15 are preserved.
-/

namespace SubexponentialSAT.SubexpJetCellProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def copyIndex : Code := .call (StackRoutines.copyProgram 103 113 114 0 1)

def arrayRead : Code := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.readProgram (0 : Fin 16) 1) id arrayPorts)

def arrayReplace : Code := .call (ProgramLinking.liftProgram
  (ArrayUpdatePrograms.replaceProgram (0 : Fin 16) 1) id arrayPorts)

def moveForward (src dst : Fin 128) : Code :=
  .seq (.call (StackRoutines.transferProgram src 118 0 1))
    (.call (StackRoutines.transferProgram 118 dst 0 1))

def clear (src : Fin 128) : Code := .call (StackRoutines.clearProgram src 0 1)

end SubexponentialSAT.SubexpJetCellProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramCell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native update of one arbitrary-degree ring coefficient in a persistent
flat polynomial array. Every scan, copy, and scalar addition is paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpJetCellProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def addCall : Code := .call
  (SubexponentialSAT.ProgramLinking.liftProgram DensePolynomialProgram.addProgram regPorts scalarPorts)

variable (p t : ℕ)
  [Fact p.Prime]
  (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
  (cache : RingProgram.ScalarCache p t)
  (hB : 0 < baseWidth p t)
  {degree : ℕ}

def updateCell : Code :=
  .seq copyIndex (.seq arrayRead (.seq (moveForward 112 9) (.seq addCall
    (.seq (moveForward 8 112) (.seq copyIndex (.seq arrayReplace (clear 112)))))))

abbrev program : Program 16 128 (StructuredCalls.size updateCell + 1) :=
  StructuredCalls.compiled updateCell 8 102


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Cell

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed-control dynamic coefficient loader

The source contains a flat vector. A preserved unary width word determines
how many bits are removed. Exactly that many bits are prefixed, in their
original order, to the destination. Control size is independent of both the
width and the number of coefficients.
-/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines ArrayPrograms

abbrev loadWord : Cmd 2 5 :=
  .seq (.call (copyProgram 2 3 4 0 1))
    (.seq (.call (countedTransferProgram 3 0 4 0 1))
      (.call (transferProgram 4 1 0 1)))

abbrev loadWordProgram : Program 2 5 (size loadWord + 1) := compiled loadWord 0 1

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanAdd
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar addition inside a flat, runtime-sized coefficient scan. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev loadY : Cmd 8 15 := .call (ProgramLinking.liftProgram loadWordProgram loadRegisters loadYStacks)

abbrev scalarAdd : Cmd 8 15 := .call (ProgramLinking.liftProgram
  ModularRingPrograms.wordAddProgram id scalarStacks)

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTriple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native three-scalar product and accumulator step. Triples are serialized
as consecutive fixed-width words; both width and triple count remain data. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev loadHead : Cmd 8 15 := .call (ProgramLinking.liftProgram
  loadWordProgram loadRegisters loadHeadStacks)

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanTripleLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-control streaming contraction of arbitrary many scalar triples. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev WordTriple (B : ℕ) := Word B × Word B × Word B

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port primitives for dynamic Cartesian triple expansion. All loop
bounds and coefficient widths are words on stacks, not generated code. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev clear (dst : Fin 16) : Cmd 2 16 := .call (clearProgram dst 0 1)

abbrev load (which : Fin 3) : Cmd 2 16 := .call
  (ProgramLinking.liftProgram RingScan.loadWordProgram id (loadPorts which))

abbrev emitTriple : Cmd 2 16 :=
  .seq (copy 6 8) (.seq (transfer 8 3) (.seq (load 0)
    (.seq (transfer 7 3) (.seq (load 1) (transfer 8 3)))))

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev jLoop : Cmd 2 16 := .while 1 (.seq emitTriple popJ)
abbrev jScan : Cmd 2 16 := .seq popJ jLoop

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleRowStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev startRow : Cmd 2 16 := .seq (load 2) (.seq (copy 1 5) (copy 9 12))

abbrev rowStep : Cmd 2 16 := .seq startRow (.seq jScan (clear 6))

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

abbrev iLoop : Cmd 2 16 := .while 1 (.seq rowStep popI)
abbrev iScan : Cmd 2 16 := .seq popI iLoop

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleExpand
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

abbrev matrixStep : Cmd 2 16 := .seq startMatrix iScan

abbrev kLoop : Cmd 2 16 := .while 1 (.seq matrixStep popK)
abbrev kScan : Cmd 2 16 := .seq popK kLoop

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingTripleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

/-- Three nested counted scans. Degree and width are runtime stack data. -/
abbrev expand : Cmd 2 16 := .seq (copy 9 10) (.seq kScan (transfer 3 4))

def program := compiled expand 2 4

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Shared native coefficient-ring ABI. All service programs have fixed size. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceClear (dst : Fin 32) : Cmd 8 32 := .call (clearProgram dst 1 3)

abbrev serviceRoute : Cmd 8 32 := .seq (serviceClear 8) (.seq (serviceClear 9)
  (.seq (serviceTransfer 23 21) (serviceTransfer 21 9)))

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanServiceLifts
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceExpand : Cmd 8 32 := .call
  (ProgramLinking.liftProgram RingTriple.program loadRegisters serviceExpandPorts)


end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingScanService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native service for arbitrary-degree coefficient-ring products. -/
namespace SubexponentialSAT.SqrtLog.RingScan
open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev serviceFinish : Cmd 8 32 := serviceClear 16

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# One actual product-and-accumulate step for packed jet convolution

The global state has sixteen Boolean registers and 256 Boolean-word stacks.
The multiplier occupies the fixed high bank beginning at 128. Its result is
moved, with order preserved, to the low-bank jet-cell accumulator service.
-/

namespace SubexponentialSAT.SubexpConvolutionPair

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

def moveProduct : Code :=
  .seq (.call (StackRoutines.transferProgram (200 : Fin 256) 119 (0 : Fin 16) 1))
    (.call (StackRoutines.transferProgram (119 : Fin 256) 8 (0 : Fin 16) 1))

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native arbitrary-width coefficient multiply-and-accumulate. The high
workspace computes the ring product; the low workspace updates one encoded
array cell. Its runtime index scans and all transfers are explicitly paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Code := SubexponentialSAT.SubexpConvolutionControl.Code

def accumulate : Code := .call (ProgramLinking.liftProgram Cell.program id lowPort)

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

abbrev Data := State 19 24

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

def value (v : Fin 64 → ℕ) : Instr → ℕ
  | .clear _ => 0
  | .load _ bits => BinaryArithmetic.toNat bits
  | .copy a _ _ => v a
  | .add a b _ _ _ => v a + v b
  | .mul a b _ _ _ => v a * v b
  | .pow a b _ _ _ => v a ^ v b
  | .quot a b _ _ _ => v a / v b
  | .sqrt a _ _ => Nat.sqrt (v a)
  | .logSucc a => Nat.log2 (v a)+1
  | .addConst a k => v a+k
  | .pred a => v a-1
  | .maxTwo a => max 2 (v a)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitRun -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Initializing the packed output jet

The input dimension is a unary word on stack 109 and the scalar word width is
the length of stack 10.  The fixed program constructs one four-word zero
coefficient on stack 104 and copies it D times to stack 102.  It preserves both
input words.  No zero array is supplied as an input certificate.
-/

namespace SubexponentialSAT.SubexpJetInitProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev repeatCell : Code := .call (ProgramLinking.liftProgram
  Subexp.BlockCopyProgram.program blockRegisters blockStacks)

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLinearFactorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime construction of a padded linear polynomial. The low and high
coefficient cells occupy stacks 100 and 101. The unary dimension is on 109,
the base-word width is on 10, and the output array is on 102. -/

namespace SubexponentialSAT.SubexpLinearFactorProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def copyLow : Code := .call (StackRoutines.copyProgram 100 102 107 0 1)
def copyHigh : Code := .call (StackRoutines.copyProgram 101 102 107 0 1)
def popDimension : Code := .base (.atom (.pop 108 0 1))

def resetRegisters : Code :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 false))) (.base (.atom (.set 2 false))))

def longCase : Code :=
  .seq resetRegisters (.seq SubexpJetInitProgram.repeatCell (.seq copyHigh copyLow))

def fromCounter : Code :=
  .seq popDimension
    (.ite 1 (.seq popDimension (.ite 1 longCase copyLow)) (.base .skip))

end SubexponentialSAT.SubexpLinearFactorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLinearFactorCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Invoke the padded-linear constructor in the 256-stack polynomial
workspace, retaining a previously constructed zero coefficient on 104. -/

namespace SubexponentialSAT.SubexpLinearFactorCall

open BitProgram StructuredCalls SubexpConvolutionControl

def command : Code :=
  liftCommand SubexpLinearFactorProgram.fromCounter 108 102 id ports

end SubexponentialSAT.SubexpLinearFactorCall

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialServiceControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical marshalling for a reusable truncated-product service. Cached
operands, a zero array, and the unary dimension occupy 240--243. The native
convolution buffers are restored after each invocation and the result goes
to 244. All copying, clearing, and reversal is performed by fixed programs. -/

namespace SubexponentialSAT.SubexpPolynomialServiceControl

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpConvolutionControl

def transfer (src dst : Fin 256) : Code :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 16) 1)

def finish : Code :=
  .seq (clear 101) (.seq (transfer 102 245) (transfer 245 244))

end SubexponentialSAT.SubexpPolynomialServiceControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable physical construction of a padded polynomial from two scalar
cells and a cached unary dimension. The native constructor buffers are
cleared on return; an order-preserving move writes the chosen cache slot. -/

namespace SubexponentialSAT.SubexpPolynomialConstructor

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer )

def move (src dst : Fin 256) : Code := .seq (transfer src 245) (transfer 245 dst)

def constructAtInputs (dst : Fin 256) : Code :=
  .seq (copy 243 108) (.seq SubexpLinearFactorCall.command
    (.seq (clear 100) (.seq (clear 101) (move 102 dst))))

def construct (low high dst : Fin 256) : Code :=
  .seq (copy low 100) (.seq (copy high 101) (constructAtInputs dst))

end SubexponentialSAT.SubexpPolynomialConstructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCRTSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual cache initialization for one local CRT correction. The zero and
one arrays are physically built from scalar cells and the runtime dimension;
the complete node stream and unary skip index are then copied into work.
-/

namespace SubexponentialSAT.SubexpLocalCRTSetup

open BitProgram StructuredCalls SubexpConvolutionControl

local infixr:55 " ;; " => seq

def clearMany : List (Fin 256) → Code
  | [] => .base .skip
  | i :: rest => clear i ;; clearMany rest

def token (dst : Fin 256) : Code :=
  .base (.seq (.atom (.set 0 true)) (.atom (.push dst 0)))

end SubexponentialSAT.SubexpLocalCRTSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpNodeScanControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed traversal of flat node cells, skipping one unary-indexed node.
The included-node service is an actual command with an actual execution
contract. This file accounts for all reads, guards, index pops, and cleanup.
-/

namespace SubexponentialSAT.SubexpNodeScanControl

open BitProgram StructuredCalls SubexpConvolutionControl

def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def choose (includeNode : Code) : Code :=
  test 217 13 ;; .ite 13 (popToken 217 ;; includeNode)
    (test 229 13 ;; .ite 13 (clear 229) includeNode)

def step (includeNode : Code) : Code :=
  takeCell 215 218 ;; choose includeNode ;; clear 218 ;; clear 219

def command (includeNode : Code) : Code :=
  test 215 15 ;; .while 15 (step includeNode ;; test 215 15)

end SubexponentialSAT.SubexpNodeScanControl

end OAI.Algorithms
end


