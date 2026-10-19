-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_HonestPauliMeasurements
-- name    : MIPRE_Background_Introspection_HonestPauliMeasurements
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:00.959686+00:00
-- url     : https://prove2.me/theorems/ac3874d2-d464-4aac-b026-7158b00082e9
-- title:
--   Definitions of HonestPauliMeasurements: The honest measurements for all twenty-six Pauli question types Every measurement uses the same field register tensor…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.HonestPauliMeasurements` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The honest measurements for all twenty-six Pauli question types. Every measurement uses the same field register tensor one qubit. The low-degree questions read functions of a Pauli outcome; the commuting and anticommuting branches use the actual verifier phase. All answer constructors and inactive branches are explicit.
--
--   **Definitions** (11): `MIPRE.QLD.Honest.Space`; `MIPRE.QLD.Honest.answerOp` (All twenty-six measurements on the actual question and answer alphabets.); `MIPRE.QLD.Honest.constraintBranch`; `MIPRE.QLD.Honest.liftOp`; `MIPRE.QLD.Honest.lineAnswer` (The polynomial coefficient answer to a line query.); `MIPRE.QLD.Honest.pairBBranch`; `MIPRE.QLD.Honest.pairBranch`; `MIPRE.QLD.Honest.pairLabel`; `MIPRE.QLD.Honest.pauliLift`; `MIPRE.QLD.Honest.probeLift`; `MIPRE.QLD.Honest.variableBranch`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `fibre_format_zero`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.HonestPauliMeasurements` (`MIPRE/Background/Introspection/HonestPauliMeasurements.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 60 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/HonestPauliMeasurements.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/HonestPauliMeasurements.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_LowDegree_LineRestrict
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables

/-! # The honest measurements for all twenty-six Pauli question types

Every measurement uses the same field register tensor one qubit. The low-degree
questions read functions of a Pauli outcome; the commuting and anticommuting
branches use the actual verifier phase. All answer constructors and inactive
branches are explicit.
-/

noncomputable section

namespace MIPRE.QLD.Honest

open Matrix Finset Weyl LCS Introspection Classical
open scoped Kronecker

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}

abbrev Space (F : Type*) (m : ℕ) := Register F m × Fin 2

def liftOp (M : Matrix (Register F m) (Register F m) ℂ) : Matrix (Space F m) (Space F m) ℂ :=
  M ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)

def pauliLift (W : Bas) (h : Register F m) : Matrix (Space F m) (Space F m) ℂ :=
  liftOp (pauliOp W h)

def probeLift (ω : Omega F m) (W : Bas) (b : ZMod 2) : Matrix (Space F m) (Space F m) ℂ :=
  liftOp (probeOp ω W b)

/-- The polynomial coefficient answer to a line query. -/
def lineAnswer (n : ℕ) (u v : LIDT.Point F m) (h : Register F m) : LIDT.LinePoly F n :=
  fun i => (LowDegree.lineRestrict u v (LowDegree.ldEnc h)).coeff i.val

def pairLabel (p : ZMod 2 × ZMod 2) : Bas → ZMod 2
  | .X => p.1
  | .Z => p.2

def pairBranch (ω : Omega F m) : (Bas → ZMod 2) → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then
    fibSum (fun p : ZMod 2 × ZMod 2 => probeLift ω .X p.1 * probeLift ω .Z p.2) pairLabel
  else readout (fun _ : Space F m => (0 : Bas → ZMod 2))

def pairBBranch (ω : Omega F m) (W : Bas) : ZMod 2 → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then probeLift ω W else readout (fun _ : Space F m => (0 : ZMod 2))

def constraintBranch (ω : Omega F m) (c : Fin LCS.MagicSquare.layout.r) :
    (Fin 3 → ZMod 2) → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then readout (fun _ : Space F m => (0 : Fin 3 → ZMod 2))
  else HonestMagicSquare.constraintOp (basis .X (probeVector ω .X)) (basis .Z (probeVector ω .Z)) c

def variableBranch (ω : Omega F m) (j : Fin LCS.MagicSquare.layout.s) :
    ZMod 2 → Matrix (Space F m) (Space F m) ℂ :=
  if gam ω = 0 then readout (fun _ : Space F m => (0 : ZMod 2))
  else HonestMagicSquare.variableOp (basis .X (probeVector ω .X)) (basis .Z (probeVector ω .Z)) j

/-- All twenty-six measurements on the actual question and answer alphabets. -/
def answerOp [NeZero m] (hm : m ∣ Fintype.card F) :
    Question F m → Answer F m d → Matrix (Space F m) (Space F m) ℂ
  | .point W u => fibSum (pauliLift W) (fun h => .val (MvPolynomial.eval u (LowDegree.ldEnc h)))
  | .aline W u s => fibSum (pauliLift W)
      (fun h => .apoly (lineAnswer d u (Pi.single (LIDT.CL.chi hm s) 1) h))
  | .dline W u _ v => fibSum (pauliLift W) (fun h => .dpoly (lineAnswer (m * d) u v h))
  | .pauli W => fibSum (pauliLift W) Answer.pauliAns
  | .pairB W ω => fibSum (pairBBranch ω W) Answer.bit
  | .pair ω => fibSum (pairBranch ω) Answer.bitPair
  | .con c ω => fibSum (constraintBranch ω c) Answer.bitTriple
  | .var j ω => fibSum (variableBranch ω j) Answer.bit

omit [Field F] [Fintype F] [Algebra (ZMod 2) F] in
theorem fibre_format_zero {X : Type*} [Fintype X]
    (P : X → Matrix (Space F m) (Space F m) ℂ) (f : X → Answer F m d)
    (q : Question F m) (hf : ∀ x, q.fmtOk (f x) = true) (a : Answer F m d)
    (ha : q.fmtOk a = false) : fibSum P f a = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hx' : f x = a := (Finset.mem_filter.mp hx).2
  have hh := hf x
  rw [hx', ha] at hh
  contradiction

end MIPRE.QLD.Honest


