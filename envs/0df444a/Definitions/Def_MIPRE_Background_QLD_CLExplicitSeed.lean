-- Prove2me | Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
-- name    : MIPRE_Background_QLD_CLExplicitSeed
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:04:36.522991+00:00
-- url     : https://prove2.me/theorems/2d2220b3-589b-4d5e-bc81-d2141032c03c
-- title:
--   Definitions of CLExplicitSeed: Pauli sampling with the explicit binary seed enumeration The sampler retains its canonical binary seed and uses the…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.CLExplicitSeed` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pauli sampling with the explicit binary seed enumeration. The sampler retains its canonical binary seed and uses the efficient high-bit selector. Only the mathematical decoder permutes that seed to the enumeration used in `qldGame`. A permutation of the common random content proves equality with the existing QLD question law, including the line seeds in the questions.
--
--   **Definitions** (8): `MIPRE.QLD.PauliCL.ExplicitSeed.binaryDecode`; `MIPRE.QLD.PauliCL.ExplicitSeed.binaryPresentation`; `MIPRE.QLD.PauliCL.ExplicitSeed.contentPermutation` (Permute just the shared seed; all other random content stays fixed.); `MIPRE.QLD.PauliCL.ExplicitSeed.decode` (Decode the explicit seed into the fixed enumeration used by the legacy QLD question type.); `MIPRE.QLD.PauliCL.ExplicitSeed.finalMap`; `MIPRE.QLD.PauliCL.ExplicitSeed.presentation` (The concrete three-stage presentation with a specified seed selector.); `MIPRE.QLD.PauliCL.ExplicitSeed.secondMap`; `MIPRE.QLD.PauliCL.ExplicitSeed.seedPermutation` (The concrete permutation from canonical bit rank to the legacy numbering.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.CLExplicitSeed` (`MIPRE/Background/QLD/CLExplicitSeed.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 53 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLExplicitSeed.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLExplicitSeed.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
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
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex

/-! # Pauli sampling with the explicit binary seed enumeration

The sampler retains its canonical binary seed and uses the efficient high-bit
selector. Only the mathematical decoder permutes that seed to the enumeration
used in `qldGame`. A permutation of the common random content proves equality
with the existing QLD question law, including the line seeds in the questions.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
open MIPRE.Introspection.SeedProgram
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

def secondMap (χ : F → Fin m) (t : Ty) (s : F) :
    CL.RegLinear F (directionSet m) :=
  match t with
  | .dline _ => directionMap (χ s)
  | _ => 0

def finalMap (χ : F → Fin m) (t : Ty) (s : F) (v : Fin m → F) :
    CL.RegLinear F (finalSet m) :=
  match t with
  | .point W => pointMap W LinearMap.id
  | .aline W => pointMap W (CL.canonLin (Submodule.span F {Pi.single (χ s) 1}))
  | .dline W => pointMap W (CL.canonLin (Submodule.span F {v}))
  | .pauli _ => 0
  | _ => CL.RegLinear.id _

/-- The concrete three-stage presentation with a specified seed selector. -/
def presentation (χ : F → Fin m) (t : Ty) : CL.CLFun F (Coord m) 3 :=
  .cons (seedSet m) (seedMap t) fun y =>
    .cons (directionSet m) (secondMap χ t (y .seed)) fun z =>
      .cons (finalSet m) (finalMap χ t (y .seed) (fun i => z (.direction i)))
        fun _ => .zero

/-- Permute just the shared seed; all other random content stays fixed. -/
def contentPermutation (π : F ≃ F) : Content F m ≃ Content F m where
  toFun c := ⟨c.uX, c.uZ, π c.s, c.v, c.rX, c.rZ⟩
  invFun c := ⟨c.uX, c.uZ, π.symm c.s, c.v, c.rX, c.rZ⟩
  left_inv c := by cases c; simp
  right_inv c := by cases c; simp

/-- Decode the explicit seed into the fixed enumeration used by the legacy
QLD question type. No program needs to evaluate this mathematical relabelling. -/
def decode (π : F ≃ F) (t : Ty) (x : Coord m → F) : Question F m :=
  let c := contentPermutation π (vectorContent x)
  match t with
  | .point W => .point W (c.pt W)
  | .aline W => .aline W (c.pt W) c.s
  | .dline W => .dline W (c.pt W) c.s c.v
  | .pauli W => .pauli W
  | .pairB W => .pairB W c.omega
  | .pair => .pair c.omega
  | .con i => .con i c.omega
  | .var j => .var j c.omega

variable [NeZero m]

section Binary
variable [Algebra (ZMod 2) F] {t : ℕ}

def binaryPresentation (χ : F → Fin m) (b : Module.Basis (Fin t) (ZMod 2) F) (T : Ty) :
    CL.CLFun (ZMod 2) (Fin ((3 * m + 3) * t)) 3 :=
  ((presentation χ T).downsize b).reindex (binaryCoordEquiv m t)

def binaryDecode (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (T : Ty) (x : Fin ((3 * m + 3) * t) → ZMod 2) : Question F m :=
  decode π T ((binaryVectorEquiv b).symm x)

end Binary

/-- The concrete permutation from canonical bit rank to the legacy numbering. -/
def seedPermutation {k : ℕ} (E : SAT.BinField k) : E.carrier ≃ E.carrier :=
  ((fieldEnumeration E).trans (finCongr E.card_carrier.symm)).trans
    (Fintype.equivFin E.carrier).symm

end MIPRE.QLD.PauliCL.ExplicitSeed
end


