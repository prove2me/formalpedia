-- Prove2me | Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
-- name    : MIPRE_Background_QLD_CLExplicitTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:05:25.78234+00:00
-- url     : https://prove2.me/theorems/f20e01c5-da11-4b2d-a2a2-2a4978d947ff
-- title:
--   Definitions of CLExplicitTransport: Equivalences between explicit and legacy Pauli question contents Only line questions carry the seed
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.CLExplicitTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Equivalences between explicit and legacy Pauli question contents. Only line questions carry the seed. Permuting that coordinate on their raw contents gives a genuine equivalence, including contents outside the support of the sampler. The same permutation of the shared random seed intertwines all twenty-six sampled question maps simultaneously.
--
--   **Definitions** (4): `MIPRE.QLD.PauliCL.ExplicitSeed.binaryOutputPermutation` (Raw binary output-question equivalence, in the supplied basis.); `MIPRE.QLD.PauliCL.ExplicitSeed.binarySeedPermutation` (The corresponding permutation of the common binary random content.); `MIPRE.QLD.PauliCL.ExplicitSeed.outputPermutation` (Raw output-question equivalence; only the two line families retain a seed.); `MIPRE.QLD.PauliCL.ExplicitSeed.vectorPermutation` (Change the field seed coordinate and leave every other coordinate intact.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `binaryOutputPermutation_pauli`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.CLExplicitTransport` (`MIPRE/Background/QLD/CLExplicitTransport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 54 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLExplicitTransport.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLExplicitTransport.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed

/-! # Equivalences between explicit and legacy Pauli question contents

Only line questions carry the seed. Permuting that coordinate on their raw
contents gives a genuine equivalence, including contents outside the support
of the sampler. The same permutation of the shared random seed intertwines
all twenty-six sampled question maps simultaneously.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL.ExplicitSeed
open Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- Change the field seed coordinate and leave every other coordinate intact. -/
def vectorPermutation (π : F ≃ F) : (Coord m → F) ≃ (Coord m → F) :=
  contentEquiv.symm.trans ((contentPermutation π).trans contentEquiv)

/-- Raw output-question equivalence; only the two line families retain a seed. -/
def outputPermutation (π : F ≃ F) : Ty → ((Coord m → F) ≃ (Coord m → F))
  | .aline _ | .dline _ => vectorPermutation π
  | _ => Equiv.refl _

variable [NeZero m]

section Binary
variable [Algebra (ZMod 2) F] {t : ℕ}

/-- Raw binary output-question equivalence, in the supplied basis. -/
def binaryOutputPermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (T : Ty) : (Fin ((3*m+3)*t) → ZMod 2) ≃ (Fin ((3*m+3)*t) → ZMod 2) :=
  (binaryVectorEquiv b).toEquiv.symm.trans
    ((outputPermutation π T).trans (binaryVectorEquiv b).toEquiv)

/-- The corresponding permutation of the common binary random content. -/
def binarySeedPermutation (π : F ≃ F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    (Fin ((3*m+3)*t) → ZMod 2) ≃ (Fin ((3*m+3)*t) → ZMod 2) :=
  (binaryVectorEquiv b).toEquiv.symm.trans
    ((vectorPermutation π).trans (binaryVectorEquiv b).toEquiv)

@[simp] theorem binaryOutputPermutation_pauli (π : F ≃ F)
    (b : Module.Basis (Fin t) (ZMod 2) F) (W : Bas)
    (x : Fin ((3*m+3)*t) → ZMod 2) :
    binaryOutputPermutation π b (.pauli W) x = x :=
  (binaryVectorEquiv b).apply_symm_apply x

end Binary
end MIPRE.QLD.PauliCL.ExplicitSeed


