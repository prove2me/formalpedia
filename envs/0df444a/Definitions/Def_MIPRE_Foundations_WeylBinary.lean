-- Prove2me | Definitions.Def_MIPRE_Foundations_WeylBinary
-- name    : MIPRE_Foundations_WeylBinary
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:22.873453+00:00
-- url     : https://prove2.me/theorems/09f70bc4-43eb-41c8-b3eb-03b0f47b79b4
-- title:
--   Definitions of WeylBinary: From qudits to qubits: the generalized Pauli system is a qubit Pauli system Blueprint `lem:pauli-binary`
-- statement:
--   The definitions of the module `MIPRE.Foundations.WeylBinary` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). From qudits to qubits: the generalized Pauli system is a qubit Pauli system. Blueprint `lem:pauli-binary`. A self-dual basis of `F_q` over `F_2` identifies `F_q^n` with `F_2^{n x k}`, and under that identification **every piece of the Weyl data over `F_q` becomes the corresponding piece over `F_2`**: the form `trDot`, the two operator families, their spectral projectors, and the maximally entangled state.
--
--   **Definitions** (1): `MIPRE.Weyl.binEquiv` (**The coordinate relabelling** `F_q^n ≃ F_2^{n x k}` attached to a basis `b` of `F_q` over `F_2`: send `a` to its matrix of coordinates.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `binEquiv_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.WeylBinary` (`MIPRE/Foundations/WeylBinary.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 18 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/WeylBinary.lean; blueprint lem:pauli-binary

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/WeylBinary.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDual
import Definitions.Def_MIPRE_Foundations_LowDegree_NormalBasis
import Definitions.Def_MIPRE_Foundations_WeylEPR

/-!
# From qudits to qubits: the generalized Pauli system is a qubit Pauli system

Blueprint `lem:pauli-binary`. A self-dual basis of `F_q` over `F_2` identifies `F_q^n` with
`F_2^{n x k}`, and under that identification **every piece of the Weyl data over `F_q` becomes the
corresponding piece over `F_2`**: the form `trDot`, the two operator families, their spectral
projectors, and the maximally entangled state.
-/

noncomputable section

namespace MIPRE.Weyl

open Finset Matrix MIPRE MIPRE.LowDegree

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

/-! ## The relabelling -/

/-- **The coordinate relabelling** `F_q^n ≃ F_2^{n x k}` attached to a basis `b` of `F_q` over
`F_2`: send `a` to its matrix of coordinates. -/
def binEquiv (b : Module.Basis ι (ZMod 2) F) : (n → F) ≃ (n × ι → ZMod 2) :=
  (Equiv.piCongrRight fun _ => b.equivFun.toEquiv).trans (Equiv.curry n ι (ZMod 2)).symm

variable {b : Module.Basis ι (ZMod 2) F}

@[simp] theorem binEquiv_apply (a : n → F) (p : n × ι) :
    binEquiv (n := n) b a p = b.repr (a p.1) p.2 := rfl

/-! ## The form -/

/-! ## The operator families

Both are carried over by `Matrix.submatrix` along the relabelling --- which is conjugation by the
permutation unitary the paper calls the isometry `phi`, written as a reindexing of rows and
columns so that no unitary has to be constructed. -/

/-! ## The spectral projectors

The Fourier average commutes with the relabelling: the index group is reindexed by it, the
character is the transported form, and the normalization is the same cardinality counted on
either side. -/

/-! ## The maximally entangled state -/

/-! ## The five items together -/

/-! ## The target system is qubits, register by register

The binary Weyl system is `Weyl` at `F = F_2` and index set `n x k`, whose matrices are indexed by
the functions `n x k → F_2` --- that is, by the computational basis of `(C^2)^{⊗ nk}`. These three
identities say that the operators are the *tensor products* of the single-qubit ones, in the only
sense the one-matrix presentation can state it: entry by entry, as a product over the qubits. They
are what makes "these are qubit Paulis" a checked statement rather than a reading of the encoding.
-/

section Qubits

variable {m : Type*} [Fintype m] [DecidableEq m]

end Qubits

end MIPRE.Weyl

end


