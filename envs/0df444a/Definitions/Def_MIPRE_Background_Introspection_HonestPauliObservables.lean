-- Prove2me | Definitions.Def_MIPRE_Background_Introspection_HonestPauliObservables
-- name    : MIPRE_Background_Introspection_HonestPauliObservables
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:48.775132+00:00
-- url     : https://prove2.me/theorems/f74a5abc-240e-4c16-8167-56c1428aa290
-- title:
--   Definitions of HonestPauliObservables: The concrete Pauli probes of the honest QLD strategy Low-degree evaluation followed by the verifier's field trace is…
-- statement:
--   The definitions of the module `MIPRE.Background.Introspection.HonestPauliObservables` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The concrete Pauli probes of the honest QLD strategy. Low-degree evaluation followed by the verifier's field trace is exactly the binary spectral measurement of a Weyl observable. The verifier's `gam` is proved to equal the commutation phase of the two observables.
--
--   **Definitions** (6): `MIPRE.QLD.Honest.Register`; `MIPRE.QLD.Honest.basis`; `MIPRE.QLD.Honest.pauliOp`; `MIPRE.QLD.Honest.probeLabel`; `MIPRE.QLD.Honest.probeOp`; `MIPRE.QLD.Honest.probeVector`.
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `signed_fibre`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.Introspection.HonestPauliObservables` (`MIPRE/Background/Introspection/HonestPauliObservables.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 42 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/HonestPauliObservables.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Introspection/HonestPauliObservables.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_HonestMagicSquare
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! # The concrete Pauli probes of the honest QLD strategy

Low-degree evaluation followed by the verifier's field trace is exactly the
binary spectral measurement of a Weyl observable. The verifier's `gam` is
proved to equal the commutation phase of the two observables.
-/

noncomputable section

namespace MIPRE.QLD.Honest

open Matrix Finset Weyl LCS

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m : ℕ}

abbrev Register (F : Type*) (m : ℕ) := (Fin m → Bool) → F

def basis (W : Bas) : Register F m → Matrix (Register F m) (Register F m) ℂ :=
  match W with
  | .X => wX
  | .Z => wZ

def pauliOp (W : Bas) : Register F m → Matrix (Register F m) (Register F m) ℂ := proj (basis W)

def probeVector (ω : Omega F m) (W : Bas) : Register F m :=
  ω.r W • LowDegree.indVec (ω.pt W)

def probeLabel (ω : Omega F m) (W : Bas) (h : Register F m) : ZMod 2 :=
  prb (MvPolynomial.eval (ω.pt W) (LowDegree.ldEnc h)) (ω.r W)

def probeOp (ω : Omega F m) (W : Bas) : ZMod 2 → Matrix (Register F m) (Register F m) ℂ :=
  fibSum (pauliOp W) (probeLabel ω W)

theorem signed_fibre {X I : Type*} [Fintype X] [Fintype I] [DecidableEq I]
    (P : X → Matrix I I ℂ) (f : X → ZMod 2) :
    ∑ b : ZMod 2, sgn b • fibSum P f b = ∑ x, sgn (f x) • P x := by
  unfold fibSum
  simp only [Finset.smul_sum]
  calc
    _ = ∑ b : ZMod 2, ∑ x ∈ univ.filter (fun x => f x = b), sgn (f x) • P x := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := Finset.sum_fiberwise univ f (fun x => sgn (f x) • P x)

end MIPRE.QLD.Honest


