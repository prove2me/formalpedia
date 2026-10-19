-- Prove2me | Definitions.Def_MIPRE_Background_QLD_CLTransport
-- name    : MIPRE_Background_QLD_CLTransport
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:04:29.892226+00:00
-- url     : https://prove2.me/theorems/38893622-d656-4f5b-9abe-f8e10b589463
-- title:
--   Definitions of CLTransport: Exact strategy transport between the Pauli game and its binary CL form Question content has a canonical ambient…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.CLTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact strategy transport between the Pauli game and its binary CL form. Question content has a canonical ambient encoding, with unused registers set to zero. This encoding inverts the decoder on every attained CL output. Consequently arbitrary strategies for the binary typed game pull back to the existing Pauli game with exactly the same state, dimensions, and value.
--
--   **Definitions** (9): `MIPRE.QLD.PauliCL.BinaryQuestion`; `MIPRE.QLD.PauliCL.binaryGame` (The actual typed binary CL game, with the existing Pauli acceptance rule applied to decoded questions.); `MIPRE.QLD.PauliCL.binaryQuery`; `MIPRE.QLD.PauliCL.canonicalVector` (The canonical ambient encoding of question content.); `MIPRE.QLD.PauliCL.decodeQuestion`; `MIPRE.QLD.PauliCL.encodeQuestion`; `MIPRE.QLD.PauliCL.omegaContent`; `MIPRE.QLD.PauliCL.pointContent`; `MIPRE.QLD.PauliCL.pullbackStrategy` (Play the binary game's measurements at the canonical encoding of each Pauli question.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.CLTransport` (`MIPRE/Background/QLD/CLTransport.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/CLTransport.lean

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/CLTransport.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
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

/-! # Exact strategy transport between the Pauli game and its binary CL form

Question content has a canonical ambient encoding, with unused registers set
to zero. This encoding inverts the decoder on every attained CL output.
Consequently arbitrary strategies for the binary typed game pull back to the
existing Pauli game with exactly the same state, dimensions, and value.
-/

noncomputable section
namespace MIPRE.QLD.PauliCL
open Finset Classical
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

def pointContent (W : Bas) (u : Fin m → F) (s : F) (v : Fin m → F) : Content F m :=
  match W with
  | .X => ⟨u, 0, s, v, 0, 0⟩
  | .Z => ⟨0, u, s, v, 0, 0⟩

def omegaContent (ω : Omega F m) : Content F m := ⟨ω.uX, ω.uZ, 0, 0, ω.rX, ω.rZ⟩

/-- The canonical ambient encoding of question content. -/
def canonicalVector (q : Question F m) : Coord m → F :=
  contentVector (match q with
    | .point W u => pointContent W u 0 0
    | .aline W u s => pointContent W u s 0
    | .dline W u s v => pointContent W u s v
    | .pauli _ => ⟨0, 0, 0, 0, 0, 0⟩
    | .pairB _ ω | .pair ω | .con _ ω | .var _ ω => omegaContent ω)

variable [Algebra (ZMod 2) F] [NeZero m] {t d : ℕ}

abbrev BinaryQuestion (m t : ℕ) := Ty × (Fin ((3 * m + 3) * t) → ZMod 2)

def encodeQuestion (b : Module.Basis (Fin t) (ZMod 2) F) (q : Question F m) :
    BinaryQuestion m t := (q.ty, binaryVectorEquiv b (canonicalVector q))

def decodeQuestion (b : Module.Basis (Fin t) (ZMod 2) F) (q : BinaryQuestion m t) :
    Question F m := binaryQuestion b q.1 q.2

def binaryQuery (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (w : Bool) (p : TyEdge × (Fin ((3 * m + 3) * t) → ZMod 2)) : BinaryQuestion m t :=
  let T := if w then p.1.val.2 else p.1.val.1
  (T, (binaryPresentation hm b T).eval p.2)

/-- The actual typed binary CL game, with the existing Pauli acceptance rule
applied to decoded questions. -/
def binaryGame (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F) :
    Game (BinaryQuestion m t) (BinaryQuestion m t) (Answer F m d) (Answer F m d) := by
  letI : Nonempty TyEdge := ⟨⟨(.pair, .pair), by decide⟩⟩
  exact SampledGame.game (binaryQuery hm b false) (binaryQuery hm b true)
    (fun x y a b' => accepts hm (decodeQuestion b x) (decodeQuestion b y) a b')

/-- Play the binary game's measurements at the canonical encoding of each
Pauli question. The shared state is unchanged. -/
def pullbackStrategy (hm : m ∣ Fintype.card F) (b : Module.Basis (Fin t) (ZMod 2) F)
    (S : TensorProductStrategy (binaryGame (d := d) hm b)) :
    TensorProductStrategy (qldGame (d := d) hm) where
  dA := S.dA
  dB := S.dB
  ψ := S.ψ
  ψ_unit := S.ψ_unit
  PA := S.PA.reindex (encodeQuestion b) (Equiv.refl _)
  PB := S.PB.reindex (encodeQuestion b) (Equiv.refl _)

end MIPRE.QLD.PauliCL
end


