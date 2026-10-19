-- Prove2me | Definitions.Def_MIPRE_Background_QLD_WinMS
-- name    : MIPRE_Background_QLD_WinMS
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:51.634985+00:00
-- url     : https://prove2.me/theorems/d9fe3237-dbaa-45ab-83e9-8b8306cb6954
-- title:
--   Definitions of WinMS: The Magic Square item of the win implications Blueprint `lem:qld-win`, item 6 (the paper's `enu:qld-ms` in…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.WinMS` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The Magic Square item of the win implications. Blueprint `lem:qld-win`, item 6 (the paper's `enu:qld-ms` in `lem:qld-win-implications`). It is the one item that is not a consistency relation: it says that on an *anticommuting* tuple `ω` the Pauli basis test's own `Constraint`/`Variable` measurements form a strategy for the Magic Square game of value `1 - O(ε)`. Composed with `lem:ms-direct-anticomm` --- which is what the Magic Square is in the test for --- it gives the anticommutator bound this file ends with, and that bound is what the expansion stage's sign cancellation runs on.
--
--   **Definitions** (6): `MIPRE.QLD.msAns` (The reading of a Pauli-test answer as an answer of the Magic Square game.); `MIPRE.QLD.msAssign` (A constraint answer read as a full assignment: its three bits at the constraint's cells and `0` elsewhere.); `MIPRE.QLD.msEps` (The error the conditional Magic Square strategy inherits: the Magic Square game's own question-weighted sum of the Pauli test's conditional…); `MIPRE.QLD.msPOVM` (**The conditional Magic Square strategy of the tuple `ω`.**); `MIPRE.QLD.msQ` (The Pauli-test question a Magic Square question corresponds to, at the tuple `ω`.); `MIPRE.QLD.msTy` (The question type a Magic Square question corresponds to.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.WinMS` (`MIPRE/Background/QLD/WinMS.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 36 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/WinMS.lean; blueprint lem:qld-win

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/WinMS.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
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
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Win
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Theorems.Thm_MIPRE_POVM_posSemidef

/-!
# The Magic Square item of the win implications

Blueprint `lem:qld-win`, item 6 (the paper's `enu:qld-ms` in `lem:qld-win-implications`). It is
the one item that is not a consistency relation: it says that on an *anticommuting* tuple `ω`
the Pauli basis test's own `Constraint`/`Variable` measurements form a strategy for the Magic
Square game of value `1 - O(ε)`. Composed with `lem:ms-direct-anticomm` --- which is what the
Magic Square is in the test for --- it gives the anticommutator bound this file ends with, and
that bound is what the expansion stage's sign cancellation runs on.

## The conditional strategy

`msPOVM M ω` is the strategy: at a Magic Square question `x` it is the Pauli test's measurement
at the corresponding question `msQ ω x`, relabelled into the Magic Square's answer alphabet by
`msAns`. The relabelling is where the paper's `F_2^3` constraint answers meet the layout's full
`F_2^9` assignments: `msAssign` places the three bits at the constraint's cells
(`MIPRE.LCS.MagicSquare.cell`) and `0` elsewhere, which is invisible to the Magic Square decider
because it reads only the support.

`sum_weight_bornProb_map` is what makes the relabelling harmless: relabelling outcomes is data
processing, so the relabelled strategy wins whenever the original answers would have been
accepted. That is `condFail_ms_le` --- the Magic Square failure at an incidence is at most the
Pauli test's failure at the corresponding question pair.

## The error, and why it is a sum over the incidences

`msEps` is the Magic Square game's own question-weighted sum of those Pauli-test failures, so
`one_sub_povmValue_ms_le` is immediate off the support --- where the Magic Square distribution
puts no mass, and the two deciders need not agree at all. On the support the pair *is* an
oriented incidence, hence an edge of the Pauli test's type graph, and `subtest_le` applies. The
average of `msEps` over the anticommuting tuples is then `86 ε`, one factor of `86` and not
thirty-six, because the Magic Square's own distribution is normalized.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LCS.MagicSquare

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The conditional Magic Square strategy -/

/-- The question type a Magic Square question corresponds to. -/
def msTy : layout.Question → Ty
  | .inl i => .con i
  | .inr j => .var j

/-- The Pauli-test question a Magic Square question corresponds to, at the tuple `ω`. -/
def msQ (ω : Omega F m) : layout.Question → Question F m
  | .inl i => .con i ω
  | .inr j => .var j ω

/-- A constraint answer read as a full assignment: its three bits at the constraint's cells and
`0` elsewhere. The Magic Square decider reads only the support, so the padding is invisible. -/
def msAssign (i : Fin layout.r) : Answer F m d → (Fin layout.s → ZMod 2)
  | .bitTriple α => fun k => ∑ t : Fin 3, if cell i t = k then α t else 0
  | _ => fun _ => 0

/-- The reading of a Pauli-test answer as an answer of the Magic Square game. -/
def msAns : layout.Question → Answer F m d → layout.Answer
  | .inl i, a => .inl (msAssign i a)
  | .inr _, a => .inr (rdBit a)

/-- **The conditional Magic Square strategy of the tuple `ω`.** -/
def msPOVM (M : Question F m → POVM (Answer F m d) dA) (ω : Omega F m) :
    layout.Question → POVM layout.Answer dA :=
  fun x => (M (msQ ω x)).map (msAns x)

/-! ## The assignment reads the three bits -/

/-! ## The Pauli test's Magic Square rule implies the Magic Square game's decider -/

/-! ## The failure transfers -/

section Transfer

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}

/-- The error the conditional Magic Square strategy inherits: the Magic Square game's own
question-weighted sum of the Pauli test's conditional failures. -/
def msEps (hm : m ∣ Fintype.card F) (ψ : dA × dB → ℂ)
    (MA : Question F m → POVM (Answer F m d) dA) (MB : Question F m → POVM (Answer F m d) dB)
    (ω : Omega F m) : ℝ :=
  ∑ x : layout.Question, ∑ y : layout.Question,
    layout.questionDist x y * condFail (qldGame hm) ψ MA MB (msQ ω x) (msQ ω y)

/-! ## The point observables

The first half of the paper's `lem:qld-win-implications-obs`: item 1 at the two-outcome probe,
then `xStateDist_obsOf_le`. -/

/-! ## The anticommutator bound

`lem:ms-direct-anticomm` applied to the conditional strategy of each anticommuting tuple, then
averaged. This is what the expansion stage consumes. -/

end Transfer

end MIPRE.QLD

end


