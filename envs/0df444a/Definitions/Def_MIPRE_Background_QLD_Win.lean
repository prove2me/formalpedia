-- Prove2me | Definitions.Def_MIPRE_Background_QLD_Win
-- name    : MIPRE_Background_QLD_Win
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:11.670491+00:00
-- url     : https://prove2.me/theorems/2bd183a4-b880-41a2-995d-ef1d8c892625
-- title:
--   Definitions of Win: What winning the Pauli basis test implies Blueprint `lem:qld-win`, the paper's `lem:qld-win-implications`…
-- statement:
--   The definitions of the module `MIPRE.Background.QLD.Win` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). What winning the Pauli basis test implies. Blueprint `lem:qld-win`, the paper's `lem:qld-win-implications` (`qld-commutation.tex`). A strategy succeeding with probability `1 - ε` satisfies one cross-party consistency relation per subtest, each at error `O(ε)` --- and the blueprint's proof is exactly one sentence: "each item is the definition of the value of the corresponding subtest, divided by the probability that the subtest is selected". This file makes that sentence mechanical, in two steps.
--
--   **Definitions** (9): `MIPRE.QLD.acommSet` (The contents whose tuple is *anticommuting*, `γ(ω) ≠ 0`.); `MIPRE.QLD.commSet` (The contents whose tuple is *commuting*, `γ(ω) = 0`.); `MIPRE.QLD.dirOf` (The axis-parallel direction the seed selects.); `MIPRE.QLD.rdBit` (The bit a `(Pair, W)` or `Variable_j` answer reports.); `MIPRE.QLD.rdBitPair` (The `W`-component of a `Pair` answer.); `MIPRE.QLD.rdPauli` (The low-degree encoding of a `(Pauli, W)` answer, evaluated at `y`: the paper's `g_h(y)`.); `MIPRE.QLD.rdProbe` (The trace probe `tr(a · r)` of a point answer: the two-outcome measurement the commutation and Magic Square checks compare against.); `MIPRE.QLD.rdProbeAt` (The trace probe of a point answer against the `W`-side qubit basis element of the content.); `MIPRE.QLD.rdVal` (The field element a point answer reports.).
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.QLD.Win` (`MIPRE/Background/QLD/Win.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 32 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/Win.lean; blueprint def:qld-game

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Win.lean (definition bundle: declarations the uploaded statements rest on);
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

/-!
# What winning the Pauli basis test implies

Blueprint `lem:qld-win`, the paper's `lem:qld-win-implications` (`qld-commutation.tex`). A
strategy succeeding with probability `1 - ε` satisfies one cross-party consistency relation per
subtest, each at error `O(ε)` --- and the blueprint's proof is exactly one sentence: "each item
is the definition of the value of the corresponding subtest, divided by the probability that the
subtest is selected".

This file makes that sentence mechanical, in two steps.

## Step one: every subtest is selected with probability at least `1/86`

`qldGame`'s question distribution is uniform over `TyEdge × Content`, so a question pair arising
from a *fixed* ordered type edge has probability at least `1/86` times the conditional
probability of its content (`le_qldGame_mu`). `subtest_le` is the consequence: for any edge
`(t, u)` of the type graph, the content-averaged conditional failure at that edge is at most
`86 ε`. The `86` is `card_adj`, the ordered pairs of the type graph, and it is where the
paper's "the probability of any of the subtests being executed is at least some universal
constant" becomes a number.

Nothing here is about which subtest it is: one lemma serves all seven, because the
distribution factors.

## Step two: each item is an agreement subtest

`MIPRE.xSqNorm_sum_le_condFail` turns "the decider accepts iff `f a = g b`" into a bound on the
cross-party deviation of the POVMs coarse-grained along `f` and `g`. So each item of the lemma
is: name `f` and `g`, check the decider against them, and compose with `subtest_le`. That
composition is `agree_subtest_le`, and the seven items below are its instances --- the
identity for the plain consistency check, a polynomial evaluation for the low-degree check, the
low-degree encoding for Pauli-basis consistency, a projection for the commutation check, and the
trace probe `prb` for the two commutation- and Magic-Square-consistency checks.

The Magic Square item itself is not of this shape --- it is a statement about the *value* of a
conditional Magic Square strategy, which is what `lem:ms-direct-anticomm` consumes --- and it is
in `MIPRE/Background/QLD/WinMS.lean`.
-/

noncomputable section

namespace MIPRE.QLD

open Finset MIPRE MIPRE.LIDT MIPRE.LCS.MagicSquare

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m d : ℕ}
  [NeZero m] {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]

/-! ## The size of the sample space -/

/-! ## Every subtest is selected with probability at least `1/86` -/

/-! ## Each item is an agreement subtest -/

/-! ## The readings each rule compares

A rule of `fig:decider_pauli` compares a post-processing of Alice's answer with one of Bob's.
Each is named here, with `0` on answers of the wrong format --- which costs nothing, because the
format check rejects those before any rule runs, and `xSqNorm_sum_le_condFail` only needs
*accept implies agree*. -/

/-- The field element a point answer reports. -/
def rdVal : Answer F m d → F
  | .val a => a
  | _ => 0

/-- The low-degree encoding of a `(Pauli, W)` answer, evaluated at `y`: the paper's
`g_h(y)`. -/
def rdPauli (y : Point F m) : Answer F m d → F
  | .pauliAns h => MvPolynomial.eval y (MIPRE.LowDegree.ldEnc h)
  | _ => 0

/-- The bit a `(Pair, W)` or `Variable_j` answer reports. -/
def rdBit : Answer F m d → ZMod 2
  | .bit b => b
  | _ => 0

/-- The `W`-component of a `Pair` answer. -/
def rdBitPair (W : Bas) : Answer F m d → ZMod 2
  | .bitPair β => β W
  | _ => 0

/-- The trace probe `tr(a · r)` of a point answer: the two-outcome measurement the commutation
and Magic Square checks compare against. -/
def rdProbe (r : F) : Answer F m d → ZMod 2
  | .val a => prb a r
  | _ => 0

/-- The axis-parallel direction the seed selects. -/
def dirOf (hm : m ∣ Fintype.card F) (c : Content F m) : Point F m :=
  Pi.single (MIPRE.LIDT.CL.chi hm c.s) 1

/-! ## The commuting and anticommuting contents

Four rules are gated on `γ(ω)` and check nothing on the other value, so their statements carry
the gate as a restriction of the content average. -/

/-- The contents whose tuple is *commuting*, `γ(ω) = 0`. -/
def commSet : Finset (Content F m) := univ.filter fun c => gam c.omega = 0

/-- The contents whose tuple is *anticommuting*, `γ(ω) ≠ 0`. -/
def acommSet : Finset (Content F m) := univ.filter fun c => gam c.omega ≠ 0

/-! ## The edges the rules live on -/

/-! ## The items

Each is `agree_subtest_le` at a named edge with the two readings the rule compares. -/

section Items

variable {hm : m ∣ Fintype.card F} {ψ : dA × dB → ℂ}
  {MA : Question F m → POVM (Answer F m d) dA} {MB : Question F m → POVM (Answer F m d) dB}
  {ε : ℝ}

/-! ### Inverting the format check

`accepts` rejects before any rule runs unless both answers have the shape their question's type
prescribes, so each rule may be read on one pair of constructors only. These are the inversions,
one per answer format; they are what keeps the proofs of the items below to a single branch
instead of the forty-nine a blind case split would produce. -/

/-- The trace probe of a point answer against the `W`-side qubit basis element of the
content. -/
def rdProbeAt (W : Bas) (c : Content F m) : Answer F m d → ZMod 2 :=
  rdProbe (c.omega.r W)

end Items

end MIPRE.QLD

end


