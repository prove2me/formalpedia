-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularTensor
-- name    : MIPRE_Foundations_OracularTensor
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:25.964381+00:00
-- url     : https://prove2.me/theorems/74eb78fc-e807-4c84-bfe7-3c7f312bff88
-- title:
--   Definitions of OracularTensor: Soundness of oracularization, for bipartite strategies Item 2 of blueprint `thm:oracularization`…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularTensor` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization, for bipartite strategies. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so `val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`. `MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That is not the statement a verifier-level consumer can use:…
--
--   **Definitions** (7): `MIPRE.OAns.aliceView` (An oracularized answer read as the answer meant for the original Alice: an oracle's pair is read as its first component; an isolated…); `MIPRE.OAns.bobView` (An oracularized answer read as the answer meant for the original Bob.); `MIPRE.SeededGame.accPairs` (The answer pairs the input decider accepts at the question pair the seed determines.); `MIPRE.SeededGame.oracleGood` (The oracle's own answer passes the game check: it is a pair, which the input decider accepts at the question pair the seed determines.); `MIPRE.SeededGame.oracleView` (The oracle's measurement at `(oracle, z)`, coarse-grained along a view of its answer.); `MIPRE.SeededGame.singlePairEmb` (Pairs of isolated answers.); `MIPRE.SeededGame.tensorSound` (**The strategy extracted from a bipartite strategy for the oracularization**: Alice plays the first player's isolated-Alice measurement,…).
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `toPOVM_mats_val`, `singlePairEmb_apply`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularTensor` (`MIPRE/Foundations/OracularTensor.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 21 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularTensor.lean; blueprint lem:oracular-soundness-model, lem:oracular-soundness-tensor

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
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
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex

/-!
# Soundness of oracularization, for bipartite strategies

Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness-tensor`), at the level of
games and for **arbitrary tensor-product strategies**: a strategy of value at least `1 - ε` for
`MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the input game, and so
`val*` of the oracularization above `1 - ε` puts `val*` of the input at least `1 - 24√ε`.

`MIPRE/Foundations/OracularSound.lean` proves the same bound for *synchronous* strategies. That
is not the statement a verifier-level consumer can use: `Verifier.valStar` is a supremum over
`TensorProductStrategy`, and so is the detyping transport (`restrictAmbient_value_ge`), while the
only bridge from synchronous to bipartite values, `thm:almost-sync`, is off the critical path.
The paper's `thm:oracle-soundness` is bipartite; this is its game-level form.

## The argument

Every `TensorProductStrategy` is projective, so no Naimark dilation is needed. Fix a seed `z` and
write, on the joint space, `O` for the first player's oracle measurement at `(oracle, z)`,
`O^𝖠`, `O^𝖡` for its two component marginals (`OAns.aliceView`, `OAns.bobView`), `C` for the
first player's isolated-Alice measurement at `L^𝖠 z`, and `P`, `Q` for the second player's
isolated-Alice and isolated-Bob measurements at `L^𝖠 z` and `L^𝖡 z`. Then

`C_u ⊗ Q_v - O^𝖠_u O^𝖡_v ⊗ Id = (Id ⊗ Q_v)(C_u ⊗ Id - Id ⊗ P_u)`
  `+ (Id ⊗ Q_v)(Id ⊗ P_u - O^𝖠_u ⊗ Id) + (O^𝖠_u ⊗ Id)(Id ⊗ Q_v - O^𝖡_v ⊗ Id)`

(`sum_snorm_sq_chain`). Each front factor is a projective measurement, so it costs nothing summed
over its outcome (`sum_snorm_sq_mul_le`), and each of the three deviations is the cross-party
consistency of one role pair --- `(alice, alice)`, `(oracle, alice)`, `(oracle, bob)` --- hence at
most twice that pair's conditional failure (`xSqNorm_sum_le_condFail`). So the product strategy is
within `6` times three conditional failures of the oracle's joint marginal, linearly in `ε`.

The single square root of repair 1 of `rem:oracularization-repairs` is spent once, in
`sum_snorm_sq_ge_of_close`: the paper's `fact:approx-implies-close-value` (NW19's Fact 4.31) at
the level of vectors, which compares the mass two families with total mass at most one put on the
set of outcome pairs the input decider accepts. The oracle's joint marginal puts mass at least the
oracle's own acceptance probability at `(oracle, oracle)` there.

Averaging, the four role pairs used are distinct and each carries a ninth of the question weight,
so their conditional failures average to at most `9ε` in total (`sum_failAt_four_le`), and
`val ≥ 1 - 9ε - 2√(54ε) ≥ 1 - 24√ε`: the synchronous constant. Neither the paper's
marginalization step nor its commutation step is needed, because the oracle's measurement enters
only through its joint marginal and the second player's two isolated measurements are multiplied
in one order only.

The extracted strategy (`tensorSound`) is the adapter `TensorProductStrategy.adapt`: the first
player's isolated-Alice measurement and the second player's isolated-Bob measurement, relabelled
along `OAns.singlePart` so that an oracle-shaped answer is grouped into one distinguished outcome.
-/

namespace MIPRE

open Finset Matrix
open scoped ComplexOrder MatrixOrder

/-! ## Reading an oracle's answer one component at a time -/

section Views

variable {A : Type*}

/-- An oracularized answer read as the answer meant for the original Alice: an oracle's pair is
read as its first component; an isolated player's answer is left as it is (for an oracle it is
rejected by the shape check anyway). -/
def OAns.aliceView : OAns A → OAns A
  | .pair a _ => .single a
  | .single a => .single a

/-- An oracularized answer read as the answer meant for the original Bob. -/
def OAns.bobView : OAns A → OAns A
  | .pair _ b => .single b
  | .single b => .single b

end Views

/-! ## Close measurements have close values -/

section CloseValues

variable {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]

end CloseValues

/-! ## Fibres of a projective measurement -/

section Fibres

variable {n : Type*} [Fintype n] [DecidableEq n] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

end Fibres

@[simp] theorem ProjectiveMeasurement.toPOVM_mats_val {X A : Type*} [Fintype A] {n : Type*}
    [Fintype n] [DecidableEq n] (P : ProjectiveMeasurement X A (Matrix n n ℂ)) (x : X) (a : A) :
    ((P.toPOVM x).mats a).val = P.M x a := rfl

/-! ## The chain of three deviations -/

section Chain

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

end Chain

/-! ## Born probabilities of a bipartite strategy, on the joint space -/

section Proj

variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]

end Proj

section Born

variable {X Y A' B' : Type*} [Fintype X] [Fintype Y] [Fintype A'] [Fintype B']
variable {G : Game X Y A' B'}

namespace TensorProductStrategy

end TensorProductStrategy

end Born

/-! ## The three roles -/

namespace SeededGame

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Type*} [Fintype A] [DecidableEq A] [Inhabited A]
variable (S : SeededGame V A)

/-! ## What acceptance forces -/

/-- The oracle's own answer passes the game check: it is a pair, which the input decider accepts
at the question pair the seed determines. -/
def oracleGood (z : V) : OAns A → Bool
  | .pair a b => S.D (S.LA z) (S.LB z) a b
  | .single _ => false

/-! ## The extracted strategy -/

/-- **The strategy extracted from a bipartite strategy for the oracularization**: Alice plays the
first player's isolated-Alice measurement, Bob the second player's isolated-Bob measurement, both
relabelled along `OAns.singlePart`, so that an oracle-shaped answer is grouped into one
distinguished outcome. Same state, same Hilbert spaces. -/
noncomputable def tensorSound (N : TensorProductStrategy S.oracular.toGame) :
    TensorProductStrategy S.toGame :=
  N.adapt S.toGame (fun x => (Role.alice, x)) (fun y => (Role.bob, y))
    (fun _ => OAns.singlePart) (fun _ => OAns.singlePart)

/-- The answer pairs the input decider accepts at the question pair the seed determines. -/
def accPairs (z : V) : Finset (A × A) :=
  univ.filter fun p => S.D (S.LA z) (S.LB z) p.1 p.2 = true

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
/-- Pairs of isolated answers. -/
def singlePairEmb : A × A ↪ OAns A × OAns A :=
  ⟨fun p => (OAns.single p.1, OAns.single p.2), fun p q h => by
    simp only [Prod.mk.injEq, OAns.single.injEq] at h
    exact Prod.ext h.1 h.2⟩

omit [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A] [Inhabited A] in
@[simp] theorem singlePairEmb_apply (p : A × A) :
    singlePairEmb p = (OAns.single p.1, OAns.single p.2) := rfl

variable {S}

/-- The oracle's measurement at `(oracle, z)`, coarse-grained along a view of its answer. -/
noncomputable def oracleView (N : TensorProductStrategy S.oracular.toGame) (z : V)
    (f : OAns A → OAns A) (u : OAns A) : Matrix (Fin N.dA) (Fin N.dA) ℂ :=
  ∑ w ∈ univ.filter fun w => f w = u, N.PA.M (Role.oracle, z) w

/-! ## The estimate at one seed -/

/-! ## Averaging over the seed -/

/-! ## Soundness -/

variable (S)

end SeededGame

end MIPRE


