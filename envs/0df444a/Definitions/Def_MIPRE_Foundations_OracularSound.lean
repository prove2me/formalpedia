-- Prove2me | Definitions.Def_MIPRE_Foundations_OracularSound
-- name    : MIPRE_Foundations_OracularSound
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:12.489022+00:00
-- url     : https://prove2.me/theorems/b09e5a36-e174-49c7-b1be-749108d7b4e2
-- title:
--   Definitions of OracularSound: Soundness of oracularization Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness`), at the level of…
-- statement:
--   The definitions of the module `MIPRE.Foundations.OracularSound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of oracularization. Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness`), at the level of games: a synchronous strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of value at least `1 - 24√ε` for the doubled input game. The loss carries the **single square root** that repair 1 of `rem:oracularization-repairs` insists on -- an earlier revision of the blueprint wrote `poly(ε)`, which the campaign found "not merely imprecise but false as stated". It is spent in exactly one place, `MIPRE.sum_ntr_mul_ge`; everything before it is linear in `ε`.
--
--   **Definitions** (5): `MIPRE.OAns.singlePart` (An oracularized answer read as a single answer: an isolated player's answer is itself, and an oracle's pair is grouped into the…); `MIPRE.SeededGame.cFam` (Alice's own measurement, with the oracle-shaped answers grouped into `default`.); `MIPRE.SeededGame.dFam` (Bob's own measurement, with the oracle-shaped answers grouped into `default`.); `MIPRE.SeededGame.sideMeas` (The isolated players' measurements as one projective measurement on the doubled input game's questions.); `MIPRE.SeededGame.soundStrategy` (**The extracted strategy** for the input game: the two isolated players keep their own measurements.).
--
--   **Embedded lemmas** (3): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `soundStrategy_d`, `soundStrategy_false`, `soundStrategy_true`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.OracularSound` (`MIPRE/Foundations/OracularSound.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 7 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/OracularSound.lean; blueprint lem:oracular-soundness

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularSound.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble

/-!
# Soundness of oracularization

Item 2 of blueprint `thm:oracularization` (`lem:oracular-soundness`), at the level of games: a
synchronous strategy of value at least `1 - ε` for `MIPRE.SeededGame.oracular` yields one of
value at least `1 - 24√ε` for the doubled input game.

The loss carries the **single square root** that repair 1 of `rem:oracularization-repairs`
insists on -- an earlier revision of the blueprint wrote `poly(ε)`, which the campaign found
"not merely imprecise but false as stated". It is spent in exactly one place,
`MIPRE.sum_ntr_mul_ge`; everything before it is linear in `ε`.

## The shape of the argument

* **The extracted strategy** (`soundStrategy`) is the two isolated players' own measurements,
  relabelled along `OAns.singlePart` so that an oracle-shaped answer is grouped into one
  distinguished outcome. Relabelling is what makes them *measurements* rather than
  sub-measurements, which is the game-level residue of repair 3; `SyncStrategy.push` does it,
  and a sum over a fibre is a projection because distinct outcomes are orthogonal.
* **The budget** (`budget`) is all that is taken from the hypothesis. Each of the nine ordered
  role pairs carries a ninth of the question weight, so at any one of them a set of outcome
  pairs the decider rejects carries mass at most `9ε` on average over the seed. Three
  instances (`gammaTerm_budget`, `betaTerm_budget`, `alphaTerm_budget`) are used: the oracle's
  own pair is accepted, and each isolated player agrees with the oracle's component.
* **The closeness estimate** (`sqDist_le`, from `MIPRE.sum_hsNormSq_sub_le`) bounds the
  squared Hilbert--Schmidt distance between the oracle's relabelled measurement and the
  product of the two isolated players' by three times the sum of the two disagreements --
  linearly, with no square root.
* **The value comparison** (`valSeed_ge`, from `MIPRE.sum_ntr_mul_ge`) is where the square
  root enters, and one more Cauchy--Schwarz takes the average inside it.

For a synchronous strategy the state is the normalized trace, so the paper's state-dependent
`≈_δ` is the normalized Hilbert--Schmidt distance of `MIPRE/Foundations/Distances.lean`; see
blueprint `rem:distance-state`. `MIPRE/Foundations/Closeness.lean` is that calculus.

## Scope

Nothing here inhabits `MIPRE.Oracularization`: that is done at the level of verifiers, in
`Foundations/Pipeline/Oracularization.lean`, whose bipartite soundness rests on
`Foundations/OracularTensor.lean` rather than on the synchronous argument here. The complexity
clause, the bounded parse and its grouping, the truncation to `B_𝒟(n)` and the level accounting
are all statements about a verifier and none of them appears at this level;
`rem:oracular-game-level` records that.
-/

namespace MIPRE

open Finset Matrix

/-! ## Relabelling an oracularized answer -/

variable {A : Type*} [Inhabited A]

/-- An oracularized answer read as a single answer: an isolated player's answer is itself, and
an oracle's pair is grouped into the distinguished outcome `default`. -/
def OAns.singlePart : OAns A → A
  | .single a => a
  | .pair _ _ => default

namespace SeededGame

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype A] [DecidableEq A]
variable (S : SeededGame V A)

/-! ## Averages over the seed

Both question distributions are pushforwards of the uniform distribution on the seed space, so
every sum against them is an average over seeds. -/

/-! ## The three relabelled families, and the extracted strategy -/

variable {S}

/-- Alice's own measurement, with the oracle-shaped answers grouped into `default`. -/
noncomputable def cFam (N : SyncStrategy S.oracular) (x : V) (a : A) :
    Matrix (Fin N.d) (Fin N.d) ℂ := (N.push OAns.singlePart).M (.alice, x) a

/-- Bob's own measurement, with the oracle-shaped answers grouped into `default`. -/
noncomputable def dFam (N : SyncStrategy S.oracular) (y : V) (b : A) :
    Matrix (Fin N.d) (Fin N.d) ℂ := (N.push OAns.singlePart).M (.bob, y) b

/-- The isolated players' measurements as one projective measurement on the doubled input
game's questions. -/
noncomputable def sideMeas (N : SyncStrategy S.oracular) :
    ProjectiveMeasurement (Bool × V) A (Matrix (Fin N.d) (Fin N.d) ℂ) where
  M p a := (N.push OAns.singlePart).M
    (if p.1 then (Role.bob, p.2) else (Role.alice, p.2)) a
  selfAdjoint _p a := (N.push OAns.singlePart).selfAdjoint _ a
  projective _p a := (N.push OAns.singlePart).projective _ a
  normalized _p := (N.push OAns.singlePart).normalized _

/-- **The extracted strategy** for the input game: the two isolated players keep their own
measurements. -/
noncomputable def soundStrategy (N : SyncStrategy S.oracular) :
    SyncStrategy S.toGame.doubled where
  d := N.d
  d_pos := N.d_pos
  P := sideMeas N

@[simp] theorem soundStrategy_d (N : SyncStrategy S.oracular) : (soundStrategy N).d = N.d := rfl

@[simp] theorem soundStrategy_false (N : SyncStrategy S.oracular) (x : V) (a : A) :
    (soundStrategy N).P.M (false, x) a = cFam N x a := rfl

@[simp] theorem soundStrategy_true (N : SyncStrategy S.oracular) (y : V) (b : A) :
    (soundStrategy N).P.M (true, y) b = dFam N y b := rfl

/-! ## The two values, as averages over the seed -/

/-! ## The rejection budget

Everything the argument takes from `1 - ε ≤ val(oracular)` is this: at any one ordered pair of
roles, a set of outcome pairs the decider rejects carries mass at most `9ε` on average over the
seed. The `9` is the number of ordered role pairs. -/

/-! ## Relabelled sums, unrelabelled

Each budget below is stated about the *relabelled* families, and the budget lemma is about the
strategy's own operators. This is the translation: a sum over a set of relabelled outcome pairs
is the sum over the outcome pairs whose labels land in that set. -/

/-! ## The three rejection sets, and their budgets

The decider's checks that the argument uses are three: the oracle's own pair must satisfy the
input predicate, and each isolated player's answer must agree with the oracle's corresponding
component. Each is a set of outcome pairs on which `oaccepts` is false, so each carries mass at
most `9ε`. -/

/-! ## The three budgets, on the relabelled families

Each budget is now a statement about the relabelled families `oFam`, `cFam`, `dFam`: the
oracle's own answer is accepted, and each isolated player agrees with the oracle's component,
all but `9ε` of the time. -/

/-! ## The three families are projective measurements -/

/-! ## The per-seed quantities -/

/-! ## The three budgets, averaged over the seed -/

/-! ## Soundness -/

end SeededGame

end MIPRE


