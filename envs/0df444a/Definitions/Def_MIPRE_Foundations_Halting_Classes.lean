-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Classes
-- name    : MIPRE_Foundations_Halting_Classes
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:31:44.611184+00:00
-- url     : https://prove2.me/theorems/ac3be3af-62a6-477f-aa7d-b7c7460980c1
-- title:
--   The classes $A$ and $B$ of the compressibility criterion, read at the level of verifiers
-- statement:
--   Let `V : Verifier ℓ` be a normal form verifier (a sampler `V.sampler : CL.Sampler ℓ` and a decider `V.decider`, the decider accepting only questions of the sampler's dimension), $n$ a level and $T$ an answer-length bound. Three notions from earlier bundles enter: `V.IsBounded n` (for every $m \ge 2$, $s(m) \le m^n$ and the sampler and the decider halt within cost $m^n (|d|+1)^n$ on every input $(m, d)$; and the description length of $V$ is at most $n$); `V.RejectsLong n T` (for all $x, y, a, b$, if $T < |a|$ or $T < |b|$ then the decider does not accept $(n, x, y, a, b)$); `V.HasPerfectPCC n T` (some PCC synchronous strategy of the doubled game `V.doubledGame n T` has value $1$); and `V.valStar n T`, the quantum value of the game $\mathcal{V}_n$ with answers of length at most $T$.
--
--   The bundle holds two definitions, the classes of blueprint `rem:compression-abstract`, item 1, as predicates on a verifier: `MIPRE.Verifier.InClassA V n T` and `MIPRE.Verifier.InClassB V n T`, with
--
--   $$\mathrm{InClassA}\,(V, n, T) :\Leftrightarrow \mathrm{IsBounded}\,(V, n) \wedge \mathrm{RejectsLong}\,(V, n, T) \wedge \mathrm{HasPerfectPCC}\,(V, n, T), \qquad \mathrm{InClassB}\,(V, n, T) :\Leftrightarrow \mathrm{IsBounded}\,(V, n) \wedge \mathrm{RejectsLong}\,(V, n, T) \wedge \mathrm{val}^*(V, n, T) \le \tfrac12 .$$
--
--   These are the classes the compressibility criterion is instantiated with at level $n$: the strings whose verifier is $n$-bounded, rejects long answers and has a value-$1$ PCC strategy, and those that are $n$-bounded, reject long answers and have value at most $1/2$. The bundle contains no lemmas; the module's results about the classes (disjointness, the two distinguished verifiers) are not part of it.
--
--   **Formalization Note**. Both classes are `Prop`-valued definitions on a `Verifier ℓ`, a level `n : ℕ` and a bound `T : ℕ`, unfolding to the stated conjunctions. The rejection clause is part of the class rather than imposed on strings: the paper's $V^{\mathrm{halt}}$ has it by construction (an explicit length check in its decider), whereas over arbitrary strings it has to be asked for, since without it the soundness direction of the compressor's obligation cannot raise the answer bound a class is read with to the one the gap compression theorem takes its hypothesis at. `HasPerfectPCC` is read on the doubled question set, so no synchronicity is asked of the decider; `valStar` is a real number and $1/2$ the real $1/2$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Classes.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Classes.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze

/-!
# The classes of the compressibility criterion, at the level of verifiers

Blueprint `rem:compression-abstract`, item 1: the classes the criterion is instantiated with
are, at level `n`, the strings whose verifier is `n`-bounded, rejects every answer longer than
the answer bound at index `n`, and has a value-`1` PCC strategy there (`A n`), and those that
are `n`-bounded, reject long answers, and have `val* ≤ 1/2` there (`B n`). This file is the
part that does not depend on how a string is read as a verifier: the two conditions themselves
(`Verifier.InClassA`, `Verifier.InClassB`), their disjointness, and the two distinguished
verifiers the criterion needs.

The rejection clause (`Verifier.RejectsLong`) is what the paper's `V^halt` has by construction
— Step 6 of its decider is an explicit length check, and the amended proof of
`lem:dhalt-values` spends it to identify the answer alphabets of `V^halt_n` and `V^compr_n`.
Over arbitrary strings it has to be asked for: without it the soundness direction of the
compressor's obligation cannot raise the answer bound from the one a class is read with to
the one `GapCompression.soundness` takes its hypothesis at (`Verifier.valStar_eq_of_rejects`
is the step, and `valStar_le_of_le` goes the wrong way). `planning/h4-assembly.md` §4 item 4
has the argument, and the choice to put the clause in the classes rather than through the
criterion.

* `Verifier.InClassA n T`, `Verifier.InClassB n T` and `not_inClassB_of_inClassA`: the classes
  are disjoint, because a perfect PCC strategy gives `val* = 1`
  (`Verifier.valStar_eq_one_of_hasPerfectPCC`).
* `Verifier.hasPerfectPCC_of_accepts_diagonal`: a decider that accepts the constant answer `a₀`
  on every question pair has a value-`1` PCC strategy there — the paper's "trivial strategy:
  for all questions the players return a fixed answer", which is where `y_yes` comes from.
  `HasPerfectPCC` lives on the doubled game, so nothing is asked of the decider on the
  diagonal; `y_yes` still accepts only the empty answers, which keeps it rejecting long ones.
* `Verifier.valStar_eq_zero_of_rejects_all` and `isSynchronousAt_of_rejects_all`: a decider that
  accepts nothing at `n` gives `val* = 0`, where `y_no` comes from.

What remains for the classes is the reading of a string as a verifier — the wrapper decider
around the string's own decider — and the two strings realizing these verifiers
(`planning/formalization-plan.md`, H4).
-/

namespace MIPRE

open Cost

namespace Verifier

variable {ℓ : ℕ} (V : Verifier ℓ)

/-! ## The classes -/

/-- The class `A` at level `n`, with answer-length bound `T`: the verifier is `n`-bounded, its
decider rejects every answer longer than `T` at index `n`, and its `n`-th game has a value-`1`
PCC strategy. -/
def InClassA (n T : ℕ) : Prop := V.IsBounded n ∧ V.RejectsLong n T ∧ V.HasPerfectPCC n T

/-- The class `B` at level `n`, with answer-length bound `T`: the verifier is `n`-bounded, its
decider rejects every answer longer than `T` at index `n`, and its `n`-th game has quantum
value at most `1/2`. -/
def InClassB (n T : ℕ) : Prop := V.IsBounded n ∧ V.RejectsLong n T ∧ V.valStar n T ≤ 1 / 2

/-! ## The trivially accepting verifier -/

/-! ## The trivially rejecting verifier -/

/-! ## Transport along the frozen verifier -/

end Verifier

end MIPRE


