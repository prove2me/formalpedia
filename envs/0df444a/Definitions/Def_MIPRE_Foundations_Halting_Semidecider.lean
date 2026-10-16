-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Semidecider
-- name    : MIPRE_Foundations_Halting_Semidecider
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:52:18.101166+00:00
-- url     : https://prove2.me/theorems/13e8776f-e409-4c2b-8525-e847685d8d00
-- title:
--   Witnesses for the violation of $\lambda$-boundedness and for the acceptance of a long answer
-- statement:
--   Obligation O3 of the halting reduction asks for a program halting on $(x, n)$ exactly when the string $x$ lies outside the class $B$ at level $n$, a disjunction of three $\Sigma_1$ statements: the verifier is not $n$-bounded, its decider accepts an answer longer than the bound, its game has value above $1/2$. This bundle defines the witnesses that make the first two searchable (blueprint `lem:bounded-violation-re`, `lem:halting-semidecider`) and the presentation hypothesis on a family of verifiers; the enumeration lemmas and `exists_sem` are theorems of the module.
--
--   Let $V : \mathrm{Verifier}\ \ell$. `MIPRE.Verifier.boundBudget lam m d = m ^ lam * (d.size + 1) ^ lam` is the budget the time bounds of `def:lambda-bounded` allow at index $m$ on $d$. `MIPRE.Verifier.BoundViolation V lam w`, for a witness $w = (w_1, w_2)$ of two data, with $m =$ `Data.natOf w.1` and $B =$ `boundBudget lam m w.2`, is
--   $$\neg\, V.\mathrm{size} \le \lambda \;\lor\; \Big(2 \le m \land \big(\neg\, V.\mathrm{sampler.dim}\, m \le m^\lambda \lor \neg\,\mathrm{HaltsWithin}\, V.\mathrm{sampler.prog}\, (\mathrm{encode}\, m, w_2)\, B \lor \neg\,\mathrm{HaltsWithin}\, V.\mathrm{decider.prog}\, (\mathrm{encode}\, m, w_2)\, B\big)\Big) ;$$
--   `boundViolationB V lam w : Bool` is the same test with `decide` and `Machine.haltsWithinB`. `MIPRE.Verifier.LongAcceptance V n T w`, for $w = ((x, y, a, b), k)$ of four bit strings and a step budget, says that $T < |a|$ or $T < |b|$ and that `Machine.runForD (encode V.decider.prog) (encode (n, x, y, a, b)) k = some (encode true)`; `longAcceptanceB V n T w : Bool` is its decidable form; the private abbreviation `LongZ α = (α × ℕ) × ((BitStr × BitStr × BitStr × BitStr) × ℕ)` is the search space of the enumeration.
--
--   `MIPRE.Verifier.ComputablyPresented V`, for a family `V : α → Verifier ℓ` over a `Primcodable` type, is the `Prop`-valued structure with the fields `samplerProg` and `deciderProg` (the programs of `V a`, as data, are computable in $a$) and `dim` (the sampler's dimension is computable in $(a, n)$).
--
--   **Formalization Note**. `BoundViolation` negates the clauses of `Verifier.IsBounded lam` at one index and one input; the index is carried as a datum so that its encoding is primitive recursive in the witness. The `Bool` forms use `Machine.haltsWithinB` of `Halting/CostBudget.lean`. `longAcceptanceB` tests `T + 1 ≤ length` where the proposition says `T < length`. The bundle has no embedded lemmas.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Semidecider.lean; blueprint lem:bounded-violation-re, lem:halting-semidecider

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Semidecider.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawInt
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_ValueApprox
import Definitions.Def_MIPRE_Foundations_ValueApprox_Cayley
import Definitions.Def_MIPRE_Foundations_ValueApprox_Projective
import Definitions.Def_MIPRE_Foundations_ValueApprox_Gaussian
import Definitions.Def_MIPRE_Foundations_ValueApprox_Norms
import Definitions.Def_MIPRE_Foundations_ValueApprox_Dense
import Definitions.Def_MIPRE_Foundations_ValueApprox_Strategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawStrategy
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawSemantics
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawComplete
import Definitions.Def_MIPRE_Foundations_ValueApprox_RawPrimrec
import Definitions.Def_MIPRE_Foundations_ValueApprox_RE
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Halting_Freeze
import Definitions.Def_MIPRE_Foundations_Halting_Classes
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Wrapper
import Definitions.Def_MIPRE_Foundations_Halting_Enumerate
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Definitions.Def_MIPRE_Foundations_Halting_Tabulate
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Compression
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial

/-!
# The semidecider of the halting reduction (obligation O3)

Obligation O3 of the halting reduction (`Halting/Reduction.lean`) asks for a closed program
halting on `encode (x, n)` exactly when the string `x` lies outside the class `B` at level
`n`. By
`Verifier.not_inClassB_iff` that is a disjunction of three `Σ₁` statements — the verifier `x`
denotes is not `n`-bounded, or its decider accepts some answer longer than the answer bound,
or its `n`-th game has value more than `1/2` — and the obligation is an *equivalence*, so all
three have to be recognized exactly.

The second disjunct is the tabulation's, and is O2's to supply: with a computable game
description whose value is that of `𝒱_n`, `lem:value-lower-approx`
(`MIPRE.ValueApprox.rePred_lt_quantumValue`) enumerates the strategies. The first is proved
here, and it is the part of O3 that O2 does not contain:

* `Verifier.BoundViolation` is a witness that `λ`-boundedness fails: an index and one input of
  the sampler or the decider at that index. The index is carried as a *datum*, not a number,
  so that the encoding `encode m` under which `Decider.TimeBoundAt` reads its input is
  primitive recursive in the witness (`Data.encode_natOf`); every index arises this way
  (`Data.natOf_encode`), so nothing is lost.
* `Verifier.not_isBounded_iff_exists` is the characterization: `λ`-boundedness fails exactly
  when some witness works. Each clause of `def:lambda-bounded` is a `∀`, over indices and over
  inputs, so its negation is a search — and what makes the search effective is that
  `Prog.HaltsWithin` is decidable (`Halting/CostBudget.lean`), which needs the *cost* of a run
  and not only its length.
* `Verifier.rePred_not_isBounded`: hence, **for a computably presented family of verifiers
  (`Verifier.ComputablyPresented`), the boundedness violation is recursively enumerable**.
* `Verifier.rePred_not_rejectsLong`: the acceptance of a long answer is recursively enumerable
  too, by the same pattern with a simpler witness — the tuple and a step budget — and one
  budgeted run of the decider (`Machine.runForD`).
* `Halting.exists_sem_of_tab` merges the three disjuncts (`REPred.or`, by `Partrec.merge'`) and
  hands the result to `Cost.exists_semidecider_prod_nat`, which is `Cost.exists_semidecider`
  on pair-encoded inputs. Out comes `sem`, `sem_closed` and `sem_spec`.

## What was assumed, and what discharged it

`exists_sem_of_tab` takes the tabulation and the presentation of the family as hypotheses.
Both are O2's: a `GameData` for `𝒱_n` cannot be computed without the sampler's dimension and
the two programs. Stating them rather than proving them keeps the mathematical content here —
that the *violation* of a `∀`-clause over an infinite index set is enumerable — independent of
how the tabulation is built. Both are now supplied: `Halting.computablyPresented_Vof` at the
end of this file, and `Halting.tab_value` in `Halting/Instantiation.lean`, so that
**`Halting.exists_sem` takes no hypotheses**; `halting_reduction` (`Halting/Reduction.lean`,
below this file in the import order) applies it directly, and `Obligations` has no O3 field.

Two things found in the writing, both recorded in `planning/h4-assembly.md`, and both since
discharged — by different repairs. The findings are kept because they say where the seams
were:

1. **O3 is not "O2 plus a disjunction"**, as the plan and `Obligations`' docstring said. The
   hypothesis `hval` below asks the tabulation to have the value of `𝒱_n` for every
   `n`-bounded verifier, and the match as it then stood gave that only for a verifier
   *synchronous* at `n` — because a `GameData` describes a synchronous game by construction
   (`MIPRE.Verifier.isSynchronousAt_of_game_matches`). Membership in `B` does not carry
   synchronicity, so the equivalence `sem_spec` demands was not available. Three ways out were
   on the record; the one taken is the doubled question set of `Foundations/GameDouble.lean`.
   `MIPRE.Halting.tab_match` now matches `(Vof G U x).doubledGame`, whose distribution puts no
   weight on the diagonal a `GameData` vetoes, and `MIPRE.Halting.tab_value` is `hval` on the
   nose — the equality, in both directions, at every `n`-bounded string.
2. `Primrec fun n : ℕ => (encode n : Data)` — natural numbers encode in binary (`Nat.bits`) —
   was missing and is a prerequisite of `ComputablyPresented` for the verifier a string
   denotes, hence of O2's tabulation too. It is now `MIPRE.Cost.Data.primrec_encode_nat`. The
   witness trick above is what kept *this* file from needing it in the first place.
-/

namespace MIPRE

open Cost
open HaltingGameValue (GameData)

/-! ## Two closure properties of recursively enumerable predicates -/

/-! ## The boundedness violation -/

namespace Verifier

/-- A family of verifiers is **computably presented** when the two programs of `V a` and the
dimension of its sampler are computable in `a` — the programs as the data that encode them,
which is the form every computability statement of the ambient model takes.

This is what a computable tabulation of the games of the family needs anyway
(`MIPRE.Halting.tab_computable`): the question weights come from running the
sampler over `𝔽₂^{s(n)}`, so `s(n)` has to be computed before anything else can be. -/
structure ComputablyPresented {α : Type*} [Primcodable α] {ℓ : ℕ} (V : α → Verifier ℓ) :
    Prop where
  /-- The sampler's program, as data. -/
  samplerProg : Computable fun a : α => (encode (V a).sampler.prog : Data)
  /-- The decider's program, as data. -/
  deciderProg : Computable fun a : α => (encode (V a).decider.prog : Data)
  /-- The dimension `s(n)` of the sampler's ambient space, uniformly in `a` and `n`. -/
  dim : Computable fun q : α × ℕ => (V q.1).sampler.dim q.2

section

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- The budget the time bounds of `def:lambda-bounded` allow at index `m` on the input `d`:
`m ^ λ · (|d| + 1) ^ λ`, read off the shape of `Decider.TimeBoundAt`. -/
def boundBudget (lam m : ℕ) (d : Data) : ℕ := m ^ lam * (d.size + 1) ^ lam

/-- **A witness that `λ`-boundedness fails.** The index at which a clause of
`def:lambda-bounded` breaks is carried as a datum `w.1` — read as the number `Data.natOf w.1`,
so that the encoding `encode (Data.natOf w.1)` the two time bounds prepend to their input is
`Data.normBin w.1`, primitive recursive in the witness — and `w.2` is an input of the sampler
or of the decider at that index on which the time bound fails. -/
def BoundViolation (lam : ℕ) (w : Data × Data) : Prop :=
  ¬ V.size ≤ lam ∨
    (2 ≤ Data.natOf w.1 ∧
      (¬ V.sampler.dim (Data.natOf w.1) ≤ Data.natOf w.1 ^ lam ∨
        ¬ HaltsWithin V.sampler.prog (.cons (encode (Data.natOf w.1)) w.2)
            (boundBudget lam (Data.natOf w.1) w.2) ∨
        ¬ HaltsWithin V.decider.prog (.cons (encode (Data.natOf w.1)) w.2)
            (boundBudget lam (Data.natOf w.1) w.2)))

/-- The witness test, as a `Bool`: every clause of `BoundViolation` is decidable, the two time
bounds by `Machine.haltsWithinB` (`Halting/CostBudget.lean`). -/
def boundViolationB (lam : ℕ) (w : Data × Data) : Bool :=
  !decide (V.size ≤ lam) ||
    (decide (2 ≤ Data.natOf w.1) &&
      (!decide (V.sampler.dim (Data.natOf w.1) ≤ Data.natOf w.1 ^ lam) ||
        !Machine.haltsWithinB (encode V.sampler.prog)
            (.cons (encode (Data.natOf w.1)) w.2) (boundBudget lam (Data.natOf w.1) w.2) ||
        !Machine.haltsWithinB (encode V.decider.prog)
            (.cons (encode (Data.natOf w.1)) w.2) (boundBudget lam (Data.natOf w.1) w.2)))

end

/-! ## The rejection of long answers, violated -/

section

variable {ℓ : ℕ} (V : Verifier ℓ)

/-- **A witness that the decider accepts a long answer at index `n`**: a tuple of two questions
and two answers, one of the answers longer than `T`, and a step budget within which the
decider's run on the tuple returns `true`. The budget is what makes the acceptance, a `Σ₁`
statement, testable. -/
def LongAcceptance (n T : ℕ) (w : (BitStr × BitStr × BitStr × BitStr) × ℕ) : Prop :=
  (T < w.1.2.2.1.length ∨ T < w.1.2.2.2.length) ∧
    Machine.runForD (encode V.decider.prog)
      (encode (n, w.1.1, w.1.2.1, w.1.2.2.1, w.1.2.2.2)) w.2 = some (encode true)

/-- The witness test, as a `Bool`. -/
def longAcceptanceB (n T : ℕ) (w : (BitStr × BitStr × BitStr × BitStr) × ℕ) : Bool :=
  (decide (T + 1 ≤ w.1.2.2.1.length) || decide (T + 1 ≤ w.1.2.2.2.length)) &&
    decide (Machine.runForD (encode V.decider.prog)
      (encode (n, w.1.1, w.1.2.1, w.1.2.2.1, w.1.2.2.2)) w.2 = some (encode true))

end

section

variable {α : Type*} [Primcodable α] {ℓ : ℕ} {V : α → Verifier ℓ}

/-- The search space of `rePred_not_rejectsLong`: a witness paired with the parameters. -/
abbrev LongZ (α : Type*) := (α × ℕ) × ((BitStr × BitStr × BitStr × BitStr) × ℕ)

end

end Verifier

/-! ## The semidecider -/

namespace Halting

variable {G : GapCompression} {U : UniversalMachine}

end Halting

end MIPRE


