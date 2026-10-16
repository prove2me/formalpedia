-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Instantiation
-- name    : MIPRE_Foundations_Halting_Instantiation
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:49:42.230988+00:00
-- url     : https://prove2.me/theorems/b6039a26-6e6a-4244-a520-1b82f6b00e6b
-- title:
--   The verifier a string denotes, the two classes and the tabulation of its games
-- statement:
--   Fix a gap-preserving compression $G$ (`MIPRE.GapCompression`) and a universal machine $U$. This bundle defines the objects of the halting reduction of blueprint `thm:halting`.
--
--   **Descriptions.** `MIPRE.Halting.descLam x = Data.natOf (Data.parse x).left` is the parameter a bit string $x$ denotes, normalized to a canonical binary numeral; `descDecD x = (Data.parse x).right` the decider datum; `descOf lam dec`, the string denoting a parameter and a decider program, is the postorder serialization of `cons (encode lam) (encode dec)`.
--
--   **The verifier and the classes.** `Vof G U x : Verifier 7` is `Verifier.ofSamplerDeciderD U (G.sampler (descLam x)) (descDecD x)`: the compressed sampler at the string's parameter and the string's decider datum, run by $U$ in the question-length wrapper. `ansBound G x n = G.bound.eval (n + descLam x)` is the answer-length budget at level $n$, and the classes are the sets of strings
--   $$\mathrm{classA}\;n = \{x \mid (\mathrm{Vof}\;x).\mathrm{InClassA}\;n\;(\mathrm{ansBound}\;x\;n)\},\qquad \mathrm{classB}\;n = \{x \mid (\mathrm{Vof}\;x).\mathrm{InClassB}\;n\;(\mathrm{ansBound}\;x\;n)\},$$
--   `InClassA n T`: $n$-bounded, rejects answers longer than $T$ at index $n$, has a value-$1$ PCC strategy; `InClassB n T`: the same with $\mathrm{val}^*(\mathcal{V}_n) \le 1/2$ in place of the strategy.
--
--   **The tabulation.** `sampData G x = encode (G.samplerProg (descLam x))` and `decProgData G U x` (the wrapper's description around `descDecD x`) are the encoded programs; `tab G U x n : GameData` is `tabOf` on them with dimension `dimOf`, answer bound and sampler budget `ansBound G x n`, degree `G.deg` and level $n$: the doubled game of $\mathcal{V}_n$ as a finite table. `eXof G U x n : Fin (nX + 1) ≃ Bool × (Vof G U x).Questions n` and `eAof G U x n : Fin (nA + 1) ≃ Verifier.Answers (ansBound G x n)` are the relabelings.
--
--   The embedded lemmas are the round trips of `descOf`, computability statements for `descLam`, `sampData`, `decProgData`, `ansBound` and `dimOf`, the sampler's time bound at every string and level, `dimOf_eq` (the tabulated dimension is the sampler's for all $x$, $n$) and the cardinalities `tab_nX`, `tab_nA`.
--
--   **Formalization Note**. `G`, `U` are explicit arguments of every declaration; `tab`, `eXof`, `eAof` are `noncomputable`; `tab_computable`, `tab_match`, `tab_value` are theorems of the module not in this bundle. The game tabulated is the doubled game `(Vof G U x).doubledGame`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Instantiation.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Instantiation.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
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
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_HaltingGameValue
import Definitions.Def_MIPRE_Foundations_GameDescription
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

/-!
# The halting reduction, assembled

Blueprint `thm:halting`: the computable map from machines to game descriptions whose game has
value `1` when the machine halts and value at most `1/2` when it does not. It is proved here
from gap-preserving compression as a hypothesis (`MIPRE.GapCompression`, blueprint
`thm:compression`) through the per-level compressibility criterion
(`MIPRE.Cost.compressibility_criterion_levels`, blueprint `lem:compressible-criterion`),
along the dictionary of blueprint `rem:compression-abstract`.

## What a string denotes

A string is a *description*, never a game: a pair `(λ, 𝒟)` of a compression parameter and a
decider program, serialized by `Data.toBitsPost` and read back by `Data.parse`. Every string
names such a pair — `descLam` normalizes the parameter (`Data.natOf`), `descDecD` is the
decider as the datum it is — so no validity condition on strings appears anywhere. The
verifier it denotes is

  `Vof x = (S^compr_{descLam x}, wrap (descDecD x))`   (`Verifier.ofSamplerDeciderD`),

the compressed sampler at the string's own parameter (which depends on `λ` alone, blueprint
`lem:compress-sampler-indep`, the field `GapCompression.sampler`) together with the string's
decider, run by the universal machine, wrapped in the question-length check of
`def:normal-verifier` (`Decider.wrap`). That the decider is a datum and not a decoded program
is deliberate: a datum that is not an encoding still names a verifier, whatever the interpreter
does with it, and the compressor's decider of O4 can copy a datum into a syntax tree where it
could not decode one. The
two classes of the criterion are then

  `classA n = {x | Vof x is n-bounded, rejects long answers, and 𝒱_n has a value-1 PCC strategy}`,
  `classB n = {x | Vof x is n-bounded, rejects long answers, and val*(𝒱_n) ≤ 1/2}`,

with answers cut at `ansBound x n = bound (n + descLam x)`, the length beyond which a
compressed decider with parameter `descLam x` rejects (`GapCompression.output_rejects_long`);
`Vof x` is not literally an output of `Compress`, so that field does not apply to it directly
— `ansBound` is the answer alphabet the classes are read with, and relating it to the
compressor's output is part of `Obligations.compr_spec`. Tying the boundedness parameter to
the level (`n`-bounded at level `n`) is what replaces the paper's choice of `λ` along the
recursion (blueprint `rem:compression-abstract`, item 1, and `lem:lambda`).

## Where the assembly is

`halting_reduction`, and the structure `MIPRE.Halting.Obligations` of what it still owes, are
in `Halting/Reduction.lean`, which sits below this file, `Halting/Strings.lean` and
`Halting/Semidecider.lean` in the import order, so that the two distinguished strings (O1) and
the semidecider (O3) are applied there as theorems rather than assumed as fields. What this
file contributes to it, beyond the objects above, is the tabulation:

* **O2** — the tabulation of `𝒱_n` as a game description matching it along relabelings of
  the two alphabets: `tab`, `tab_computable`, `tab_match`, `tab_value` and
  `gameValue_tab_eq_one`, in the last section of this file, which `halting_reduction` uses
  directly; the relabelings are `Verifier.tagEquiv` and
  `answerEquiv`, transported across the two sizes. Three features of their shape are
  deliberate and each is explained where it is stated: the match and the value hold of an
  `n`-bounded verifier and could not hold of every string, acceptance being `Σ₁` — while
  `dimOf_eq` and `margOf_eq`, budgeted from the compressed sampler's own time bound, hold at
  every string and every level; `tab_match` delivers the relabelings rather than only the
  value they equate, because `synval ≤ val*` points the wrong way for item 1 of `thm:halting`;
  and the game it matches is the *doubled* one, `(Vof G U x).doubledGame`, so that the
  diagonal a `GameData` vetoes carries no weight and no synchronicity is asked of the
  verifier. That last one is what makes the tabulation usable by O3, and the paragraph below
  the list says how.

O3 was recorded in `planning/h4-assembly.md` as "O2 plus a disjunction"; it is not, and the
reason is worth naming, because it shaped the tabulation.
`Halting.exists_sem_of_tab` needs the tabulation to have the value of `𝒱_n` at every
`n`-bounded string, in both directions, because `sem_spec` is an equivalence — while a match
against `(Vof G U x).game` gives that only where the verifier is also *synchronous* at `n`,
a `GameData` describing a synchronous game by construction
(`Verifier.isSynchronousAt_of_game_matches`), and `classB n` does not ask for synchronicity.
Three repairs were on the record in blueprint `lem:halting-semidecider`: tabulate on a doubled
question set so that the distribution avoids the diagonal, make `Decider.wrap` reject unequal
answers to equal questions so that every string names a synchronous verifier, or put
synchronicity into `classB` and pay for it in `compr_spec`. **The first is the one made**
(`Foundations/GameDouble.lean`, `Verifier.doubledGame`): it is the cheapest and the only one
that changes nothing outside the tabulation. So `tab_match` and `tab_value` below ask the
verifier's decider for nothing beyond `n`-boundedness, and `exists_sem_of_tab`'s `hval` is
`tab_value` itself.
-/

namespace MIPRE.Halting

open Cost
open HaltingGameValue (GameData)

/-! ## What a string denotes -/

/-- The compression parameter a string denotes: the left component of the data it parses to,
normalized to a canonical binary numeral (`Data.natOf`), so that every string names one. -/
def descLam (x : BitStr) : ℕ := Data.natOf (Data.parse x).left

/-- The decider a string denotes: the right component of the data it parses to, a datum that
the universal machine runs (`Verifier.ofSamplerDeciderD`). It need not be the encoding of a
program; every string names one. -/
def descDecD (x : BitStr) : Data := (Data.parse x).right

/-- The string denoting a parameter and a decider: the postorder serialization of the pair. -/
def descOf (lam : ℕ) (dec : Prog) : BitStr :=
  (Data.cons (encode lam) (encode dec)).toBitsPost

@[simp] theorem descLam_descOf (lam : ℕ) (dec : Prog) : descLam (descOf lam dec) = lam := by
  simp [descLam, descOf]

@[simp] theorem descDecD_descOf (lam : ℕ) (dec : Prog) :
    descDecD (descOf lam dec) = encode dec := by
  simp [descDecD, descOf]

/-! ## The verifier a string denotes, and the two classes -/

variable (G : GapCompression) (U : UniversalMachine)

/-- **The verifier a string denotes**: the compressed sampler at the string's own parameter,
and the string's decider — a datum, run by the universal machine — wrapped in the
question-length check. Every string denotes one, well formed or not. -/
def Vof (x : BitStr) : Verifier 7 :=
  Verifier.ofSamplerDeciderD U (G.sampler (descLam x)) (descDecD x)

/-- The answer-length budget the classes are read with at level `n`: the bound a compressed
decider with the string's parameter obeys at index `n`. -/
def ansBound (x : BitStr) (n : ℕ) : ℕ := G.bound.eval (n + descLam x)

/-! ### The answer budget of a short description

What obligation O4 needs of `ansBound`: on a string short enough to have come out of the
compressibility criterion, the budget the classes are read with at level `2n + 1` is below the
budget `GapCompression.completeness` supplies strategies at. Both bounds are exponential in
`n`; the point is which exponent, and the string's own parameter is what could have broken it.
-/

/-- **The class `A` at level `n`**: the strings whose verifier is `n`-bounded and whose `n`-th
game has a value-`1` PCC strategy. -/
def classA (n : ℕ) : Set BitStr := {x | (Vof G U x).InClassA n (ansBound G x n)}

/-- **The class `B` at level `n`**: the strings whose verifier is `n`-bounded and whose `n`-th
game has quantum value at most `1/2`. -/
def classB (n : ℕ) : Set BitStr := {x | (Vof G U x).InClassB n (ansBound G x n)}

/-! ## The tabulation of the verifier a string denotes

`tab x n` is the `GameData` for `(Vof G U x)`'s `n`-th game, and it is computable because it
is `Tabulate`'s `tabOf` — a function of two encoded programs and five numbers — fed what the
string and the level supply: the two programs, the sampler's dimension, the answer cut
`ansBound G x n`, and that same `ansBound` with `G.deg` as the budget of the sampler runs.
Two of the seven take work:

* `sampData x`, the encoded sampler program, is `G.samplerProg (descLam x)` encoded. A
  `PolyTimeFun` is not a Mathlib-computable function of its argument in any direct sense; what
  makes this go through is that it is run by the ambient machine on an encoded input
  (`Cost.PolyTimeFun.computable_encode_comp`).
* `decProgData x`, the encoded decider program, is the *wrapper* around the string's own
  decider (`Decider.wrap`, through `Verifier.ofSamplerDecider`). Encoding it means building
  `Cost.Prog.wrapCore`'s syntax tree directly in `Data` (`Cost.Prog.ProgD.dWrapCore`), because
  `Prog` is not a `Primcodable` and so no `Primrec` statement can mention it. The string's
  decider is the datum `descDecD x` and enters as it is.

The three bridges at the end — `accOf_iff`, `dimOf_eq`, `margOf_eq` — are what the rest of O2
rests on: the tabulated numbers *are* the verifier's own sampler and decider. `dimOf_eq` and
`margOf_eq` say so at every string and every level, their budget being the compressed
sampler's own (`sampler_timeBound`, from `GapCompression.sampler_time`); `accOf_iff` says so
on an `n`-bounded verifier, whose budget is the only one the string's own decider has.
-/

/-- The encoded sampler program of the verifier a string denotes. -/
def sampData (x : BitStr) : Data := encode (G.samplerProg (descLam x))

/-- The encoded decider program of the verifier a string denotes: the question-length wrapper
around the string's decider, built in `Data` rather than in `Prog`. -/
def decProgData (x : BitStr) : Data :=
  Prog.ProgD.dWrapCore (encode U.univ) (sampData G x) (descDecD x)

/-! The two concrete instantiations of `Tabulate`'s generic `Primrec` statements. `s` and `B`
are paired so that `n` stays at the depth it has in the tuple today: that is what keeps this
one instantiation cheap, and what lets `tabOf`'s argument list grow without re-running the
expensive `primrec_accOf`. -/

theorem primrec_dimOf_tuple (k : ℕ) :
    Primrec fun q : (Data × ℕ) × ℕ => dimOf q.1.1 q.2 k q.1.2 :=
  primrec_dimOf k (Primrec.fst.comp Primrec.fst) Primrec.snd (Primrec.snd.comp Primrec.fst)

/-- **The tabulation of `(Vof G U x)`'s `n`-th game**, doubled and re-budgeted.  The sampler
runs under the budget the *compressed sampler's own* time bound supplies — coefficient
`ansBound G x n = G.bound.eval (n + descLam x)`, degree `G.deg` — neither of which needs
`(Vof G U x).IsBounded n`. -/
noncomputable def tab (x : BitStr) (n : ℕ) : GameData :=
  tabOf (sampData G x) (decProgData G U x)
    (dimOf (sampData G x) (ansBound G x n) G.deg n) (ansBound G x n) (ansBound G x n) G.deg n

/-! ### The tabulation is computable -/

theorem primrec_descLam : Primrec descLam :=
  Data.primrec_natOf.comp (Data.primrec_left.comp Data.primrec_parse)

theorem computable_sampData : Computable fun x : BitStr => sampData G x :=
  PolyTimeFun.computable_encode_comp G.samplerProg descLam
    (Data.primrec_encode_nat.comp primrec_descLam).to_comp

theorem computable_decProgData : Computable fun x : BitStr => decProgData G U x :=
  (Prog.ProgD.primrec_dWrapCore (encode U.univ)).to_comp.comp (computable_sampData G)
    (Data.primrec_right.comp Data.primrec_parse).to_comp

theorem computable_ansBound : Computable fun p : BitStr × ℕ => ansBound G p.1 p.2 :=
  ((primrec_poly_eval G.bound).comp
    (Primrec.nat_add.comp Primrec.snd (primrec_descLam.comp Primrec.fst))).to_comp

/-! The seven arguments of `tabOf` are assembled one declaration at a time. Inlining them into
a single term is not a stylistic choice: the tuple is nested four deep and elaborating it in
one go does not terminate within any heartbeat budget worth setting. -/

theorem computable_sampData_fst : Computable fun p : BitStr × ℕ => sampData G p.1 :=
  (computable_sampData G).comp Computable.fst

theorem computable_decProgData_fst : Computable fun p : BitStr × ℕ => decProgData G U p.1 :=
  (computable_decProgData G U).comp Computable.fst

theorem computable_dimOf_fst : Computable fun p : BitStr × ℕ =>
    dimOf (sampData G p.1) (ansBound G p.1 p.2) G.deg p.2 :=
  ((primrec_dimOf_tuple G.deg).to_comp.comp
    (((computable_sampData_fst G).pair Computable.snd).pair (computable_ansBound G))).of_eq
    fun _ => rfl

/-! ### The tabulated numbers are the verifier's own

`sampData_eq` and `decProgData_eq` only unfold the two encodings, and hold at every `n`. The
other three — `accOf_iff`, `dimOf_eq`, `margOf_eq` — are the same shape: rewrite the budgeted
run into `CL.Sampler.queryUnder` or `Verifier.accepts_iff_runForD`, which a time bound then
evaluates. Which bound differs, and that is the point of the re-budget. The two sampler runs
take `sampler_timeBound` — `GapCompression.sampler_time` at the string's own parameter, a
bound at *every* index — so `dimOf_eq` and `margOf_eq` carry no hypothesis. `accOf_iff` has
only `IsBounded n` to draw on, and `IsBounded.two_le` supplies the `2 ≤ n` it needs — see the
warning there: at `n = 0, 1` the time clauses say nothing and no budget exists. -/

theorem sampData_eq (x : BitStr) : sampData G x = encode ((G.sampler (descLam x)).prog) := by
  rw [sampData, G.samplerProg_eq]

/-- The sampler's time bound at the string's own compression parameter, with no hypothesis. -/
theorem sampler_timeBound (x : BitStr) (n : ℕ) :
    (G.sampler (descLam x)).TimeBoundAt n (ansBound G x n) G.deg :=
  G.sampler_time (descLam x) n

/-- **The tabulated dimension is the sampler's, at every string and every level** — `n = 0`
and `n = 1` included, which the `n ^ n` budget could never reach. -/
theorem dimOf_eq (x : BitStr) (n : ℕ) :
    dimOf (sampData G x) (ansBound G x n) G.deg n = (Vof G U x).sampler.dim n := by
  have hS := sampler_timeBound G x n
  rw [dimOf, sampData_eq,
    show Machine.runForD (encode ((G.sampler (descLam x)).prog))
        (encode (n, CL.Sampler.Query.dimension))
        (ansBound G x n * ((encode CL.Sampler.Query.dimension : Data).size + 1) ^ G.deg)
      = (G.sampler (descLam x)).queryUnder (ansBound G x n) G.deg n CL.Sampler.Query.dimension
      from rfl,
    (G.sampler (descLam x)).queryUnder_dimension hS]
  simp [SizedEncoding.decode_encode]
  rfl

/-! ## The tabulation matches the verifier, doubled

What remains is the dictionary between the two namings of each alphabet. A `GameData` names
its questions `Fin (nX + 1)` and its answers `Fin (nA + 1)`; the doubled game names them
`Bool × 𝔽₂^{s(n)}` and the bit strings of length at most `T`. `Verifier.tagEquiv` and
`Verifier.answerEquiv` are the two bijections, and `eXof`/`eAof` are them transported across
the arithmetic of `tab`'s two sizes (`tab_nX`, `tab_nA`) — `nX + 1 = 2 ^ (s(n) + 1)`, the
extra bit being the tag.

The two clauses are then separate pieces of work. The `μ` clause (`mu_clause`) is a counting
argument: the tabulated weight of a question pair is the number of points of `𝔽₂^{s(n)}` whose
two tagged marginals land on it, and the total weight is still `2 ^ s(n)`, which is exactly
the quotient `CL.clDist` is — the weight list enumerates `𝔽₂^{s(n)}` once, not the strings of
length `s(n) + 1`. The `D` clause is the acceptance table read back (`acc_mem_iff`), and the
one place where the two notions of game differ has stopped costing anything: a `GameData`
rejects unequal answers to equal questions by construction, and the doubled game puts no
weight there and rejects there too, so `tab_match` is a *total* match and needs nothing of the
decider beyond `n`-boundedness.
-/

theorem tab_nX (x : BitStr) (n : ℕ) :
    (tab G U x n).nX + 1 = 2 ^ ((Vof G U x).sampler.dim n + 1) := by
  show 2 ^ (dimOf (sampData G x) (ansBound G x n) G.deg n + 1) - 1 + 1 = _
  rw [dimOf_eq G U x n]
  exact Nat.succ_pred_eq_of_pos (Nat.two_pow_pos _)

theorem tab_nA (x : BitStr) (n : ℕ) :
    (tab G U x n).nA + 1 = (Verifier.answerList (ansBound G x n)).length := by
  show (Data.bitStrsLE (ansBound G x n)).length - 1 + 1 = _
  rw [Verifier.answerList, List.length_map]
  exact Nat.succ_pred_eq_of_pos (Data.length_bitStrsLE_pos _)

/-- The question relabeling: a tabulated question index is a *tag* and a point of `𝔽₂^{s(n)}`. -/
noncomputable def eXof (x : BitStr) (n : ℕ) :
    Fin ((tab G U x n).nX + 1) ≃ Bool × (Vof G U x).Questions n :=
  (finCongr (tab_nX G U x n)).trans (Verifier.tagEquiv _).symm

/-- The answer relabeling: a tabulated answer index is a bit string of length at most the
answer bound. Only the questions are doubled, so this is unchanged by it. -/
noncomputable def eAof (x : BitStr) (n : ℕ) :
    Fin ((tab G U x n).nA + 1) ≃ Verifier.Answers (ansBound G x n) :=
  (finCongr (tab_nA G U x n)).trans (Verifier.answerEquiv _)

end MIPRE.Halting


