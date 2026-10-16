-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Reduction
-- name    : MIPRE_Foundations_Halting_Reduction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:54:48.089476+00:00
-- url     : https://prove2.me/theorems/f8664a89-6087-44a6-8dbe-dd03f614add3
-- title:
--   What the halting reduction owes: the `Obligations` and `CompressorSpec` structures
-- statement:
--   Blueprint `thm:halting` is proved in `MIPRE.Foundations.Halting.Reduction` from gap-preserving compression, a universal machine and the four obligations of `rem:compression-abstract`; three are theorems the proof applies, and this bundle defines the two structures stating the fourth, the compressor. Fix $G : \mathrm{GapCompression}$ and $U : \mathrm{UniversalMachine}$, with the objects of `Halting/Instantiation.lean`; `IsSuccinctDesc c n x` says that the closed program $c$ answers bit queries about $x$ within $(n+1)(\mathrm{size}\,m + 1)^2$ and $|x| \le 2^n$.
--
--   `MIPRE.Halting.Obligations G U` has three fields: a level `n₀ : ℕ`; the compressor `compr : PolyTimeFun (Prog × ℕ) BitStr`; and `compr_spec`, the class transfer: for all $c$, $x$, $n$ with $n_0 \le n$, $2\,\mathrm{esize}\,c \le n$, `IsSuccinctDesc c n x` and $|x| \le n + 1$,
--   $$\big(x \in \mathrm{classA}\,(2n+1) \to \mathrm{compr}\,(c, n) \in \mathrm{classA}\,n\big) \;\land\; \big(x \in \mathrm{classB}\,(2n+1) \to \mathrm{compr}\,(c, n) \in \mathrm{classB}\,n\big).$$
--
--   `MIPRE.Halting.CompressorSpec G U` is what the construction of the compressor proves of its program (the class transfer follows, `CompressorSpec.toObligations`): `n₀` with `C₀_le : G.C₀ ≤ n₀`; `compr` as above; `lam : ℕ → ℕ` with `descLam_compr : descLam (compr (c, n)) = lam n`; `accepts_compr`: under the four hypotheses of `compr_spec`, at every index and tuple, the decider of `Vof G U (compr (c, n))` accepts iff the decider of `G.output` on the programs of `(Vof G U x).freeze (2n+1)` at parameter `lam n` accepts; `isBounded_compr`: under the same hypotheses and `(Vof G U x).IsBounded (2n+1)`, `(Vof G U (compr (c, n))).IsBounded n`; `lam_ge`: for $n \ge n_0$, $(2n+1)^{2n+1} + \mathrm{esize}(2n+1) + 4 \le 2^{\mathrm{lam}\,n}$ and $2n + 1 + \mathrm{esize}(2n+1) + 53 \le \mathrm{lam}\,n$; `ansBound_le`: for $n \ge n_0$ and $|x| \le n+1$, `ansBound G x (2n+1) ≤ (2 ^ n) ^ lam n`. The bundle has no embedded lemmas.
--
--   **Formalization Note**. The hypothesis $|x| \le n + 1$ in `compr_spec` is not slack: it bounds `descLam x` by $2^{n+1}$ and so relates `ansBound G x (2n+1)` to the bound $(2^n)^\lambda$ at which `GapCompression.completeness` supplies strategies. Both structures are `Type`-valued (`compr` is data); `halting_reduction` is proved from an inhabitant of `Obligations`, `exists_compressorSpec` (`CompressorProgram.lean`) supplies one, and the conclusion is in $\mathrm{val}^*$.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Reduction.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Reduction.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings

/-!
# The halting reduction, assembled, and what it still owes

Blueprint `thm:halting`: the computable map from machines to game descriptions whose game has
value `1` when the machine halts and value at most `1/2` when it does not, proved from
gap-preserving compression as a hypothesis (`MIPRE.GapCompression`, blueprint
`thm:compression`) through the per-level compressibility criterion
(`MIPRE.Cost.compressibility_criterion_levels`, blueprint `lem:compressible-criterion`), along
the dictionary of blueprint `rem:compression-abstract`. The objects — the verifier a string
denotes, the two classes, the tabulation — are in `Halting/Instantiation.lean`. This module
sits below that file, below `Halting/Strings.lean` and below `Halting/Semidecider.lean` in the
import order, which is what lets `Obligations` say exactly what is left.

## What is proved and what is assumed

`halting_reduction` is complete: no `sorry`, and its only hypotheses are a `GapCompression`,
a `UniversalMachine` (`exists_efficient_universal` provides one) and an `Obligations`
structure. Of the four obligations of `rem:compression-abstract`, three are theorems that the
proof applies directly, and the structure's content is the fourth:

* **O1** — the two distinguished strings, `yYes_mem` and `yNo_mem` (`Halting/Strings.lean`),
  on the wrapper's time bound (`Halting/WrapperCost.lean`) and the verifier-level statements
  `Verifier.inClassA_of_accepts_diagonal` and `inClassB_of_rejects_all`. Each comes with its
  own threshold; the proof takes the larger.
* **O2** — the tabulation of `𝒱_n` as a game description matching it along relabelings of the
  two alphabets: `tab`, `tab_computable`, `tab_match`, `tab_value` and `gameValue_tab_eq_one`
  (`Halting/Instantiation.lean`). The game it matches is the *doubled* one,
  `(Vof G U x).doubledGame`, so that the diagonal a `GameData` vetoes carries no weight and no
  synchronicity is asked of the verifier; that is what lets O3 use it, and the module docstring
  of `Instantiation.lean` says how.
* **O3** — a program halting on `(x, n)` exactly off `classB n`: `exists_sem`
  (`Halting/Semidecider.lean`), which takes no hypotheses.
* **O4** (`compr`, `compr_spec`) — the compressor: the decider that reads its description by
  bit queries, freezes the verifier at index `2n + 1` (`Verifier.freeze`), runs `Compress`,
  and its time accounting. Its `λ` is chosen by `lem:lambda-bound`
  (`MIPRE.Halting.lambda_bound`), which turns the output's `poly(n, λ)` running times into the
  `n ^ λ` that `IsBounded` asks for. The field's fourth hypothesis, `x.length ≤ n + 1`, is what
  makes it satisfiable at all; its docstring says why, and
  `Cost.compressibility_criterion_levels` supplies it from a bound its own proof already had,
  and `exists_ansBound_le` (below, checked) is the step that consumes it: it puts the answer
  budget of level `2n + 1` under the one `GapCompression.completeness` supplies strategies at.
  What is not here yet is the construction — the ambient program, its agreement with
  `G.output`, and its cost accounting.

O4 is the substance that is left, and `planning/h4-assembly.md` §4 item 4 has the plan. Its
consumer is written first, below: `CompressorSpec` says what the compressor's program has to
satisfy — the parameter it carries, the agreement of its decider with the compressed decider
of the frozen verifier, its boundedness, the growth of the parameter — and
`CompressorSpec.toObligations` is the class transfer from those fields alone, so that the
construction owes the fields and nothing that would come out in a proof later.

## What this is not

`halting_reduction` concludes in `val*`: the quantum value of the game is `1`, respectively at
most `1/2`. The blueprint's item 1 says more — the witness is a value-`1` *PCC* strategy, so
`synval = val* = 1` — and the headline `HaltingGameValue.halting_reduces_to_gameValue` is
stated in `synval`. The two steps that carry the conclusion there are in Lean and neither is
part of this assembly: a synchronous strategy transports along a relabeling of the alphabets
(`MIPRE.syncValue_eq_of_equiv`), and `MIPRE.syncValue` and `HaltingGameValue.gameValue` are the
same number on the same description (`HaltingGameValue.GameData.gameValue_eq_syncValue`).
`MIPRE.Verifier.gameValue_toGame_eq_one` is the two composed, in `Foundations/SyncTransport.lean`.

Both take the tabulation's agreement with `𝒱_n` as the *matching data* — the two alphabet
equivalences with `hμ` and `hD` — rather than the equality of `val*` it implies, which is why
`tab_match` has the shape it has. The soundness half needs neither step, only
`synval ≤ val*` (`MIPRE.syncValue_le_quantumValue`, blueprint `lem:sync-le-valstar`);
`Verifier.gameValue_toGame_le_of_valStar_le` is it in that vocabulary.

So what stands between `halting_reduction` and the headline is an inhabitant of `Obligations`
and nothing else.
-/

namespace MIPRE.Halting

open Cost
open HaltingGameValue (GameData)

variable (G : GapCompression) (U : UniversalMachine)

/-! ## The obligation -/

/-- **What the halting reduction still owes: obligation O4, the compressor.** The other three
obligations of blueprint `rem:compression-abstract` are theorems — `yYes_mem` and `yNo_mem`
(O1), the tabulation `tab` with `tab_computable` and `tab_value` (O2), `exists_sem` (O3) —
and `halting_reduction` below applies them; this structure holds what is not yet a theorem,
so that what is open can be enumerated rather than searched for. Nothing else is assumed:
`halting_reduction` is proved outright from an inhabitant. `planning/h4-assembly.md` §4 item 4
has the plan for the compressor, and issue #53 tracks it. -/
structure Obligations (G : GapCompression) (U : UniversalMachine) where
  /-- The level above which the guarantees hold. -/
  n₀ : ℕ
  /-- **O4.** The compressor: a polynomial-time map on `(description, level)` pairs. -/
  compr : PolyTimeFun (Prog × ℕ) BitStr
  /-- **O4.** On a succinct description of a string at level `2n + 1`, with the size slack and
  the length bound the criterion provides, the compressor preserves both classes down to level
  `n`.

  The clause `x.length ≤ n + 1` is not slack either, and it is what makes the field
  *satisfiable*. `classA G U (2n+1)` asks for a value-`1` PCC strategy at the answer bound
  `ansBound G x (2n+1) = G.bound.eval (2n+1 + descLam x)`, while the only source of such a
  strategy for a compressed verifier is `GapCompression.completeness`, which takes its input at
  the bound `(2 ^ n) ^ λ` with `λ` the parameter the compressor writes into its output — so `λ`
  is bounded by the compressor's own output size and cannot be made arbitrarily large. Without a
  bound on `descLam x` the two cannot be related: nothing in `IsBounded` constrains a string's
  compression parameter (for a `G` whose compressed sampler does not vary with `λ`, membership
  in either class is insensitive to it), while `ansBound` grows with it. With
  `x.length ≤ n + 1` we get `descLam x < 2 ^ (n+1)`, hence
  `ansBound G x (2n+1) ≤ G.bound.eval (2n+1 + 2^(n+1)) ≤ (2 ^ n) ^ λ` already for
  `λ ≥ 2 · deg(G.bound) + 1` and `n` above a threshold read off `G.bound` too, and
  `hasPerfectPCC_of_le` carries the hypothesis across. `exists_ansBound_le`
  (`Halting/Instantiation.lean`) is that step, checked; note the threshold is set by the
  polynomial `G.bound`, not by `G.deg`.

  **Both directions close from these hypotheses, and the second needs the rejection clause of
  the classes.** The `classA` direction is the argument above, `hasPerfectPCC_of_le` raising the
  answer bound. The `classB` direction runs the other way: `G.soundness` wants
  `valStar (2 ^ n) ((2 ^ n) ^ λ) ≤ 1/2`, membership in `classB G U (2n+1)` gives it at
  `ansBound G x (2n+1)`, and `valStar_le_of_le` only *raises* a value with its bound. What
  carries it is `valStar_eq_of_rejects`: membership carries `Verifier.RejectsLong`, the decider
  rejecting every answer longer than `ansBound G x (2n+1)` at index `2n + 1`, so raising the
  bound to `(2 ^ n) ^ λ` does not move the value. In return the output has to reject beyond
  `ansBound G (compr (c, n)) n` to be in either class, which `GapCompression.output_rejects_long`
  supplies once the output's decider is a compressed decider. The paper's `V^halt` has both by
  construction, Step 6 of its decider `F` being an explicit length check spent in the amended
  proof of `lem:dhalt-values`; `planning/h4-assembly.md` §4 item 4 has the argument and the
  choice to put the clause in the classes rather than through the criterion. -/
  compr_spec : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
      (x ∈ classA G U (2 * n + 1) → compr (c, n) ∈ classA G U n) ∧
      (x ∈ classB G U (2 * n + 1) → compr (c, n) ∈ classB G U n)

/-! ## What the compressor must supply

The consumer of obligation O4, written before its construction (`planning/h4-assembly.md` §1,
"write the consumer first"): a structure `CompressorSpec` of the properties the compressor's
program has to have, and the theorem `obligations_of_spec` turning one into an `Obligations`.
It is the class transfer of `rem:compression-abstract` item 2 done once, against named
hypotheses, so that what the construction owes is exactly the fields below and nothing that
comes out in a proof later.

The reading. On a succinct description `c` of a short string `x` at level `n`, the output
`compr (c, n)` is a string denoting the parameter `lam n` and a decider that, at every index,
accepts what the compressed decider of *the verifier of `x` frozen at index `2n + 1`* accepts
(`accepts_compr`); its verifier is `n`-bounded (`isBounded_compr`, the accounting); and `lam n`
grows fast enough for the frozen verifier to be `lam n`-bounded (`lam_ge`, consumed by
`Verifier.freeze_isBounded`) and for the answer budget of level `2n + 1` to fit under the one
`GapCompression.completeness` takes its hypothesis at (`ansBound_le`, from `exists_ansBound_le`
with `n₀` past its threshold). -/

/-- **The specification of the compressor.** What obligation O4's construction has to prove of
its program; `obligations_of_spec` is the class transfer on top. -/
structure CompressorSpec (G : GapCompression) (U : UniversalMachine) where
  /-- The level above which everything holds; at least `G.C₀`. -/
  n₀ : ℕ
  C₀_le : G.C₀ ≤ n₀
  /-- The compressor. -/
  compr : PolyTimeFun (Prog × ℕ) BitStr
  /-- The parameter the output carries at level `n`. -/
  lam : ℕ → ℕ
  /-- The output at level `n` denotes the parameter `lam n`. -/
  descLam_compr : ∀ (c : Prog) (n : ℕ), descLam (compr (c, n)) = lam n
  /-- **Acceptance agreement.** The output's decider accepts, at every index, exactly what the
  compressed decider of the verifier of `x` frozen at `2n + 1` accepts. -/
  accepts_compr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 →
    ∀ (m : ℕ) (x' y' a b : BitStr),
      (Vof G U (compr (c, n))).decider.Accepts m x' y' a b ↔
        (G.output (((Vof G U x).freeze (2 * n + 1)).sampler.prog,
          ((Vof G U x).freeze (2 * n + 1)).decider.prog) (lam n)).decider.Accepts m x' y' a b
  /-- **The accounting.** The output's verifier is `n`-bounded, given that the described
  verifier is `(2n + 1)`-bounded. -/
  isBounded_compr : ∀ (c : Prog) (x : BitStr) (n : ℕ), n₀ ≤ n → 2 * esize c ≤ n →
    IsSuccinctDesc c n x → x.length ≤ n + 1 → (Vof G U x).IsBounded (2 * n + 1) →
    (Vof G U (compr (c, n))).IsBounded n
  /-- **Growth of the parameter**, as `Verifier.freeze_isBounded` consumes it: the running
  times and dimension of a `(2n + 1)`-bounded verifier at index `2n + 1`, shifted by the cost
  of freezing, fit under `2 ^ lam n`, and the index and the size fit under `lam n`. -/
  lam_ge : ∀ n, n₀ ≤ n →
    (2 * n + 1) ^ (2 * n + 1) + esize (2 * n + 1) + 4 ≤ 2 ^ lam n ∧
    2 * n + 1 + esize (2 * n + 1) + 53 ≤ lam n
  /-- **The answer budget fits**: `exists_ansBound_le` with `n₀` past its threshold and `lam n`
  past `lam₀`. -/
  ansBound_le : ∀ (x : BitStr) (n : ℕ), n₀ ≤ n → x.length ≤ n + 1 →
    ansBound G x (2 * n + 1) ≤ (2 ^ n) ^ lam n

namespace CompressorSpec

variable {G U} (S : CompressorSpec G U)

end CompressorSpec

/-! ## The reduction -/

-- The tabulation is opaque from here on. `halting_reduction` only ever feeds it to
-- `tab_computable` and `tab_value` (once as an equality, once through `.le`); letting
-- unification unfold it into `tabOf` and the two budgeted runs instead costs more heartbeats
-- than any budget worth setting.
attribute [local irreducible] MIPRE.Halting.tab

end MIPRE.Halting


