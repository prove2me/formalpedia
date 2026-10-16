-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Induction
-- name    : MIPRE_Foundations_Halting_Paper_Induction
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:13:27.081386+00:00
-- url     : https://prove2.me/theorems/e4fed09b-d0f6-49b6-96e9-fea04b7cdb02
-- title:
--   The two classes along the levels $C, 2^C, 2^{2^C}, \dots$ of the paper's recursion
-- statement:
--   Blueprint `thm:halting` in the paper's form is proved in `Paper/Induction.lean` at a fixed level, from the decider of `Paper/Decider.lean` and gap-preserving compression: if $M$ halts on the empty input, $\mathcal{V}^{\mathrm{halt}}$ has a value-$1$ PCC strategy at level $C$, and otherwise $\mathrm{val}^*(\mathcal{V}^{\mathrm{halt}}_C) \le 1/2$. This bundle defines the level, the levels of the recursion, the compressed verifier, the two branch events and the two classes the induction runs on. Fix $G$, $U$, $UT$ and $S'$.
--
--   `MIPRE.Halting.C G = max G.C₀ 2` is the level the reduction outputs, so that the time clauses of `IsBounded` apply there; `lv G : ℕ → ℕ` are the levels of the recursion started at $C$, `lv G 0 = C G` and `lv G (j + 1) = 2 ^ lv G j`. `W G U UT S' M lam` is the compressed verifier of $\mathcal{V}^{\mathrm{halt}}$, `G.output ((Vhalt …).sampler.prog, (Vhalt …).decider.prog) lam`, the same at every level. `branch1 M n` says that the first branch fires, `(evalWithin M nil (Nat.size n)).isSome = true`: $M$ halts on the empty input within $\mathrm{size}\,n$; `branch2 G U UT S' M lam n` says that the second fires: the search `searchP S' lam (dec …)` halts on the empty input within $\mathrm{size}\,n$. The classes at level $n$ are
--   $$A\;n \;:\Leftrightarrow\; (\mathrm{Vhalt}\;M\;\lambda).\mathrm{HasPerfectPCC}\;n\;(n^\lambda), \qquad B\;n \;:\Leftrightarrow\; (\mathrm{Vhalt}\;M\;\lambda).\mathrm{valStar}\;n\;(n^\lambda) \le 1/2,$$
--   a value-$1$ PCC strategy, respectively value at most $1/2$, with answers of length at most $n^\lambda$. The two embedded lemmas are the `@[simp]` equations `lv_zero` and `lv_succ`.
--
--   The argument of the module (theorems not part of this bundle) is the compressibility criterion's at the fixed level $C$: `GapCompression.completeness` and `soundness` carry $A(2^n) \to A(n)$ and $B(2^n) \to B(n)$ where neither branch fires (blueprint `lem:dhalt-values`), branch 1 puts a level in $A$ and branch 2 in $B$, and the search halts exactly when the start level has value above $1/2$.
--
--   **Formalization Note**. `A` and `B` are `Prop`-valued functions of $S'$, $M$, $\lambda$ and $n$, not sets of strings as `classA` and `classB` of the criterion route are; their answer bound is $n^\lambda$, while the final statement cuts answers at `G.bound (C + λ)`. `W` is a `noncomputable abbrev`; `branch1` and `branch2` are stated through the `noncomputable` `evalWithin`, as the equation `= true` on the `Bool` `isSome`. `C` and `lv` take only `G`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Induction.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Induction.lean (definition bundle: declarations the uploaded statements rest on);
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
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_ManyOne
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_CostBudget
import Definitions.Def_MIPRE_Foundations_Halting_Instantiation
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Halting_Semidecider
import Definitions.Def_MIPRE_Foundations_Halting_WrapperCost
import Definitions.Def_MIPRE_Foundations_Halting_Strings
import Definitions.Def_MIPRE_Foundations_Halting_Reduction
import Definitions.Def_MIPRE_Foundations_Halting_Compressor
import Definitions.Def_MIPRE_Foundations_Halting_Paper_TabulateL
import Definitions.Def_MIPRE_Foundations_Halting_Paper_Decider

/-!
# The halting verifier along the paper's route: the values at level `C`

Blueprint `thm:halting` in the paper's form, at a fixed level, from the decider of
`Paper/Decider.lean` and gap-preserving compression: for a machine `M` and a parameter `λ`
such that `𝒱^halt_{M,λ}` is `λ`-bounded (the accounting of `Paper/Cost.lean` supplies one),

* if `M` halts on the empty input, `𝒱^halt` has a value-`1` PCC strategy at level `C`;
* if it does not, `val*(𝒱^halt_C) ≤ 1/2`;

with `C = max C₀ 2` and answers of length at most `G.bound (C + λ)`.

The argument is the criterion's (`Cost.compressibility_criterion_levels`) at the fixed level
`C`, along the levels `C, 2 ^ C, 2 ^ (2 ^ C), …` of the recursion (`lv`): the two classes are
`A n`, a value-`1` PCC strategy at level `n` with answers of length at most `n ^ λ`, and `B n`,
value at most `1/2` there; `GapCompression.completeness` and `soundness` carry `A (2 ^ n) → A n`
and `B (2 ^ n) → B n` at every level where neither of the decider's first two branches fires
(`lem:dhalt-values`, the acceptance agreement with the compressed verifier); branch 1 puts a
level in `A` outright and branch 2 in `B`; and the search halts exactly when the start level
has value above `1/2` (`exists_semL`, `tabL_value`), which is what rules the search out below
the level where `M` halts, and rules the start level out of `B`'s complement when `M` does not.
-/

namespace MIPRE.Halting

open Cost Cost.Prog

variable (G : GapCompression) (U : UniversalMachine) (UT : ClockedUniversalMachine)

/-- The level the reduction outputs: `max C₀ 2`, so that the time clauses of `IsBounded` apply
there. -/
def C (G : GapCompression) : ℕ := max G.C₀ 2

/-- The levels of the recursion started at `C`: `C, 2 ^ C, 2 ^ (2 ^ C), …`. -/
def lv (G : GapCompression) : ℕ → ℕ
  | 0 => C G
  | j + 1 => 2 ^ lv G j

@[simp] theorem lv_zero : lv G 0 = C G := rfl

@[simp] theorem lv_succ (j : ℕ) : lv G (j + 1) = 2 ^ lv G j := rfl

section

variable {S' : Prog} (hS' : S'.WellScoped 1)
  (hsem : ∀ x : BitStr, Halts S' (encode x) ↔
    (1 : ℝ) / 2 < quantumValue (tabL G U x (C G)).game)
  (M : Prog) (lam : ℕ)
  (hb : (Vhalt G U UT S' M lam).IsBounded lam)
  (hpoly : ∀ n, 2 ≤ n → G.bound.eval (n + lam) ≤ n ^ lam)

include hS' hsem hb hpoly

/-- The compressed verifier of `𝒱^halt`, the same at every level. -/
noncomputable abbrev W (S' M : Prog) (lam : ℕ) : Verifier 7 :=
  G.output ((Vhalt G U UT S' M lam).sampler.prog, (Vhalt G U UT S' M lam).decider.prog) lam

/-- The first branch fires: `M` halts within `Nat.size n`. -/
def branch1 (M : Prog) (n : ℕ) : Prop := (evalWithin M .nil (Nat.size n)).isSome = true

/-- The second branch fires: the search halts within `Nat.size n`. -/
def branch2 (S' M : Prog) (lam n : ℕ) : Prop :=
  (evalWithin (searchP S' lam (dec G U UT S' M lam)) .nil (Nat.size n)).isSome = true

/-! ## The acceptance of `𝒱^halt` at a level, by branch -/

/-! ## The two classes and the compression steps -/

/-- The class `A` at level `n`: a value-`1` PCC strategy with answers of length at most `n ^ λ`. -/
def A (S' M : Prog) (lam n : ℕ) : Prop := (Vhalt G U UT S' M lam).HasPerfectPCC n (n ^ lam)

/-- The class `B` at level `n`: value at most `1/2` with answers of length at most `n ^ λ`. -/
def B (S' M : Prog) (lam n : ℕ) : Prop := (Vhalt G U UT S' M lam).valStar n (n ^ lam) ≤ 1 / 2

/-! ## The search and the start level -/

/-! ## The two cases -/

end

end MIPRE.Halting


