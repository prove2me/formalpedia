-- Prove2me | Definitions.Def_MIPRE_Foundations_SAT_Succinct
-- name    : MIPRE_Foundations_SAT_Succinct
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:43.990572+00:00
-- url     : https://prove2.me/theorems/d7f7e851-6270-499d-b9e6-cb9f246e722b
-- title:
--   Definitions of Succinct: The succinct Cook–Levin theorem: the statement `MIPRE.SAT.SuccinctCookLevin` is blueprint `thm:succinct-sat` — the…
-- statement:
--   The definitions of the module `MIPRE.Foundations.SAT.Succinct` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The succinct Cook–Levin theorem: the statement. `MIPRE.SAT.SuccinctCookLevin` is blueprint `thm:succinct-sat` — the paper's `prop:standard-succinct-sat` (`answer_reduction.tex`, `sec:cook-levin`) — in the vocabulary of the ambient model: a polynomial-time algorithm that, on a decider `𝒟`, an index `n`, a time bound `T`, a question length `Q`, a description-length bound `σ` and questions `x, y`, outputs a circuit `C` on `3m + 3` inputs which succinctly describes a 3SAT formula `C.formula3 m` on `2^m` variables (`def:succinct-formulas`: `C(i₁, i₂, i₃, o₁, o₂, o₃) = 1` iff `x_{i₁}^{o₁} ∨…
--
--   **Definitions** (9): `MIPRE.Decider.AcceptsWithin` (`𝒟` accepts `(n, x, y, a, b)` within cost `T`.); `MIPRE.SAT.Circuit.formula3` (The 3SAT formula on `2^m` variables that `C` succinctly describes: the clauses `C` accepts (`def:succinct-formulas`).); `MIPRE.SAT.DescInput` (The input of the describer: `((𝒟, n, T, Q, σ), x, y)`.); `MIPRE.SAT.EncodesAccepted` (`a` is the tape encoding of a string of length at most `T` on which, together with the string encoded by `b`, the decider accepts within…); `MIPRE.SAT.ExtendsAnswers` (A satisfying assignment of a formula on `2^m ≥ 4T` variables extending the answer blocks `a, b ∈ {0,1}^{2T}` on the first `4T` variables.); `MIPRE.SAT.Valid` (The validity hypotheses of the paper's proposition: `max{Q, 2⌈log n⌉} ≤ T`, `|𝒟| ≤ σ` and `|x|, |y| ≤ Q`.); `MIPRE.SAT.cellBits` (The two-bit encoding of a tape cell: `0 ↦ 00`, `1 ↦ 01`, blank `↦ 10` (the boundary symbol of the tableau is `11`).); `MIPRE.SAT.clauseInput` (The input bits presenting a clause to a describer on `3m + 3` inputs: the three `m`-bit indices, then the three signs.); `MIPRE.SAT.tapeBits` (The bits of a tape holding `s` followed by blanks: position `p` is bit `p % 2` of cell `p / 2`.).
--
--   **Embedded lemmas** (1): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `length_clauseInput`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.SAT.Succinct` (`MIPRE/Foundations/SAT/Succinct.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 12 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Succinct.lean; blueprint def:succinct-3sat

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Succinct.lean (definition bundle: declarations the uploaded statements rest on);
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
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier

/-!
# The succinct Cook–Levin theorem: the statement

`MIPRE.SAT.SuccinctCookLevin` is blueprint `thm:succinct-sat` — the paper's
`prop:standard-succinct-sat` (`answer_reduction.tex`, `sec:cook-levin`) — in the vocabulary
of the ambient model: a polynomial-time algorithm that, on a decider `𝒟`, an index `n`, a
time bound `T`, a question length `Q`, a description-length bound `σ` and questions `x, y`,
outputs a circuit `C` on `3m + 3` inputs which succinctly describes a 3SAT formula
`C.formula3 m` on `2^m` variables (`def:succinct-formulas`: `C(i₁, i₂, i₃, o₁, o₂, o₃) = 1`
iff `x_{i₁}^{o₁} ∨ x_{i₂}^{o₂} ∨ x_{i₃}^{o₃}` is a clause), such that

1. for all `a, b ∈ {0,1}^{2T}`, the formula has a satisfying assignment extending `a` and `b`
   on its first `4T` variables iff `a` and `b` are the two-bit tape encodings
   (`tapeBits`: `0 ↦ 00`, `1 ↦ 01`, blank `↦ 10`) of strings of length at most `T` on which
   `𝒟` accepts `(n, x, y, ·, ·)` within cost `T` (`Decider.AcceptsWithin`);
2. `m = O(log T + log σ)` and `2^m ≥ 4T`;
3. `C` has at most `s(n, T, Q, σ) = poly(log n, log T, Q, σ)` gates;
4. the algorithm runs in polynomial time (`PolyTimeFun`, whose bound is a polynomial in the
   size of the input, itself at most `poly(log n, log T, Q, σ)` under the validity
   hypotheses);
5. `m` and `s` are polynomial-time computable from the parameters.

"Within `T` steps" is cost at most `T` in the ambient model, the reading of every time bound
of the pipeline (`Decider.TimeBoundAt`). An instance of this structure is the theorem; its
inhabitation is `planning/succinct-cook-levin.md`. The validity hypotheses `Valid` are the
paper's: `max{Q, 2⌈log n⌉} ≤ T`, `|𝒟| ≤ σ`, `|x|, |y| ≤ Q`.
-/

namespace MIPRE.SAT

open Cost

/-! ## Succinctly described 3SAT formulas -/

/-- The input bits presenting a clause to a describer on `3m + 3` inputs: the three `m`-bit
indices, then the three signs. -/
def clauseInput (m : ℕ) (c : Clause3 (Fin (2 ^ m))) : List Bool :=
  bitsOfNat m c.l₁.var ++ bitsOfNat m c.l₂.var ++ bitsOfNat m c.l₃.var ++
    [c.l₁.pos, c.l₂.pos, c.l₃.pos]

@[simp] theorem length_clauseInput (m : ℕ) (c : Clause3 (Fin (2 ^ m))) :
    (clauseInput m c).length = 3 * m + 3 := by
  simp [clauseInput]; omega

/-- The 3SAT formula on `2^m` variables that `C` succinctly describes: the clauses `C`
accepts (`def:succinct-formulas`). -/
def Circuit.formula3 (C : Circuit) (m : ℕ) : Cnf3 (Fin (2 ^ m)) :=
  {c | C.evalBits (clauseInput m c) = true}

/-! ## Tape encodings of answers -/

/-- The two-bit encoding of a tape cell: `0 ↦ 00`, `1 ↦ 01`, blank `↦ 10` (the boundary
symbol of the tableau is `11`). -/
def cellBits : Option Bool → Bool × Bool
  | some false => (false, false)
  | some true => (false, true)
  | none => (true, false)

/-- The bits of a tape holding `s` followed by blanks: position `p` is bit `p % 2` of cell
`p / 2`. -/
def tapeBits (s : Cost.BitStr) (p : ℕ) : Bool :=
  if p % 2 = 0 then (cellBits s[p / 2]?).1 else (cellBits s[p / 2]?).2

/-! ## Deciders accepting within a cost -/

/-- `𝒟` accepts `(n, x, y, a, b)` within cost `T`. -/
def _root_.MIPRE.Decider.AcceptsWithin (D : Decider) (n : ℕ) (x y a b : Cost.BitStr) (T : ℕ) :
    Prop :=
  ∃ t ≤ T, D.prog.Runs (encode (n, x, y, a, b)) (encode true) t

/-! ## The theorem -/

/-- The input of the describer: `((𝒟, n, T, Q, σ), x, y)`. -/
abbrev DescInput : Type := (Prog × ℕ × ℕ × ℕ × ℕ) × Cost.BitStr × Cost.BitStr

/-- The validity hypotheses of the paper's proposition: `max{Q, 2⌈log n⌉} ≤ T`, `|𝒟| ≤ σ`
and `|x|, |y| ≤ Q`. -/
structure Valid (D : Prog) (n T Q σ : ℕ) (x y : Cost.BitStr) : Prop where
  q_le : Q ≤ T
  logn_le : 2 * Nat.size n ≤ T
  size_le : esize D ≤ σ
  x_le : x.length ≤ Q
  y_le : y.length ≤ Q

/-- A satisfying assignment of a formula on `2^m ≥ 4T` variables extending the answer blocks
`a, b ∈ {0,1}^{2T}` on the first `4T` variables. -/
def ExtendsAnswers {m T : ℕ} (h : 4 * T ≤ 2 ^ m) (φ : Cnf3 (Fin (2 ^ m)))
    (a b : Fin (2 * T) → Bool) : Prop :=
  ∃ w : Fin (2 ^ m) → Bool, (∀ j : Fin (2 * T), w ⟨j, by omega⟩ = a j) ∧
    (∀ j : Fin (2 * T), w ⟨2 * T + j, by omega⟩ = b j) ∧ φ.Sat w

/-- `a` is the tape encoding of a string of length at most `T` on which, together with the
string encoded by `b`, the decider accepts within cost `T`: the right-hand side of item 1. -/
def EncodesAccepted (D : Decider) (n : ℕ) (x y : Cost.BitStr) (T : ℕ)
    (a b : Fin (2 * T) → Bool) : Prop :=
  ∃ ap bp : Cost.BitStr, ap.length ≤ T ∧ bp.length ≤ T ∧ (∀ j : Fin (2 * T), a j = tapeBits ap j) ∧
    (∀ j : Fin (2 * T), b j = tapeBits bp j) ∧ D.AcceptsWithin n x y ap bp T

end MIPRE.SAT


