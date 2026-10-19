-- Prove2me | Definitions.Def_MIPRE_Background_AnswerReduction_Predicate
-- name    : MIPRE_Background_AnswerReduction_Predicate
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:09.716279+00:00
-- url     : https://prove2.me/theorems/f9b884bc-f3f1-49f8-848b-4da511cce532
-- title:
--   Definitions of Predicate: The answer-reduced decision predicate Piece AR-3b of `planning/answer-reduction.md`: the decision procedure `D̂^ar` of…
-- statement:
--   The definitions of the module `MIPRE.Background.AnswerReduction.Predicate` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The answer-reduced decision predicate. Piece AR-3b of `planning/answer-reduction.md`: the decision procedure `D̂^ar` of the paper's `fig:decider-pcp` (`ld_compiler.tex`), on parsed answers, as a Boolean predicate. A type of the answer-reduced verifier is a pair `(r, t)` of an oracularization role `r` and a PCP type `t = (i, τ)`, a copy of the low-degree test and a test type. A question carries, besides the type, the oracle part `x_Q` (whatever the input sampler's seed space is: a type parameter `X` here) and the PCP part, a vector of `V^pcp`. An answer is an answer of the copy's low-degree…
--
--   **Definitions** (15): `MIPRE.AnswerReduction.Ans` (**Answers** of the answer-reduced verifier: an answer of the `m`-variable test with one codeword (copies `1`–`5`), or of the `m'`-variable…); `MIPRE.AnswerReduction.Q` (A question of the answer-reduced verifier, decoded: the type, the oracle part and the PCP vector.); `MIPRE.AnswerReduction.accepts` (**The answer-reduced decision predicate** (`fig:decider-pcp`): the format preamble, the global consistency check, and the other four steps…); `MIPRE.AnswerReduction.ans1` (The `m`-variable test's answer, the zero point answer otherwise.); `MIPRE.AnswerReduction.ans6` (The `m'`-variable test's answer, the zero point answer otherwise.); `MIPRE.AnswerReduction.ansFmt` (**The format preamble** for one answer: of its copy's test, in its type's format.); `MIPRE.AnswerReduction.dPcp` (The individual degree bound of the PCP, `d = 7`.); `MIPRE.AnswerReduction.q1` (The `m`-variable test's question of copy `i ≤ 5` at a vector.); `MIPRE.AnswerReduction.q6` (The `m'`-variable test's question of copy 6 at a vector.); `MIPRE.AnswerReduction.roleIdx` (The index `v - 1` of the input codeword an isolated player's role names: `0` for Alice, `1` for Bob.); `MIPRE.AnswerReduction.side` (**One side of the five steps**, for the player asked `p` and answering `a`, against the other player asked `q` and answering `b`.); `MIPRE.AnswerReduction.tyFmt` (The format a test type prescribes, on an answer of any test.); and -15 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.AnswerReduction.Predicate` (`MIPRE/Background/AnswerReduction/Predicate.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 28 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/AnswerReduction/Predicate.lean; blueprint def:ar-decider-predicate

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/AnswerReduction/Predicate.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Background_AnswerReduction_PcpPresentation
import Definitions.Def_MIPRE_Foundations_OracularGame

/-!
# The answer-reduced decision predicate

Piece AR-3b of `planning/answer-reduction.md`: the decision procedure `D̂^ar` of the paper's
`fig:decider-pcp` (`ld_compiler.tex`), on parsed answers, as a Boolean predicate.

A type of the answer-reduced verifier is a pair `(r, t)` of an oracularization role `r` and a PCP
type `t = (i, τ)`, a copy of the low-degree test and a test type. A question carries, besides the
type, the oracle part `x_Q` (whatever the input sampler's seed space is: a type parameter `X`
here) and the PCP part, a vector of `V^pcp`. An answer is an answer of the copy's low-degree test:
of the `m`-variable test with one codeword for the first five copies, of the `m'`-variable test
with `m' + 6` codewords for the sixth (`Ans`). The oracle answers of the input verifier are never
sent: that is the answer reduction.

The predicate (`accepts`) is the format preamble and then the five steps, each for both players:

1. equal types, equal answers;
2. the oracle's `Point_6` answer against an isolated player `v`'s `Point_v` answer, on the `v`-th
   component (`α'_v = α_v`), `v = 1, 2` for Alice and Bob;
3. an isolated player's own input codeword, on copy `v`: the `m`-variable low-degree test;
4. between two oracles, on copies `3, 4, 5`: the consistency `α_i = α'_i` against copy 6, and the
   individual `m`-variable low-degree test; on copy 6, the simultaneous `m'`-variable test with
   `m' + 6` codewords;
5. the game check: an oracle's `Point_6` answer, with the point, is a PCP view, and the PCP
   verifier (`check`, a parameter here) must accept it.

The format preamble checks every answer, including those no step reads (the paper's round-12
repair to its preamble): each answer must be of its copy's test and of the format its test type
prescribes (`ansFmt`).
-/

noncomputable section

namespace MIPRE.AnswerReduction

open Finset MIPRE.LIDT MIPRE.LIDT.CL SAT Pcp

variable (P : PcpParams) (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The individual degree bound of the PCP, `d = 7`. -/
abbrev dPcp : ℕ := PcpParams.d

/-- **Answers** of the answer-reduced verifier: an answer of the `m`-variable test with one
codeword (copies `1`–`5`), or of the `m'`-variable test with `m' + 6` codewords (copy `6`). -/
abbrev Ans := CL.Answer F P.m dPcp 1 ⊕ CL.Answer F P.m' dPcp (P.m' + 6)

variable {P F}

/-- The format a test type prescribes, on an answer of any test. -/
def tyFmt {n d ldc : ℕ} : LIDT.CL.Ty → CL.Answer F n d ldc → Bool
  | .point, .values _ => true
  | .aline, .apolys _ => true
  | .dline, .dpolys _ => true
  | _, _ => false

/-- **The format preamble** for one answer: of its copy's test, in its type's format. -/
def ansFmt (t : PcpTy) : Ans P F → Bool
  | .inl a => decide ((t.1 : ℕ) < 5) && tyFmt t.2 a
  | .inr a => decide ((t.1 : ℕ) = 5) && tyFmt t.2 a

/-- The single value of a point answer of copies `1`–`5`, `0` otherwise. -/
def val1 : Ans P F → F
  | .inl (.values a) => a 0
  | _ => 0

/-- The `i`-th component of a `Point_6` answer, `0` otherwise. The first five components are the
`α'_i`, the rest the `β_j` of the constraint polynomials. -/
def val6 (i : Fin (P.m' + 6)) : Ans P F → F
  | .inr (.values a) => a i
  | _ => 0

/-- The point answer of copy 6 as a vector, `0` otherwise: the PCP view's evaluation part. -/
def vals6 : Ans P F → Fin (P.m' + 6) → F
  | .inr (.values a) => a
  | _ => 0

/-- The `m`-variable test's answer, the zero point answer otherwise. -/
def ans1 : Ans P F → CL.Answer F P.m dPcp 1
  | .inl a => a
  | _ => .values 0

/-- The `m'`-variable test's answer, the zero point answer otherwise. -/
def ans6 : Ans P F → CL.Answer F P.m' dPcp (P.m' + 6)
  | .inr a => a
  | _ => .values 0

/-- The index `v - 1` of the input codeword an isolated player's role names: `0` for Alice, `1`
for Bob. -/
def roleIdx : Role → Option (Fin 5)
  | .oracle => none
  | .alice => some 0
  | .bob => some 1

variable [NeZero P.m] {hm : P.m ∣ Fintype.card F} {hm' : P.m' ∣ Fintype.card F}
  (S : Sel F P.m hm) (S' : Sel F P.m' hm')

/-- The `m'`-variable test's question of copy 6 at a vector. -/
def q6 (τ : LIDT.CL.Ty) (x : Coord P → F) : LIDT.CL.Question F P.m' :=
  (((regs6 P).sampleOf S' τ x).question hm' τ)

/-- The `m`-variable test's question of copy `i ≤ 5` at a vector. -/
def q1 (i : Fin 5) (τ : LIDT.CL.Ty) (x : Coord P → F) : LIDT.CL.Question F P.m :=
  (((regs P i).sampleOf S τ x).question hm τ)

variable {X : Type*}

/-- A question of the answer-reduced verifier, decoded: the type, the oracle part and the PCP
vector. -/
abbrev Q (P : PcpParams) (F : Type*) (X : Type*) := (Role × PcpTy) × X × (Coord P → F)

/-- **One side of the five steps**, for the player asked `p` and answering `a`, against the other
player asked `q` and answering `b`. `check x z α` is the PCP verifier's decision on the view
`(z, α)` for the input question pair read off the oracle part `x`. -/
def side (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
    (p q : Q P F X) (a b : Ans P F) : Bool :=
  let r := p.1.1; let i := p.1.2.1; let τ := p.1.2.2
  let r' := q.1.1; let i' := q.1.2.1; let τ' := q.1.2.2
  -- step 2: the oracle's `Point_6` against an isolated player's `Point_v`
  (match r, roleIdx r' with
    | .oracle, some v =>
      if (i : ℕ) = 5 ∧ τ = .point ∧ (i' : ℕ) = v ∧ τ' = .point then
        decide (val6 ⟨v, by have := v.isLt; omega⟩ a = val1 b)
      else true
    | _, _ => true) &&
  -- step 3: an isolated player's input codeword
  (match roleIdx r, roleIdx r' with
    | some v, some v' =>
      if v = v' ∧ (i : ℕ) = v ∧ (i' : ℕ) = v ∧ τ = .point ∧ τ' ≠ .point then
        CL.accepts hm (q1 S v τ p.2.2) (q1 S v τ' q.2.2) (ans1 a) (ans1 b)
      else true
    | _, _ => true) &&
  -- step 4: between two oracles
  (if r = .oracle ∧ r' = .oracle then
    (if h : 2 ≤ (i : ℕ) ∧ (i : ℕ) < 5 ∧ τ = .point ∧ (i' : ℕ) = 5 ∧ τ' = .point then
      decide (val1 a = val6 ⟨i, by omega⟩ b) else true) &&
    (if h : 2 ≤ (i : ℕ) ∧ (i : ℕ) < 5 ∧ i' = i ∧ τ = .point ∧ τ' ≠ .point then
      CL.accepts hm (q1 S ⟨i, h.2.1⟩ τ p.2.2) (q1 S ⟨i, h.2.1⟩ τ' q.2.2) (ans1 a) (ans1 b)
      else true) &&
    (if (i : ℕ) = 5 ∧ (i' : ℕ) = 5 ∧ τ = .point ∧ τ' ≠ .point then
      CL.accepts hm' (q6 S' τ p.2.2) (q6 S' τ' q.2.2) (ans6 a) (ans6 b)
      else true)
  else true) &&
  -- step 5: the game check
  (if r = .oracle ∧ (i : ℕ) = 5 ∧ τ = .point then
    check p.2.1 ((regs6 P).ptOf p.2.2) (vals6 a)
  else true)

/-- **The answer-reduced decision predicate** (`fig:decider-pcp`): the format preamble, the global
consistency check, and the other four steps for both players. -/
def accepts (check : X → (Fin P.m' → F) → (Fin (P.m' + 6) → F) → Bool)
    (p q : Q P F X) (a b : Ans P F) : Bool :=
  ansFmt p.1.2 a && ansFmt q.1.2 b &&
  (if p.1 = q.1 then decide (a = b) else true) &&
  side S S' check p q a b && side S S' check q p b a

end MIPRE.AnswerReduction

end


