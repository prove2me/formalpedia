-- Prove2me | Definitions.Def_MIPRE_Foundations_Repeat_DecMain
-- name    : MIPRE_Foundations_Repeat_DecMain
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T14:39:13.656544+00:00
-- url     : https://prove2.me/theorems/4b497b7f-e74c-4735-94b5-c43fd35a5f5c
-- title:
--   Definitions of DecMain: The program of the repeated decider The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`;…
-- statement:
--   The definitions of the module `MIPRE.Foundations.Repeat.DecMain` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The program of the repeated decider. The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`; `planning/repetition-verifier.md`, R3(c)) as a program of the ambient model, before the s-m-n construction. On `((S̄, D̄, λ, τ, β), (n, x, y, a, b))` it 1. sanitizes `x, y, a, b` into bit strings (`bitsProg`: every element read as a bit), so that the rest of the program is total on every datum; 2. computes, in unary, `s = s(n)` from `S̄`, `m = τ(|λ| + |n|)`, the repetition count `k = 2^m`, the question length `k s`, and the parse length `B = 2^{β(|λ| + |n|)}`; 3. checks `|x| = |y| = k s`…
--
--   **Definitions** (19): `MIPRE.Cost.Prog.andExpr` (`ok₁ ∧ ok₂ ∧ ok₃ ∧ ok₄` on encoded booleans at the given indices (each test extends the environment by two entries).); `MIPRE.Cost.Prog.bitsBody` (Body of the sanitizer: on `cons rem acc`, move the head of `rem`, read as a bit, onto `acc`.); `MIPRE.Cost.Prog.bitsCost` (The cost of the sanitizer on a list of length `L` and size `sz`.); `MIPRE.Cost.Prog.bitsProg` (The sanitizer: the bits of a list, `encode (bitsOf l)`.); `MIPRE.Cost.Prog.decInput` (The input of `prepProg`: `(S̄, D̄, λ, τ, β, n, x, y, a, b)`.); `MIPRE.Cost.Prog.decMain` (The main program: the preparation, then the coordinate loop on its state.); `MIPRE.Cost.Prog.decParams` (The hardcoded datum `((S̄, D̄), λ, τ, β)`.); `MIPRE.Cost.Prog.eqCost` (The cost of `eqBitsProg` on `l₁`, `l₂`.); `MIPRE.Cost.Prog.lenCost` (The cost of `lenProg` on a list of length `L` and size `sz`.); `MIPRE.Cost.Prog.parseCost` (The cost of `parseProg` on `x`.); `MIPRE.Cost.Prog.prepCost` (The cost of `prepProg`.); `MIPRE.Cost.Prog.prepEnv` (The environment of `prepProg` after its straight-line prefix, in terms of the parameters.); `MIPRE.Cost.Prog.prepOk` (The four verdicts of the checks: `|x| = |y| = k s`, and `a`, `b` canonical.); `MIPRE.Cost.Prog.prepPreCost` (The cost of the straight-line prefix of `prepProg`.); `MIPRE.Cost.Prog.prepProg` (Steps 1–3 of the repeated decider, returning the state of the coordinate loop or `nil`.); and -21 more.
--
--   **Formalization Note** The bundle is the module `MIPRE.Foundations.Repeat.DecMain` (`MIPRE/Foundations/Repeat/DecMain.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 31 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/DecMain.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecMain.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Prog_parseProg_runs

/-!
# The program of the repeated decider

The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`;
`planning/repetition-verifier.md`, R3(c)) as a program of the ambient model, before the s-m-n
construction. On `((S̄, D̄, λ, τ, β), (n, x, y, a, b))` it

1. sanitizes `x, y, a, b` into bit strings (`bitsProg`: every element read as a bit), so that
   the rest of the program is total on every datum;
2. computes, in unary, `s = s(n)` from `S̄`, `m = τ(|λ| + |n|)`, the repetition count
   `k = 2^m`, the question length `k s`, and the parse length `B = 2^{β(|λ| + |n|)}`;
3. checks `|x| = |y| = k s` and that `a`, `b` are the serializations of the data they parse to
   (`Data.parse`, `Data.toBitsPost`), the four verdicts combined by `andExpr`;
4. runs the coordinate loop `coordBody` on the state `(k, x, y, parse a, parse b, (D̄, n, s, B))`.

`prepProg` is steps 1–3, returning the state of the loop or `nil`; its run lemma
`prepProg_runs` is a straight line of deterministic steps, generated mechanically.
-/

namespace MIPRE.Cost

open Data

namespace Prog

/-! ## Sanitizing a list into a bit string -/

/-- Body of the sanitizer: on `cons rem acc`, move the head of `rem`, read as a bit, onto `acc`. -/
def bitsBody : Prog :=
  .elim 0 .nil
    (.elim 0 (.cons .nil (.var 1))
      (.elim 0
        (.cons (.cons .nil .nil) (.cons (.var 1) (.cons .nil (.var 3))))
        (.cons (.cons .nil .nil) (.cons (.var 3) (.cons (.cons .nil .nil) (.var 5))))))

/-- The sanitizer: the bits of a list, `encode (bitsOf l)`. -/
def bitsProg : Prog := .let_ (.cons (.var 0) .nil) (.let_ (.loop bitsBody) (callVar 0 revProg))

/-! ## Conjunction of four verdicts -/

/-- `ok₁ ∧ ok₂ ∧ ok₃ ∧ ok₄` on encoded booleans at the given indices (each test extends the
environment by two entries). -/
def andExpr (i₁ i₂ i₃ i₄ : ℕ) : Prog :=
  .elim i₁ .nil (.elim (i₂ + 2) .nil (.elim (i₃ + 4) .nil (.elim (i₄ + 6) .nil (.cons .nil .nil))))

/-! ## The straight-line prefix of the decider (generated) -/

/-- The input of `prepProg`: `(S̄, D̄, λ, τ, β, n, x, y, a, b)`. -/
def decInput (sP dP lamD tauD betaD nD xD yD aD bD : Data) : Data :=
  (Data.cons sP (Data.cons dP (Data.cons lamD (Data.cons tauD (Data.cons betaD (Data.cons nD (Data.cons xD (Data.cons yD (Data.cons aD bD)))))))))

/-- Steps 1–3 of the repeated decider, returning the state of the coordinate loop or `nil`. -/
def prepProg (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.elim 1 .nil (.let_ (.cons (.var 16) (.cons (.var 6) (.const (encode CL.Sampler.Query.dimension)))) (.let_ (callVar 0 univ) (.let_ (callVar 0 toUnaryProg) (.let_ (callVar 13 toUnaryProg) (.let_ (.cons (.var 0) (.cons (.var 16) (.cons (.var 10) .nil))) (.let_ (callVar 0 (.loop powBody)) (.let_ (.cons (.var 0) (.var 3)) (.let_ (callVar 0 (.loop dblBody)) (.let_ (.const (ofNat 1)) (.let_ (.cons (.var 3) (.var 0)) (.let_ (callVar 0 (.loop dblBody)) (.let_ (callVar 19 toUnaryProg) (.let_ (.cons (.var 0) (.cons (.var 24) (.cons (.var 18) .nil))) (.let_ (callVar 0 (.loop powBody)) (.let_ (.cons (.var 0) (.var 5)) (.let_ (callVar 0 (.loop dblBody)) (.let_ (callVar 20 bitsProg) (.let_ (callVar 19 bitsProg) (.let_ (callVar 18 bitsProg) (.let_ (callVar 20 bitsProg) (.let_ (callVar 3 lenProg) (.let_ (.cons (.var 0) (.var 13)) (.let_ (callVar 0 eqBitsProg) (.let_ (callVar 5 lenProg) (.let_ (.cons (.var 0) (.var 16)) (.let_ (callVar 0 eqBitsProg) (.let_ (callVar 7 parseProg) (.let_ (callVar 0 serProg) (.let_ (.cons (.var 0) (.var 9)) (.let_ (callVar 0 eqBitsProg) (.let_ (callVar 10 parseProg) (.let_ (callVar 0 serProg) (.let_ (.cons (.var 0) (.var 12)) (.let_ (callVar 0 eqBitsProg) ((.let_ (andExpr 11 8 4 0) (.let_ (.cons (.var 49) (.cons (.var 41) (.cons (.var 32) (.var 19)))) (.elim 1 .nil (.cons (.var 27) (.cons (.var 21) (.cons (.var 20) (.cons (.var 11) (.cons (.var 7) (.var 2))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The environment of `prepProg` after its straight-line prefix, in terms of the parameters. -/
def prepEnv (univ : Prog) (sP dP : Data) (lam tau beta n s : ℕ) (xD yD aD bD : Data) : Env :=
  [(ofBool ((parse (bitsOf (toList bD))).toBitsPost == (bitsOf (toList bD)))), (Data.cons (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD)))), (encode (parse (bitsOf (toList bD))).toBitsPost), (parse (bitsOf (toList bD))), (ofBool ((parse (bitsOf (toList aD))).toBitsPost == (bitsOf (toList aD)))), (Data.cons (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD)))), (encode (parse (bitsOf (toList aD))).toBitsPost), (parse (bitsOf (toList aD))), (ofBool (decide ((bitsOf (toList yD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))), (Data.cons (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))), (ofNat (bitsOf (toList yD)).length), (ofBool (decide ((bitsOf (toList xD)).length = (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)))), (Data.cons (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s))), (ofNat (bitsOf (toList xD)).length), (encode (bitsOf (toList bD))), (encode (bitsOf (toList aD))), (encode (bitsOf (toList yD))), (encode (bitsOf (toList xD))), (ofNat (2 ^ (beta * (Nat.size lam + Nat.size n)))), (Data.cons (ofNat (beta * (Nat.size lam + Nat.size n))) (ofNat 1)), (ofNat (beta * (Nat.size lam + Nat.size n))), (Data.cons (ofNat beta) (Data.cons (encode lam) (Data.cons (encode n) Data.nil))), (ofNat beta), (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))), (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat 1)), (ofNat 1), (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)), (Data.cons (ofNat (tau * (Nat.size lam + Nat.size n))) (ofNat s)), (ofNat (tau * (Nat.size lam + Nat.size n))), (Data.cons (ofNat tau) (Data.cons (encode lam) (Data.cons (encode n) Data.nil))), (ofNat tau), (ofNat s), (encode s), (Data.cons sP (Data.cons (encode n) (encode CL.Sampler.Query.dimension))), aD, bD, yD, (Data.cons aD bD), xD, (Data.cons yD (Data.cons aD bD)), (encode n), (Data.cons xD (Data.cons yD (Data.cons aD bD))), (encode beta), (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))), (encode tau), (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))), (encode lam), (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))), dP, (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD))))))), sP, (Data.cons dP (Data.cons (encode lam) (Data.cons (encode tau) (Data.cons (encode beta) (Data.cons (encode n) (Data.cons xD (Data.cons yD (Data.cons aD bD)))))))), decInput sP dP (encode lam) (encode tau) (encode beta) (encode n) xD yD aD bD]

-- indices: ex 11, ey 8, ea 4, eb 0, ok 1; final: uk 27, xq 21, yq 20, pa 11, pb 7, ctx 2

/-- The cost of the sanitizer on a list of length `L` and size `sz`. -/
def bitsCost (L sz : ℕ) : ℕ := (L + 2) * (sz + 2 * L + 15) + (L + 2) * (4 * L + 20)

/-- The cost of `lenProg` on a list of length `L` and size `sz`. -/
def lenCost (L sz : ℕ) : ℕ := (L + 1 + 1) * (sz + 1 + 2 * L + 13)

/-- The cost of `eqBitsProg` on `l₁`, `l₂`. -/
def eqCost (l₁ l₂ : Data) : ℕ := (l₁.spine + 1) * (l₁.size + l₂.size + 21)

/-- The cost of `parseProg` on `x`. -/
def parseCost (x : BitStr) : ℕ := (x.length + 2) * ((encode x : Data).size + 2 * x.length + 25)

/-- The cost of `serProg` on `d`. -/
def serCost (d : Data) : ℕ := (3 * d.size + 2) * (16 * d.size + 42) + (d.size + 2) * (5 * d.size + 30)

/-- The cost of the straight-line prefix of `prepProg`. -/
def prepPreCost (sP dP : Data) (lam tau beta n s : ℕ) (xD yD aD bD : Data) (td : ℕ) : ℕ :=
  6 * (td + toUnaryCost s + toUnaryCost tau + toUnaryCost beta +
    powCost tau (Nat.size lam + Nat.size n) ((encode lam : Data).size + (encode n : Data).size + 1) +
    powCost beta (Nat.size lam + Nat.size n) ((encode lam : Data).size + (encode n : Data).size + 1) +
    dblCost (tau * (Nat.size lam + Nat.size n)) s + dblCost (tau * (Nat.size lam + Nat.size n)) 1 + dblCost (beta * (Nat.size lam + Nat.size n)) 1 +
    bitsCost (toList xD).length xD.size + bitsCost (toList yD).length yD.size +
    bitsCost (toList aD).length aD.size + bitsCost (toList bD).length bD.size +
    lenCost (bitsOf (toList xD)).length (encode (bitsOf (toList xD)) : Data).size + lenCost (bitsOf (toList yD)).length (encode (bitsOf (toList yD)) : Data).size +
    eqCost (ofNat (bitsOf (toList xD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) + eqCost (ofNat (bitsOf (toList yD)).length) (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)) * s)) +
    parseCost (bitsOf (toList aD)) + serCost (parse (bitsOf (toList aD))) +
    eqCost (encode (parse (bitsOf (toList aD))).toBitsPost) (encode (bitsOf (toList aD))) +
    parseCost (bitsOf (toList bD)) + serCost (parse (bitsOf (toList bD))) +
    eqCost (encode (parse (bitsOf (toList bD))).toBitsPost) (encode (bitsOf (toList bD)))) +
  8 * (sP.size + dP.size + (encode lam : Data).size + (encode tau : Data).size +
    (encode beta : Data).size + (encode n : Data).size + xD.size + yD.size + aD.size + bD.size) + 500

/-! ## The full preparation, the main program and the core -/

/-- The four verdicts of the checks: `|x| = |y| = k s`, and `a`, `b` canonical. -/
def prepOk (lam tau n s : ℕ) (x y a b : BitStr) : Bool :=
  decide (x.length = 2 ^ (tau * (Nat.size lam + Nat.size n)) * s) &&
    decide (y.length = 2 ^ (tau * (Nat.size lam + Nat.size n)) * s) &&
    ((parse a).toBitsPost == a) && ((parse b).toBitsPost == b)

/-- The state of the coordinate loop assembled by `prepProg`. -/
def prepState (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) : Data :=
  .cons (ofNat (2 ^ (tau * (Nat.size lam + Nat.size n)))) (.cons (encode x) (.cons (encode y)
    (.cons (parse a) (.cons (parse b)
      (decCtx dP (encode n) s (2 ^ (beta * (Nat.size lam + Nat.size n))))))))

/-- The result of `prepProg`: the state when the checks pass, `nil` otherwise. -/
def prepResult (dP : Data) (lam tau beta n s : ℕ) (x y a b : BitStr) : Data :=
  if prepOk lam tau n s x y a b then prepState dP lam tau beta n s x y a b else .nil

/-- The cost of `prepProg`. -/
def prepCost (sP dP : Data) (lam tau beta n s : ℕ) (xD yD aD bD : Data) (td : ℕ) : ℕ :=
  prepPreCost sP dP lam tau beta n s xD yD aD bD td +
    8 * (dP.size + (encode n : Data).size + 2 * s + 2 * 2 ^ (beta * (Nat.size lam + Nat.size n)) +
      2 * 2 ^ (tau * (Nat.size lam + Nat.size n)) + (encode (bitsOf (toList xD)) : Data).size +
      (encode (bitsOf (toList yD)) : Data).size + (parse (bitsOf (toList aD))).size +
      (parse (bitsOf (toList bD))).size) + 100

/-- The main program: the preparation, then the coordinate loop on its state. -/
def decMain (univ : Prog) : Prog :=
  .let_ (prepProg univ) (.elim 0 .nil (callVar 2 (.loop (coordBody univ))))

/-- The hardcoded datum `((S̄, D̄), λ, τ, β)`. -/
def decParams (sP dP lamD tauD betaD : Data) : Data :=
  .cons (.cons sP dP) (.cons lamD (.cons tauD betaD))

/-- The core of the repeated decider, before the s-m-n construction: on
`(((S̄, D̄), λ, τ, β), (n, x, y, a, b))`, the main program on `(S̄, D̄, λ, τ, β, n, x, y, a, b)`. -/
def repDecCore (univ : Prog) : Prog :=
  .elim 0 .nil (.elim 0 .nil (.elim 0 .nil (.elim 3 .nil (.elim 1 .nil (.elim 9 .nil (.elim 1 .nil
    (.elim 1 .nil (.elim 1 .nil
      (.let_ (.cons (.var 12) (.cons (.var 13) (.cons (.var 10) (.cons (.var 8) (.cons (.var 9)
          (.cons (.var 6) (.cons (.var 4) (.cons (.var 2) (.cons (.var 0) (.var 1))))))))))
        (callVar 0 (decMain univ)))))))))))

end Prog

end MIPRE.Cost


