-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Paper_Stages
-- name    : MIPRE_Foundations_Halting_Paper_Stages
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T19:14:10.725583+00:00
-- url     : https://prove2.me/theorems/b4436322-7353-4aef-87ce-a455821ba60f
-- title:
--   Stages of the class verifier's programs: sequencing, universal calls and unary conversions
-- statement:
--   The sampler and the decider of the class verifier of the polynomial-time halting reduction are chains of stages: polynomial-time functions run by their `code`, calls of the universal machine on a program and an input the previous stage produced, and one binary-to-unary conversion of the sampler's dimension. The universal calls and the conversion are not `PolyTimeFun`s (the first is polynomial in the simulated program's own time, the second in the number it converts), so the chain is assembled at the level of programs. This bundle provides the stage combinators and four polynomial-time pieces.
--
--   **Programs.** `MIPRE.Cost.Prog.seq p q = let_ p (callVar 0 q)` runs $p$, then the closed program $q$ on its output. `runUK univ`, on `encode ((c, v), s)`, runs `univ` on $(c, v)$ and returns `encode (s, r)` where $c$ on $v$ returns $r$, keeping the state $s$. `unaryStage`, on `encode (s, n)`, returns `encode (s, unary n)` through `toUnaryProg`.
--
--   **Polynomial-time functions** (`Unary` is `List Unit`, `unary n` the list of $n$ units): `MIPRE.Cost.PolyTimeFun.expBits : PolyTimeFun Unary ℕ` is $u \mapsto 2^{|u|}$, by `expBitsProg`, with time bound $(X + 2)(4X + 20)$; `addConstU K : PolyTimeFun Unary Unary` is $u \mapsto \mathrm{unary}(K + |u|)$, by `addConstProg K`; `unaryMul D : PolyTimeFun Unary Unary` is $u \mapsto \mathrm{unary}(D\cdot|u|)$, $D$ copies of $u$ appended, by recursion on $D$ from `const []` and `append`; `lenBin : PolyTimeFun (List α) ℕ`, for any `SizedEncoding α`, is the length of a list in binary, `unaryToBin.comp length`.
--
--   The embedded lemmas are the well-scopedness at length $1$ of `seq p q` (for closed $p$, $q$), `runUK univ` (for closed `univ`) and `unaryStage`, and the four application equations, among them
--   $$\mathrm{unaryMul}\;D\;u = \mathrm{unary}\,(D \cdot |u|) \quad\text{and}\quad \mathrm{lenBin}\;l = |l| .$$
--
--   **Formalization Note**. These are building blocks of the class verifier (`Halting/Paper/ClassVerifier.lean`, named by the module docstring) and of `cutF` and `lamF` in `Paper/Build.lean`. `runUK` and `unaryStage` are literal programs over `callVar`; the forward run lemmas the module docstring describes are not among this bundle's declarations. The `PolyTimeFun`s are `noncomputable` and carry explicit polynomial time bounds; `expBits_apply`, `addConstU_apply` and `lenBin_apply` are `@[simp]`. The cost of a chain is the sum of the stages' costs plus the sizes of the intermediate values.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Paper/Stages.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Paper/Stages.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
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
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_SizeProgram

/-!
# Stages of the class verifier's programs

The sampler and the decider of the class verifier of the polynomial-time halting reduction
(`Halting/Paper/ClassVerifier.lean`) are chains of stages: polynomial-time functions
(`PolyTimeFun`, run by their `code`), calls of the universal machine on a program and an input
the previous stage produced, and one binary-to-unary conversion of the sampler's dimension.
The universal calls and the conversion are not `PolyTimeFun`s — the first is polynomial in the
simulated program's own time, the second in the number it converts — so the chain is assembled
at the level of programs and `Eval`, with forward run lemmas: each stage is a closed program,
`seq p q` runs `p` then `q` on its output, and the cost of the chain is the sum of the stages'
costs plus the sizes of the intermediate values.

* `runUK univ` on `encode ((c, v), s)` runs `univ` on `(c, v)` and returns `encode (s, r)`,
  keeping the state `s`; `runU univ` returns `r` alone.
* `unaryStage` on `encode (s, n)` returns `encode (s, unary n)` (`toUnaryProg`).
* The polynomial-time pieces: `expBits` (`u ↦ 2 ^ |u|`), `addConstU K` (`u ↦ unary (K + |u|)`),
  `unaryMul D` (`u ↦ unary (D · |u|)`), `lenBin` (the length of a string, in binary).
-/

namespace MIPRE.Cost

open Polynomial

namespace Prog

/-! ## Sequencing, and the universal calls -/

/-- Run `p`, then the closed program `q` on its output. -/
def seq (p q : Prog) : Prog := .let_ p (callVar 0 q)

theorem seq_wellScoped {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (seq p q).WellScoped 1 :=
  ⟨hp, callVar_wellScoped (by decide) hq⟩

/-- Run the universal program on the pair in the input's first component, keeping the second:
`encode ((c, v), s) ↦ encode (s, r)` where `c` on `v` returns `r`. -/
def runUK (univ : Prog) : Prog :=
  .elim 0 .nil (.let_ (callVar 0 univ) (.cons (.var 2) (.var 0)))

theorem runUK_wellScoped {univ : Prog} (hU : univ.WellScoped 1) : (runUK univ).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, ⟨Nat.zero_lt_succ _, hU.mono (by omega) _⟩,
    show (2 : ℕ) < 1 + 2 + 1 by omega, show (0 : ℕ) < 1 + 2 + 1 by omega⟩

/-- Convert the second component from binary to unary: `encode (s, n) ↦ encode (s, unary n)`. -/
def unaryStage : Prog := .elim 0 .nil (.cons (.var 0) (callVar 1 toUnaryProg))

theorem unaryStage_wellScoped : unaryStage.WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, Nat.zero_lt_succ _, show (1 : ℕ) < 1 + 2 by omega,
    toUnaryProg_wellScoped.mono (by omega) _⟩

end Prog

/-! ## Polynomial-time pieces -/

namespace PolyTimeFun

/-- `u ↦ 2 ^ |u|` on unary numerals, by `expBitsProg`. -/
noncomputable def expBits : PolyTimeFun Unary ℕ where
  toFun u := 2 ^ u.length
  code := Prog.expBitsProg
  closed := Prog.expBitsProg_wellScoped
  timeBound := (X + 2) * (C 4 * X + 20)
  computes u := by
    obtain ⟨n, rfl⟩ : ∃ n, u = unary n := ⟨u.length, (unary_length u).symm⟩
    obtain ⟨t, ht, h⟩ := Prog.expBitsProg_runs n
    simp only [length_unary]
    refine ⟨t, ?_, ?_⟩
    · have e : esize (unary n) = 2 * n + 1 := by
        show (encode (unary n) : Data).size = _
        rw [encode_unary, Data.size_ofNat]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_ofNat, e]
      nlinarith
    · show Prog.expBitsProg.Runs (encode (unary n)) _ t
      rw [encode_unary]
      exact h

@[simp] theorem expBits_apply (u : Unary) : expBits u = 2 ^ u.length := rfl

/-- `u ↦ unary (K + |u|)`, by `addConstProg`. -/
noncomputable def addConstU (K : ℕ) : PolyTimeFun Unary Unary where
  toFun u := unary (K + u.length)
  code := Prog.addConstProg K
  closed := Prog.addConstProg_wellScoped K
  timeBound := C ((K + 1) * (4 * K + 15) + 2 * K + 5) + C (K + 2) * X
  computes u := by
    obtain ⟨n, rfl⟩ : ∃ n, u = unary n := ⟨u.length, (unary_length u).symm⟩
    obtain ⟨t, ht, h⟩ := Prog.addConstProg_runs K n
    simp only [length_unary]
    refine ⟨t, ?_, ?_⟩
    · have e : esize (unary n) = 2 * n + 1 := by
        show (encode (unary n) : Data).size = _
        rw [encode_unary, Data.size_ofNat]
      simp only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        e]
      nlinarith
    · show (Prog.addConstProg K).Runs (encode (unary n)) (encode (unary (K + n))) t
      rw [encode_unary, encode_unary]
      exact h

@[simp] theorem addConstU_apply (K : ℕ) (u : Unary) : addConstU K u = unary (K + u.length) :=
  rfl

/-- `u ↦ unary (D · |u|)`: `D` copies of `u`, appended. -/
noncomputable def unaryMul : ℕ → PolyTimeFun Unary Unary
  | 0 => const []
  | D + 1 => append.comp (pair (id Unary) (unaryMul D))

theorem unaryMul_apply (D : ℕ) (u : Unary) : unaryMul D u = unary (D * u.length) := by
  obtain ⟨n, rfl⟩ : ∃ n, u = unary n := ⟨u.length, (unary_length u).symm⟩
  rw [length_unary]
  induction D with
  | zero => simp [unaryMul, unary]
  | succ D ih =>
    show (id Unary (unary n) ++ unaryMul D (unary n)) = _
    rw [ih, id_apply, Nat.succ_mul, Nat.add_comm]
    simp only [unary, List.replicate_add]

/-- The length of a string, in binary. -/
noncomputable def lenBin {α : Type*} [SizedEncoding α] : PolyTimeFun (List α) ℕ :=
  unaryToBin.comp length

@[simp] theorem lenBin_apply {α : Type*} [SizedEncoding α] (l : List α) :
    lenBin l = l.length := by
  show (length l).length = _
  rw [length_apply, length_unary]

end PolyTimeFun

end MIPRE.Cost


