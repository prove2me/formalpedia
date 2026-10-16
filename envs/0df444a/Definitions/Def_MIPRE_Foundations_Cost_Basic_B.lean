-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Basic_B
-- name    : MIPRE_Foundations_Cost_Basic_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:04:25.831303+00:00
-- url     : https://prove2.me/theorems/305e105c-8511-4ee0-9162-d00332d84cc7
-- title:
--   Halting within a cost bound in the ambient cost model (addition to the published cost-model bundle)
-- statement:
--   This bundle adds one declaration to the already published bundle `MIPRE_Foundations_Cost_Basic`, the ambient cost model of the formalization: programs `Prog` of a small first-order language on binary-tree data `Data`, the timed big-step semantics `Eval env p r t` ("in the environment $\mathit{env}$, the program $p$ halts with the result $r$ at cost $t$"), and `Halts p x`, which says that $p$ run on the input $x$ (the environment $[x]$) halts at some cost.
--
--   **Bounded halting.** `MIPRE.Cost.HaltsWithin p x t`, for a program $p$, an input $x$ and a budget $t \in \mathbb{N}$, says that $p$ halts on $x$ within cost $t$:
--   $$\mathrm{HaltsWithin}(p, x, t) \iff \exists\, r\ \exists\, t' \le t,\ \ \mathrm{Eval}([x],\, p,\, r,\, t').$$
--   This is the primitive in which the time bounds of the project are spelled out: the total time bound `TimeBound` of the same module (a bound as a function of the input size) and the sampler bound `Sampler.TimeBoundAt` of the bundle `MIPRE_Foundations_CL_Sampler` are both of the form "for every input in a class, `HaltsWithin` with a stated budget".
--
--   There are no embedded lemmas in this addition.
--
--   **Formalization Note**. The declaration is `MIPRE.Cost.HaltsWithin : Prog → Data → ℕ → Prop` of `MIPRE/Foundations/Cost/Basic.lean`; it was not among the declarations kept in the published cost-model bundle and is added here because the sampler bundle of this upload uses it. The cost $t'$ is the one charged by `Eval` (one unit per rule, except that reading a variable or a literal costs the size of the value); the budget $t$ is an upper bound, not an exact cost.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Basic.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Basic.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_Basic does not carry);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Notation
import Definitions.Def_MIPRE_Foundations_Cost_Basic

/-!
# The ambient cost model

This file fixes the cost model in which **every** polynomial-time statement of the
project is made: the transformations of the compression pipeline (introspection,
oracularization, answer reduction, parallel repetition), the `Compress` map, the
efficient computability toolkit (universal machine, s-m-n, Kleene fixed point;
blueprint Section `sec:rr-computability`), and the recursive compression lemma
(blueprint `lem:recursive-compression`, [MNY] Lemma 5.1).

## The model

Data are binary trees (`Data`: `nil` and `cons`), the S-expressions in which bit
strings, numbers, pairs and programs are all encoded (`Cost.Encoding`). `Data.size`
counts nodes; it is the bit-length of the preorder serialization `Data.toBits`, so
sizes are additive under pairing (R4 below).

Programs (`Prog`) form a minimal first-order language with de Bruijn variables over an
environment of `Data` values: `var i` reads a variable, `nil`, `const d` and `cons h t`
build values, `elim i n c` inspects the `i`-th variable (binding the two components of
a `cons`), `let_ e b` binds, and `loop b` iterates `b` on the state held in variable `0`
until it signals stop. The timed big-step semantics `Eval env p r t` charges one unit
per rule, except that reading a variable or a literal costs the size of the value:
**values are copied when read and inspected in place by `elim`**. Consequently a run
of cost `t` produces a result of size at most `t` (`Eval.size_le`), so every value
occurring in a computation is polynomially bounded by the running time — which is what
makes the unit costs honest under a pointer-machine, and then Turing-machine, simulation
with polynomial overhead (meta-remark below).

## Why this model (decision record)

The choice is driven by the requirements extracted from the JNVWY pipeline:

* **R1 (programmability)**: deciders perform real algorithms (linear algebra over
  `𝔽₂`/`𝔽_{2^k}`, low-degree evaluations, simulations); their polynomial time bounds
  must be provable via a compositional closure library.
* **R2 (self-reference)**: efficient universal machine, s-m-n, and Kleene fixed
  point, with explicit polynomial overheads (the recursion in [MNY, Lemma 5.1] and
  the λ-boundedness bookkeeping of [JNVWY, §12] need them).
* **R3 (arithmetizable tableaux)**: answer reduction needs bounded computations of
  *this* model to have succinct, formula-uniform 3SAT tableaux (blueprint
  `thm:succinct-sat`). This is discharged through a single gateway theorem whose
  proof compiles the model to the machine model of `MIPRE/TM` (planned Milestone H1
  of `planning/tm-infrastructure.md`). The low-level machine appears in no statement
  outside that proof.
* **R4 (binary-length sizes)**: indices `n` enter in binary; "succinct" means
  `poly(log)` of the described object.

Three natural alternatives fail:

* `Nat.Partrec.Code` (with any cost semantics) is **not** a viable carrier of
  polynomial time: its primitives reach large values only through `succ`-chains,
  value-indexed `prec` recursion, or `rfind` search, so even `n ↦ 2n` on binary
  representations has no `polylog(n)`-cost program — the induced "P" would not
  contain binary addition. Its numeric pairing (`Nat.pair`, quadratic) also
  distorts lengths exponentially under nesting. It remains the model of the *final*
  computability statements (`MIPRE.HaltingGameValue`), reached via a one-time
  compilation (`Foundations/Compression.lean`).
* Mathlib's `Turing.ToPartrec.Code`, the model used until 2026-09-08, cannot rebuild
  lists in polynomial time. Its primitives act only on the front of a single `List ℕ`
  value (prepend, drop or replace the first cell), and the value is passed by value; so
  every output has the form `p ++ v.drop k`, and the input suffix can only be discarded
  by first dropping everything built in front of it, which retains a program-size-bounded
  number of cells of polynomially bounded value — `O(log t)` bits of information. Hence
  `List.reverse`, `x ↦ x ++ [b]`, binary addition and the runtime s-m-n map are not
  polynomial-time computable there: it is a one-stack machine with a read-only input,
  adequate for Mathlib's numeric use (`Code.exists_code` returns singletons `[n]`) but
  not for string processing. (Trailing `0` cells are moreover invisible to every program.)
* Turing machines (`Turing.TM2`, `Turing.FinTM2`, the project's own `Turing.Code i`)
  satisfy R3 natively but fail R1/R2 in practice: Mathlib has no universal machine, no
  composition, and no way to program nontrivial algorithms; machine-level combinator
  libraries (CSLib's, under construction) cost hundreds of lines per combinator.

`Prog` sits in the sweet spot: `cons` builds and `elim` destructs anywhere in a value, so
string algorithms and recursion on notation are direct (R1); programs are trees, hence
data with additive sizes (`Prog.toData` in `Cost.Encoding`), and hardcoding an argument is
`let_ (cons (const d) (var 0))` at linear cost (R2, R4); and the language is small enough
for its metatheory and for a self-interpreter — the universal machine of `Cost.Toolkit` —
to be manageable, and to be compiled to the machine model for R3. The design follows the
"rose tree machine" idea of C. Reitwiessner (CSLib issue #611) with binary trees in place of
rose trees and a time-only semantics.

**Meta-remark (not formalized).** A pointer machine represents values as DAGs of `cons`
cells: `cons`, `elim` and `let_` are constant-time, `var i` and `const d` copy a value in
time proportional to its size (exactly the charged cost), so a run of cost `t` takes `O(t)`
pointer-machine time on `O(t + input)` cells, and Turing-machine time polynomial in that.
This justifies reading `PolyTimeFun` as honest "polynomial time"; nothing in the project
depends on it formally, since the final theorem only claims `Computable`.

## Main definitions

* `MIPRE.Cost.Data`, `Data.size`, `Data.toBits`, `Data.ofNat` (unary numerals).
* `MIPRE.Cost.Prog`, `Prog.WellScoped`.
* `MIPRE.Cost.Env`, `Env.get`.
* `MIPRE.Cost.Eval`: the timed big-step semantics; `Eval.deterministic`, `Eval.pos`,
  `Eval.size_le`, and the scoping lemmas `Eval.append_of_wellScoped` /
  `Eval.of_append_of_wellScoped` (extra environment entries are inert for well-scoped
  programs).
* `MIPRE.Cost.evalFuel`: an executable evaluator with fuel, sound for `Eval`.
* `MIPRE.Cost.Halts`, `HaltsWithin`, `TimeBound`.

Blueprint: this file is part of `sec:rr-computability` (efficient computability
toolkit), infrastructure level.
-/

namespace MIPRE.Cost

namespace Data

end Data

namespace Prog

end Prog

namespace Eval

end Eval

/-- `p` halts on `x` within cost `t`. -/
def HaltsWithin (p : Prog) (x : Data) (t : ℕ) : Prop := ∃ r t', t' ≤ t ∧ Eval [x] p r t'

end MIPRE.Cost


