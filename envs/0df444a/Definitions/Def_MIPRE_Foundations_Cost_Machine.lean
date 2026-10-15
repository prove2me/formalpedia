-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Machine
-- name    : MIPRE_Foundations_Cost_Machine
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:09:04.597763+00:00
-- url     : https://prove2.me/theorems/4c18dea4-c1a4-4ff6-8c8a-b91da01b521f
-- title:
--   The evaluation machine: a CEK-style small-step machine with exact cost accounting
-- statement:
--   This bundle defines a small-step abstract machine for the ambient language, the common core of the self-interpreter (the universal machine) and of the proof that ambient evaluation is partial recursive.
--
--   `MIPRE.Cost.Machine.Frame` is the type of continuation frames: $\mathtt{cons1}(t, \mathit{env})$ ("the head of a $\mathtt{cons}$ is being evaluated; next evaluate $t$ in $\mathit{env}$"), $\mathtt{cons2}(a)$ ("the head value is $a$; next return $\mathtt{cons}(a, v)$ for the tail value $v$"), $\mathtt{let1}(b, \mathit{env})$ ("the binding of a $\mathtt{let}$ is being evaluated; next evaluate $b$ in $v :: \mathit{env}$") and $\mathtt{loop1}(b, \mathit{env})$ ("the body of a $\mathtt{loop}$ is being evaluated in $\mathit{env}$; next dispatch on its value"). `MIPRE.Cost.Machine.Ctrl` is the control: either $\mathtt{ev}(p)$, a program to evaluate, or $\mathtt{ret}(v)$, a value being returned. `MIPRE.Cost.Machine.Cfg` is a configuration: a control, an environment and a stack (a list) of frames.
--
--   `MIPRE.Cost.Machine.step` is the transition function $\mathrm{Cfg} \to \mathrm{Cfg}$, with one case per evaluation rule: $\mathtt{var}$, $\mathtt{nil}$ and $\mathtt{const}$ return their value at once; $\mathtt{cons}$, $\mathtt{let}$ and $\mathtt{loop}$ push a frame and evaluate their first subterm; $\mathtt{elim}$ inspects the variable and continues with the selected branch (binding the two components in the $\mathtt{cons}$ case); returning into a frame proceeds as the frame prescribes, and returning into a $\mathtt{loop1}$ frame dispatches on the value exactly as the big-step rules do: stop on $\mathtt{nil}$ or $\mathtt{cons}(\mathtt{nil}, r)$, and otherwise continue with the new state in place of the head of the environment. Final configurations, a returned value with an empty stack, are fixed points of $\mathrm{step}$.
--
--   `MIPRE.Cost.Machine.stepCost` charges, at each step, the cost of the corresponding evaluation rule: the size of the value plus one for $\mathtt{var}$, the size of the literal for $\mathtt{const}$, one unit for $\mathtt{nil}$, $\mathtt{cons}$, $\mathtt{elim}$ and $\mathtt{let}$, nothing when a $\mathtt{loop}$ is entered, one unit when a loop body's value is dispatched (a return into a $\mathtt{loop1}$ frame), and nothing on other returns. `MIPRE.Cost.Machine.costSum` $c\ N$ is the cost accumulated over the first $N$ steps from $c$, and `MIPRE.Cost.Machine.Steps` $c\ N\ c'\ t$ says that $N$ steps lead from $c$ to $c'$ with accumulated cost $t$:
--   $$\mathrm{step}^{N}(c) = c' \quad\text{and}\quad \mathrm{costSum}(c, N) = t .$$
--   `MIPRE.Cost.Machine.IsFinal` $c$ says that $c$ is final: $c = \langle \mathtt{ret}(r), e, [\,] \rangle$ for some value $r$ and environment $e$.
--
--   No lemma is proved inside this bundle; the two directions of the correspondence with the big-step semantics — a derivation of cost $t$ yields a machine run of the same accumulated cost reaching a final configuration (`eval_steps`), and a machine run reaching a final configuration yields a derivation (`eval_of_steps`) — are uploaded separately.
--
--   **Formalization Note**. The machine is deterministic and total (`step` is a function, with final configurations as its fixed points), and the cost of each evaluation rule is charged at one designated step, so that the accumulated cost of a run is *exactly* the cost of the derivation it simulates. This exactness is what lets the clocked universal machine decrement a cost budget by the cost of each step and decide "halts within cost $k$" precisely, rather than up to a polynomial. The step function is written so that it can be transported to data and implemented by a fixed program, in the `MachineData` and `Interpreter` bundles.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Machine.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Machine.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime

/-!
# The evaluation machine

A small-step abstract machine (CEK style) for the ambient language: a configuration is a
control (a program to evaluate, or a value being returned), an environment and a stack of
continuation frames. It is the common core of the two "universal" artifacts of the
project:

* Mathlib-computability of ambient evaluation (`Cost/Partrec.lean`): the step function,
  transported to `Data`, is primitive recursive and evaluation is its `PFun.fix`;
* the self-interpreter of the ambient model in the ambient model (route β of the
  universal-machine gate): a program implementing the step function inside a `loop`.

The machine charges the cost of each `Eval` rule at a designated step (`stepCost`), so
that the accumulated cost of a run is exactly the cost of the `Eval` derivation. The two
directions of the correspondence are `eval_steps` (a derivation yields a run of the
machine) and `eval_of_steps` (a halting run of the machine yields a derivation).
-/

namespace MIPRE.Cost

namespace Machine

/-- Continuation frames. -/
inductive Frame
  /-- Evaluating the head of `cons h t`; next evaluate `t` in `env`. -/
  | cons1 (t : Prog) (env : Env)
  /-- The head value `a` of a `cons`; next return `cons a v`. -/
  | cons2 (a : Data)
  /-- Evaluating the binding of `let_ e b`; next evaluate `b` in `v :: env`. -/
  | let1 (b : Prog) (env : Env)
  /-- Evaluating the body of `loop b` in `env`; next dispatch on the value. -/
  | loop1 (b : Prog) (env : Env)
  deriving DecidableEq

/-- The control: a program to evaluate, or a value being returned. -/
inductive Ctrl
  | ev (p : Prog)
  | ret (v : Data)
  deriving DecidableEq

/-- Configurations. -/
structure Cfg where
  ctrl : Ctrl
  env : Env
  kont : List Frame
  deriving DecidableEq

/-- One step of the machine. Final configurations (a value with an empty stack) are fixed. -/
def step : Cfg → Cfg
  | ⟨.ev (.var i), env, k⟩ => ⟨.ret (env.get i), env, k⟩
  | ⟨.ev .nil, env, k⟩ => ⟨.ret .nil, env, k⟩
  | ⟨.ev (.const d), env, k⟩ => ⟨.ret d, env, k⟩
  | ⟨.ev (.cons h t), env, k⟩ => ⟨.ev h, env, .cons1 t env :: k⟩
  | ⟨.ev (.elim i n c), env, k⟩ =>
    match env.get i with
    | .nil => ⟨.ev n, env, k⟩
    | .cons a b => ⟨.ev c, a :: b :: env, k⟩
  | ⟨.ev (.let_ e b), env, k⟩ => ⟨.ev e, env, .let1 b env :: k⟩
  | ⟨.ev (.loop b), env, k⟩ => ⟨.ev b, env, .loop1 b env :: k⟩
  | ⟨.ret v, env, []⟩ => ⟨.ret v, env, []⟩
  | ⟨.ret v, _, .cons1 t env :: k⟩ => ⟨.ev t, env, .cons2 v :: k⟩
  | ⟨.ret v, env, .cons2 a :: k⟩ => ⟨.ret (.cons a v), env, k⟩
  | ⟨.ret v, _, .let1 b env :: k⟩ => ⟨.ev b, v :: env, k⟩
  | ⟨.ret v, _, .loop1 b env :: k⟩ =>
    match v with
    | .nil => ⟨.ret .nil, env, k⟩
    | .cons .nil r => ⟨.ret r, env, k⟩
    | .cons (.cons _ _) v' => ⟨.ev b, v' :: env.tail, .loop1 b (v' :: env.tail) :: k⟩

/-- The `Eval` cost charged at a step: the rule's own unit (plus the size of the value
read, for `var` and `const`); `loop` rules are charged when the body's value is
dispatched. -/
def stepCost : Cfg → ℕ
  | ⟨.ev (.var i), env, _⟩ => (env.get i).size + 1
  | ⟨.ev .nil, _, _⟩ => 1
  | ⟨.ev (.const d), _, _⟩ => d.size
  | ⟨.ev (.cons _ _), _, _⟩ => 1
  | ⟨.ev (.elim _ _ _), _, _⟩ => 1
  | ⟨.ev (.let_ _ _), _, _⟩ => 1
  | ⟨.ev (.loop _), _, _⟩ => 0
  | ⟨.ret _, _, .loop1 _ _ :: _⟩ => 1
  | ⟨.ret _, _, _⟩ => 0

/-- The cost accumulated over `n` steps. -/
def costSum (c : Cfg) : ℕ → ℕ
  | 0 => 0
  | n + 1 => stepCost c + costSum (step c) n

/-- `Steps c N c' t`: `N` steps lead from `c` to `c'`, accumulating cost `t`. -/
def Steps (c : Cfg) (N : ℕ) (c' : Cfg) (t : ℕ) : Prop :=
  step^[N] c = c' ∧ costSum c N = t

namespace Steps

end Steps

/-! ## Forward: derivations give machine runs -/

/-! ## Backward: halting runs give derivations -/

/-- A final configuration: a value with an empty stack. -/
def IsFinal (c : Cfg) : Prop := ∃ r e, c = ⟨.ret r, e, []⟩

end Machine

end MIPRE.Cost


