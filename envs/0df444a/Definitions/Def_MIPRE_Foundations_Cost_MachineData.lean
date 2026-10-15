-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_MachineData
-- name    : MIPRE_Foundations_Cost_MachineData
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:11:20.718288+00:00
-- url     : https://prove2.me/theorems/92629817-fd4d-4f33-9d05-0b5ae36fe9b9
-- title:
--   The evaluation machine on data: encoded configurations and the first-order step function
-- statement:
--   This bundle transports the evaluation machine to the data type of the ambient model, so that configurations are trees and the step function is a first-order operation on trees.
--
--   **Encoding.** `MIPRE.Cost.Machine.evD` $p = \mathtt{cons}(\mathtt{nil}, p)$ is the control "evaluate the program $p$" (given as data), and `MIPRE.Cost.Machine.retD` $v = \mathtt{cons}(\mathtt{cons}(\mathtt{nil}, \mathtt{nil}), v)$ the control "return the value $v$"; `MIPRE.Cost.Machine.Ctrl.toData` encodes a control accordingly, programs being serialized by `Prog.toData`. `MIPRE.Cost.Machine.Frame.toData` encodes a frame as $\mathtt{cons}(\mathrm{ofNat}\ \mathit{tag}, \mathit{payload})$ with unary tags $0$ to $3$ for $\mathtt{cons1}(t, \mathit{env})$ (payload $\mathtt{cons}(t, \mathit{env})$), $\mathtt{cons2}(a)$ (payload $a$), $\mathtt{let1}(b, \mathit{env})$ and $\mathtt{loop1}(b, \mathit{env})$, environments being encoded as $\mathtt{cons}$-chains. `MIPRE.Cost.Machine.Cfg.toData` encodes a configuration as
--   $$\mathtt{cons}(\mathit{ctrl}, \mathtt{cons}(\mathit{env}, \mathit{kont}))$$
--   with the environment and the stack as $\mathtt{cons}$-chains. `MIPRE.Cost.Machine.initData` $p\ x = \mathtt{cons}(\mathrm{evD}\ p, \mathtt{cons}(\mathtt{cons}(x, \mathtt{nil}), \mathtt{nil}))$ is the initial configuration for the program $p$ on the input $x$: evaluate $p$ in the one-entry environment $[x]$ with an empty stack. `MIPRE.Cost.Machine.IsFinalD` $d$ says that the encoded configuration $d$ is final (its control is a return and its stack is empty); it is a decidable predicate (`MIPRE.Cost.Machine.instDecidablePredDataIsFinalD`), and `MIPRE.Cost.Machine.resultD` $d$ is the returned value of a final configuration.
--
--   **The step.** `MIPRE.Cost.Machine.stepEv` $p\ \mathit{env}\ \mathit{kont}$ is the step on an "evaluate $p$" control, dispatching on the unary tag of $p$ ($0$ to $6$ for $\mathtt{var}$, $\mathtt{nil}$, $\mathtt{cons}$, $\mathtt{elim}$, $\mathtt{let}$, $\mathtt{loop}$, $\mathtt{const}$) exactly as `Machine.step` does, with the variable looked up by `getList` at the index read by `unaryToNat`; `MIPRE.Cost.Machine.stepRet` $v\ \mathit{env}\ \mathit{kont}$ is the step on a "return $v$" control, dispatching on the tag of the top frame (and fixing the configuration when the stack is empty); and `MIPRE.Cost.Machine.stepData` $d$ combines them according to the control of $d$. The defining property, proved separately, is
--   $$\mathrm{stepData}(\mathrm{toData}\ c) = \mathrm{toData}(\mathrm{step}\ c)$$
--   for every configuration $c$.
--
--   No lemma is proved inside this bundle.
--
--   **Formalization Note**. The step on data is defined using only the first-order operations `left`, `right`, `cons`, `unaryToNat` and `getList`, together with equality tests against `nil`, and no recursion on the structure of the configuration: this is what makes it primitive recursive, for Mathlib's computability interface, and implementable by a fixed program of the ambient model, for the self-interpreter. Both artifacts are built on the one function `stepData`, so a single correspondence lemma with `Machine.step` serves both. On malformed data (which never arises from an encoded configuration) the step is some arbitrary tree; the correctness statements are only about encodings.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineData.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineData.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable

/-!
# The evaluation machine on data

Configurations of the evaluation machine (`Cost/Machine.lean`) encoded as `Data`
(`Machine.Cfg.toData`), and the step function transported to `Data` (`Machine.stepData`),
defined by the first-order operations `left`, `right`, `cons`, `unaryToNat`, `getList`
only — so that it is primitive recursive (`Cost/Partrec.lean`) and implementable by a
program of the ambient model (the self-interpreter). The correspondence is
`stepData_toData : stepData c.toData = (step c).toData`.

Encoding: a control is `cons nil (toData p)` ("evaluate `p`") or `cons (cons nil nil) v`
("return `v`"); a configuration is `cons ctrl (cons env kont)` with the environment and the
stack as `cons`-chains; a frame is `cons (ofNat tag) payload` with tags `0`–`3` for
`cons1 t env` (payload `cons t env`), `cons2 a` (payload `a`), `let1 b env`, `loop1 b env`.
-/

namespace MIPRE.Cost

namespace Machine

/-! ## Encoding -/

/-- The control "evaluate the program `p`" (as data). -/
def evD (p : Data) : Data := .cons .nil p

/-- The control "return the value `v`". -/
def retD (v : Data) : Data := .cons (.cons .nil .nil) v

/-- Controls as data. -/
def Ctrl.toData : Ctrl → Data
  | .ev p => evD p.toData
  | .ret v => retD v

/-- Frames as data. -/
def Frame.toData : Frame → Data
  | .cons1 t env => .cons (.ofNat 0) (.cons t.toData (.list env))
  | .cons2 a => .cons (.ofNat 1) a
  | .let1 b env => .cons (.ofNat 2) (.cons b.toData (.list env))
  | .loop1 b env => .cons (.ofNat 3) (.cons b.toData (.list env))

/-- Configurations as data. -/
def Cfg.toData (c : Cfg) : Data :=
  .cons c.ctrl.toData (.cons (.list c.env) (.list (c.kont.map Frame.toData)))

/-- The initial configuration for the program `p` (as data) on the input `x`. -/
def initData (p x : Data) : Data := .cons (evD p) (.cons (.cons x .nil) .nil)

/-- Final configurations, as data: a returned value with an empty stack. -/
def IsFinalD (d : Data) : Prop := d.left.left ≠ .nil ∧ d.right.right = .nil

instance : DecidablePred IsFinalD := fun d => by unfold IsFinalD; infer_instance

/-- The value of a final configuration. -/
def resultD (d : Data) : Data := d.left.right

/-! ## The step function on data -/

/-- The step on "evaluate `p`" with environment `env` and stack `kont`. -/
def stepEv (p env kont : Data) : Data :=
  if Data.unaryToNat p.left = 0 then
    .cons (retD (Data.getList env (Data.unaryToNat p.right))) (.cons env kont)
  else if Data.unaryToNat p.left = 1 then .cons (retD .nil) (.cons env kont)
  else if Data.unaryToNat p.left = 2 then
    .cons (evD p.right.left) (.cons env (.cons (.cons (.ofNat 0) (.cons p.right.right env)) kont))
  else if Data.unaryToNat p.left = 3 then
    if Data.getList env (Data.unaryToNat p.right.left) = .nil then
      .cons (evD p.right.right.left) (.cons env kont)
    else
      .cons (evD p.right.right.right)
        (.cons (.cons (Data.getList env (Data.unaryToNat p.right.left)).left
          (.cons (Data.getList env (Data.unaryToNat p.right.left)).right env)) kont)
  else if Data.unaryToNat p.left = 4 then
    .cons (evD p.right.left) (.cons env (.cons (.cons (.ofNat 2) (.cons p.right.right env)) kont))
  else if Data.unaryToNat p.left = 5 then
    .cons (evD p.right) (.cons env (.cons (.cons (.ofNat 3) (.cons p.right env)) kont))
  else .cons (retD p.right) (.cons env kont)

/-- The step on "return `v`" with environment `env` and stack `kont`. -/
def stepRet (v env kont : Data) : Data :=
  if kont = .nil then .cons (retD v) (.cons env kont)
  else if Data.unaryToNat kont.left.left = 0 then
    .cons (evD kont.left.right.left)
      (.cons kont.left.right.right (.cons (.cons (.ofNat 1) v) kont.right))
  else if Data.unaryToNat kont.left.left = 1 then
    .cons (retD (.cons kont.left.right v)) (.cons env kont.right)
  else if Data.unaryToNat kont.left.left = 2 then
    .cons (evD kont.left.right.left) (.cons (.cons v kont.left.right.right) kont.right)
  else if v = .nil then .cons (retD .nil) (.cons kont.left.right.right kont.right)
  else if v.left = .nil then .cons (retD v.right) (.cons kont.left.right.right kont.right)
  else
    .cons (evD kont.left.right.left)
      (.cons (.cons v.right kont.left.right.right.right)
        (.cons (.cons (.ofNat 3)
          (.cons kont.left.right.left (.cons v.right kont.left.right.right.right)))
          kont.right))

/-- The step function on data. -/
def stepData (d : Data) : Data :=
  if d.left.left = .nil then stepEv d.left.right d.right.left d.right.right
  else stepRet d.left.right d.right.left d.right.right

end Machine

end MIPRE.Cost


