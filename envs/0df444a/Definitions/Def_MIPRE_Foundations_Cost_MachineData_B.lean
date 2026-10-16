-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
-- name    : MIPRE_Foundations_Cost_MachineData_B
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:21:43.795038+00:00
-- url     : https://prove2.me/theorems/5496e895-933d-4923-94e0-8d2d38157133
-- title:
--   Initial and final configurations of the evaluation machine, as data (machine-data addendum)
-- statement:
--   This bundle adds three theorems, and no new definitions, to the already published bundle `MIPRE_Foundations_Cost_MachineData`, which encodes the configurations of the evaluation machine as `Data` (`Cfg.toData`: a configuration is $\mathrm{cons}\,\mathit{ctrl}\,(\mathrm{cons}\,\mathit{env}\,\mathit{kont})$, with the control $\mathrm{cons}\,\mathrm{nil}\,(\mathrm{toData}\,p)$ for "evaluate $p$" and $\mathrm{cons}\,(\mathrm{cons}\,\mathrm{nil}\,\mathrm{nil})\,v$ for "return $v$") and transports the step function to data. The added lemmas relate three data-level operations to the machine: `initData p x`, the initial configuration of a program given as data on the input $x$, satisfies $\mathrm{initData}\,(\mathrm{toData}\,p)\,x = \mathrm{toData}\,\langle \mathrm{ev}\,p, [x], [\,]\rangle$ for every program $p$; the finality test `IsFinalD` (first component of the control not `nil`, empty stack) characterizes the encoded final configurations,
--
--   $$\mathrm{IsFinalD}\,(\mathrm{toData}\,c) \;\longleftrightarrow\; \exists\, r\ e,\ c = \langle \mathrm{ret}\,r,\ e,\ [\,]\rangle;$$
--
--   and the result extraction satisfies $\mathrm{resultD}\,(\mathrm{toData}\,\langle \mathrm{ret}\,r, e, [\,]\rangle) = r$. These are the equations under which the data-level evaluation loop of `Cost/Partrec.lean` and the interpreter programs of `Cost/Universal.lean` recognize the start and the end of a simulated run.
--
--   **Formalization Note** `IsFinalD d` unfolds to `d.left.left ≠ .nil ∧ d.right.right = .nil`, `resultD d` to `d.left.right`, and `initData p x` to `.cons (evD p) (.cons (.cons x .nil) .nil)`; the characterization is stated for every `c : Cfg` with an existential over the returned value `r : Data` and the environment `e : Env`. The theorems are `initData_eq`, `isFinalD_toData` and `resultD_toData`.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineData.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineData.lean (delta bundle: declarations the new statements need that the published bundle Def_MIPRE_Foundations_Cost_MachineData does not carry);
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

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

theorem initData_eq (p : Prog) (x : Data) : initData p.toData x = Cfg.toData ⟨.ev p, [x], []⟩ :=
  rfl

theorem isFinalD_toData (c : Cfg) : IsFinalD c.toData ↔ ∃ r e, c = ⟨.ret r, e, []⟩ := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    simp [IsFinalD, Cfg.toData, Ctrl.toData, evD]
  | ret v =>
    cases kont with
    | nil => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]
    | cons f k => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]

theorem resultD_toData (r : Data) (e : Env) : resultD (Cfg.toData ⟨.ret r, e, []⟩) = r := rfl

/-! ## The step function on data -/

end Machine

end MIPRE.Cost


