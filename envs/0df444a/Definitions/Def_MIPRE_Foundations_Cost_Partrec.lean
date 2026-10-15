-- Prove2me | Definitions.Def_MIPRE_Foundations_Cost_Partrec
-- name    : MIPRE_Foundations_Cost_Partrec
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-12T16:24:23.742739+00:00
-- url     : https://prove2.me/theorems/e9c98a6d-4272-4274-ac6d-fd7f7eeeb1b6
-- title:
--   Ambient evaluation as a partial recursive function on data
-- statement:
--   This bundle defines evaluation in the ambient model as a partial function in Mathlib's sense, the bridge from the cost model to Mathlib's computability theory.
--
--   `MIPRE.Cost.Machine.evalStep` $d$ is one iteration of the evaluation loop on an encoded configuration $d$, with values in the sum type $\mathrm{Data} \oplus \mathrm{Data}$: if $d$ is final (`IsFinalD`) it returns $\mathrm{inl}(\mathrm{resultD}\ d)$, the result of the computation; otherwise it returns $\mathrm{inr}(\mathrm{stepData}\ d)$, the next configuration.
--
--   `MIPRE.Cost.Machine.evalData` $p\ x$, for a program $p$ (as data) and an input $x$, is the partial value (`Part Data`) obtained as the fixed point, in the sense of Mathlib's `PFun.fix`, of the evaluation loop started from the initial configuration:
--   $$\mathrm{evalData}(p, x) = \mathrm{PFun.fix}\ \bigl(d \mapsto \mathrm{evalStep}\ d\bigr)\ (\mathrm{initData}\ p\ x),$$
--   that is, the result of iterating `stepData` from $\mathrm{initData}\ p\ x$ until a final configuration is reached, defined exactly when one is.
--
--   No lemma is proved inside this bundle.
--
--   **Formalization Note**. The step on data is primitive recursive (`primrec_stepData`: it is built from the primitive recursive operations `left`, `right`, `cons`, `unaryToNat` and `getList` on the `Primcodable` type `Data`), so `evalData` is partial recursive (`partrec_evalData`) and agrees with the big-step semantics: $r \in \mathrm{evalData}(\mathrm{toData}\ p, x)$ if and only if $\mathrm{Eval}([x], p, r, t)$ for some cost $t$ (`mem_evalData_iff`). Consequently a polynomial-time function of the ambient model is Mathlib-`Computable` as soon as its input is produced by a computable encoding (`PolyTimeFun.computable_comp`); this is how the halting-problem form of the compression lemma is transported to Mathlib's `Nat.Partrec.Code`. The other bridge, from `Nat.Partrec.Code` into the model, is the `FromPartrec` bundle. No time bounds are involved here: only computability is transferred.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/Partrec.lean

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Partrec.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
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
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-!
# Ambient evaluation is partial recursive

The step of the evaluation machine on data is primitive recursive (`primrec_stepData`),
so evaluation — its `PFun.fix` from the initial configuration — is partial recursive
(`partrec_evalData`), and agrees with `Eval` (`mem_evalData_iff`). Consequently a
polynomial-time function of the ambient model is Mathlib-computable, as soon as its input
is produced by a computable encoding (`PolyTimeFun.computable_comp`). This is the bridge
from the ambient model to Mathlib's computability used by the halting-problem form of the
compression lemma; the other bridge (from `Nat.Partrec.Code` into the model) is
`Cost/FromPartrec.lean`.
-/

namespace MIPRE.Cost

namespace Machine

open Primrec

/-! ## The step is primitive recursive -/

/-! ## Evaluation as a fixed point -/

/-- One iteration of the evaluation loop: stop with the value on a final configuration,
otherwise step. -/
def evalStep (d : Data) : Data ⊕ Data :=
  if IsFinalD d then Sum.inl (resultD d) else Sum.inr (stepData d)

/-- Evaluation of the program `p` (as data) on `x`, as a partial function: the fixed
point of the evaluation loop from the initial configuration. -/
def evalData (p x : Data) : Part Data :=
  PFun.fix (fun d => Part.some (evalStep d)) (initData p x)

end Machine

/-! ## Polynomial-time functions are computable -/

end MIPRE.Cost


