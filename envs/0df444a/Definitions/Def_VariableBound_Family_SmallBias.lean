-- Prove2me | Definitions.Def_VariableBound_Family_SmallBias
-- name    : VariableBound_Family_SmallBias
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:17:41.075212+00:00
-- url     : https://prove2.me/theorems/a6bac556-9a84-4971-8987-6b07cda994cc
-- title:
--   Small Bias
-- statement:
--   Definitions and structural lemmas for Small Bias, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/variables/VariableBound/Family/SmallBias.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppVariablesStatement
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
section
section
@[expose] section
namespace VariableBound.SmallBias
open Finset AppVariables
section Strings
variable {s : ℕ}
end Strings
section Sum
variable {F : Type} [Field F] [Algebra (ZMod 2) F] {m s : ℕ}
end Sum
section Poly
variable {F : Type} [Field F] {m : ℕ}
@[expose] noncomputable def poly (F : Type) [Field F] {m : ℕ} (V' : Finset (Fin m)) : Polynomial F := ∑ E ∈ V', Polynomial.X ^ E.val
end Poly
section Half
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {s : ℕ}
end Half
section Counts
variable {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F] {m s : ℕ}
end Counts
end VariableBound.SmallBias


