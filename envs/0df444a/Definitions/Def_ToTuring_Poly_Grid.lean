-- Prove2me | Definitions.Def_ToTuring_Poly_Grid
-- name    : ToTuring_Poly_Grid
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T20:02:02.049485+00:00
-- url     : https://prove2.me/theorems/14e039e5-8ba3-4d5b-8823-7c56a374b132
-- title:
--   Grid
-- statement:
--   Definitions and structural lemmas for Grid, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Grid.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_StepMachines_Prog_GridLoop
set_option autoImplicit false
section
section
namespace Groundwork.Prog
open Stepped
def NetFormer.Keeps (F : NetFormer) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ),
    Unary lam → Nonempty (IsPolyT R) → (F lam R).Keeps
section
variable {C : Type} [Enc C] {lam : C → ℕ}
end
end Groundwork.Prog


