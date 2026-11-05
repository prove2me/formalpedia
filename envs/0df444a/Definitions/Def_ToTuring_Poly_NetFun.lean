-- Prove2me | Definitions.Def_ToTuring_Poly_NetFun
-- name    : ToTuring_Poly_NetFun
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:46:53.155872+00:00
-- url     : https://prove2.me/theorems/99c73132-0a90-4388-9960-d8f213900000
-- title:
--   Net Fun
-- statement:
--   Definitions and structural lemmas for Net Fun, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
set_option autoImplicit false
section
section
namespace Groundwork.Prog.NetE
variable {α β : Type} [Enc α] [Enc β]
variable (K g : ℕ)
variable {C : Type} [Enc C] {Np : PNet C}
section
variable (h : Np.Keeps)
include h
end
def capWord (g : ℕ) (Np : PNet C) (u : ((X0 C × ℕ) × ℕ) × ℕ) : List Bool :=
  toWord (Np.cap u.1.1.1.1.1 (u.1.2 / g) (u.1.2 % g)) u.2
section
variable (h : Np.Keeps)
include h
end
end Groundwork.Prog.NetE


