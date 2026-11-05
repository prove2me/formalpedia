-- Prove2me | Definitions.Def_ToTuring_Poly_Spec
-- name    : ToTuring_Poly_Spec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T19:28:26.487701+00:00
-- url     : https://prove2.me/theorems/86b4726b-7610-4577-99b3-a9ba7b6fb553
-- title:
--   Spec
-- statement:
--   Definitions and structural lemmas for Spec, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Spec.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_StepMachines_Prog_Spec
set_option autoImplicit false
section
section
namespace Groundwork.Prog
def Evaluator.Keeps (E : Evaluator) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (lam : C → ℕ) (R : Stepped (C × IQ) ℤ),
    Unary lam → Nonempty (IsPolyT R) → Nonempty (IsPolyT (E.app lam R))
structure PNet.Keeps {C : Type} [Enc C] (Np : PNet C) : Prop where
  n : Unary fun p : C × ℕ => Np.n p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => Np.cap p.1 p.2.1 p.2.2
  W : Nonempty (IsPolyT Np.W)
  f : Nonempty (IsPolyT Np.f)
def NetEvaluator.Keeps (NE : NetEvaluator) : Prop :=
  ∀ (C : Type) [HasSize C] [Enc C] [Carried C] (Np : PNet C), Np.Keeps → Nonempty (IsPolyT (NE.app Np))
end Groundwork.Prog


