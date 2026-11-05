-- Prove2me | Definitions.Def_StepMachineStatements
-- name    : StepMachineStatements
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T15:18:08.922246+00:00
-- url     : https://prove2.me/theorems/c05c511a-7983-4667-b44f-404ad9742c08
-- title:
--   Step Machine Statements
-- statement:
--   Definitions and structural lemmas for Step Machine Statements, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/statements/StepMachineStatements.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
set_option autoImplicit false
section
section
namespace Groundwork
class HasSize (α : Type) where
  size : α → ℕ
export HasSize (size)
section sizes
variable {α β : Type}
instance : HasSize ℕ := ⟨fun n => n.size + 1⟩
instance : HasSize ℤ := ⟨fun z => z.natAbs.size + 1⟩
instance : HasSize Bool := ⟨fun _ => 1⟩
instance : HasSize Unit := ⟨fun _ => 1⟩
instance [HasSize α] [HasSize β] : HasSize (α × β) := ⟨fun p => size p.1 + size p.2⟩
instance [HasSize α] [HasSize β] : HasSize (α ⊕ β) :=
  ⟨fun x => match x with | .inl a => size a + 1 | .inr b => size b + 1⟩
instance [HasSize α] : HasSize (Option α) :=
  ⟨fun x => match x with | none => 1 | some a => size a + 1⟩
instance [HasSize α] : HasSize (List α) := ⟨fun l => (l.map fun x => size x + 1).sum + 1⟩
end sizes
structure Stepped (α β : Type) : Type 1 where
  σ : Type
  [sz : HasSize σ]
  init : α → σ
  step : σ → σ
  out : σ → Option β
attribute [instance] Stepped.sz
namespace Stepped
variable {α β : Type}
inductive Reaches (M : Stepped α β) (S : ℕ) (b : β) : M.σ → ℕ → Prop
  | halt {s : M.σ} {t : ℕ} : M.out s = some b → size s ≤ S → Reaches M S b s t
  | step {s : M.σ} {t : ℕ} : M.out s = none → size s ≤ S → Reaches M S b (M.step s) t →
      Reaches M S b s (t + 1)
def Runs (M : Stepped α β) (a : α) (t S : ℕ) (b : β) : Prop := M.Reaches S b (M.init a) t
end Stepped
def DecidesInSteps (M : Stepped (List Bool) Bool) (δ : ℝ) : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ →
    ∃ (T : ℕ) (b : Bool), M.Runs (Sat3.enc φ) T (c * ((Sat3.enc φ).length + 1) ^ c) b ∧
      (b = true ↔ Sat3.Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)
end Groundwork


