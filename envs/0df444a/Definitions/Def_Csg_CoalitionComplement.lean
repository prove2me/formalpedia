-- Prove2me | Definitions.Def_Csg_CoalitionComplement
-- name    : Csg_CoalitionComplement
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T21:42:34.415809+00:00
-- url     : https://prove2.me/theorems/78dfeff8-084a-4616-be89-7d93f5639b0a
-- title:
--   Coalition Complement
-- statement:
--   Definitions and structural lemmas for Coalition Complement, from Gabriel Santos and contributors. Lean reformalization following Maximilian Schäffeler and Mohammad Abdulaziz’s Isabelle AFP proof strategy.'s pinned Correctness of policy iteration for discounted Markov decision processes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/CoalitionComplement.lean

import Definitions.Def_Csg_Coalition
set_option autoImplicit true
namespace Csg
namespace NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players)
theorem mem_compl_compl (i : Players) : i ∈ (C : Finset Players)ᶜᶜ ↔ i ∈ C := by
  simp
def complCoalitionEquiv : ComplementAction A Cᶜ ≃ CoalitionAction A C where
  toFun x i := x ⟨i.1, (mem_compl_compl C i.1).mpr i.2⟩
  invFun y i := y ⟨i.1, (mem_compl_compl C i.1).mp i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable (G : NCSG S Players A)
end NCSG
end Csg


