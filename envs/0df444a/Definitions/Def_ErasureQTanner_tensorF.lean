-- Prove2me | Definitions.Def_ErasureQTanner_tensorF
-- name    : ErasureQTanner_tensorF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:45.147472+00:00
-- url     : https://prove2.me/theorems/f68932cb-b3c1-4fe1-9624-c5e09f635e98
-- title:
--   The tensor code $C_1\otimes C_2$ over a field
-- statement:
--   For linear codes $C_1\subseteq\mathbb F^\alpha$, $C_2\subseteq\mathbb F^\beta$, the **tensor code** $C_1\otimes C_2\subseteq\mathbb F^{\alpha\times\beta}$ consists of the matrices all of whose columns lie in $C_1$ and all of whose rows lie in $C_2$.
--
--   **Formalization Note** Theorem 7 is stated over $\mathbb F_q$ with unequal lengths. At $\mathbb F=\mathbb F_2$ this is the published `QAlgorithms.tensorCode`, which the binary statements use.
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), §4, p.7; Theorem 7, p.17

import Mathlib

set_option autoImplicit false

namespace ErasureQTanner

/-- The tensor code `C₁ ⊗ C₂` over an arbitrary field: Pfister, Sprumont, Zémor, STOC 2027 submission (manuscript
sha256 bf7a84a5…), §4, p.7: "`C_A ⊗ C_B` has columns in `C_A` and rows in `C_B`".

**Formalization Note.** A word is `x : α × β → F`, the first index the row. At `F = ZMod 2` this is
`QAlgorithms.tensorCode`, which is binary; Theorem 7 (p.17) is `q`-ary and has unequal lengths. -/
def tensorF {F α β : Type*} [Field F] (C₁ : Submodule F (α → F)) (C₂ : Submodule F (β → F)) :
    Submodule F (α × β → F) where
  carrier := {x | (∀ b, (fun a => x (a, b)) ∈ C₁) ∧ ∀ a, (fun b => x (a, b)) ∈ C₂}
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    exact ⟨fun b => C₁.add_mem (hx₁ b) (hy₁ b), fun a => C₂.add_mem (hx₂ a) (hy₂ a)⟩
  zero_mem' := ⟨fun _ => C₁.zero_mem, fun _ => C₂.zero_mem⟩
  smul_mem' := by
    rintro r x ⟨hx₁, hx₂⟩
    exact ⟨fun b => C₁.smul_mem r (hx₁ b), fun a => C₂.smul_mem r (hx₂ a)⟩

end ErasureQTanner


