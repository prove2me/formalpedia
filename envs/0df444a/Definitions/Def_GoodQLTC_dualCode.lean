-- Prove2me | Definitions.Def_GoodQLTC_dualCode
-- name    : GoodQLTC_dualCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:41:14.47482+00:00
-- url     : https://prove2.me/theorems/f39702f0-5585-410c-b6bf-3131b9aca684
-- title:
--   Dual code $C^{\perp}$
-- statement:
--   For a linear code $C\subseteq F^{\Omega}$ with $\langle x,y\rangle=\sum_\omega x_\omega y_\omega$,
--   $$
--   C^{\perp}=\{y\in F^{\Omega}:\langle x,y\rangle=0\ \text{for every }x\in C\}.
--   $$
--
--   The dual local codes enter the systolic (homological) half of the argument.
-- source:
--   Gay, Jeronimo, Asymptotically Good Quantum Locally Testable Codes, arXiv:2609.20780 (held version, sha256 04ad03ca…), §4.2, p.16 (PDF p.19)

import Mathlib

namespace GoodQLTC

/-- The **dual code** `C^⊥ := {y ∈ F^Ω : ⟨x, y⟩ = 0 for every x ∈ C}` of a linear code
`C ⊆ F^Ω`, with `⟨x, y⟩ := ∑_ω x_ω y_ω`, Gay–Jeronimo, arXiv:2609.20780 (held version), §4.2,
p.16. -/
def dualCode {F : Type} [Field F] {Ω : Type} [Fintype Ω] (C : Submodule F (Ω → F)) :
    Submodule F (Ω → F) where
  carrier := {y | ∀ x ∈ C, x ⬝ᵥ y = 0}
  add_mem' := by
    intro a b ha hb x hx
    rw [dotProduct_add, ha x hx, hb x hx, add_zero]
  zero_mem' := by
    intro x _
    exact dotProduct_zero x
  smul_mem' := by
    intro c a ha x hx
    rw [dotProduct_smul, ha x hx, smul_zero]

end GoodQLTC


