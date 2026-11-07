-- Prove2me | Definitions.Def_CompNonlocal_PolySize
-- name    : CompNonlocal_PolySize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:41:40.141118+00:00
-- url     : https://prove2.me/theorems/64787738-b39f-49d1-b84a-8fca263efb92
-- title:
--   Polynomial-size circuit families
-- statement:
--   A family $\{C_\kappa\}$ has **polynomial size** if one polynomial $p$ bounds, for every $\kappa$, both the number of gates and the number of wires of $C_\kappa$. These are the adversaries of the paper: "polynomial-size quantum circuit families with classical advice" (the advice is hard-wired).
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §4, p.18

import Mathlib
import Definitions.Def_CompNonlocal_Family

set_option autoImplicit false

namespace CompNonlocal

/-- Polynomial-size circuit families (with classical advice). Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), §4, p.18: "Unless explicitly stated otherwise, adversaries are polynomial-size quantum
circuit families with classical advice."

**Formalization Note** One polynomial bounds both the number of instructions and the number of
wires (hence the input, output and ancilla counts) at every `κ`. Classical advice of polynomial
length is subsumed: a non-uniform family may hard-wire it. -/
def PolySize (F : Family) : Prop :=
  ∃ p : Polynomial ℕ, ∀ κ : ℕ, (F κ).size ≤ p.eval κ ∧ (F κ).width ≤ p.eval κ

end CompNonlocal


