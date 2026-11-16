-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_Lambda
-- name    : RobustBoolPCSP_Supplement_Lambda
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:23:11.435196+00:00
-- url     : https://prove2.me/theorems/dce7b00f-6412-41ce-8178-e4af91c41e27
-- title:
--   The template $\Lambda$ of Theorem 2.13 and $\Lambda^{=}$
-- statement:
--   Let $A=\{-1,0,1\}$ and $B=\mathbb Z/5\mathbb Z$. The template $\Lambda$ has the single four-ary pair
--
--   $$P=\Big\{a\in A^4:\sum_{i=1}^4a_i=0,\ a\neq(0,0,0,0)\Big\},\qquad Q=\{b\in B^4: b_i-b_j\in\{2,-2\}\ (\mathrm{mod}\ 5)\text{ for some }i,j\},$$
--
--   and $\Lambda^{=}$ is its soft-equality expansion.
--
--   $\Lambda$ is the fixed template showing that the transfer exponent $p/(2p+1)$ cannot be improved (Theorem 2.13).
--
--   **Formalization Note** $A$ is Mathlib's `SignType`, with values cast to $\mathbb Z$.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 2.13, pp.12–13, eqs. (4)–(5)

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_Classes

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- The strong relation (4) of `Λ`: `P = {a ∈ A⁴ : Σ_{i=1}^4 a_i = 0, a ≠ (0,0,0,0)}` over
`A = {−1, 0, 1}` (`SignType`, with its integer values). -/
def PLam : Set (Fin 4 → SignType) :=
  {a | (∑ i, (a i : ℤ)) = 0 ∧ a ≠ fun _ => 0}

/-- The weak relation (5) of `Λ`: `Q = {b ∈ B⁴ : b_i − b_j ∈ {2, −2} (mod 5) for some i, j}` over
`B = Z/5Z`. -/
def QLam : Set (Fin 4 → ZMod 5) :=
  {b | ∃ i j, b i - b j = 2 ∨ b i - b j = -2}

/-- The template **`Λ`** of Theorem 2.13.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), Theorem 2.13, pp.12–13: "Let A = {−1, 0, 1}, B = Z/5Z, and let Λ have the single
four-ary relation pair P = {a ∈ A⁴ : Σ⁴_{i=1} a_i = 0, a ≠ (0, 0, 0, 0)}, (4)
Q = {b ∈ B⁴ : b_i − b_j ∈ {2, −2} (mod 5) for some i, j}. (5)"

**Formalization Note.** `A = {−1, 0, 1}` is Mathlib's `SignType` (elements `-1, 0, 1`, cast to
`ℤ`); `B` is `ZMod 5`; index type `Unit`. -/
def Lam : Template Unit SignType (ZMod 5) := Template.single (k := 4) PLam QLam

/-- The soft-equality expansion `Λ^=` (p.11), `withEq Lam`. -/
def LamEq : Template (Option Unit) SignType (ZMod 5) := withEq Lam

end RobustBoolPCSP.Supplement


