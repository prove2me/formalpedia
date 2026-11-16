-- Prove2me | Definitions.Def_RobustBoolPCSP_Supplement_BalancedPair
-- name    : RobustBoolPCSP_Supplement_BalancedPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:27:34.686831+00:00
-- url     : https://prove2.me/theorems/3dd5c1b7-9e7a-4b9f-8fe8-ec94e2ec00ac
-- title:
--   Balanced and constant-excluding relation pairs
-- statement:
--   A relation pair $(P,Q)$ of arity $k$ is **balanced and constant-excluding** if some rational probability distribution $\lambda$ supported on $P$ has all $k$ coordinate marginals equal to one distribution $\nu$ on $A$, and $(b,\dots,b)\notin Q$ for every $b\in B$.
--
--   Together with soft equality, one such pair gives square-root hardness (Theorem 8.5).
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Definition 8.4, p.71

import Mathlib

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-- A relation pair `(P, Q)` of arity `k` is **balanced and constant-excluding**.
Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03, sha256
fd1be0d0…), Definition 8.4, p.71: "A relation pair (P, Q) of arity k in a template with domains A
and B is balanced and constant-excluding if some rational probability distribution λ supported on P
has all k coordinate marginals equal to one distribution ν on A, and (b, …, b) ∉ Q for every b ∈ B."

**Formalization Note.** `λ` is a rational probability vector on `A^k` vanishing off `P`; `ν : A → ℚ`
is the common marginal (it is then itself a probability vector). -/
def IsBalancedConstExcl {A B : Type} [Fintype A] [DecidableEq A] {k : ℕ}
    (P : Set (Fin k → A)) (Q : Set (Fin k → B)) : Prop :=
  (∃ (lam : (Fin k → A) → ℚ) (nu : A → ℚ), (∀ x, 0 ≤ lam x) ∧ (∀ x, lam x ≠ 0 → x ∈ P) ∧
    (∑ x, lam x = 1) ∧
      ∀ (i : Fin k) (a : A), ∑ x ∈ Finset.univ.filter (fun x : Fin k → A => x i = a), lam x = nu a) ∧
    ∀ b : B, (fun _ => b) ∉ Q

end RobustBoolPCSP.Supplement


