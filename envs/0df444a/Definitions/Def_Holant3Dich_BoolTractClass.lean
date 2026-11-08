-- Prove2me | Definitions.Def_Holant3Dich_BoolTractClass
-- name    : Holant3Dich_BoolTractClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:38.848197+00:00
-- url     : https://prove2.me/theorems/1837bac8-a02d-43fc-a4ed-1720cd95eba0
-- title:
--   Types $\mathrm I(a,b)$ and $\mathrm{II}$, and the three tractable classes of the Boolean $\mathrm{Holant}^*$ dichotomy
-- statement:
--   A symmetric Boolean signature $[x_0,x_1,\dots,x_n]$ with $n\ge2$ ($x_k$ the value on inputs of Hamming weight $k$) **has type $\mathrm I(a,b)$** if $a x_k+b x_{k+1}=a x_{k+2}$ for $0\le k\le n-2$, and **has type $\mathrm{II}$** if $x_k=-x_{k+2}$ for $0\le k\le n-2$ (Definition 2.4, p.15, after [CC17a]).
--
--   A set $S$ of symmetric Boolean signatures lies in a **tractable class of Theorem 2.5** if
--
--   1. every member has arity $\le 2$; or
--   2. there are $a,b$, not both $0$, such that every member has type $\mathrm I(a,b)$ or has arity 2 and the form $[2a\lambda,b\lambda,-2a\lambda]$; or
--   3. every member has type $\mathrm{II}$ or has arity 2 and the form $[\lambda,0,\lambda]$.
--
--   These classes describe the tractable side of the Boolean dichotomy used throughout the paper, and Item 3(c) of the criterion of Theorem 4.9.
--
--   **Formalization Note** The pair $(a,b)$ is a parameter of type $\mathrm I$; "not both $0$" is imposed in class 2, where the pair is quantified.
-- source:
--   Cai, Ihm, Group Action and Spin Representation Lead to a Holant* Complexity Dichotomy on Domain Size 3, STOC 2027 submission, arXiv:2610.04750 (held manuscript sha256 b608db44…), Definition 2.4 p.15; Theorem 2.5 p.15

import Mathlib
import Definitions.Def_Holant3Dich_Sig

set_option autoImplicit false

namespace Holant3Dich

/-- A symmetric Boolean signature `[x₀, x₁, …, x_n]` (`n ≥ 2`) **has type I(a, b)** if
`a x_k + b x_{k+1} = a x_{k+2}` for `0 ≤ k ≤ n − 2`. Cai–Ihm, *Group Action and Spin Representation
Lead to a Holant\* Complexity Dichotomy on Domain Size 3*, STOC 2027 submission, arXiv:2610.04750
(held manuscript sha256 b608db44…), Definition 2.4 (Definition 2.9 in [CC17a]), p.15: "A signature
[x0, x1, . . . , xn], where n ≥ 2, has type I(a, b), if there exist a and b (not both 0), such that
a x_k + b x_{k+1} = a x_{k+2} for 0 ≤ k ≤ n − 2. We say it is of type II, if x_k = −x_{k+2} for
0 ≤ k ≤ n − 2."

**Formalization Note.** The pair `(a, b)` is a parameter; "not both 0" is imposed where the pair
is quantified (`BoolTractClass`). `x_k` is `boolVal F k`. -/
def TypeI (a b : ℂ) (F : Sig 2) : Prop :=
  2 ≤ F.1 ∧ ∀ k, k + 2 ≤ F.1 → a * boolVal F k + b * boolVal F (k + 1) = a * boolVal F (k + 2)

/-- A symmetric Boolean signature `[x₀, …, x_n]` (`n ≥ 2`) **has type II** if
`x_k = −x_{k+2}` for `0 ≤ k ≤ n − 2`. Cai–Ihm, Definition 2.4, p.15. -/
def TypeII (F : Sig 2) : Prop :=
  2 ≤ F.1 ∧ ∀ k, k + 2 ≤ F.1 → boolVal F k = -boolVal F (k + 2)

/-- A set `S` of symmetric Boolean signatures lies in one of the **three tractable classes of
Theorem 2.5**. Cai–Ihm, Theorem 2.5 (Theorem 2.12 in [CC17a]), p.15:
"1. Every signature in F is of arity ≤ 2.
2. There exists a and b (not both 0, depending only on F), such that every signature in F either
(1) has type I(a, b) or (2) has arity 2 and is of the form [2aλ, bλ, −2aλ].
3. Every signature in F either (1) has type II or (2) has arity 2 and is of the form [λ, 0, λ]." -/
def BoolTractClass (S : Set (Sig 2)) : Prop :=
  (∀ F ∈ S, F.1 ≤ 2) ∨
  (∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ F ∈ S, TypeI a b F ∨
    (F.1 = 2 ∧ ∃ l : ℂ, boolVal F 0 = 2 * a * l ∧ boolVal F 1 = b * l ∧
      boolVal F 2 = -(2 * a * l))) ∨
  (∀ F ∈ S, TypeII F ∨
    (F.1 = 2 ∧ ∃ l : ℂ, boolVal F 0 = l ∧ boolVal F 1 = 0 ∧ boolVal F 2 = l))

end Holant3Dich


