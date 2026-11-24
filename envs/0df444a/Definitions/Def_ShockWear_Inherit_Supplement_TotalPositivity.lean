-- Prove2me | Definitions.Def_ShockWear_Inherit_Supplement_TotalPositivity
-- name    : ShockWear_Inherit_Supplement_TotalPositivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:48:56.561802+00:00
-- url     : https://prove2.me/theorems/2d0ffc0c-5afb-4e89-aab0-8271dcf1a6fe
-- title:
--   Definition 2.3 — SCₙ, TPₙ and real/integer PF₂ difference kernels
-- statement:
--   Let $K:A\times B\to\mathbb R$ be a kernel on two ordered domains. For a positive integer $n$ and sign $\varepsilon\in\{-1,1\}$, sign consistency of order $n$ means
--
--   $$
--   \varepsilon\det[K(x_i,y_j)]_{i,j=1}^n\ge0
--   \quad(x_1<\cdots<x_n\text{ in }A,\ y_1<\cdots<y_n\text{ in }B).
--   $$
--
--   Total positivity of order $n$ requires this condition with positive sign at every order $1,\ldots,n$. A real function is PF₂ when its difference kernel $f(x-y)$ is TP₂ on $\mathbb R^2$. A sequence indexed by nonnegative integers is PF₂ when its extension by zero to negative integers has a TP₂ integer difference kernel. These are the source's determinant notions, needed for arbitrary-order transfers and convolution-CDF implications.
--
--   **Formalization Note** Ordered samples use `Fin n` and `StrictMono`. SCₙ alone imposes only size $n$; TPₙ also imposes every smaller positive size. No integrability is bundled into these predicates: a proper CDF is not integrable over the whole real line.
-- source:
--   Esary, Marshall and Proschan, Shock Models and Wear Processes, Ann. Probability 1 (1973), pp. 630–632, Definition 2.3 and ageing definitions; https://doi.org/10.1214/aop/1176996891

import Mathlib

namespace ShockWear.Inherit.Supplement

/-- Definition 2.3: the ordered minors of size n have sign eps.
Theorems restrict n to positive orders and eps to the two signs. -/
def IsSC {α β : Type*} [LinearOrder α] [LinearOrder β]
    (n : ℕ) (eps : ℝ) (A : Set α) (B : Set β) (K : α → β → ℝ) : Prop :=
  ∀ x : Fin n → α, ∀ y : Fin n → β,
    (∀ i, x i ∈ A) → (∀ i, y i ∈ B) → StrictMono x → StrictMono y →
    0 ≤ eps * (Matrix.of fun i j => K (x i) (y j)).det

/-- Definition 2.3: every order from 1 through n is positive. -/
def IsTP {α β : Type*} [LinearOrder α] [LinearOrder β]
    (n : ℕ) (A : Set α) (B : Set β) (K : α → β → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → IsSC m 1 A B K

/-- PF₂ of a real function is TP₂ of its difference kernel on the whole line. -/
def IsPF2Function (f : ℝ → ℝ) : Prop :=
  IsTP 2 Set.univ Set.univ (fun x y : ℝ => f (x - y))

/-- The natural-indexed sequence is extended by zero to the negative integers. -/
def seqOnInt (a : ℕ → ℝ) (z : ℤ) : ℝ :=
  if 0 ≤ z then a z.toNat else 0

/-- PF₂ of a sequence means TP₂ of its integer difference kernel, including order 1. -/
def IsPF2Sequence (a : ℕ → ℝ) : Prop :=
  IsTP 2 Set.univ Set.univ (fun j k : ℤ => seqOnInt a (j - k))

end ShockWear.Inherit.Supplement


