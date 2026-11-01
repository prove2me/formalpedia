-- Prove2me | Definitions.Def_FracMPGA_IsCalmOn
-- name    : FracMPGA_IsCalmOn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:39:09.842982+00:00
-- url     : https://prove2.me/theorems/d5b5a629-a6ab-4fd6-b52d-f01ffd9611c5
-- title:
--   Calmness condition relative to a set
-- statement:
--   A function $\varphi:V\to(-\infty,+\infty]$ satisfies the **calmness condition at $x\in\operatorname{dom}\varphi$ relative to $A$** if there are $\kappa_x>0$ and a neighbourhood $B(x)$ of $x$ such that
--   $$
--   |\varphi(u)-\varphi(x)|\le\kappa_x\|u-x\|_2\qquad\text{for all } u\in B(x)\cap A.
--   $$
--   It satisfies the calmness condition **on $A$** if it does so at every point of $A$, relative to $A$.
--
--   Assumption 4 of the paper asks that $g^*$ be calm on its domain; Proposition 2.1(ii) needs calmness of $\varphi_2^*$ at one point.
--
--   **Formalization Note** The absolute value is written as two inequalities in the extended reals; with $\varphi(x)$ finite this is the displayed bound and forces $\varphi(u)$ finite on $B(x)\cap A$.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §2.1, p.6 (calmness condition)

import Mathlib

open Topology

namespace FracMPGA

/-- The **calmness condition at a point relative to a set** (Zhou, Zhang, Li,
arXiv:2311.00957v2, §2.1, p.6): `φ : V → (−∞, +∞]` satisfies the calmness condition at
`x ∈ dom(φ)` relative to `A` if there are `κ > 0` and a neighbourhood `U` of `x` with
`|φ(u) − φ(x)| ≤ κ ‖u − x‖₂` for every `u ∈ U ∩ A`.

**Formalization Note** The absolute value is written as the two inequalities
`φ u ≤ φ x + κ‖u − x‖` and `φ x ≤ φ u + κ‖u − x‖` in `EReal`; with `φ x` finite they say exactly
that `φ u` is finite and `|φ u − φ x| ≤ κ‖u − x‖`. The page introduces the notion for
"`φ : R → (−∞, +∞]`", a typo for `ℝⁿ`. -/
def IsCalmAt {V : Type*} [NormedAddCommGroup V] (φ : V → EReal) (x : V) (A : Set V) : Prop :=
  φ x ≠ ⊤ ∧ ∃ κ : ℝ, 0 < κ ∧ ∃ U ∈ 𝓝 x, ∀ u ∈ U ∩ A,
    φ u ≤ φ x + ((κ * ‖u - x‖ : ℝ) : EReal) ∧ φ x ≤ φ u + ((κ * ‖u - x‖ : ℝ) : EReal)

/-- `φ` satisfies the **calmness condition on `A`** if it satisfies the calmness condition at
each point of `A` relative to `A` (Zhou, Zhang, Li, arXiv:2311.00957v2, §2.1, p.6). -/
def IsCalmOn {V : Type*} [NormedAddCommGroup V] (φ : V → EReal) (A : Set V) : Prop :=
  ∀ x ∈ A, IsCalmAt φ x A

end FracMPGA


