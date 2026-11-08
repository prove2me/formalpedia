-- Prove2me | Definitions.Def_ParityCubes_anfCoeff
-- name    : ParityCubes_anfCoeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:55.528679+00:00
-- url     : https://prove2.me/theorems/a21b07de-4dcc-465d-84ca-ab78d9d2270c
-- title:
--   Algebraic normal form: coefficient $c_A$, supports and maximal supports
-- statement:
--   Every Boolean function has a unique representation $f=\sum_A c_A x_A$ over $\mathbb F_2$, with $x_A=\prod_{i\in A}x_i$. This definition gives the coefficient by Möbius inversion,
--
--   $$c_A=\bigoplus_{B\subseteq A} f(\mathbf 1_B),$$
--
--   where $\mathbf 1_B$ is the indicator assignment of $B$. The sets $A$ with $c_A=1$ are the **supports** of $f$; a **maximal support** is a support with no strict superset that is a support.
--
--   These notions state the maximal-term rule (Lemma 2.1), which is the common tool of the paper's proofs.
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), §2.1, p.3 (PDF p.4), and Lemma 2.1, p.3

import Mathlib
import Definitions.Def_ParityCubes_cubeSum

set_option autoImplicit false

namespace ParityCubes

/-- The coefficient `c_A` of the monomial `x_A = ∏_{i ∈ A} x_i` in the **algebraic normal form**
`f = Σ_A c_A x_A` over `𝔽₂` (Sheshadri–Smirnov, arXiv:2611.00289, manuscript sha256 95994d2d…,
§2.1, p.3 (PDF p.4)).

**Formalization Note.** The ANF is unique; its coefficients are given by Möbius inversion,
`c_A = ⨁_{B ⊆ A} f(1_B)`, where `1_B` is the indicator assignment of `B`. This is the formula used
here. -/
def anfCoeff {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) (A : Finset α) :
    Bool :=
  decide (Odd (A.powerset.filter (fun B => f (fun i => decide (i ∈ B)) = true)).card)

/-- `A` is a **support** of `f`: `c_A = 1` (§2.1, p.3 (PDF p.4)). -/
def IsSupport {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) (A : Finset α) :
    Prop :=
  anfCoeff f A = true

/-- `A` is a **maximal support** of `f`: a support no strict superset of which is a support
(Lemma 2.1, p.3 (PDF p.4)). -/
def IsMaxSupport {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool)
    (A : Finset α) : Prop :=
  IsSupport f A ∧ ∀ B : Finset α, A ⊂ B → ¬ IsSupport f B

end ParityCubes


