-- Prove2me | Definitions.Def_ParityCubes_cubeSum
-- name    : ParityCubes_cubeSum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:06.689374+00:00
-- url     : https://prove2.me/theorems/85999edb-f601-4657-975b-0f3eead0c114
-- title:
--   Cube sum $D_S f$, certificates, zero cubes, $\mathrm{cert}(f)$ and $\zeta(f)$
-- statement:
--   Let $f$ be a Boolean function of finitely many variables and $S$ a set of these variables. The **cube sum** of $f$ over $S$ is
--
--   $$(D_S f)(y)=\bigoplus_{z\in\{0,1\}^S} f(z,y),$$
--
--   the parity of the number of completions on $S$ of the outside assignment $y$ on which $f$ is true. A nonempty $S$ is a **derivative certificate** of $f$ if $D_S f\equiv 1$ and a **zero cube** if $D_S f\equiv 0$. The quantities $\mathrm{cert}(f)$ and $\zeta(f)$ are the smallest sizes of a certificate and of a zero cube, with value $+\infty$ when no such set exists.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** The point $y$ is a full assignment whose values on $S$ are ignored. On $S=\emptyset$ the sum is $f$ itself, the convention $D_\emptyset f=f$ of Lemma 4.2; certificates and zero cubes range over nonempty sets only. $\mathrm{cert}$ and $\zeta$ take values in $\mathbb N_\infty$.
-- source:
--   Sheshadri, Smirnov, The Complexity of Choosing Parity Projections, arXiv:2611.00289 (manuscript sha256 95994d2d…), §1, p.1 (PDF p.2)

import Mathlib

set_option autoImplicit false

namespace ParityCubes

/-- **Cube sum** `D_S f` (Sheshadri–Smirnov, *The Complexity of Choosing Parity Projections*,
arXiv:2611.00289, manuscript sha256 95994d2d…, §1, p.1 (PDF p.2)). For a Boolean function `f` of the
variables `α` and a set `S` of variables, `cubeSum f S y` is the parity of the number of assignments
`x` that agree with `y` outside `S` and satisfy `f x = true`, i.e.
`(D_S f)(y) = ⨁_{z ∈ {0,1}^S} f(z, y)`.

**Formalization Note.** The values of `y` on `S` are ignored, so `cubeSum f S` is a function of the
variables outside `S`, as on p.1. On `S = ∅` the only such `x` is `y` itself, so `cubeSum f ∅ = f`:
this is the convention `D_∅ f = f` of Lemma 4.2 (p.8). Certificates and zero cubes below range over
nonempty `S` only. -/
def cubeSum {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) (S : Finset α)
    (y : α → Bool) : Bool :=
  decide (Odd (Finset.univ.filter (fun x : α → Bool => (∀ i, i ∉ S → x i = y i) ∧ f x = true)).card)

/-- `S` is a **derivative certificate** of `f` (§1, p.1 (PDF p.2)): `S` is nonempty and
`D_S f ≡ 1`. -/
def IsCertificate {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool)
    (S : Finset α) : Prop :=
  S.Nonempty ∧ ∀ y : α → Bool, cubeSum f S y = true

/-- `S` is a **zero cube** of `f` (§1, p.1 (PDF p.2)): `S` is nonempty and `D_S f ≡ 0`. -/
def IsZeroCube {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool)
    (S : Finset α) : Prop :=
  S.Nonempty ∧ ∀ y : α → Bool, cubeSum f S y = false

/-- `cert(f)`, the size of a smallest certificate of `f`, and `+∞` (`⊤`) when there is none
(§1, p.1 (PDF p.2)). -/
noncomputable def cert {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) : ℕ∞ :=
  ⨅ (S : Finset α) (_ : IsCertificate f S), (S.card : ℕ∞)

/-- `ζ(f)`, the size of a smallest zero cube of `f`, and `+∞` (`⊤`) when there is none
(§1, p.1 (PDF p.2)). -/
noncomputable def zeta {α : Type*} [Fintype α] [DecidableEq α] (f : (α → Bool) → Bool) : ℕ∞ :=
  ⨅ (S : Finset α) (_ : IsZeroCube f S), (S.card : ℕ∞)

end ParityCubes


