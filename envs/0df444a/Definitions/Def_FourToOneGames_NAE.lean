-- Prove2me | Definitions.Def_FourToOneGames_NAE
-- name    : FourToOneGames_NAE
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T23:02:32.443638+00:00
-- url     : https://prove2.me/theorems/4d54cabe-b59f-45d5-9292-babb9ed80743
-- title:
--   Tripled sets, the NAE predicate, and NAE-satisfiability
-- statement:
--   Definitions 4.1, 4.9, 4.10, 4.11 and 4.12 of the source paper.
--
--   A **tripled set** is a finite set together with a partition into triples; here a tripled set with triple-index set $\iota$ is modelled as $E = \iota \times \{0,1,2\}$, the triple indexed by $i$ being $\{(i,0),(i,1),(i,2)\}$, and $\mathbb{F}_2^{E}$ is the space of functions $E \to \mathbb{F}_2$.
--
--   The **not-all-equal predicate** is $\mathrm{NAE}_3(x_1,x_2,x_3) = x_1+x_2+x_3+x_1x_2+x_2x_3+x_3x_1$ over $\mathbb{F}_2$, which equals $1$ exactly when $x_1,x_2,x_3$ are not all equal.
--
--   For a linear functional $f : \mathbb{F}_2^{E} \to \mathbb{F}_2$, its coefficient vector is $a_v = f(e_v)$, so that $f(x) = \sum_{v \in E} a_v x_v$; linear functionals $f^{(1)},\dots,f^{(r)}$ are **jointly NAE-satisfying** when $\sum_{i \le r} \mathrm{NAE}_3(a^{(i)}_{v_1}, a^{(i)}_{v_2}, a^{(i)}_{v_3}) = 1$ for every triple $\{v_1,v_2,v_3\}$. For a symmetric bilinear form $f$ with matrix $X_{uv} = f(e_u \otimes e_v)$, being **NAE-satisfying** means $X_{v_1v_1}+X_{v_2v_2}+X_{v_3v_3}+X_{v_1v_2}+X_{v_2v_3}+X_{v_3v_1} = 1$ for every triple.
--
--   A **tensor decomposition** of a bilinear form $f$ is a family of linear functionals $f^{(1)},\dots,f^{(r)}$ such that each $f^{(i)}$ is of the form $y \mapsto f(x^{(i)} \otimes y)$ and $f(x \otimes y) = \sum_{i \le r} f^{(i)}(x) f^{(i)}(y)$ for all $x,y$.
-- source:
--   Yumou Fei, Dor Minzer, Shuo Wang, "On the Hardness of 4-to-1 Games with Perfect Completeness", ECCC Report No. TR26-179 (2026), https://eccc.weizmann.ac.il/report/2026/179/, pp. 18-21, Definitions 4.1, 4.9, 4.10, 4.11, 4.12

import Mathlib

/-!
# Tripled sets, the NAE predicate, and NAE-satisfiability

Definitions 4.1, 4.9, 4.10, 4.11 and 4.12 of Fei–Minzer–Wang, *On the Hardness of 4-to-1 Games
with Perfect Completeness* (ECCC TR26-179).

A *tripled set* (Definition 4.1) is a finite set equipped with a partition into triples.  Here a
tripled set with triple-index type `ι` is modelled as the product `ι × Fin 3`: the triple
indexed by `i : ι` is `{(i, 0), (i, 1), (i, 2)}`.
-/

namespace FourToOneGames

open scoped BigOperators

/-- The Not-All-Equal predicate over `F₂` (Definition 4.9):
`NAE3 x₁ x₂ x₃ = x₁ + x₂ + x₃ + x₁x₂ + x₂x₃ + x₃x₁`, which equals `1` exactly when
`x₁, x₂, x₃` are not all equal. -/
def NAE3 (x₁ x₂ x₃ : ZMod 2) : ZMod 2 :=
  x₁ + x₂ + x₃ + x₁ * x₂ + x₂ * x₃ + x₃ * x₁

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `F₂`-vector space `F₂^E` attached to the tripled set `E = ι × Fin 3`. -/
abbrev TripledSpace (ι : Type) : Type := (ι × Fin 3) → ZMod 2

/-- The coefficient `a_v` of a linear functional `φ : F₂^E → F₂`, i.e. the value of `φ` on the
standard basis vector `e_v`; thus `φ x = ∑_{v ∈ E} a_v x_v`. -/
def coeff (φ : TripledSpace ι →ₗ[ZMod 2] ZMod 2) (v : ι × Fin 3) : ZMod 2 :=
  φ (Pi.single v 1)

/-- The entry `X_{u,v}` of the matrix representing a bilinear form `f` on `F₂^E`, i.e. the value
of `f` on the pair of standard basis vectors `e_u, e_v`. -/
def bilinCoeff (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (u v : ι × Fin 3) : ZMod 2 := f (Pi.single u 1) (Pi.single v 1)

/-- `f` is a symmetric bilinear form. -/
def IsSymmetricForm (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ x y, f x y = f y x

/-- The linear functionals `φ 0, …, φ (r-1) : F₂^E → F₂` are *jointly NAE-satisfying*
(Definition 4.10): for every triple `{v₁, v₂, v₃}` of `E`,
`∑_{j < r} NAE3 (a^{(j)}_{v₁}, a^{(j)}_{v₂}, a^{(j)}_{v₃}) = 1`, where `a^{(j)}` is the
coefficient vector of `φ j`. -/
def JointlyNAESatisfying {r : ℕ} (φ : Fin r → TripledSpace ι →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ i : ι, (∑ j : Fin r, NAE3 (coeff (φ j) (i, 0)) (coeff (φ j) (i, 1)) (coeff (φ j) (i, 2))) = 1

/-- A symmetric bilinear form `f` on `F₂^E` is *NAE-satisfying* (Definition 4.11): for every
triple `{v₁, v₂, v₃}` of `E`,
`X_{v₁v₁} + X_{v₂v₂} + X_{v₃v₃} + X_{v₁v₂} + X_{v₂v₃} + X_{v₃v₁} = 1`. -/
def NAESatisfyingForm (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2) : Prop :=
  ∀ i : ι,
    bilinCoeff f (i, 0) (i, 0) + bilinCoeff f (i, 1) (i, 1) + bilinCoeff f (i, 2) (i, 2)
      + bilinCoeff f (i, 0) (i, 1) + bilinCoeff f (i, 1) (i, 2) + bilinCoeff f (i, 2) (i, 0) = 1

/-- `(φ 0, …, φ (r-1))` is a *tensor decomposition* of the symmetric bilinear form `f`
(Definition 4.12): each `φ j` lies in the image of the map `x ↦ f (x ⊗ ·)`, and
`f (x ⊗ y) = ∑_{j < r} φ j x * φ j y` for all `x, y`. -/
def IsTensorDecomposition {r : ℕ}
    (f : TripledSpace ι →ₗ[ZMod 2] TripledSpace ι →ₗ[ZMod 2] ZMod 2)
    (φ : Fin r → TripledSpace ι →ₗ[ZMod 2] ZMod 2) : Prop :=
  (∀ j : Fin r, ∃ x : TripledSpace ι, ∀ y : TripledSpace ι, φ j y = f x y) ∧
    (∀ x y : TripledSpace ι, f x y = ∑ j : Fin r, φ j x * φ j y)

end FourToOneGames


