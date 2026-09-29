-- Prove2me | Definitions.Def_DoCarmo_regular_surface
-- name    : DoCarmo_regular_surface
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T01:20:25.260266+00:00
-- url     : https://prove2.me/theorems/f5a6355b-8ac8-47fc-9d2c-b30f7b38e76c
-- title:
--   Regular surface, parametrization, graphs and regular values
-- statement:
--   do Carmo §2-2, Definitions 1 and 2.
--
--   A subset $S \subseteq \mathbb{R}^3$ is a **regular surface** if every $p \in S$ has an open neighbourhood $V$ in $\mathbb{R}^3$ such that $V \cap S$ is the image of a map $x : U \to \mathbb{R}^3$ on an open $U \subseteq \mathbb{R}^2$ which is (1) differentiable, i.e. $C^\infty$; (2) a homeomorphism of $U$ onto $V \cap S$; and (3) regular, meaning $dx_q$ is injective for every $q \in U$. Such an $x$ is called a **parametrization**.
--
--   The file also introduces the graph of a function of two of the three coordinates — in the three forms $z = f(x,y)$, $y = g(x,z)$, $x = h(y,z)$ needed for do Carmo's Proposition 3 — and the notion of a **regular value** of a function $f : U \subseteq \mathbb{R}^3 \to \mathbb{R}$: a value $a$ such that $df_p$ is surjective, equivalently nonzero, at every point $p$ of the level set (Definition 2).
-- source:
--   Manfredo P. do Carmo, Differential Geometry of Curves and Surfaces, 2nd ed., Dover, 2016, Chapter 2, Section 2-2 (pp. 54-71)

import Mathlib

namespace DoCarmoDG

/-- A parametrization (system of local coordinates) of a subset `S ⊆ ℝ³`, in the sense of the
three conditions of do Carmo's Definition 1 of §2-2: `x` is smooth on the open set `U`, is a
homeomorphism of `U` onto its image (injective with continuous inverse), takes values in `S`,
and has injective differential at every point of `U`. -/
def IsSurfaceParametrization (U : Set (ℝ × ℝ)) (x : ℝ × ℝ → EuclideanSpace ℝ (Fin 3))
    (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ (⊤ : ℕ∞) x U ∧ Set.InjOn x U ∧ x '' U ⊆ S ∧
    (∃ g : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ,
      ContinuousOn g (x '' U) ∧ ∀ q ∈ U, g (x q) = q) ∧
    ∀ q ∈ U, Function.Injective (fderiv ℝ x q)

/-- A regular surface, do Carmo §2-2, Definition 1: a subset `S ⊆ ℝ³` such that every point of
`S` has a neighbourhood `V` in `ℝ³` for which `V ∩ S` is the image of a parametrization. -/
def IsRegularSurface (S : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ p ∈ S, ∃ (V : Set (EuclideanSpace ℝ (Fin 3))) (U : Set (ℝ × ℝ))
      (x : ℝ × ℝ → EuclideanSpace ℝ (Fin 3)),
    IsOpen V ∧ p ∈ V ∧ IsSurfaceParametrization U x S ∧ x '' U = V ∩ S

/-- The graph of a function of two variables, as a subset of `ℝ³` (do Carmo §2-2). -/
def graphOf (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ((p 0, p 1) ∈ U) ∧ p 2 = f (p 0, p 1)}

/-- The graph of a function of the variables `x, z`, as a subset of `ℝ³`. -/
def graphOfXZ (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ((p 0, p 2) ∈ U) ∧ p 1 = f (p 0, p 2)}

/-- The graph of a function of the variables `y, z`, as a subset of `ℝ³`. -/
def graphOfYZ (U : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {p | ((p 1, p 2) ∈ U) ∧ p 0 = f (p 1, p 2)}

/-- A regular value of a real-valued function on an open set of `ℝ³`, do Carmo §2-2,
Definition 2: a value `a` such that the differential is surjective — equivalently, nonzero —
at every point of the level set. -/
def IsRegularValue (U : Set (EuclideanSpace ℝ (Fin 3))) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (a : ℝ) : Prop :=
  ∀ p ∈ U, f p = a → fderiv ℝ f p ≠ 0

end DoCarmoDG


