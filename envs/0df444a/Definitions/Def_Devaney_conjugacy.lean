-- Prove2me | Definitions.Def_Devaney_conjugacy
-- name    : Devaney_conjugacy
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T07:14:49.471805+00:00
-- url     : https://prove2.me/theorems/3c521dfa-5eb0-4987-b12c-4386068fb66e
-- title:
--   Topological conjugacy and Cantor sets
-- statement:
--   Two structural notions from Chapter 1.
--
--   **Topological conjugacy (Definition 7.4).** Maps $f : A \to A$ and $g : B \to B$ of topological spaces are *topologically conjugate* if there is a homeomorphism $h : A \to B$ with $h \circ f = g \circ h$. Conjugate maps are completely equivalent dynamically: $h$ matches fixed points with fixed points, periodic orbits of period $n$ with periodic orbits of period $n$, and transitive systems with transitive systems.
--
--   **Cantor set (Definition 5.4).** A set $S \subseteq [0,1]$ is a *Cantor set* if it is closed, totally disconnected — meaning it contains no nondegenerate interval — and perfect — meaning every point of $S$ is an accumulation point of $S$. The Cantor middle-thirds set is the classical example, and the invariant set $\Lambda$ of the quadratic family is the example this mission is about.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.7, p. 47, Definition 7.4; §1.5, p. 37, Definition 5.4

import Mathlib

namespace Devaney

/-- Devaney, Definition 7.4: two maps `f : A → A` and `g : B → B` are topologically
conjugate if there is a homeomorphism `h : A ≃ₜ B` with `h ∘ f = g ∘ h`. -/
def TopologicallyConjugate {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → A) (g : B → B) : Prop :=
  ∃ h : A ≃ₜ B, ∀ x : A, h (f x) = g (h x)

/-- Devaney, Definition 5.4: a subset of the unit interval is a Cantor set if it is closed,
totally disconnected (it contains no nondegenerate interval), and perfect (each of its points
is an accumulation point of the set). -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S ⊆ Set.Icc (0 : ℝ) 1 ∧ IsClosed S ∧
    (∀ x y : ℝ, x < y → ¬ Set.Icc x y ⊆ S) ∧
    (∀ x ∈ S, AccPt x (Filter.principal S))

end Devaney


