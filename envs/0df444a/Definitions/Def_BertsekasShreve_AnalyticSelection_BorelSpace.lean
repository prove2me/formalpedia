-- Prove2me | Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
-- name    : BertsekasShreve_AnalyticSelection_BorelSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:27.683554+00:00
-- url     : https://prove2.me/theorems/a63fcc0b-eb38-409c-946b-3c8896359620
-- title:
--   Borel spaces (Definition 7.7): topological spaces homeomorphic to a Borel subset of a complete separable metric space
-- statement:
--   Let $X$ be a topological space. $X$ is a **Borel space** if there exist a complete separable metric space $Z$ and a Borel subset $B\in\mathscr B_Z$ such that $X$ is homeomorphic to $B$ (with the subspace topology). The empty set is also regarded as a Borel space; it is covered by the definition, being homeomorphic to $\emptyset\subseteq Z$.
--
--   Every Borel space is separable and metrizable, and every complete separable metric space (in particular $\mathbb R$, $\mathbb R^n$, the extended real line $R^*=[-\infty,\infty]$, and the Baire space $\mathscr N=\mathbb N^{\mathbb N}$) is a Borel space. Borel spaces are the state, control and disturbance spaces of the stochastic models of Part II of the book, and every result of Sections 7.6–7.7 is stated for them.
--
--   **Formalization Note** The predicate is the class `IsBorelSpace X` on a type with a topology; the ambient space $Z$ is taken in the same universe as $X$ (no loss of generality, since every separable metric space embeds in the Hilbert cube). It is distinct from Mathlib's class `BorelSpace X`, which says that the measurable structure of $X$ is its Borel σ-algebra $\mathscr B_X$; the theorems of this mission assume both, so that "measurable" means Borel-measurable in the book's sense.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 118, Definition 7.7

import Mathlib

namespace BertsekasShreve.AnalyticSelection

open MeasureTheory

universe u

/-- **Definition 7.7** (Bertsekas–Shreve, p. 118). A topological space `X` is a *Borel space* if
it is homeomorphic to a Borel subset `B` of some complete separable metric space `Z`. (The empty
space is covered: it is homeomorphic to `∅ ⊆ Z`.) The ambient space `Z` is taken in the universe
of `X`. This is a property of the topology only; theorems additionally equip `X` with its Borel
σ-algebra through Mathlib's `[MeasurableSpace X] [BorelSpace X]`. -/
class IsBorelSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_homeomorph_borel :
    ∃ (Z : Type u) (_ : MetricSpace Z) (_ : CompleteSpace Z)
      (_ : TopologicalSpace.SeparableSpace Z) (B : Set Z),
      MeasurableSet[borel Z] B ∧ Nonempty (X ≃ₜ B)

end BertsekasShreve.AnalyticSelection


