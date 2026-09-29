-- Prove2me | Definitions.Def_opg434_weak_pentagon
-- name    : opg434_weak_pentagon
-- status  : Definition
-- author  : @hao jia
-- created : 2026-09-08T05:04:22.665576+00:00
-- url     : https://prove2.me/theorems/29f1ea7e-0284-49cf-82f8-8367429e26c2
-- title:
--   Weak-pentagon edge labels, odd cycles, and the sixteen-vertex target
-- statement:
--   This module defines a symmetric five-label assignment on graph edges; values on nonedges are irrelevant. The assignment is weak-pentagon when deleting each one color class leaves a bipartite spanning graph. Properness and surjectivity are not required.
--
--   Simple cycles are cyclic lists of at least three distinct vertices and need not be induced. A color meets every odd cycle when some cyclically consecutive edge of each simple odd cycle has that color.
--
--   The module also fixes an explicit sixteen-vertex homomorphism target. Its vertices are the four-bit vectors, and two labels are related when their Hamming distance is exactly three or four. This is the four-bit model of the Clebsch graph used by the existence reformulation.
-- source:
--   Robert Samal, Weak pentagon problem, Open Problem Garden, https://www.openproblemgarden.org/op/weak_pentagon_problem; target model compared with DeVos--Samal, arXiv:math/0602580v2, Observation 3.1

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card

namespace OPG434

universe u

/-- A symmetric edge labeling. Values away from graph edges are irrelevant. -/
structure EdgeColoring {V : Type u} (G : SimpleGraph V) (K : Type*) where
  color : V → V → K
  color_symm : ∀ ⦃u v : V⦄, G.Adj u v → color u v = color v u

/-- The graph is finite, triangle-free, and every vertex has exactly three
neighbors. -/
def IsTriangleFreeCubic {V : Type u} (G : SimpleGraph V) : Prop :=
  (∀ ⦃a b c : V⦄, G.Adj a b → G.Adj b c → ¬ G.Adj c a) ∧
  ∀ v : V, (G.neighborSet v).encard = 3

/-- After deleting one color class, the remaining spanning graph is
bipartite, witnessed by a Boolean side assignment. -/
def ComplementOfColorIsBipartite {V : Type u} {G : SimpleGraph V}
    (c : EdgeColoring G (Fin 5)) (i : Fin 5) : Prop :=
  ∃ side : V → Bool,
    ∀ ⦃u v : V⦄, G.Adj u v → c.color u v ≠ i → side u ≠ side v

/-- The weak-pentagon five-color condition. No properness or surjectivity is
required. -/
def IsWeakPentagonColoring {V : Type u} {G : SimpleGraph V}
    (c : EdgeColoring G (Fin 5)) : Prop :=
  ∀ i : Fin 5, ComplementOfColorIsBipartite c i

def HasWeakPentagonColoring {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ c : EdgeColoring G (Fin 5), IsWeakPentagonColoring c

/-- A simple cycle encoded by a nonempty cyclic list of distinct vertices. -/
def IsCycleList {V : Type u} (G : SimpleGraph V) (vs : List V) : Prop :=
  ∃ x y : V, ∃ middle : List V,
    vs = x :: (middle ++ [y]) ∧ 3 ≤ vs.length ∧
    vs.Nodup ∧ vs.Chain' G.Adj ∧ G.Adj y x

/-- Two vertices occur consecutively in the cyclic order of `vs`. -/
def ConsecutiveInCycle {V : Type u} (vs : List V) (x y : V) : Prop :=
  (∃ before after : List V, vs = before ++ x :: y :: after) ∨
  (vs.head? = some y ∧ vs.getLast? = some x)

/-- Color `i` meets every simple odd cycle of `G`. -/
def ColorMeetsEveryOddCycle {V : Type u} {G : SimpleGraph V}
    (c : EdgeColoring G (Fin 5)) (i : Fin 5) : Prop :=
  ∀ vs : List V, IsCycleList G vs → (∃ m : ℕ, vs.length = 2 * m + 1) →
    ∃ x y : V, ConsecutiveInCycle vs x y ∧ c.color x y = i

/-- Four-bit labels; this type has sixteen elements. -/
abbrev Bit4 := Fin 4 → Bool

def hammingDistance (x y : Bit4) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/-- The explicit sixteen-vertex target relation: Hamming distance three or
four. It is an even-coordinate model of the Clebsch graph. -/
def HasClebsch16Homomorphism {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ f : V → Bit4,
    ∀ ⦃u v : V⦄, G.Adj u v →
      hammingDistance (f u) (f v) = 3 ∨ hammingDistance (f u) (f v) = 4

end OPG434


