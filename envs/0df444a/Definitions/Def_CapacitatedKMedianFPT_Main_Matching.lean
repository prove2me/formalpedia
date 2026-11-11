-- Prove2me | Definitions.Def_CapacitatedKMedianFPT_Main_Matching
-- name    : CapacitatedKMedianFPT_Main_Matching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:23.877736+00:00
-- url     : https://prove2.me/theorems/f0ef2c89-1213-46be-89f3-ff70e20f8d61
-- title:
--   Maximum-weight matchings that use only a given set of right vertices
-- statement:
--   Let $G$ be a bipartite graph with finite vertex sets $L$ (left) and $R$ (right), edge set $E\subseteq L\times R$ and edge weights $w:L\times R\to\mathbb R$ of any sign. A **matching using only $X\subseteq R$** assigns to each left vertex at most one right vertex of $X$ along an edge, with no right vertex used twice; its weight is the sum of the weights of the matched edges. For $X\subseteq R$,
--   $$u(X)=\max\{\text{weight of a matching using only }X\},$$
--   a maximum over a finite nonempty set (the empty matching has weight $0$).
--
--   This is the function of Theorem 5 (Shapley).
--
--   **Formalization Note** A matching is a map $L\to R\cup\{\text{none}\}$ that is injective on its matched vertices.
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 13, Theorem 5

import Mathlib

set_option autoImplicit false

/-!
# Maximum-weight matchings restricted to a set of right vertices (Theorem 5)

Anand–Huang–Jaiswal–Kumar–Lee–Yadav, STOC 2027 submission #1646, §4, p. 13.
-/

namespace CapacitatedKMedianFPT.Main

open scoped BigOperators

noncomputable section

variable {L R : Type} [Fintype L]

/-- `M` is a matching of the bipartite graph with edge relation `E` (left side `L`, right side
`R`) that matches only right vertices in `X`: every left vertex is matched to at most one right
vertex (`M l = some r`), along an edge, into `X`, and no right vertex is matched twice. -/
def IsMatchingWithin (E : L → R → Prop) (X : Finset R) (M : L → Option R) : Prop :=
  (∀ l r, M l = some r → E l r ∧ r ∈ X) ∧ ∀ l₁ l₂ r, M l₁ = some r → M l₂ = some r → l₁ = l₂

/-- The weight of a matching, for edge weights `w` (of any sign). -/
def matchingWeight (w : L → R → ℝ) (M : L → Option R) : ℝ :=
  ∑ l, (match M l with
    | some r => w l r
    | none => 0)

/-- `u(X)`: the maximum weight of a matching that matches only right vertices in `X` (a maximum
over a finite nonempty set when `R` is finite; the empty matching is admissible). -/
def maxMatchingWeight (E : L → R → Prop) (w : L → R → ℝ) (X : Finset R) : ℝ :=
  sSup {x : ℝ | ∃ M : L → Option R, IsMatchingWithin E X M ∧ x = matchingWeight w M}

end

end CapacitatedKMedianFPT.Main


