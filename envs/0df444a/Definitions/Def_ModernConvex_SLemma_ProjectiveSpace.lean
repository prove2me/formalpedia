-- Prove2me | Definitions.Def_ModernConvex_SLemma_ProjectiveSpace
-- name    : ModernConvex_SLemma_ProjectiveSpace
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:14.611809+00:00
-- url     : https://prove2.me/theorems/4bdb381d-5871-4144-8349-a77254cc43db
-- title:
--   Projective space Pⁿ⁻¹ as the unit sphere modulo ±, and the canonical projection Φ
-- statement:
--   This file fixes the projective space and its canonical projection used in §4.10.5 of Ben-Tal–Nemirovski (p. 308).
--
--   Let $S^{n-1} = \{e \in \mathbb R^n : \|e\|_2 = 1\}$ be the unit Euclidean sphere. A point of the **projective space** $P^{n-1}$ is a line through the origin of $\mathbb R^n$; such a line meets $S^{n-1}$ in exactly two antipodal points $\pm e$. Accordingly, $P^{n-1}$ is the quotient of $S^{n-1}$ by the equivalence relation
--   $$e \sim e' \iff e' = e \ \text{ or } \ e' = -e,$$
--   and the **canonical projection** $\Phi : S^{n-1} \to P^{n-1}$ maps a unit vector $e$ to its class, i.e. to the line spanned by $e$. In particular $\Phi(e) = \Phi(-e)$.
--
--   These are the objects of Propositions 4.10.2 and 4.10.4, the topological steps of the proof of Polyak's convexity theorem (SL.D).
--
--   **Formalization Note** The sphere is `Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1` with Mathlib's negation on it. `ProjSpace n` is the book's $P^{n-1}$ (the book writes $P^n$ for lines in $\mathbb R^{n+1}$; here the index is that of the ambient space $\mathbb R^n$). It carries the quotient topology. The book instead puts the metric $d(\Phi(e), \Phi(e')) = \min\{\|e+e'\|_2, \|e-e'\|_2\}$ on $P^{n-1}$. The two topologies coincide: $\Phi$ is a continuous surjection from a compact space onto a Hausdorff space for that metric, so it is a quotient map. Only topological notions (connectedness, continuous curves) are used with this space, so the choice does not change any statement.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 308 (projective space Pⁿ, its metric and the canonical projection)

import Mathlib

namespace ModernConvex.SLemma

/-- The antipodal identification on the unit Euclidean sphere `Sⁿ⁻¹ ⊂ ℝⁿ`: two unit vectors are
identified when they span the same line through the origin, i.e. `e' = e` or `e' = -e`
(Ben-Tal–Nemirovski, p. 308). -/
def antipodalSetoid (n : ℕ) : Setoid (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) where
  r x y := x = y ∨ x = -y
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun {x y} h => by
        rcases h with h | h
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h, neg_neg])
      trans := fun {x y z} h₁ h₂ => by
        rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
        · exact Or.inl (h₁.trans h₂)
        · exact Or.inr (h₁.trans h₂)
        · exact Or.inr (by rw [h₁, h₂])
        · exact Or.inl (by rw [h₁, h₂, neg_neg]) }

/-- The projective space `Pⁿ⁻¹` of lines through the origin of `ℝⁿ` (p. 308), realised as the
unit sphere `Sⁿ⁻¹` modulo `e ∼ -e`, with the quotient topology. -/
abbrev ProjSpace (n : ℕ) : Type := Quotient (antipodalSetoid n)

/-- The canonical projection `Φ : Sⁿ⁻¹ → Pⁿ⁻¹`, mapping a unit vector `e` to the line it spans
(p. 308). -/
def canonicalProjection (n : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ProjSpace n :=
  Quotient.mk (antipodalSetoid n)

end ModernConvex.SLemma


