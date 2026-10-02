-- Prove2me | Definitions.Def_LeblSCV_Pseudoconvex_IsDomainOfHolomorphy
-- name    : LeblSCV_Pseudoconvex_IsDomainOfHolomorphy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T04:56:41.610981+00:00
-- url     : https://prove2.me/theorems/3cab307a-afd0-4d91-a53b-d6f43b368dc9
-- title:
--   Definition 2.1.1 — domain of holomorphy
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain (connected open set). $U$ is a **domain of holomorphy** if there do not exist nonempty open sets $V$ and $W$ with the following properties: $V \subset U \cap W$, $W \not\subset U$, $W$ is connected, and for every $f \in \mathcal{O}(U)$ there exists $F \in \mathcal{O}(W)$ with
--   $$f(z) = F(z) \quad \text{for all } z \in V.$$
--
--   Informally, no holomorphic function on $U$ extends across any part of the boundary.
--
--   **Formalization Note.** **Formalization Note.** $\mathbb{C}^n$ is `EuclideanSpace ℂ (Fin n)`, so its norm, balls and distances are Euclidean, as in the book. Holomorphic on an open set is `DifferentiableOn ℂ`, which is equivalent to the book's Definition 1.1.2 on open sets (Proposition 1.1.3 and Theorem 1.2.1). The definition is restated in this mission's namespace, because a draft cannot import another chapter's draft; chapter III (`LeblSCV.Levi`) has the same shape on `Fin n → ℂ`. Nonemptiness of $W$ follows from $W \not\subset U$.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 47, Definition 2.1.1

import Mathlib

namespace LeblSCV.Pseudoconvex

/-- Definition 2.1.1 (Lebl, p. 47). A domain `U ⊆ ℂⁿ` (connected open set) is a *domain of
holomorphy* if there do not exist nonempty open sets `V`, `W` with `V ⊆ U ∩ W`, `W ⊄ U` and
`W` connected, such that for every `f ∈ 𝒪(U)` there exists an `F ∈ 𝒪(W)` with `f = F` on `V`.
Holomorphic on an open set is `DifferentiableOn ℂ`. -/
def IsDomainOfHolomorphy {n : ℕ} (U : Set (EuclideanSpace ℂ (Fin n))) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ¬ ∃ V W : Set (EuclideanSpace ℂ (Fin n)), IsOpen V ∧ V.Nonempty ∧ IsOpen W ∧ IsConnected W ∧
        V ⊆ U ∩ W ∧ ¬ W ⊆ U ∧
        ∀ f : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ f U →
          ∃ F : EuclideanSpace ℂ (Fin n) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ V, f z = F z

end LeblSCV.Pseudoconvex


