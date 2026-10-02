-- Prove2me | Definitions.Def_LeblSCV_Shared_IsDomainOfHolomorphy
-- name    : LeblSCV_Shared_IsDomainOfHolomorphy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:41:11.393349+00:00
-- url     : https://prove2.me/theorems/b6ca37f2-224a-4b97-a14a-c2919ecb8570
-- title:
--   Definition 2.1.1 — domain of holomorphy
-- statement:
--   Let $U \subset \mathbb{C}^n$ be a domain (a nonempty connected open set). $U$ is a **domain of holomorphy** if there do not exist nonempty open sets $V$ and $W$, with $V \subset U \cap W$, $W \not\subset U$ and $W$ connected, such that for every $f \in \mathcal{O}(U)$ there is an $F \in \mathcal{O}(W)$ with
--   $$f(z) = F(z) \quad \text{for all } z \in V.$$
--
--   It serves chunk III (the tomato can principle, Theorem 2.3.11, p. 75, whose consequence is that a domain that is not pseudoconvex at a boundary point is not a domain of holomorphy) and chunk VII (Theorem 4.5.6, p. 149: vanishing of $H^{(0,q)}$ for $1 \le q \le n-1$ implies domain of holomorphy).
--
--   **Formalization Note.** `IsDomainOfHolomorphy U` includes `IsOpen U ∧ IsConnected U` (Mathlib's `IsConnected` includes nonemptiness). $\mathcal{O}(U)$ is the set of `f : (Fin n → ℂ) → ℂ` with `DifferentiableOn ℂ f U`. Values of `f` off `U` are irrelevant.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 47, Definition 2.1.1

import Mathlib

namespace LeblSCV.Shared

/-- Definition 2.1.1 (Lebl, p. 47). A domain `U ⊆ ℂⁿ` (connected open set) is a *domain of
holomorphy* if there do not exist nonempty open sets `V`, `W` with `V ⊆ U ∩ W`, `W ⊄ U` and
`W` connected, such that every `f ∈ 𝒪(U)` agrees on `V` with some `F ∈ 𝒪(W)`. Holomorphic on
an open set is `DifferentiableOn ℂ`. -/
def IsDomainOfHolomorphy {n : ℕ} (U : Set (Fin n → ℂ)) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ¬ ∃ V W : Set (Fin n → ℂ), IsOpen V ∧ V.Nonempty ∧ IsOpen W ∧ IsConnected W ∧
        V ⊆ U ∩ W ∧ ¬ W ⊆ U ∧
        ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f U →
          ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧ ∀ z ∈ V, f z = F z

end LeblSCV.Shared


