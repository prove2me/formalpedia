-- Prove2me | Definitions.Def_LeblSCV_BallPolydisc_IsCircularDomain
-- name    : LeblSCV_BallPolydisc_IsCircularDomain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:18:38.917344+00:00
-- url     : https://prove2.me/theorems/fe0da776-5bdc-46af-9c25-1956d1fe145f
-- title:
--   Circular domain
-- statement:
--   A **circular domain** is a domain (a nonempty connected open set) $U \subset \mathbb{C}^n$ such that
--   $$z \in U \implies e^{i\theta} z \in U \quad \text{for all } \theta \in \mathbb{R}.$$
--   The unit ball $\mathbb{B}_n$ and every polydisc centred at the origin are circular domains.
--
--   **Formalization Note.** A domain is `IsOpen U ∧ IsConnected U` (Mathlib's `IsConnected` includes nonemptiness, matching the book's convention on p. 6). The rotation is `Complex.exp (θ * I) • z`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 39 (definition preceding Corollary 1.5.2)

import Mathlib

namespace LeblSCV.BallPolydisc

/-- A circular domain (Lebl, p. 39): a domain (nonempty connected open set) `U ⊆ ℂⁿ` such that
`z ∈ U` implies `e^{iθ} z ∈ U` for all `θ ∈ ℝ`. -/
def IsCircularDomain {n : ℕ} (U : Set (Fin n → ℂ)) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ z ∈ U, ∀ θ : ℝ, Complex.exp ((θ : ℂ) * Complex.I) • z ∈ U

end LeblSCV.BallPolydisc


