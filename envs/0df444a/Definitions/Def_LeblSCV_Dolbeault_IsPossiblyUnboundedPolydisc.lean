-- Prove2me | Definitions.Def_LeblSCV_Dolbeault_IsPossiblyUnboundedPolydisc
-- name    : LeblSCV_Dolbeault_IsPossiblyUnboundedPolydisc
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T20:09:59.885183+00:00
-- url     : https://prove2.me/theorems/f5dd518c-1b85-4341-8d56-032286055484
-- title:
--   Possibly unbounded polydisc
-- statement:
--   A **possibly unbounded polydisc** is a set $\Delta = D_1 \times \cdots \times D_n \subset \mathbb{C}^n$ where each $D_k$ is either a disc $\{|z_k - a_k| < \rho_k\}$ with $0<\rho_k<\infty$ or all of $\mathbb{C}$. In particular $\mathbb{C}^n$ itself is one.
--
--   **Formalization Note.** Radii are taken in `ℝ≥0∞` with $\rho_k = \infty$ standing for $D_k = \mathbb{C}$: $\Delta = \{z : \operatorname{edist}(z_k, a_k) < \rho_k \ \forall k\}$ with every $\rho_k > 0$. A sorry-free check shows that $\mathbb{C}^n$ qualifies.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 141 (definition before Theorem 4.4.5)

import Mathlib

open scoped ENNReal

namespace LeblSCV.Dolbeault

/-- A possibly unbounded polydisc (Lebl, p. 141): `Δ = D_1 × ⋯ × D_n ⊆ ℂⁿ` where each `D_k` is either
a disc `{|z_k - a_k| < ρ_k}` with `0 < ρ_k < ∞` or all of `ℂ`. Encoded with radii in `ℝ≥0∞`, the
radius `ρ_k = ∞` giving the factor `ℂ` (every `edist` in `ℂ` is finite). -/
def IsPossiblyUnboundedPolydisc {n : ℕ} (Δ : Set (Fin n → ℂ)) : Prop :=
  ∃ (a : Fin n → ℂ) (ρ : Fin n → ℝ≥0∞), (∀ k, 0 < ρ k) ∧
    Δ = {z | ∀ k : Fin n, edist (z k) (a k) < ρ k}

end LeblSCV.Dolbeault


