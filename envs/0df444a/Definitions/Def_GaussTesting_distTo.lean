-- Prove2me | Definitions.Def_GaussTesting_distTo
-- name    : GaussTesting_distTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:58:35.029996+00:00
-- url     : https://prove2.me/theorems/c3624c65-60b1-4f48-8319-d6bed4a30d2d
-- title:
--   Trace distance of pure states and distance to a class, $\mathrm{dist}(\psi,\mathcal C)$
-- statement:
--   For unit vectors $|\psi\rangle,|\phi\rangle$ the trace distance of the corresponding pure states is
--
--   $$
--   \mathrm{dist}(\psi,\phi)=\sqrt{1-|\langle\psi|\phi\rangle|^2},
--   $$
--
--   and the distance of $\psi$ to a class $\mathcal C$ of pure states is $\mathrm{dist}(\psi,\mathcal C)=\inf_{\phi\in\mathcal C}\mathrm{dist}(\psi,\phi)$ (3.1).
--
--   **Formalization Note** Lean's infimum of the empty set is $0$; every class of the mission contains the vacuum, and the generic theorems assume $\mathcal C$ nonempty as the paper does.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §2 (Notation), p.12; eq. (3.1), p.21

import Definitions.Def_GaussTesting_Ell2

namespace GaussTesting

/-- The trace distance of two pure states, `dist(ψ, ϕ) = √(1 − |⟨ψ|ϕ⟩|²)`. -/
noncomputable def pdist {α : Type*} (ψ φ : Ell2 α) : ℝ := Real.sqrt (1 - ‖inner ℂ φ ψ‖ ^ 2)

/-- The distance of a pure state to a class of pure states, `dist(ψ, 𝒞) = inf_{ϕ ∈ 𝒞} dist(ψ, ϕ)`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §2 "Notation", p.12 ("For pure states `|ψ⟩` … `dist(ψ, ϕ) = √(1 − |⟨ψ|ϕ⟩|²)`"),
eq. (3.1), p.21.

**Formalization Note.** States are unit vectors (`‖ψ‖ = 1`), so `|⟨ψ|ϕ⟩| ≤ 1` and the square root has a
nonnegative argument. `sInf` over the empty set is `0` in Lean; every class of this mission contains
the vacuum, and the generic theorems assume `𝒞` nonempty, as the paper does. -/
noncomputable def distTo {α : Type*} (ψ : Ell2 α) (C : Set (Ell2 α)) : ℝ := sInf (pdist ψ '' C)

end GaussTesting


