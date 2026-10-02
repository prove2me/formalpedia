-- Prove2me | Definitions.Def_LeblSCV_Bergman_bergmanSpace
-- name    : LeblSCV_Bergman_bergmanSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:30:27.107587+00:00
-- url     : https://prove2.me/theorems/73a37829-7595-4a04-bdd5-574658c23ae1
-- title:
--   The Bergman space $A^2(U) = \mathcal{O}(U) \cap L^2(U)$
-- statement:
--   Let $U \subset \mathbb{C}^n$ and let $dV$ be Lebesgue measure on $\mathbb{C}^n \cong \mathbb{R}^{2n}$. The space $L^2(U)$ consists of the measurable functions $f$ on $U$ with
--   $$\|f\|_{L^2(U)}^2 = \int_U |f(z)|^2 \, dV < \infty,$$
--   identified when they agree almost everywhere, with inner product $\langle f, g \rangle = \int_U f(z)\,\overline{g(z)}\, dV$. The **Bergman space** of $U$ is
--   $$A^2(U) = \mathcal{O}(U) \cap L^2(U),$$
--   the classes in $L^2(U)$ that contain a function holomorphic on $U$. It is a complex linear subspace of $L^2(U)$ and carries the $L^2(U)$ norm $\|f\|_{A^2(U)} = \|f\|_{L^2(U)}$ and inner product.
--
--   The Bergman space is the Hilbert space on which the Bergman kernel is built (Lemma 5.2.1 shows it is closed in $L^2(U)$).
--
--   **Formalization Note.** $\mathbb{C}^n$ is `Fin n → ℂ` with its product Lebesgue measure `volume`; $L^2(U)$ is `Lp ℂ 2 (volume.restrict U)`, and $A^2(U)$ is the `Submodule ℂ` of those elements that are almost everywhere on $U$ equal to a function that is `DifferentiableOn ℂ` on $U$. For open $U$, `DifferentiableOn ℂ` is the book's Definition 1.1.2 (holomorphic), by Osgood's lemma (Proposition 1.1.3 and Theorem 1.2.1). Mathlib's `L²` inner product is conjugate-linear in the first slot, $\langle\!\langle f, g\rangle\!\rangle = \int_U \overline{f}\, g\, dV$, i.e. the book's $\langle g, f\rangle$; only orthonormality uses it in this mission, and orthonormality does not depend on the convention.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), p. 160 (definition of the Bergman space)

import Mathlib

open MeasureTheory

namespace LeblSCV.Bergman

/-- The Bergman space `A²(U) = 𝒪(U) ∩ L²(U)` of a set `U ⊆ ℂⁿ` (Lebl, p. 160): the elements of
`L²(U) = Lp ℂ 2 (volume.restrict U)` (square-integrable functions on `U` for the Lebesgue measure
`dV` on `ℂⁿ ≅ ℝ²ⁿ`, modulo equality almost everywhere) that have a representative which is
holomorphic (`DifferentiableOn ℂ`) on `U`. It carries the `L²(U)` norm and inner product. -/
noncomputable def bergmanSpace {n : ℕ} (U : Set (Fin n → ℂ)) :
    Submodule ℂ (Lp ℂ 2 (volume.restrict U)) where
  carrier := {f | ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g U ∧
    (f : (Fin n → ℂ) → ℂ) =ᵐ[volume.restrict U] g}
  zero_mem' := ⟨0, differentiableOn_const 0, Lp.coeFn_zero _ _ _⟩
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    exact ⟨g₁ + g₂, hg₁.add hg₂, (Lp.coeFn_add f₁ f₂).trans (h₁.add h₂)⟩
  smul_mem' := by
    rintro c f ⟨g, hg, h⟩
    exact ⟨c • g, hg.const_smul c, (Lp.coeFn_smul c f).trans (h.const_smul c)⟩

end LeblSCV.Bergman


