-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_jointEuclid
-- name    : RockafellianRelax_Supplement_jointEuclid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:15:20.996635+00:00
-- url     : https://prove2.me/theorems/3bd82c98-81eb-4335-8ea4-c0def718e193
-- title:
--   $\mathbb R^m\times\mathbb R^n$ as the Euclidean space $\mathbb R^{m+n}$
-- statement:
--   The bijection
--
--   $$
--   \mathbb R^m\times\mathbb R^n \cong \mathbb R^{m+n},\qquad (u,x)\mapsto (u_1,\dots,u_m,x_1,\dots,x_n)
--   $$
--
--   carries the pairing $\langle u,u'\rangle + \langle x,x'\rangle$ to the Euclidean inner product.
--
--   Subgradients and the tolerance distance of §5 are taken in this space.
--
--   **Formalization Note** The target is `EuclideanSpace ℝ (Fin m ⊕ Fin n)`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §5, p.24 (space of the subgradients), with §4.1, p.12 (Euclidean distance)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **`ℝᵐ × ℝⁿ` as the Euclidean space `ℝ^{m+n}`**, where the subgradients and the distance of §5
live. Royset, Chen & Eckstrand, arXiv:2204.04762v4, §5, p.24: subgradients "in the general sense of [51]" of `f : ℝᵐ × ℝⁿ → R̄`, and
"dist((yν, 0), ∂fν(uν, xν))", with the Euclidean `dist` of p.12.

**Formalization Note.** `(u, x)` goes to the vector on `Fin m ⊕ Fin n` with coordinates `u` then
`x`, so the inner product of the images is `⟨u, u'⟩ + ⟨x, x'⟩`. -/
noncomputable def jointEuclid {m n : ℕ} :
    (Fin m → ℝ) × (Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin m ⊕ Fin n) :=
  (Equiv.sumArrowEquivProdArrow (Fin m) (Fin n) ℝ).symm.trans (WithLp.equiv 2 _).symm

end RockafellianRelax.Supplement


