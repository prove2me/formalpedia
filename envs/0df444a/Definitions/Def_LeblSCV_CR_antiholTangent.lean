-- Prove2me | Definitions.Def_LeblSCV_CR_antiholTangent
-- name    : LeblSCV_CR_antiholTangent
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:10:30.906983+00:00
-- url     : https://prove2.me/theorems/4f7e3d1c-a1c4-430e-9c99-5412da9a2109
-- title:
--   The space $T^{(0,1)}_p M$ of antiholomorphic tangent vectors of a hypersurface
-- statement:
--   Write $z_\ell = x_\ell + i y_\ell$. The **Wirtinger derivative** of a real-differentiable $g : \mathbb{C}^n \to \mathbb{C}$ is
--   $$\frac{\partial g}{\partial \bar z_\ell} = \frac{1}{2}\left( \frac{\partial g}{\partial x_\ell} + i \frac{\partial g}{\partial y_\ell} \right).$$
--   Let $M$ be a smooth real hypersurface, $p \in M$ and $r$ a real defining function of $M$ at $p$. A complex tangent vector $X_p = \sum_k (a_k \partial/\partial z_k|_p + b_k \partial/\partial \bar z_k|_p)$ lies in $\mathbb{C}T_pM$ when $X_p r = 0$. The space of **antiholomorphic tangent vectors** of $M$ at $p$ is
--   $$T^{(0,1)}_p M = \mathbb{C}T_pM \cap T^{(0,1)}_p\mathbb{C}^n = \left\{ \sum_{k=1}^n a_k \frac{\partial}{\partial \bar z_k}\Big|_p \;:\; \sum_{k=1}^n a_k \frac{\partial r}{\partial \bar z_k}(p) = 0 \right\}.$$
--   CR functions are defined by being annihilated by these vectors.
--
--   **Formalization Note.** A vector $\sum a_k \partial/\partial\bar z_k|_p$ is identified with its coefficient vector $a \in \mathbb{C}^n$ (`Fin n → ℂ`, 0-based indices); `antiholTangent r p` is the complex subspace of those $a$ with $\sum_k a_k\, \partial r/\partial \bar z_k(p) = 0$. The real partials are `fderiv ℝ g z` applied to $e_\ell$ and $i e_\ell$. The file also defines `wirtingerZbar`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 63–64 (T^(0,1)_p ℂ^n and T^(0,1)_p M)

import Mathlib

namespace LeblSCV.CR

/-- Wirtinger derivative `∂g/∂z̄_ℓ = ½ (∂g/∂x_ℓ + i ∂g/∂y_ℓ)` at `z`, where `z_ℓ = x_ℓ + i y_ℓ`
(Lebl, §1.1). The real partials are the real Fréchet derivative in the directions `e_ℓ` and
`i e_ℓ`. -/
noncomputable def wirtingerZbar {n : ℕ} (g : (Fin n → ℂ) → ℂ) (l : Fin n) (z : Fin n → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ g z (Pi.single l 1) + Complex.I * fderiv ℝ g z (Pi.single l Complex.I))

/-- `T_p^{(0,1)} M = ℂT_pM ∩ T_p^{(0,1)} ℂⁿ` (Lebl, p. 64), computed from a real defining function
`r` of `M` at `p`: the coefficient vectors `a` of the antiholomorphic vectors
`X_p = ∑ a_k ∂/∂z̄_k|_p` with `X_p r = ∑ a_k ∂r/∂z̄_k(p) = 0`. -/
noncomputable def antiholTangent {n : ℕ} (r : (Fin n → ℂ) → ℝ) (p : Fin n → ℂ) :
    Submodule ℂ (Fin n → ℂ) where
  carrier := {a | ∑ k, a k * wirtingerZbar (fun z => (r z : ℂ)) k p = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, mul_assoc] at *
    rw [← Finset.mul_sum, ha, mul_zero]

end LeblSCV.CR


