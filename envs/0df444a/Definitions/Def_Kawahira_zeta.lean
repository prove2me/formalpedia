-- Prove2me | Definitions.Def_Kawahira_zeta
-- name    : Kawahira_zeta
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T18:27:02.930527+00:00
-- url     : https://prove2.me/theorems/bdf00224-6a98-4591-8d54-a7d6ed1dc152
-- title:
--   The nu functions $\nu_\zeta$, $\nu_\xi$ and the non-trivial zeros
-- statement:
--   This file specializes the dynamical vocabulary to the Riemann zeta function, following Sections 1, 4 and 4.4 of Kawahira (2016).
--
--   A complex number $s$ is a **non-trivial zero** of $\zeta$ when $\zeta(s) = 0$ and $s$ is none of the trivial zeros $-2, -4, -6, \dots$. Nothing about the critical strip is built into this definition.
--
--   The two dynamical systems of the paper are
--   $$\nu_\zeta(z) = z - \frac{\zeta(z)}{z\,\zeta'(z)}, \qquad \nu_\xi(z) = z - \frac{\xi(z)}{z\,\xi'(z)},$$
--   where $\xi$ is the Riemann xi function in Kawahira's normalization
--   $$\xi(z) \;=\; \tfrac{1}{2}\,z(1-z)\,\pi^{-z/2}\,\Gamma(z/2)\,\zeta(z),$$
--   an entire function whose zeros are exactly the non-trivial zeros of $\zeta$, with the same orders, and which satisfies $\xi(z) = \xi(1-z)$.
--
--   Two facts are proved here: that the definition of $\xi$ used in the file agrees with $\tfrac{1}{2}z(1-z)\Lambda(z)$ away from $z = 0$ and $z = 1$, where $\Lambda(z) = \pi^{-z/2}\Gamma(z/2)\zeta(z)$ is the completed zeta function; and that $\xi$ is entire.
--
--   **Formalization Note** $\Lambda$ has poles at $z = 0$ and $z = 1$, at which Mathlib's total function takes artefactual values, so $\xi$ is defined instead through Mathlib's entire $\Lambda_0$, with $\Lambda(z) = \Lambda_0(z) - 1/z - 1/(1-z)$; the algebraic identity $z(1-z)\Lambda(z) = z(1-z)\Lambda_0(z) - 1$ makes the two agree off $\{0,1\}$ while keeping the Lean function entire. The sign convention is Kawahira's $z(1-z)$, which is the negative of the more common $z(z-1)$; this does not affect zeros, orders, or the nu function.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Definitions.Def_Kawahira_dynamics

/-!
# The nu functions of the Riemann zeta and xi functions

Following T. Kawahira, *The Riemann Hypothesis and Holomorphic Index in Complex Dynamics*,
Experimental Mathematics (2016), Sections 1, 4 and 4.4.
-/

namespace Kawahira

/-- A **non-trivial zero** of the Riemann zeta function: a zero of `ζ` which is not one of
the trivial zeros `-2, -4, -6, …`. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ∀ n : ℕ, s ≠ -2 * (n + 1)

/-- The nu function of the Riemann zeta function, `ν_ζ (z) = z - ζ z / (z ζ' z)`. -/
noncomputable def nuZeta : ℂ → ℂ := nu riemannZeta

/-- The Riemann xi function in Kawahira's normalisation,
`ξ(z) = (1/2) z (1 - z) π^{-z/2} Γ(z/2) ζ(z)`, written here through the entire function
`Λ₀` so that the Lean definition is entire and has no removable singularities at `z = 0, 1`. -/
noncomputable def xi (z : ℂ) : ℂ := (z * (1 - z) * completedRiemannZeta₀ z - 1) / 2

/-- The nu function of the Riemann xi function, `ν_ξ (z) = z - ξ z / (z ξ' z)`. -/
noncomputable def nuXi : ℂ → ℂ := nu xi

/-- `ξ` agrees with `(1/2) z (1 - z) Λ(z)`, where `Λ(z) = π^{-z/2} Γ(z/2) ζ(z)` is the
completed zeta function, away from the two poles `z = 0` and `z = 1` of `Λ`. -/
theorem xi_eq_completed (z : ℂ) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    xi z = z * (1 - z) / 2 * completedRiemannZeta z := by
  have h1' : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [xi, completedRiemannZeta_eq]
  field_simp
  ring

/-- `ξ` is entire. -/
theorem differentiable_xi : Differentiable ℂ xi := by
  have h : Differentiable ℂ fun z : ℂ => z * (1 - z) * completedRiemannZeta₀ z - 1 :=
    ((differentiable_id.mul ((differentiable_const 1).sub differentiable_id)).mul
      differentiable_completedZeta₀).sub (differentiable_const 1)
  exact h.div_const 2

end Kawahira


