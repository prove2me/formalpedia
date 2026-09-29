-- Prove2me | Definitions.Def_Kawahira_dynamics
-- name    : Kawahira_dynamics
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T18:22:26.056543+00:00
-- url     : https://prove2.me/theorems/8991b33b-160b-41e9-bd86-e42132ddf144
-- title:
--   Fixed points, multipliers and the holomorphic index
-- statement:
--   This file fixes the vocabulary of one-dimensional complex dynamics used throughout the mission, following Sections 2 and 3 of Kawahira (2016).
--
--   For a function $g : \mathbb{C} \to \mathbb{C}$ the **nu function** is
--   $$\nu_g(z) \;=\; z - \frac{g(z)}{z\,g'(z)},$$
--   and the **Newton map** is
--   $$N_g(z) \;=\; z - \frac{g(z)}{g'(z)}.$$
--
--   A point $\alpha$ is a fixed point of $f$ when $f(\alpha) = \alpha$; its **multiplier** is $f'(\alpha)$, and the fixed point is called **attracting**, **indifferent** or **repelling** according to whether $|f'(\alpha)|$ is $< 1$, $= 1$ or $> 1$.
--
--   Finally, the **holomorphic index** (residue fixed point index) of $f$ at $\alpha$, computed on the circle of radius $r$ centred at $\alpha$, is
--   $$\iota_r(f,\alpha) \;=\; \frac{1}{2\pi i}\oint_{|z-\alpha| = r} \frac{dz}{z - f(z)}.$$
--   For all sufficiently small $r > 0$ this is independent of $r$ and equals the index of the fixed point; the radius is kept as an explicit argument so that the definition needs no analyticity hypothesis.
--
--   These notions are general: nothing about the zeta function enters here, and they are reusable for any study of fixed points of holomorphic maps.
--
--   **Formalization Note** The nu function and the Newton map are total functions $\mathbb{C} \to \mathbb{C}$; Lean's division returns $0$ when the denominator is $0$, so their values at the poles of the underlying meromorphic map are artefacts and every statement about them carries explicit guards. Derivatives are Mathlib's `deriv`, which returns $0$ at points of non-differentiability.
-- source:
--   Tomoki Kawahira, "The Riemann Hypothesis and Holomorphic Index in Complex Dynamics", Experimental Mathematics (2016), DOI: 10.1080/10586458.2016.1217443

import Mathlib

/-!
# Fixed points, multipliers and the holomorphic index

Basic vocabulary of one-dimensional complex dynamics, following
T. Kawahira, *The Riemann Hypothesis and Holomorphic Index in Complex Dynamics*,
Experimental Mathematics (2016), Sections 2 and 3.
-/

open scoped Topology

namespace Kawahira

/-- The **nu function** of `g`: `ν_g (z) = z - g z / (z * g' z)`.
Kawahira (2016), Section 3. -/
noncomputable def nu (g : ℂ → ℂ) (z : ℂ) : ℂ := z - g z / (z * deriv g z)

/-- The **Newton map** of `g`: `N_g (z) = z - g z / g' z`.
Kawahira (2016), Appendix A.1. -/
noncomputable def newton (g : ℂ → ℂ) (z : ℂ) : ℂ := z - g z / deriv g z

/-- `a` is an **attracting** fixed point of `f`: `f a = a` and the multiplier
`f' a` has modulus `< 1`. -/
def IsAttractingFixedPoint (f : ℂ → ℂ) (a : ℂ) : Prop := f a = a ∧ ‖deriv f a‖ < 1

/-- `a` is an **indifferent** fixed point of `f`: `f a = a` and the multiplier
`f' a` has modulus `= 1`. -/
def IsIndifferentFixedPoint (f : ℂ → ℂ) (a : ℂ) : Prop := f a = a ∧ ‖deriv f a‖ = 1

/-- `a` is a **repelling** fixed point of `f`: `f a = a` and the multiplier
`f' a` has modulus `> 1`. -/
def IsRepellingFixedPoint (f : ℂ → ℂ) (a : ℂ) : Prop := f a = a ∧ 1 < ‖deriv f a‖

/-- The **holomorphic index** (residue fixed point index) of `f` at `a`, computed on the
circle of radius `r` centred at `a`:
`ι(f, a) = (2πi)⁻¹ ∮_{|z - a| = r} dz / (z - f z)`.
Kawahira (2016), Section 2.3. -/
noncomputable def holomorphicIndex (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ * ∮ z in C(a, r), (z - f z)⁻¹

end Kawahira


