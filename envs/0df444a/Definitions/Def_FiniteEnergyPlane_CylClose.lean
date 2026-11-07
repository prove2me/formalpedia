-- Prove2me | Definitions.Def_FiniteEnergyPlane_CylClose
-- name    : FiniteEnergyPlane_CylClose
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-06T11:23:16.560247+00:00
-- url     : https://prove2.me/theorems/d647acc6-0ba0-463b-9ca1-5322bdf49409
-- title:
--   Uniform closeness of planes in cylindrical scale
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$ be a strictly star-shaped level, so that the symplectization $\mathbb{R} \times S$ is $V_1 \setminus \{0\}$ with $y = e^{2a(y)}\,\mathrm{proj}(y)$. For maps $f, u : \mathbb{C} \to V_1$ and $\varepsilon \in \mathbb{R}$, the predicate `IsCylCloseTo H ε f u` says that at every $z \in \mathbb{C}$:
--
--   $$|a(f(z)) - a(u(z))| \le \varepsilon, \qquad \|\mathrm{proj}(f(z)) - \mathrm{proj}(u(z))\| \le \varepsilon,$$
--
--   $$(1 + \|z\|)\Big(\|D(a \circ f)(z) - D(a \circ u)(z)\| + \|D(\mathrm{proj} \circ f)(z) - D(\mathrm{proj} \circ u)(z)\|\Big) \le \varepsilon.$$
--
--   The weight $1 + \|z\|$ is the scale of the cylindrical coordinates $z = e^{2\pi(s + it)}$ at $\infty$, in which first derivatives are multiplied by $2\pi\|z\|$. The notion is therefore a uniform $C^1$ closeness over the whole plane, including near $\infty$. It compares only the components $a$ and $\mathrm{proj}$, so the derivative terms and the $\mathrm{proj}$ term do not change when $f$ is translated in the $\mathbb{R}$-direction, and the $a$ term changes by at most the size of the translation.
-- source:
--   Scale of cylindrical coordinates at infinity as in U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6.3

import Definitions.Def_FiniteEnergyPlane_Fredholm

/-!
# Uniform closeness of planes in cylindrical scale

In the setting of `FiniteEnergyPlane_Setting`, a plane `u : ℂ → V 1` has symplectization components
`aCoord H ∘ u` and `proj H ∘ u`. Cylindrical coordinates `z = e^{2π(s + it)}` at `∞` scale first
derivatives by `2π‖z‖`, so uniform `C¹` closeness over the whole plane, invariant under the
translations `shiftA`, compares derivatives with the weight `1 + ‖z‖`.
-/

namespace FiniteEnergyPlane

noncomputable section

/-- `f` is `ε`-close to `u` in the uniform `C¹` sense of the symplectization, in cylindrical scale
at `∞`: at every `z`, the coordinates `aCoord H` and `proj H` of `f` and `u` differ by at most `ε`,
and `(1 + ‖z‖)` times the sum of the norms of the differences of their first derivatives is at most
`ε`. -/
def IsCylCloseTo (H : V 1 → ℝ) (ε : ℝ) (f u : ℂ → V 1) : Prop :=
  ∀ z : ℂ, |aCoord H (f z) - aCoord H (u z)| ≤ ε ∧ ‖proj H (f z) - proj H (u z)‖ ≤ ε ∧
    (1 + ‖z‖) * (‖fderiv ℝ (fun w => aCoord H (f w)) z - fderiv ℝ (fun w => aCoord H (u w)) z‖ +
      ‖fderiv ℝ (fun w => proj H (f w)) z - fderiv ℝ (fun w => proj H (u w)) z‖) ≤ ε

end

end FiniteEnergyPlane


