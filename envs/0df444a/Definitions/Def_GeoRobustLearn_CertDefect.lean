-- Prove2me | Definitions.Def_GeoRobustLearn_CertDefect
-- name    : GeoRobustLearn_CertDefect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:07.322331+00:00
-- url     : https://prove2.me/theorems/fcd27379-4015-41f7-95ec-7ed29a928d76
-- title:
--   Spatial gradient, offset derivative, certificate defect $\mathrm{def}_F$ and $T_s$ of a nonnegative function
-- statement:
--   For a differentiable $F:\mathbb R^d\times\mathbb R\to\mathbb R$ write $\nabla_xF$ for its gradient in the spatial variables and $\partial_aF$ for its derivative in the offset variable. The **certificate defect** is
--
--   $$\mathrm{def}_F(y,a)=\max\{0,\ \|\nabla_xF(y,a)\|_2-\partial_aF(y,a)\}.$$
--
--   It measures by how much $\partial_aF$ fails to dominate $\|\nabla_xF\|_2$; when it vanishes, the offset acts as a budget that pays for spatial displacement. For $s>0$, with $\rho_s=e^{-s}$ and $\sigma_s=\sqrt{1-e^{-2s}}$, and a nonnegative $g$ on $\mathbb R^n$,
--
--   $$(T_sg)(z)=\mathbb E_{w\sim\gamma_n}\,g(\rho_sz+\sigma_sw)\in[0,\infty].$$
--
--   **Formalization Note** Derivatives are Fréchet derivatives; Mathlib sets them to $0$ where a function is not differentiable, so every statement using them concerns a polynomial or asserts differentiability. $T_s$ of a nonnegative function is a lower Lebesgue integral with values in $[0,\infty]$, so it never takes a junk value.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), §4, p.15; §5.1, p.22; §3.3, p.14

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# Spatial gradient, offset derivative, certificate defect, and `T_s` of a nonnegative function

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…): §4 (p.15), §5.1 (p.22), §3.3 (p.14).

**Formalization Note.** On `Space (d+1)` the offset is the last coordinate. Derivatives are
Fréchet derivatives (`fderiv`), which Mathlib sets to `0` where the function is not differentiable;
every statement that uses them either concerns a polynomial (everywhere differentiable) or asserts
differentiability. `ouLin s g` is `T_s g` for a nonnegative `g`, computed as a lower Lebesgue
integral in `ℝ≥0∞`, so it never takes a junk value.
-/

/-- The offset derivative `∂_a F(z)`. -/
noncomputable def offsetDeriv {d : ℕ} (F : Space (d+1) → ℝ) (z : Space (d+1)) : ℝ :=
  fderiv ℝ F z (EuclideanSpace.single (Fin.last d) 1)

/-- The Euclidean norm of the spatial gradient, `‖∇_x F(z)‖₂`. -/
noncomputable def gradXNorm {d : ℕ} (F : Space (d+1) → ℝ) (z : Space (d+1)) : ℝ :=
  Real.sqrt (∑ i : Fin d, (fderiv ℝ F z (EuclideanSpace.single i.castSucc 1)) ^ 2)

/-- The certificate defect (p.15, p.22): `def_F(y, a) = max{0, ‖∇_x F(y, a)‖₂ − ∂_a F(y, a)}`. -/
noncomputable def certDefect {d : ℕ} (F : Space (d+1) → ℝ) (z : Space (d+1)) : ℝ :=
  max 0 (gradXNorm F z - offsetDeriv F z)

/-- `(T_s g)(z) = E_{w∼γ_n} g(ρ_s z + σ_s w)` for `g ≥ 0`, as an element of `[0, ∞]` (§3.3, p.14). -/
noncomputable def ouLin {n : ℕ} (s : ℝ) (g : Space n → ℝ) (z : Space n) : ℝ≥0∞ :=
  ∫⁻ w, ENNReal.ofReal (g (probe s z w)) ∂gaussian n

end GeoRobustLearn


