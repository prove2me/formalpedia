-- Prove2me | Definitions.Def_MIC_kink_solitons_1d
-- name    : MIC_kink_solitons_1d
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T22:11:39.980586+00:00
-- url     : https://prove2.me/theorems/0c8acbee-7be4-4f8c-a591-24b176372b0d
-- title:
--   Kink solitons in 1+1 dimensions: potentials, masses, energy, kinks
-- statement:
--   This file fixes the objects of Chapter 1 of 't Hooft's notes. Throughout, $\lambda, A, F$ are real parameters (positivity is imposed in the theorems, not here).
--
--   1. **Potentials.** Case (a), the Mexican hat (eq. (1.2)): $V_a(\varphi) = \frac{\lambda}{24}(\varphi^2 - F^2)^2$. Case (b), sine-Gordon (eq. (1.3)): $V_b(\varphi) = A\big(1 - \cos\frac{2\pi\varphi}{F}\big)$.
--   2. **Masses and coupling (Section 1.1).** Case (a): $m_a = \sqrt{\lambda F^2/3}$. Case (b): $m_b = 2\pi\sqrt A/F$ and $\lambda_b = 16\pi^4 A/F^4$.
--   3. **Static energy (eq. (1.5)).** For $V : \mathbb R \to \mathbb R$ and $\varphi : \mathbb R \to \mathbb R$,
--   $$E_V[\varphi] = \int_{\mathbb R} \Big(\tfrac12 \varphi'(x)^2 + V(\varphi(x))\Big)^{+}\,dx \in [0, \infty],$$
--   a lower Lebesgue integral of the positive part of the energy density.
--   4. **Kinks (Section 1.2).** $\varphi_a(x) = F\tanh\big(\tfrac{m_a}{2}(x - x_0)\big)$ and $\varphi_b(x) = \frac{2F}{\pi}\arctan\big(e^{m_b(x-x_0)}\big)$, with $x_0 \in \mathbb R$ the free position of the soliton.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** The derivative is Mathlib's `deriv`, which returns $0$ at points of non-differentiability; theorems therefore assume differentiability where it matters. Since $V_a, V_b \ge 0$ whenever $\lambda \ge 0$, $A \ge 0$, the positive part in the energy is inactive in the regime of the theorems. The energy takes values in $[0,\infty]$ so that configurations of infinite energy need no special treatment.
-- source:
--   G. 't Hooft, Monopoles, Instantons and Confinement (lecture notes by F. Bruckmann), arXiv:hep-th/0010225, https://arxiv.org/abs/hep-th/0010225, Chapter 1, Section 1.1 eqs. (1.2)-(1.3) and the mass relations; Section 1.2 eq. (1.5) and the explicit solutions (pp. 3-4)

import Mathlib

/-!
# Kink solitons in 1+1 dimensions — definitions

Source: G. 't Hooft, *Monopoles, Instantons and Confinement*, lecture notes by
F. Bruckmann, arXiv:hep-th/0010225, Chapter 1 (Sections 1.1–1.2) and Exercise (i).

This file is the definition layer of a Prove2Me mission-proposal draft.
-/

namespace MonopolesInstantonsConfinement

open MeasureTheory

/-- Case (a), eq. (1.2): the "Mexican-hat" (φ⁴) potential `V(φ) = (λ/4!) (φ² - F²)²`. -/
noncomputable def phi4Potential (lam F : ℝ) (φ : ℝ) : ℝ :=
  lam / 24 * (φ ^ 2 - F ^ 2) ^ 2

/-- Case (b), eq. (1.3): the sine-Gordon potential `V(φ) = A (1 - cos (2πφ / F))`. -/
noncomputable def sineGordonPotential (A F : ℝ) (φ : ℝ) : ℝ :=
  A * (1 - Real.cos (2 * Real.pi * φ / F))

/-- Case (a), Section 1.1: the elementary particle mass `m`, defined by `m² = λ F² / 3`. -/
noncomputable def phi4Mass (lam F : ℝ) : ℝ :=
  Real.sqrt (lam * F ^ 2 / 3)

/-- Case (b), Section 1.1: the elementary particle mass `m = 2π √A / F`. -/
noncomputable def sineGordonMass (A F : ℝ) : ℝ :=
  2 * Real.pi * Real.sqrt A / F

/-- Case (b), Section 1.1: the quartic coupling `λ = 16 π⁴ A / F⁴`. -/
noncomputable def sineGordonCoupling (A F : ℝ) : ℝ :=
  16 * Real.pi ^ 4 * A / F ^ 4

/-- Eq. (1.5): the energy `E = ∫ (½ (∂ₓφ)² + V(φ)) dx` of a static field configuration
`φ : ℝ → ℝ`, valued in `[0, ∞]` (an infinite value means infinite energy). -/
noncomputable def staticEnergy (V : ℝ → ℝ) (φ : ℝ → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (1 / 2 * deriv φ x ^ 2 + V (φ x))

/-- Section 1.2, case (a): the kink `φ(x) = F tanh (½ m (x - x₀))`. -/
noncomputable def phi4Kink (lam F x₀ : ℝ) (x : ℝ) : ℝ :=
  F * Real.tanh (phi4Mass lam F / 2 * (x - x₀))

/-- Section 1.2, case (b): the sine-Gordon soliton `φ(x) = (2F/π) arctan (e^{m (x - x₀)})`. -/
noncomputable def sineGordonKink (A F x₀ : ℝ) (x : ℝ) : ℝ :=
  2 * F / Real.pi * Real.arctan (Real.exp (sineGordonMass A F * (x - x₀)))

end MonopolesInstantonsConfinement


