-- Prove2me | Definitions.Def_CuspForm_PeterssonOn
-- name    : CuspForm_PeterssonOn
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/01dcf3f1-862c-592f-8852-c4ccb809930d
-- title:
--   Petersson product in weight k on a subgroup of SL2​(Z)
-- statement:
--   Fix a subgroup $\Gamma \le \mathrm{SL}(2,\mathbb{Z})$, an integer $k$, and two functions $f, g \colon \mathbb{H} \to \mathbb{C}$ on the upper half-plane; no modularity, holomorphy or growth condition is imposed on $f$ and $g$. [`CuspForm.peterssonOnIntegrand`](../def/CuspForm_PeterssonOn.html#L15) is the function of $\tau \in \mathbb{H}$ given by the finite sum (Mathlib's `∑ᶠ`, hence $0$ unless only finitely many terms are non-zero) over the left coset space $\mathrm{SL}(2,\mathbb{Z}) / \Gamma$ of the pointwise Petersson density `UpperHalfPlane.petersson k` applied to the weight-$k$ slash translates $f \mid[k] \sigma^{-1}$ and $g \mid[k] \sigma^{-1}$, where $\sigma$ is the canonical representative (`Quotient.out`) of the coset in question; thus the summand attached to a coset $q$ is $\overline{(f\mid_k \sigma^{-1})(\tau)}\,(g\mid_k \sigma^{-1})(\tau)\,(\operatorname{Im}\tau)^k$ with $\sigma = q^{\mathrm{out}}$. [`CuspForm.peterssonOn Γ k f g`](../def/CuspForm_PeterssonOn.html#L20) is then the Bochner integral of this integrand against the invariant measure on $\mathbb{H}$ restricted to Mathlib's standard fundamental domain `ModularGroup.fd` of $\mathrm{SL}(2,\mathbb{Z})$.
--
--   The definition is therefore total: a choice of coset representatives is built in through `Quotient.out`, no integrability is assumed (a non-integrable integrand gives the value $0$ by the conventions of the Bochner integral), and for a subgroup of infinite index the coset sum is $0$, so the product vanishes identically. When $f$ and $g$ are weight-$k$ invariant under $\Gamma$ the individual summands are independent of the representatives and, for $\Gamma$ of finite index, the translates $\sigma^{-1}\mathcal{D}$ assemble a fundamental domain for $\Gamma$, so that the value is the classical Petersson product $\int_{\Gamma \backslash \mathbb{H}} \overline{f}\, g\, y^{k}\, \frac{dx\,dy}{y^{2}}$, normalised without any division by the index $[\mathrm{SL}(2,\mathbb{Z}) : \Gamma]$. The auxiliary theorem [`CuspForm.peterssonOn_def`](../def/CuspForm_PeterssonOn.html#L24) records the defining equation, so that the integral form is available as a rewriting rule.
--
--   **Relation to Mathlib.** Built on Mathlib's pointwise Petersson density `UpperHalfPlane.petersson`, the weight-$k$ slash action `∣[k]`, the invariant measure on the upper half-plane and the standard fundamental domain `ModularGroup.fd`; the globalised pairing attached to an arbitrary subgroup of $\mathrm{SL}(2,\mathbb{Z})$, at the level of functions rather than of modular forms of a fixed level, is the project's own.
--
--   **Where it is used.** This pairing supplies the Petersson theory used on $\Gamma_1(N)$ and on intermediate groups such as $\Gamma_1(N) \cap \alpha^{-1}\Gamma_1(N)\alpha$: adjoints of Hecke operators, decomposition into nebentypus components, and semisimplicity of the Hecke action on cusp forms, which underlie the newform theory used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_PeterssonOn.lean

import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Petersson
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

def peterssonOnIntegrand (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOn (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonOnIntegrand Γ k f g)

theorem peterssonOn_def (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) :
    peterssonOn Γ k f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonOnIntegrand Γ k f g) := rfl

end CuspForm

end


