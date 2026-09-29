-- Prove2me | Definitions.Def_ModularCurve_XHDiamondModL
-- name    : ModularCurve_XHDiamondModL
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/9f67d82a-ccf2-565d-8f6d-3b062b75aba8
-- title:
--   Pull-back condition for diamond actions on reduced q-expansion fields
-- statement:
--   Fix a field $K$, an integer $M$ and a subgroup $H \le (\mathbb{Z}/M)^\times$. Here $\Gamma_H(M)$ is the group [`CohCarrier.GammaH M H`](../def/CohCarrier_Level.html#L133), the set of matrices in $\Gamma_0(M)$ whose $(1,1)$-entry reduces mod $M$ to a unit lying in $H$, and the field $F_K =$ `qExpFunctionFieldC K (CohCarrier.GammaH M H)` is the intermediate field of $K((q)) =$ `LaurentSeries K` generated over $K$ by all quotients $\bar p_f/\bar p_g$, where $f,g$ run over modular forms of a common integral weight on $\Gamma_H(M)$ (as a subgroup of $GL_2(\mathbb{R})$), $p_f,p_g \in \mathbb{Z}[[q]]$ are integral $q$-expansions of $f,g$ at width $1$ (i.e. their coefficientwise images in $\mathbb{C}[[q]]$ are the $q$-expansions), $\bar{(\cdot)}$ denotes the coefficientwise reduction into $K((q))$ via `intSeriesC`, and $\bar p_g \ne 0$.
--
--   The module defines a predicate `IsDiamondPullbackModL` on a group homomorphism $\rho$ from $\Gamma_0(M)$ to the group of $K$-algebra automorphisms of $F_K$. It asserts: for every $\gamma \in \Gamma_0(M)$, every weight $k \in \mathbb{Z}$, all modular forms $f,g,f_1,g_1$ of weight $k$ on $\Gamma_H(M)$ with integral $q$-expansions $p_f,p_g,p_{f_1},p_{g_1}$ such that $f_1 = f\mid_k\gamma$ and $g_1 = g\mid_k\gamma$ as functions on the upper half-plane (the slash action of $\gamma$ regarded in $SL_2(\mathbb{Z})$), and with $\bar p_g \neq 0$, every element $x \in F_K$ whose underlying Laurent series is $\bar p_{f_1}/\bar p_{g_1}$ satisfies that the Laurent series of $\rho(\gamma)(x)$ is $\bar p_f/\bar p_g$. Thus $\rho(\gamma)$ carries the reduction of $(f\mid\gamma)/(g\mid\gamma)$ to the reduction of $f/g$. Non-vanishing is required of $\bar p_g$ only; division by zero in $K((q))$ is the Lean convention. Nothing is asserted by the definition itself. The accompanying lemma `IsDiamondPullbackModL.coe_apply_eq` is the same statement in applied form, with the forms, series and element taken as implicit arguments.
--
--   **Relation to Mathlib.** Mathlib supplies the slash action, `qExpansion`, $\Gamma_0$ and $\Gamma_1$, and Laurent series; the groups $\Gamma_H(M)$, the $q$-expansion function fields inside `LaurentSeries K`, the integrality predicate `IsIntegralQExp` and the pull-back predicate defined here are the project's own.
--
--   **Where it is used.** The predicate pins down, by its effect on reduced ratios of $q$-expansions, an action of $\Gamma_0(M)$ by $K$-algebra automorphisms on the function field of $X_H(M)$ with coefficients in $K$; for $K$ of characteristic $\ell$ this is the reduction mod $\ell$ of the diamond automorphisms. Stating it over an arbitrary coefficient field allows later statements to quantify over any action with this property, whatever the field of characteristic $\ell$ in use.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_XHDiamondModL.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace ModularCurve

def IsDiamondPullbackModL (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        qExpFunctionFieldC K (CohCarrier.GammaH M H))) : Prop :=
  ∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
    (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg pf₁ pg₁ : PowerSeries ℤ),
    IsIntegralQExp f pf → IsIntegralQExp g pg →
    IsIntegralQExp f₁ pf₁ → IsIntegralQExp g₁ pg₁ →
    (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))) →
    intSeriesC K pg ≠ 0 →
    ∀ x : qExpFunctionFieldC K (CohCarrier.GammaH M H),
      (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁ →
      ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
        intSeriesC K pf / intSeriesC K pg

variable {K : Type*} [Field K] {M : ℕ} {H : Subgroup (ZMod M)ˣ}
  {ρ : CongruenceSubgroup.Gamma0 M →*
    (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K] qExpFunctionFieldC K (CohCarrier.GammaH M H))}

theorem IsDiamondPullbackModL.coe_apply_eq (hρ : IsDiamondPullbackModL K M H ρ)
    (γ : CongruenceSubgroup.Gamma0 M) {k : ℤ}
    {f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k}
    {pf pg pf₁ pg₁ : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf₁ : IsIntegralQExp f₁ pf₁) (hg₁ : IsIntegralQExp g₁ pg₁)
    (hfs : (⇑f₁ : UpperHalfPlane → ℂ) = ((⇑f : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hgs : (⇑g₁ : UpperHalfPlane → ℂ) = ((⇑g : UpperHalfPlane → ℂ) ∣[k] (γ : SL(2, ℤ))))
    (hpg : intSeriesC K pg ≠ 0)
    {x : qExpFunctionFieldC K (CohCarrier.GammaH M H)}
    (hx : (x : LaurentSeries K) = intSeriesC K pf₁ / intSeriesC K pg₁) :
    ((ρ γ x : qExpFunctionFieldC K (CohCarrier.GammaH M H)) : LaurentSeries K) =
      intSeriesC K pf / intSeriesC K pg :=
  hρ γ k f g f₁ g₁ pf pg pf₁ pg₁ hf hg hf₁ hg₁ hfs hgs hpg x hx

end ModularCurve

end


