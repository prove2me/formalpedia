-- Prove2me | Definitions.Def_SelfStructIS_LogEff_Sampler
-- name    : SelfStructIS_LogEff_Sampler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:20.780404+00:00
-- url     : https://prove2.me/theorems/8235a22a-3b2b-4051-a376-a9418efdad95
-- title:
--   Algorithm 1, (4)–(7), Table 1, §5.2 — the transformation T, its Jacobian J, ζ(u), M₂,ᵤ and pᵤ
-- statement:
--   This file fixes the self-structuring importance sampler (Algorithm 1, p. 8) for estimating $p_u=P(L(X)\ge u)$.
--
--   Let $u$ be the threshold, $l$ the hyper-parameter and $\rho>0$ the growth index of the loss. All operations on vectors are componentwise.
--
--   1. **Exponents** ((7), p. 7).
--   $$\kappa^{(1)}(x)=\frac1\rho\,\frac{\log(1+|x|)}{\|\log(1+|x|)\|_\infty},\qquad \kappa^{(2)}(x)=\frac{\log(1+|x|)}{\log l}.$$
--   2. **Transformation** ((4)/(5), pp. 7–8). $T(x)=x\,(u/l)^{\kappa(x)}$, i.e. $T_i(x)=x_i\,(u/l)^{\kappa_i(x)}$.
--   3. **Jacobian** (Table 1, p. 8). For $\kappa=\kappa^{(1)}$,
--   $$J(x)=\Big[\prod_{k=1}^d\tilde J_k(x)\Big]\frac{(u/l)^{\mathbf 1^\top\kappa(x)}}{\max_k\tilde J_k(x)},\qquad \tilde J_k(x)=1+\frac{\rho^{-1}\log(u/l)}{\|\log(1+|x|)\|_\infty}\,\frac{|x_k|}{1+|x_k|};$$
--   for $\kappa=\kappa^{(2)}$,
--   $$J(x)=\Big[\prod_{k=1}^d\bar J_k(x)\Big](u/l)^{\mathbf 1^\top\kappa(x)},\qquad \bar J_k(x)=1+\frac{\log(u/l)}{\log l}\,\frac{|x_k|}{1+|x_k|}.$$
--   4. **Estimator** (§5.2, p. 16). With $X$ of density $f_X$ and $Z=T(X)$, the single-sample estimator is
--   $$\zeta(u)=\frac{J(X)\,f_X(Z)}{f_X(X)}\,\mathbb I\big(L(Z)\ge u\big),$$
--   its second moment is $M_{2,u}=E[\zeta(u)^2]$, and the target is $p_u=P(L(X)\ge u)$.
--
--   Algorithm 1 averages $N$ independent copies of $\zeta(u)$; every efficiency statement of the paper is about $\zeta(u)$ and $M_{2,u}$.
--
--   **Formalization Note** $\zeta(u)$ is a function of the sample $x$ of $X$; $M_{2,u}$ and $p_u$ are extended nonnegative reals (a lower Lebesgue integral and a measure), so $M_{2,u}=+\infty$ is representable and not collapsed to $0$. $J$ is Table 1's closed form, not a determinant. At $x=0$, $\kappa^{(1)}$ and $\tilde J_k$ involve $0/0$, which Lean evaluates to $0$ (so $\kappa^{(1)}(0)=0$, $\tilde J_k(0)=1$); this is a Lebesgue-null set and $T(0)=0$ under any convention. The maximum $\max_k\tilde J_k$ is a supremum over `Fin d`, a maximum for $d\ge 1$. The choice of exponent is the two-constructor type `KappaChoice`.
-- source:
--   Deo, Murthy, Achieving Efficiency in Black-Box Simulation of Distribution Tails with Self-Structuring Importance Samplers, arXiv:2102.07060v3, p. 7, (4), (7); p. 8, Algorithm 1, (5), (6), Table 1; p. 16, §5.2

import Mathlib

namespace SelfStructIS.LogEff

open MeasureTheory

/-- The two exponent choices of (7), p. 7. -/
inductive KappaChoice
  | one
  | two

variable {d : ℕ}

/-- `κ⁽¹⁾(x) = (1/ρ) · log(1 + |x|)/‖log(1 + |x|)‖_∞`, (7), p. 7 (componentwise). -/
noncomputable def kappa1 (ρ : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => (1 / ρ) * (Real.log (1 + |x i|) / ‖fun j => Real.log (1 + |x j|)‖)

/-- `κ⁽²⁾(x) = log(1 + |x|)/log l`, (7), p. 7 (componentwise). -/
noncomputable def kappa2 (l : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Real.log (1 + |x i|) / Real.log l

/-- The exponent `κ` selected by the choice `c`. -/
noncomputable def kappa : KappaChoice → ℝ → ℝ → (Fin d → ℝ) → Fin d → ℝ
  | .one, ρ, _, x => kappa1 ρ x
  | .two, _, l, x => kappa2 l x

/-- The transformation `T(x) = x × (u/l)^{κ(x)}`, (4)/(5), pp. 7–8 (componentwise). -/
noncomputable def Tmap (c : KappaChoice) (ρ u l : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => x i * (u / l) ^ (kappa c ρ l x i)

/-- `J̃_k(x) = 1 + (ρ⁻¹ log(u/l)/‖log(1+|x|)‖_∞) · |x_k|/(1+|x_k|)`, Table 1, p. 8. -/
noncomputable def Jtilde (ρ u l : ℝ) (x : Fin d → ℝ) (k : Fin d) : ℝ :=
  1 + (ρ⁻¹ * Real.log (u / l) / ‖fun j => Real.log (1 + |x j|)‖) * (|x k| / (1 + |x k|))

/-- `J̄_k(x) = 1 + (log(u/l)/log l) · |x_k|/(1+|x_k|)`, Table 1, p. 8. -/
noncomputable def Jbar (u l : ℝ) (x : Fin d → ℝ) (k : Fin d) : ℝ :=
  1 + (Real.log (u / l) / Real.log l) * (|x k| / (1 + |x k|))

/-- The Jacobian `J` of Table 1, p. 8, for each exponent choice:
`J = [∏ₖ J̃ₖ] (u/l)^{𝟏ᵀκ⁽¹⁾} / maxₖ J̃ₖ` for `κ⁽¹⁾`, and `J = [∏ₖ J̄ₖ] (u/l)^{𝟏ᵀκ⁽²⁾}` for `κ⁽²⁾`. -/
noncomputable def Jac : KappaChoice → ℝ → ℝ → ℝ → (Fin d → ℝ) → ℝ
  | .one, ρ, u, l, x =>
      (∏ k, Jtilde ρ u l x k) * (u / l) ^ (∑ i, kappa1 ρ x i) / (⨆ k, Jtilde ρ u l x k)
  | .two, _, u, l, x =>
      (∏ k, Jbar u l x k) * (u / l) ^ (∑ i, kappa2 l x i)

/-- The single-sample estimator `ζ(u) = 𝓛 𝕀(L(Z) ≥ u)` with `Z = T(X)` and
`𝓛 = J(X) f_X(Z)/f_X(X)`, §5.2, p. 16, as a function of the sample `x` of `X`. -/
noncomputable def zeta (c : KappaChoice) (ρ : ℝ) (fX L : (Fin d → ℝ) → ℝ) (u l : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  Jac c ρ u l x * fX (Tmap c ρ u l x) / fX x *
    Set.indicator {z : Fin d → ℝ | u ≤ L z} (fun _ => (1 : ℝ)) (Tmap c ρ u l x)

/-- The second moment `M₂,ᵤ = E[ζ(u)²]`, §5.2, p. 16, as an extended nonnegative real. -/
noncomputable def M2 (μ : Measure (Fin d → ℝ)) (fX L : (Fin d → ℝ) → ℝ) (ρ : ℝ)
    (c : KappaChoice) (u l : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (zeta c ρ fX L u l x ^ 2) ∂μ

/-- The target probability `pᵤ = P(L(X) ≥ u)`. -/
noncomputable def pu (μ : Measure (Fin d → ℝ)) (L : (Fin d → ℝ) → ℝ) (u : ℝ) : ENNReal :=
  μ {x | u ≤ L x}

end SelfStructIS.LogEff


