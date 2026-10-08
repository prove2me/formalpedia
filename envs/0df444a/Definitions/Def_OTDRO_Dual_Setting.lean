-- Prove2me | Definitions.Def_OTDRO_Dual_Setting
-- name    : OTDRO_Dual_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:41.312979+00:00
-- url     : https://prove2.me/theorems/fe99ef0a-00fa-4ba0-a778-16c835fb0954
-- title:
--   §2.1–2.3, pp. 9–13 — Mahalanobis cost, Assumptions 1–2 and the dual objective
-- statement:
--   Let $P_0$ be a probability law on $\mathbb R^d$, let $A(x)$ be a positive definite matrix for each $x$, and let $\ell:\mathbb R\to\mathbb R$ be a loss. The **state dependent Mahalanobis cost** is
--
--   $$c(x,x')=(x-x')^{\mathsf T}A(x)(x-x').$$
--
--   Assumption 1 requires this cost to be lower semicontinuous. It also requires positive constants $\rho_{\min}$ and $\rho_{\max}$ bounding the quadratic form $v^{\mathsf T}A(x)v$ between $\rho_{\min}\|v\|^2$ and $\rho_{\max}\|v\|^2$, for $P_0$-almost every $x$ and every $v$. Assumption 2 requires convexity of $\ell$, at most quadratic growth in the stated sense, and a finite fourth moment of $P_0$.
--
--   For $\delta>0$, the central dual quantities are
--
--   $$F(\gamma,\beta,\lambda;x)=\ell\bigl(\beta^{\mathsf T}x+\gamma\sqrt\delta\,\beta^{\mathsf T}A(x)^{-1}\beta\bigr)-\lambda\sqrt\delta\bigl(\gamma^2\beta^{\mathsf T}A(x)^{-1}\beta-1\bigr),$$
--   $$\ell_{\rm rob}(\beta,\lambda;x)=\sup_{\gamma\in\mathbb R}F(\gamma,\beta,\lambda;x),\qquad f_\delta(\beta,\lambda)=E_{P_0}[\ell_{\rm rob}(\beta,\lambda;X)].$$
--
--   The file also defines the maximizer set $\Gamma^*$, the growth exponent $\kappa$, and the two threshold multipliers used later in the paper. These definitions provide a common vocabulary for the five missions in the series.
--
--   **Formalization Note** Values of $\ell_{\rm rob}$ and $f_\delta$ lie in the extended reals. The latter uses the published extended integral; the definition itself carries no integrability claim. Assumption 1 expresses its almost everywhere eigenvalue bounds in homogeneous quadratic form.
-- source:
--   arXiv:1810.02403v3, §2.1–2.3, pp. 9–13, Assumptions 1–2, (5), (7), (9)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral

namespace OTDRO.Dual

open MeasureTheory Matrix

/-- The state-dependent Mahalanobis transport cost of (5) and Assumption 1
(arXiv:1810.02403v3, pp. 4 and 9): `c(x, x') = (x − x')ᵀ A(x) (x − x')`. -/
noncomputable def mahalCost {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (x x' : EuclideanSpace ℝ (Fin d)) : ℝ :=
  dotProduct (x - x').ofLp (A x *ᵥ (x - x').ofLp)

/-- The quadratic form `βᵀ A(x)⁻¹ β` that appears throughout (7), (9), (10). -/
noncomputable def quadInv {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (β x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  dotProduct β.ofLp ((A x)⁻¹ *ᵥ β.ofLp)

/-- **Assumption 1** (p. 9): `A(x)` is positive definite for every `x`, the cost
`c(x, x') = (x − x')ᵀA(x)(x − x')` is lower semicontinuous (part a), and the eigenvalues of
`A(x)` lie in `[ρmin, ρmax]` with both bounds positive, for `P₀`-almost every `x` (part b), written in the
homogeneous form `ρmin‖v‖² ≤ vᵀA(x)v ≤ ρmax‖v‖²`. -/
structure Assumption1 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (ρmin ρmax : ℝ) : Prop where
  posDef : ∀ x, (A x).PosDef
  lsc : LowerSemicontinuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
    mahalCost A p.1 p.2)
  rhoMin_pos : 0 < ρmin
  rhoMax_pos : 0 < ρmax
  eig_bounds : ∀ᵐ x ∂P0, ∀ v : EuclideanSpace ℝ (Fin d),
    ρmin * ‖v‖ ^ 2 ≤ dotProduct v.ofLp (A x *ᵥ v.ofLp) ∧
      dotProduct v.ofLp (A x *ᵥ v.ofLp) ≤ ρmax * ‖v‖ ^ 2

/-- **Assumption 2** (p. 10): `ℓ` is convex, the growth exponent
`κ = inf {s ≥ 0 : sup_u (ℓ(u) − s u²) < ∞}` is finite (the set is nonempty), and `E_{P₀}‖X‖⁴ < ∞`. -/
structure Assumption2 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ) : Prop where
  convex : ConvexOn ℝ Set.univ ℓ
  growth : ∃ s : ℝ, 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)
  moment4 : Integrable (fun x => ‖x‖ ^ 4) P0

/-- The growth exponent `κ` of Assumption 2 (p. 10). Meaningful only under `Assumption2.growth`,
which makes the set nonempty. -/
noncomputable def growthKappa (ℓ : ℝ → ℝ) : ℝ :=
  sInf {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)}

/-- `F(γ, β, λ; x) = ℓ(βᵀx + γ√δ βᵀA(x)⁻¹β) − λ√δ(γ² βᵀA(x)⁻¹β − 1)`, display (7), p. 10. -/
noncomputable def Fobj {d : ℕ} (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ γ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ℓ (inner ℝ β x + γ * Real.sqrt δ * quadInv A β x) -
    lam * Real.sqrt δ * (γ ^ 2 * quadInv A β x - 1)

/-- `ℓ_rob(β, λ; x) = sup_{γ ∈ ℝ} F(γ, β, λ; x)` (Theorem 1, p. 10), valued in `EReal`
(it may be `+∞`). -/
noncomputable def ellRob {d : ℕ} (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) : EReal :=
  ⨆ γ : ℝ, ((Fobj ℓ A δ γ β lam x : ℝ) : EReal)

/-- The dual objective `f_δ(β, λ) = E_{P₀}[ℓ_rob(β, λ; X)]` (Theorem 1, p. 10), an extended-real
integral `∫ φ⁺ dP₀ − ∫ φ⁻ dP₀` (`ModelRiskOT.Duality.extIntegral`). -/
noncomputable def fDelta {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) : EReal :=
  ModelRiskOT.Duality.extIntegral P0 (fun x => ellRob ℓ A δ β lam x)

/-- The set of maximizers `Γ*(β, λ; x)` of `γ ↦ F(γ, β, λ; x)`, display (9), p. 13. -/
def maximizers {d : ℕ} (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (x : EuclideanSpace ℝ (Fin d)) : Set ℝ :=
  {γ | ∀ c : ℝ, Fobj ℓ A δ c β lam x ≤ Fobj ℓ A δ γ β lam x}

/-- `λ_thr(β) = κ√δ (P₀-ess-sup_x βᵀA(x)⁻¹β)`, p. 13. -/
noncomputable def lamThr {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d))) (ℓ : ℝ → ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  growthKappa ℓ * Real.sqrt δ * essSup (fun x => quadInv A β x) P0

/-- `λ'_thr(β) = ½ M √δ (P₀-ess-sup_x βᵀA(x)⁻¹β)`, p. 13 (under Assumption 3, with `ℓ'' ≤ M`). -/
noncomputable def lamThr' {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) (M δ : ℝ)
    (β : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / 2 * M * Real.sqrt δ * essSup (fun x => quadInv A β x) P0

end OTDRO.Dual


