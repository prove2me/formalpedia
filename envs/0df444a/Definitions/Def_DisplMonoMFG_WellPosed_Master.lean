-- Prove2me | Definitions.Def_DisplMonoMFG_WellPosed_Master
-- name    : DisplMonoMFG_WellPosed_Master
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:26.846488+00:00
-- url     : https://prove2.me/theorems/35e81dcf-49fb-4aa3-b121-8a9ac15a0043
-- title:
--   The master equation (1.1)–(1.2) and its classical solutions in $\mathcal C^{1,2,2}(\Theta)$
-- statement:
--   Fix $\beta\ge0$ (the intensity of the common noise), $\hat\beta^2:=1+\beta^2$, a Hamiltonian $H$ and a terminal cost $G$.
--
--   The **master equation** ((1.1), p. 2178) on $[t_0,T]$ is
--   $$
--   \begin{cases}
--   -\partial_tV-\dfrac{\hat\beta^2}{2}\operatorname{tr}(\partial_{xx}V)+H(x,\mu,\partial_xV)-\mathcal NV=0 & \text{in }(t_0,T)\times\mathbb R^d\times\mathcal P_2(\mathbb R^d),\\[4pt]
--   V(T,x,\mu)=G(x,\mu) & \text{in }\mathbb R^d\times\mathcal P_2(\mathbb R^d).
--   \end{cases}
--   $$
--   The nonlocal operator is ((1.2))
--   $$
--   \mathcal NV(t,x,\mu):=\operatorname{tr}\Big(\bar{\tilde{\mathbb E}}\Big[\frac{\hat\beta^2}{2}\partial_{\tilde x}\partial_\mu V(t,x,\mu,\tilde\xi)+\frac{\beta^2}{2}\partial_{\mu\mu}V(t,x,\mu,\bar\xi,\tilde\xi)+\beta^2\partial_x\partial_\mu V(t,x,\mu,\tilde\xi)-\partial_\mu V(t,x,\mu,\tilde\xi)(\partial_pH)^\top(\tilde\xi,\mu,\partial_xV(t,\tilde\xi,\mu))\Big]\Big),
--   $$
--   where $\tilde\xi,\bar\xi$ are independent with law $\mu$.
--
--   A **classical solution** on $[t_0,T]$ is a function $V\in\mathcal C^{1,2,2}(\Theta)$, $\Theta=[t_0,T]\times\mathbb R^d\times\mathcal P_2$ (p. 2184), that satisfies (1.1). Membership in $\mathcal C^{1,2,2}(\Theta)$ means that $\partial_tV,\partial_xV,\partial_{xx}V,\partial_\mu V,\partial_x\partial_\mu V,\partial_{\tilde x}\partial_\mu V,\partial_{\mu\mu}V$ exist on $\Theta$ and, together with $V$, are jointly continuous there.
--
--   The file also defines two further notions:
--   1. A classical solution **with bounded $\partial_xV,\partial_{xx}V,\partial_\mu V,\partial_{x\mu}V$** (Theorem 6.3) is one for which these four derivatives are bounded by one constant on $\Theta$.
--   2. **The further regularity of Theorem 4.1** holds on a time set if $V(t,\cdot,\cdot),\partial_xV(t,\cdot,\cdot),\partial_{xx}V(t,\cdot,\cdot)\in\mathcal C^2(\mathbb R^d\times\mathcal P_2)$ and $\partial_\mu V(t,\cdot,\cdot,\cdot),\partial_{x\mu}V(t,\cdot,\cdot,\cdot)\in\mathcal C^2(\mathbb R^d\times\mathcal P_2\times\mathbb R^d)$, with all their derivatives in the state and measure variables continuous in time and uniformly bounded.
--
--   The master equation characterizes the equilibrium value of a representative agent in a mean field game with idiosyncratic and common noise.
--
--   **Formalization Note** $\bar{\tilde{\mathbb E}}$ is the integral against $\mu\otimes\mu$, and the trace is $\sum_iB(e_i,e_i)$. $\partial_pH$ is the Fréchet derivative of $p\mapsto H(x,\mu,p)$. The time derivative is one-sided at the endpoints of $[t_0,T]$, and the equation is required on the open interval, as on p. 2178. The definition requires the expectations in (1.2) to exist (the integrands are integrable), which the page presupposes when it writes $\mathcal NV$. Without this, a Bochner integral of a non-integrable function would silently be $0$. Vector- and matrix-valued memberships in the further regularity are coordinatewise, which is equivalent.
-- source:
--   Gangbo, Mészáros, Mou, Zhang, Mean field games master equations with nonseparable Hamiltonians and displacement monotonicity, Ann. Probab. 50 (2022), (1.1)–(1.2) pp. 2178–2179, 𝒞^{1,2,2}(Θ) p. 2184, Theorem 4.1 p. 2195, Theorem 6.3 p. 2207

import Mathlib
import Definitions.Def_DisplMonoMFG_WellPosed_Hyp

open MeasureTheory

/-! Gangbo, Mészáros, Mou, Zhang, Ann. Probab. 50 (2022): the master equation (1.1) with the
nonlocal operator (1.2), pp. 2178–2179 (PDF pp. 1–2), its classical solutions in `𝒞^{1,2,2}(Θ)`
(p. 2184, PDF p. 7), the bounded-derivative class of Theorem 6.3 (p. 2207) and the further
regularity assumed in Theorem 4.1 (p. 2195) and obtained in Proposition 6.2(iii) (p. 2207). -/

namespace DisplMonoMFG.WellPosed

variable {d : ℕ}

/-- The vector `∂_x V(t, x, μ) ∈ ℝ^d` (the gradient), from the witness `w t`. -/
noncomputable def gradV (w : ℝ → C2W d (E d) ℝ) (t : ℝ) (x : E d) (μ : P2 d) : E d :=
  (InnerProductSpace.toDual ℝ (E d)).symm ((w t).Dx x μ)

/-- `∂_p H(x, μ, p)` as a linear functional (the Fréchet derivative of `p ↦ H(x, μ, p)`). -/
noncomputable def Hp (H : E d → P2 d → E d → ℝ) (x : E d) (μ : P2 d) (p : E d) : E d →L[ℝ] ℝ :=
  fderiv ℝ (H x μ) p

/-- The integrand of the single expectation in (1.2), at `x̃`:
`(β̂²/2) tr ∂_x̃∂_μ V(t, x, μ, x̃) + β² tr ∂_x∂_μ V(t, x, μ, x̃)
 - tr[∂_μ V(t, x, μ, x̃) (∂_p H)ᵀ(x̃, μ, ∂_x V(t, x̃, μ))]`, `β̂² = 1 + β²`. -/
noncomputable def NVint (β : ℝ) (H : E d → P2 d → E d → ℝ) (w : ℝ → C2W d (E d) ℝ)
    (t : ℝ) (x : E d) (μ : P2 d) (y : E d) : ℝ :=
  (1 + β ^ 2) / 2 * tr ((w t).DyDm x μ y) + β ^ 2 * tr ((w t).DxDm x μ y) -
    ∑ i, (w t).Dm x μ y (e i) * Hp H y μ (gradV w t y μ) (e i)

/-- The nonlocal operator (1.2), p. 2178:
`𝒩V(t, x, μ) = tr Ē̃[(β̂²/2) ∂_x̃∂_μ V(t, x, μ, ξ̃) + (β²/2) ∂_μμ V(t, x, μ, ξ̄, ξ̃)
 + β² ∂_x∂_μ V(t, x, μ, ξ̃) - ∂_μ V(t, x, μ, ξ̃)(∂_p H)ᵀ(ξ̃, μ, ∂_x V(t, ξ̃, μ))]`, with `ξ̃, ξ̄`
independent of law `μ`, so `Ē̃` is the integral against `μ ⊗ μ`. -/
noncomputable def NV (β : ℝ) (H : E d → P2 d → E d → ℝ) (w : ℝ → C2W d (E d) ℝ)
    (t : ℝ) (x : E d) (μ : P2 d) : ℝ :=
  (∫ y, NVint β H w t x μ y ∂μ.1) +
    β ^ 2 / 2 * ∫ y, ∫ y', tr ((w t).Dmm x μ y y') ∂μ.1 ∂μ.1

/-- The left side of (1.1):
`-∂_t V - (β̂²/2) tr(∂_xx V) + H(x, μ, ∂_x V) - 𝒩V` at `(t, x, μ)`. -/
noncomputable def masterOp (β : ℝ) (H : E d → P2 d → E d → ℝ) (Vt : ℝ → E d → P2 d → ℝ)
    (w : ℝ → C2W d (E d) ℝ) (t : ℝ) (x : E d) (μ : P2 d) : ℝ :=
  -Vt t x μ - (1 + β ^ 2) / 2 * tr ((w t).Dxx x μ) + H x μ (gradV w t x μ) - NV β H w t x μ

/-- `V` is a classical solution of the master equation (1.1) on `[t₀, T]` with time derivative
`Vt` and spatial/measure witnesses `w t`: `V ∈ 𝒞^{1,2,2}(Θ)` (p. 2184), i.e. `∂_t V` (one-sided at
the endpoints), `∂_x V`, `∂_xx V`, `∂_μ V`, `∂_x∂_μ V`, `∂_x̃∂_μ V`, `∂_μμ V` exist on
`[t₀, T] × ℝ^d × 𝒫₂` and, together with `V`, are jointly continuous there; the equation holds on
`(t₀, T) × ℝ^d × 𝒫₂` (open interval, as on p. 2178); and `V(T, ·, ·) = G`. Formalization Note:
the expectations in (1.2) are required to exist (integrability of the integrands), as the page's
writing of `𝒩V` presupposes; otherwise a Bochner integral would silently be `0`. -/
def IsClassicalSol (β t₀ T : ℝ) (H : E d → P2 d → E d → ℝ) (G : E d → P2 d → ℝ)
    (V Vt : ℝ → E d → P2 d → ℝ) (w : ℝ → C2W d (E d) ℝ) : Prop :=
  (∀ t ∈ Set.Icc t₀ T, ∀ x μ, HasDerivWithinAt (fun s => V s x μ) (Vt t x μ) (Set.Icc t₀ T) t) ∧
  (∀ t ∈ Set.Icc t₀ T, IsC2With (V t) (w t)) ∧
  ContTXP (Set.Icc t₀ T) V ∧ ContTXP (Set.Icc t₀ T) Vt ∧ C2W.ContT (Set.Icc t₀ T) w ∧
  (∀ t ∈ Set.Ioo t₀ T, ∀ x μ,
    Integrable (fun y => NVint β H w t x μ y) μ.1 ∧
    Integrable (fun q : E d × E d => tr ((w t).Dmm x μ q.1 q.2)) (μ.1.prod μ.1) ∧
    masterOp β H Vt w t x μ = 0) ∧
  ∀ x μ, V T x μ = G x μ

/-- A classical solution on `[t₀, T]` "with bounded `∂_x V`, `∂_xx V`, `∂_μ V` and `∂_xμ V`"
(Theorem 6.3, p. 2207): some witnesses make `V` a classical solution and these four derivatives
are bounded by one constant on `[t₀, T] × ℝ^d × 𝒫₂ (× ℝ^d)`. -/
def IsClassicalSolBdd (β t₀ T : ℝ) (H : E d → P2 d → E d → ℝ) (G : E d → P2 d → ℝ)
    (V : ℝ → E d → P2 d → ℝ) : Prop :=
  ∃ (Vt : ℝ → E d → P2 d → ℝ) (w : ℝ → C2W d (E d) ℝ), IsClassicalSol β t₀ T H G V Vt w ∧
    ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ T, ∀ (x : E d) (μ : P2 d) (y : E d),
      ‖(w t).Dx x μ‖ ≤ C ∧ ‖(w t).Dxx x μ‖ ≤ C ∧ ‖(w t).Dm x μ y‖ ≤ C ∧ ‖(w t).DxDm x μ y‖ ≤ C

/-- The further regularity of Theorem 4.1 (p. 2195) and Proposition 6.2(iii) (p. 2207) on the
time set `I`: `V(t,·,·), ∂_x V(t,·,·), ∂_xx V(t,·,·) ∈ 𝒞²(ℝ^d × 𝒫₂)` and
`∂_μ V(t,·,·,·), ∂_xμ V(t,·,·,·) ∈ 𝒞²(ℝ^d × 𝒫₂ × ℝ^d)` (as functions of `((x, x̃), μ)`), and all
their derivatives in the state and measure variables are continuous in time and uniformly bounded
(one bound over `t ∈ I`). For `V(t,·,·)` the witnesses are `w t`. Formalization Note: the
vector- and matrix-valued functions are treated coordinatewise, which is equivalent. -/
def HighReg (I : Set ℝ) (V : ℝ → E d → P2 d → ℝ) (w : ℝ → C2W d (E d) ℝ) : Prop :=
  IsC2T I V w ∧
  (∀ i, ∃ w' : ℝ → C2W d (E d) ℝ, IsC2T I (fun t x μ => (w t).Dx x μ (e i)) w') ∧
  (∀ i j, ∃ w' : ℝ → C2W d (E d) ℝ, IsC2T I (fun t x μ => (w t).Dxx x μ (e i) (e j)) w') ∧
  (∀ k, ∃ w' : ℝ → C2W d (E d × E d) ℝ,
    IsC2T I (fun t (q : E d × E d) μ => (w t).Dm q.1 μ q.2 (e k)) w') ∧
  (∀ i k, ∃ w' : ℝ → C2W d (E d × E d) ℝ,
    IsC2T I (fun t (q : E d × E d) μ => (w t).DxDm q.1 μ q.2 (e i) (e k)) w')

end DisplMonoMFG.WellPosed


