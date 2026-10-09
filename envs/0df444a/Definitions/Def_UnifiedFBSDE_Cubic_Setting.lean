-- Prove2me | Definitions.Def_UnifiedFBSDE_Cubic_Setting
-- name    : UnifiedFBSDE_Cubic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:26.406986+00:00
-- url     : https://prove2.me/theorems/5e618052-ddd4-4828-b05f-648874a1b8d5
-- title:
--   (5.3)–(5.4), pp. 20–21 — the cubic F of the constant-coefficient linear FBSDE with σ₃ = 0 and solutions of backward ODEs y_t = h + ∫ₜᵀ G(s, y_s) ds
-- statement:
--   This file fixes the objects of §5 and §5.1, Case 1, of Ma, Wu, Zhang and Zhang.
--
--   **Coefficients.** The linear FBSDE (4.1) with constant coefficients reads
--   $$
--   \mathcal X_t = 1+\int_0^t (b_1\mathcal X_s+b_2\mathcal Y_s+b_3\mathcal Z_s)\,ds+\int_0^t(\sigma_1\mathcal X_s+\sigma_2\mathcal Y_s+\sigma_3\mathcal Z_s)\,dB_s,\qquad
--   \mathcal Y_t = h\mathcal X_T+\int_t^T(f_1\mathcal X_s+f_2\mathcal Y_s+f_3\mathcal Z_s)\,ds-\int_t^T\mathcal Z_s\,dB_s .
--   $$
--   In Case 1 one has $\sigma_3=0$, so the data are eight real numbers $b_1,b_2,b_3,\sigma_1,\sigma_2,f_1,f_2,f_3$ (a structure `Coeffs`) together with the terminal coefficient $h\in\mathbb R$.
--
--   **The cubic (5.4).** The dominating ODE of the FBSDE has right-hand side
--   $$
--   F(y)=f_1+[f_2+b_1+\sigma_1 f_3]\,y+[b_2+f_3\sigma_2+b_3\sigma_1]\,y^2+\sigma_2 b_3\,y^3 ,
--   $$
--   and, as in (A.3), we write $a_1=f_2+b_1+\sigma_1 f_3$, $a_2=b_2+f_3\sigma_2+b_3\sigma_1$, $a_3=\sigma_2 b_3$, so that $F(y)=f_1+a_1y+a_2y^2+a_3y^3$.
--
--   **Backward integral equations.** For $G:\mathbb R\times\mathbb R\to\mathbb R$, $h\in\mathbb R$ and $T$, a function $y$ is a *solution on $[0,T]$* of
--   $$
--   y_t = h+\int_t^T G(s,y_s)\,ds,\qquad t\in[0,T],
--   $$
--   if for every $t\in[0,T]$ the map $s\mapsto G(s,y_s)$ is integrable on $[t,T]$ and the equation holds at $t$. A *bounded solution* is a solution with $\sup_{t\in[0,T]}|y_t|<\infty$. The dominating ODE (5.3) is the case $G(s,y)=F(y)$.
--
--   **Condition (iv) of Lemma 5.1.** For $L,C\in\mathbb R$ and $c:\mathbb R\to\mathbb R$, the pair $(C,c)$ satisfies (iv) on $[0,T]$ if
--   $$
--   C\ \ge\ \int_t^T e^{-\int_s^T\alpha_r\,dr}\,c_s\,ds\qquad\text{for all }t\in[0,T]
--   $$
--   and every measurable $\alpha$ with $|\alpha|\le L$.
--
--   These are the objects of every statement in this mission: the comparison Lemma 5.1, the sharp criterion Theorem 5.3, and the blow-up estimates of the Appendix.
--
--   **Formalization Note.** $\sigma_3$ is not a field of `Coeffs` because it is $0$ in this case. Integrability of the integrand is part of the solution predicate: without it, Lean's integral of a non-integrable function is $0$ and any $y$ with $y_t=h$ would count as a solution. "Bounded" is stated explicitly although a solution on a compact interval is automatically continuous and hence bounded. The functions $\alpha$ in (iv) are taken measurable. Integrability of $c$ on $[0,T]$ is not part of `CondIV`, because Lean's integral of a non-integrable function is $0$. Lemma 5.1 and the first clause of Remark 5.2 therefore assume `IntegrableOn c (Icc 0 T)` as a separate hypothesis. The solution predicates are vacuous for $T<0$, so every statement using them assumes $0<T$ or restricts to $t\in[0,T]$. The solution predicate `IsSolution` is shared: mission 3 of this series (the rational $F$ of (3.9) with $\sigma_3\neq0$) uses it for its own dominating ODE.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 12, (4.1); pp. 19–20, (5.1)–(5.2), Lemma 5.1(iv); p. 20, (5.3)–(5.4); p. 46, (A.3)

import Mathlib

namespace UnifiedFBSDE.Cubic

/-- The constant coefficients of the linear FBSDE (4.1)
`𝒳_t = 1 + ∫₀ᵗ (b₁𝒳 + b₂𝒴 + b₃𝒵) ds + ∫₀ᵗ (σ₁𝒳 + σ₂𝒴 + σ₃𝒵) dB`,
`𝒴_t = h𝒳_T + ∫ₜᵀ (f₁𝒳 + f₂𝒴 + f₃𝒵) ds − ∫ₜᵀ 𝒵 dB`
in Case 1 of §5.1, where σ₃ = 0; σ₃ is therefore not a field. The terminal coefficient `h`
is kept as a separate real parameter of every statement. -/
structure Coeffs where
  b₁ : ℝ
  b₂ : ℝ
  b₃ : ℝ
  σ₁ : ℝ
  σ₂ : ℝ
  f₁ : ℝ
  f₂ : ℝ
  f₃ : ℝ

/-- The cubic (5.4): `F(y) = f₁ + [f₂ + b₁ + σ₁f₃]y + [b₂ + f₃σ₂ + b₃σ₁]y² + σ₂b₃y³`. -/
def Coeffs.F (c : Coeffs) (y : ℝ) : ℝ :=
  c.f₁ + (c.f₂ + c.b₁ + c.σ₁ * c.f₃) * y + (c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁) * y ^ 2
    + c.σ₂ * c.b₃ * y ^ 3

/-- (A.3): `a₁ = f₂ + b₁ + σ₁f₃`. -/
def Coeffs.a₁ (c : Coeffs) : ℝ := c.f₂ + c.b₁ + c.σ₁ * c.f₃

/-- (A.3): `a₂ = b₂ + f₃σ₂ + b₃σ₁`. -/
def Coeffs.a₂ (c : Coeffs) : ℝ := c.b₂ + c.f₃ * c.σ₂ + c.b₃ * c.σ₁

/-- (A.3): `a₃ = σ₂b₃`. -/
def Coeffs.a₃ (c : Coeffs) : ℝ := c.σ₂ * c.b₃

/-- `y` solves the backward integral equation `y_t = h + ∫ₜᵀ G(s, y_s) ds` on `[0, T]`:
for every `t ∈ [0, T]` the integrand `s ↦ G(s, y_s)` is integrable on `[t, T]` and the
equation holds at `t`. Values of `y` outside `[0, T]` are irrelevant. -/
def IsSolution (G : ℝ → ℝ → ℝ) (h T : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 T,
    MeasureTheory.IntegrableOn (fun s => G s (y s)) (Set.Icc t T) ∧
      y t = h + ∫ s in t..T, G s (y s)

/-- A bounded solution on `[0, T]`: a solution with `sup_{t ∈ [0,T]} |y_t| < ∞`. -/
def IsBoundedSolution (G : ℝ → ℝ → ℝ) (h T : ℝ) (y : ℝ → ℝ) : Prop :=
  IsSolution G h T y ∧ ∃ C : ℝ, ∀ t ∈ Set.Icc 0 T, |y t| ≤ C

/-- Condition (iv) of Lemma 5.1 for one pair `(C, c)`:
`C ≥ ∫ₜᵀ e^{-∫ₛᵀ α_r dr} c_s ds` for all `t ∈ [0, T]` and every measurable `α` with `|α| ≤ L`. -/
def CondIV (L C : ℝ) (c : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ α : ℝ → ℝ, Measurable α → (∀ s, |α s| ≤ L) →
    ∀ t ∈ Set.Icc 0 T, ∫ s in t..T, Real.exp (-∫ r in s..T, α r) * c s ≤ C

end UnifiedFBSDE.Cubic


