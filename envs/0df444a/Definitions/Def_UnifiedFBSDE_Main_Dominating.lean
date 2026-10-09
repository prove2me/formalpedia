-- Prove2me | Definitions.Def_UnifiedFBSDE_Main_Dominating
-- name    : UnifiedFBSDE_Main_Dominating
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:22:32.986388+00:00
-- url     : https://prove2.me/theorems/0345adec-ca07-4895-bbef-e4a175ce3b38
-- title:
--   (3.1), (3.9), (3.12)–(3.13), (5.9), (5.13)–(5.22), pp. 8–11, 22–27 — difference quotients, F̄ and F̲, the dominating ODEs and Cases I–III
-- statement:
--   Let the coefficients $b,\sigma,f,g$ be as in `UnifiedFBSDE.Main.Setting`. For $\theta_j=(x_j,y_j,z_j)$, $j=1,2$, and $\varphi=b,\sigma,f$, the **difference quotients** (3.1) are
--
--   $$
--   \tilde h(x_1,x_2)=\frac{g(x_1)-g(x_2)}{x_1-x_2},\quad
--   \tilde\varphi_1=\frac{\varphi(t,x_1,y_1,z_1)-\varphi(t,x_2,y_1,z_1)}{x_1-x_2},\quad
--   \tilde\varphi_2=\frac{\varphi(t,x_2,y_1,z_1)-\varphi(t,x_2,y_2,z_1)}{y_1-y_2},\quad
--   \tilde\varphi_3=\frac{\varphi(t,x_2,y_2,z_1)-\varphi(t,x_2,y_2,z_2)}{z_1-z_2}.
--   $$
--
--   Replacing $\varphi_i$ by $\tilde\varphi_i(t,\theta_1,\theta_2)$ in $F_s(y)=f_1+f_2y+y(b_1+b_2y)+(f_3+b_3y)y(\sigma_1+\sigma_2y)/(1-\sigma_3y)$ of (3.9) gives $F(\theta_1,\theta_2;t,y)$, and (3.12) defines the deterministic bounds
--
--   $$
--   \overline F(t,y)=\operatorname{esssup}\sup_{x_1\ne x_2,\,y_1\ne y_2,\,z_1\ne z_2}F(\theta_1,\theta_2;t,y),\qquad
--   \underline F(t,y)=\operatorname{essinf}\inf F(\theta_1,\theta_2;t,y),
--   $$
--
--   with $\overline h,\underline h$ the same for $\tilde h$ over $x_1\ne x_2$. The **dominating ODEs** (3.13) are $\overline y_t=\overline h+\int_t^T\overline F(s,\overline y_s)ds$ and $\underline y_t=\underline h+\int_t^T\underline F(s,\underline y_s)ds$. Also defined:
--
--   1. $\alpha_3=b_2-b_3\sigma_2/\sigma_3$ (p. 35), in terms of the quotients;
--   2. condition (5.9) for a deterministic $y$: $y$ and $(1-\sigma_3y)^{-1}$ are bounded;
--   3. (5.13): $c_1>0$, $0<c_2<c_3$, $c_1c_3<1$;
--   4. the nine conditions (5.14) (Case I), (5.15)–(5.18) (Case II, Table 2) and (5.19)–(5.22) (Case III, Table 3), each involving $\sigma_3$, $h$, a one-sided bound $\overline F(t,\pm c)\le\varepsilon$ or $\underline F(t,\pm c)\ge-\varepsilon$, and a sign condition on $f_1$ or $\alpha_3$;
--   5. the difference quotient $(u(t,x_1)-u(t,x_2))/(x_1-x_2)$ of a random field and bounds on it;
--   6. the conclusion of the small-duration theorems 6.1–6.3, with a general band in place of (6.2).
--
--   Following the paper (pp. 23, 27), every condition on the coefficients holds **uniformly for all $\theta_j$**: for every $t\in[0,T]$, almost surely, for all $\theta_1,\theta_2$ with distinct coordinates (for $h$: almost surely, for all $x_1\ne x_2$).
--
--   **Formalization Note** $\overline F,\underline F,\overline h,\underline h$ take values in $\mathbb{\overline R}$ (`EReal`), where the essential supremum of an unbounded family is $+\infty$, not a junk $0$; a solution of (3.13) must keep them finite along its path, and integrates their real values. The bounds $\overline F(t,c)\le\varepsilon$, $\underline F(t,c)\ge-\varepsilon$ are stated directly as a.s. bounds for all $\theta_j$, which is equivalent and avoids the essential supremum. "$(1-\sigma_3y)^{-1}$ is bounded" is stated as $|1-\tilde\sigma_3 y_t|\ge\kappa>0$, because Lean's $1/0=0$ would make a bound on the inverse vacuous at the pole. Every use of $\alpha_3$ carries $\tilde\sigma_3\ne0$ (Tables 2 and 3 are headed "$\sigma_3\ne0$"). Quotients are only ever evaluated at distinct coordinates.
-- source:
--   Ma, Wu, Zhang and Zhang, On well-posedness of forward–backward SDEs—a unified approach, arXiv:1110.4658v2, p. 8, (3.1); p. 10, (3.9), (3.10); pp. 10–11, (3.11)–(3.13); p. 22, (5.9); pp. 25–27, (5.13)–(5.22); p. 27, (6.1)–(6.3); pp. 35–36, Cases I–III, Tables 2–3

import Mathlib
import Definitions.Def_UnifiedFBSDE_Main_Setting
import Definitions.Def_UnifiedFBSDE_Main_BackwardODE

namespace UnifiedFBSDE.Main

open MeasureTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `θ₁ = (x₁, y₁, z₁)` and `θ₂ = (x₂, y₂, z₂)` differ in every coordinate:
`x₁ ≠ x₂`, `y₁ ≠ y₂`, `z₁ ≠ z₂` (the range of the suprema in (3.12)). -/
def Distinct (θ₁ θ₂ : ℝ × ℝ × ℝ) : Prop :=
  θ₁.1 ≠ θ₂.1 ∧ θ₁.2.1 ≠ θ₂.2.1 ∧ θ₁.2.2 ≠ θ₂.2.2

/-- `φ̃₁(t, θ₁, θ₂) = [φ(t, x₁, y₁, z₁) − φ(t, x₂, y₁, z₁)]/[x₁ − x₂]` of (3.1). -/
noncomputable def dq1 (φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω)
    (θ₁ θ₂ : ℝ × ℝ × ℝ) : ℝ :=
  (φ t ω θ₁.1 θ₁.2.1 θ₁.2.2 - φ t ω θ₂.1 θ₁.2.1 θ₁.2.2) / (θ₁.1 - θ₂.1)

/-- `φ̃₂(t, θ₁, θ₂) = [φ(t, x₂, y₁, z₁) − φ(t, x₂, y₂, z₁)]/[y₁ − y₂]` of (3.1). -/
noncomputable def dq2 (φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω)
    (θ₁ θ₂ : ℝ × ℝ × ℝ) : ℝ :=
  (φ t ω θ₂.1 θ₁.2.1 θ₁.2.2 - φ t ω θ₂.1 θ₂.2.1 θ₁.2.2) / (θ₁.2.1 - θ₂.2.1)

/-- `φ̃₃(t, θ₁, θ₂) = [φ(t, x₂, y₂, z₁) − φ(t, x₂, y₂, z₂)]/[z₁ − z₂]` of (3.1). -/
noncomputable def dq3 (φ : ℝ≥0 → Ω → ℝ → ℝ → ℝ → ℝ) (t : ℝ≥0) (ω : Ω)
    (θ₁ θ₂ : ℝ × ℝ × ℝ) : ℝ :=
  (φ t ω θ₂.1 θ₂.2.1 θ₁.2.2 - φ t ω θ₂.1 θ₂.2.1 θ₂.2.2) / (θ₁.2.2 - θ₂.2.2)

/-- `h̃(x₁, x₂) = [g(x₁) − g(x₂)]/[x₁ − x₂]` of (3.1). -/
noncomputable def htil (c : Coeffs Ω) (ω : Ω) (x₁ x₂ : ℝ) : ℝ :=
  (c.g x₁ ω - c.g x₂ ω) / (x₁ - x₂)

/-- `F(θ₁, θ₂; t, y)`: the function `F_s(y)` of (3.9),
`f₁ + f₂y + y(b₁ + b₂y) + (f₃ + b₃y)y(σ₁ + σ₂y)/(1 − σ₃y)`, with each `φᵢ` replaced by
`φ̃ᵢ(t, θ₁, θ₂)` of (3.1), `φ = b, σ, f` (evaluated at `ω`). -/
noncomputable def Fθ (c : Coeffs Ω) (t : ℝ≥0) (ω : Ω) (θ₁ θ₂ : ℝ × ℝ × ℝ) (y : ℝ) : ℝ :=
  dq1 c.f t ω θ₁ θ₂ + dq2 c.f t ω θ₁ θ₂ * y
    + y * (dq1 c.b t ω θ₁ θ₂ + dq2 c.b t ω θ₁ θ₂ * y)
    + (dq3 c.f t ω θ₁ θ₂ + dq3 c.b t ω θ₁ θ₂ * y) * y
        * (dq1 c.σ t ω θ₁ θ₂ + dq2 c.σ t ω θ₁ θ₂ * y) / (1 - dq3 c.σ t ω θ₁ θ₂ * y)

/-- `α₃ = b₂ − b₃σ₂/σ₃` (p. 35), built from the difference quotients of (3.1). -/
noncomputable def alpha3 (c : Coeffs Ω) (t : ℝ≥0) (ω : Ω) (θ₁ θ₂ : ℝ × ℝ × ℝ) : ℝ :=
  dq2 c.b t ω θ₁ θ₂ - dq3 c.b t ω θ₁ θ₂ * dq2 c.σ t ω θ₁ θ₂ / dq3 c.σ t ω θ₁ θ₂

/-- `F̄(t, y) = esssup (sup_{x₁≠x₂, y₁≠y₂, z₁≠z₂} F(θ₁, θ₂; t, y))` of (3.12), valued in `EReal`. -/
noncomputable def Fbar (c : Coeffs Ω) (P : Measure Ω) (t : ℝ≥0) (y : ℝ) : EReal :=
  essSup (fun ω => ⨆ (θ₁ : ℝ × ℝ × ℝ) (θ₂ : ℝ × ℝ × ℝ) (_ : Distinct θ₁ θ₂),
    ((Fθ c t ω θ₁ θ₂ y : ℝ) : EReal)) P

/-- `F̲(t, y) = essinf (inf_{x₁≠x₂, y₁≠y₂, z₁≠z₂} F(θ₁, θ₂; t, y))` of (3.12), valued in `EReal`. -/
noncomputable def Fund (c : Coeffs Ω) (P : Measure Ω) (t : ℝ≥0) (y : ℝ) : EReal :=
  essInf (fun ω => ⨅ (θ₁ : ℝ × ℝ × ℝ) (θ₂ : ℝ × ℝ × ℝ) (_ : Distinct θ₁ θ₂),
    ((Fθ c t ω θ₁ θ₂ y : ℝ) : EReal)) P

/-- `h̄ = esssup (sup_{x₁≠x₂} h̃(x₁, x₂))` of (3.12), valued in `EReal`. -/
noncomputable def hbar (c : Coeffs Ω) (P : Measure Ω) : EReal :=
  essSup (fun ω => ⨆ (x₁ : ℝ) (x₂ : ℝ) (_ : x₁ ≠ x₂), ((htil c ω x₁ x₂ : ℝ) : EReal)) P

/-- `h̲ = essinf (inf_{x₁≠x₂} h̃(x₁, x₂))` of (3.12), valued in `EReal`. -/
noncomputable def hund (c : Coeffs Ω) (P : Measure Ω) : EReal :=
  essInf (fun ω => ⨅ (x₁ : ℝ) (x₂ : ℝ) (_ : x₁ ≠ x₂), ((htil c ω x₁ x₂ : ℝ) : EReal)) P

/-- `ȳ` solves the upper ODE of (3.13), `ȳ_t = h̄ + ∫ₜᵀ F̄(s, ȳ_s) ds` on `[0, T]`: `h̄` is finite,
`F̄(s, ȳ_s)` is finite for every `s ∈ [0, T]`, and the real-valued integral equation holds (with
the integrand integrable). -/
def SolvesUpperODE (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ybar : ℝ → ℝ) : Prop :=
  hbar c P ≠ ⊤ ∧ hbar c P ≠ ⊥ ∧
    (∀ s ∈ Icc (0 : ℝ) T, Fbar c P s.toNNReal (ybar s) ≠ ⊤ ∧ Fbar c P s.toNNReal (ybar s) ≠ ⊥) ∧
    SolvesBackwardODE T (hbar c P).toReal (fun s y => (Fbar c P s.toNNReal y).toReal) ybar

/-- `y̲` solves the lower ODE of (3.13), `y̲_t = h̲ + ∫ₜᵀ F̲(s, y̲_s) ds` on `[0, T]` (finiteness as in
`SolvesUpperODE`). -/
def SolvesLowerODE (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (yund : ℝ → ℝ) : Prop :=
  hund c P ≠ ⊤ ∧ hund c P ≠ ⊥ ∧
    (∀ s ∈ Icc (0 : ℝ) T, Fund c P s.toNNReal (yund s) ≠ ⊤ ∧ Fund c P s.toNNReal (yund s) ≠ ⊥) ∧
    SolvesBackwardODE T (hund c P).toReal (fun s y => (Fund c P s.toNNReal y).toReal) yund

/-- A condition on the coefficient quotients holding "uniformly for all `θⱼ`" (pp. 23, 27):
for every `t ∈ [0, T]`, for `P`-a.e. `ω`, for all `θ₁, θ₂` with distinct coordinates. -/
def UnifCoef (P : Measure Ω) (T : ℝ≥0) (p : ℝ≥0 → Ω → ℝ × ℝ × ℝ → ℝ × ℝ × ℝ → Prop) : Prop :=
  ∀ t ≤ T, ∀ᵐ ω ∂P, ∀ θ₁ θ₂ : ℝ × ℝ × ℝ, Distinct θ₁ θ₂ → p t ω θ₁ θ₂

/-- A condition on `h̃` holding uniformly: for `P`-a.e. `ω`, for all `x₁ ≠ x₂`. -/
def UnifTerm (P : Measure Ω) (p : Ω → ℝ → ℝ → Prop) : Prop :=
  ∀ᵐ ω ∂P, ∀ x₁ x₂ : ℝ, x₁ ≠ x₂ → p ω x₁ x₂

/-- (5.9) for a deterministic `y` on `[0, T]`: `y` is bounded and `(1 − σ₃y)⁻¹` is bounded, i.e.
there is `κ > 0` with `κ ≤ |1 − σ̃₃(t, θ₁, θ₂) y_t|` for every `t ∈ [0, T]`, a.s., for all `θⱼ`. -/
def Cond59 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (y : ℝ → ℝ) : Prop :=
  BoundedOn T y ∧ ∃ κ : ℝ, 0 < κ ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => κ ≤ |1 - dq3 c.σ t ω θ₁ θ₂ * y t|)

/-- (5.13): `c₁ > 0`, `0 < c₂ < c₃`, `c₁c₃ < 1`. -/
def Cond513 (c₁ c₂ c₃ : ℝ) : Prop :=
  0 < c₁ ∧ 0 < c₂ ∧ c₂ < c₃ ∧ c₁ * c₃ < 1

/-- (5.14) (Case I): `|σ₃| ≤ c₁`, `|h| ≤ c₂`, `F̄(t, c₃) ≤ ε`, `F̲(t, −c₃) ≥ −ε`, uniformly. -/
def Cond514 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => |dq3 c.σ t ω θ₁ θ₂| ≤ c₁) ∧
    UnifTerm P (fun ω x₁ x₂ => |htil c ω x₁ x₂| ≤ c₂) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => Fθ c t ω θ₁ θ₂ c₃ ≤ ε) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => -ε ≤ Fθ c t ω θ₁ θ₂ (-c₃))

/-- (5.15): `σ₃ ≥ c₁⁻¹`, `h ≥ c₂⁻¹`, `F̲(t, c₃⁻¹) ≥ −ε`, `b₂ − b₃σ₂/σ₃ ≤ ε` (with `σ₃ ≠ 0`),
uniformly. -/
def Cond515 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => c₁⁻¹ ≤ dq3 c.σ t ω θ₁ θ₂) ∧
    UnifTerm P (fun ω x₁ x₂ => c₂⁻¹ ≤ htil c ω x₁ x₂) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => -ε ≤ Fθ c t ω θ₁ θ₂ c₃⁻¹) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0 ∧ alpha3 c t ω θ₁ θ₂ ≤ ε)

/-- (5.16): `σ₃ ≤ −c₁⁻¹`, `h ≥ c₂⁻¹`, `F̲(t, c₃⁻¹) ≥ −ε`, `b₂ − b₃σ₂/σ₃ ≤ ε` (with `σ₃ ≠ 0`),
uniformly. -/
def Cond516 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≤ -c₁⁻¹) ∧
    UnifTerm P (fun ω x₁ x₂ => c₂⁻¹ ≤ htil c ω x₁ x₂) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => -ε ≤ Fθ c t ω θ₁ θ₂ c₃⁻¹) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0 ∧ alpha3 c t ω θ₁ θ₂ ≤ ε)

/-- (5.17): `σ₃ ≥ c₁⁻¹`, `h ≤ −c₂⁻¹`, `F̄(t, −c₃⁻¹) ≤ ε`, `b₂ − b₃σ₂/σ₃ ≥ −ε` (with `σ₃ ≠ 0`),
uniformly. -/
def Cond517 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => c₁⁻¹ ≤ dq3 c.σ t ω θ₁ θ₂) ∧
    UnifTerm P (fun ω x₁ x₂ => htil c ω x₁ x₂ ≤ -c₂⁻¹) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => Fθ c t ω θ₁ θ₂ (-c₃⁻¹) ≤ ε) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0 ∧ -ε ≤ alpha3 c t ω θ₁ θ₂)

/-- (5.18): `σ₃ ≤ −c₁⁻¹`, `h ≤ −c₂⁻¹`, `F̄(t, −c₃⁻¹) ≤ ε`, `b₂ − b₃σ₂/σ₃ ≥ −ε` (with `σ₃ ≠ 0`),
uniformly. -/
def Cond518 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≤ -c₁⁻¹) ∧
    UnifTerm P (fun ω x₁ x₂ => htil c ω x₁ x₂ ≤ -c₂⁻¹) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => Fθ c t ω θ₁ θ₂ (-c₃⁻¹) ≤ ε) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0 ∧ -ε ≤ alpha3 c t ω θ₁ θ₂)

/-- (5.19): `σ₃ ≤ c₁`, `0 ≤ h ≤ c₂`, `F̄(t, c₃) ≤ ε`, `f₁ ≥ 0`, uniformly. -/
def Cond519 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≤ c₁) ∧
    UnifTerm P (fun ω x₁ x₂ => 0 ≤ htil c ω x₁ x₂ ∧ htil c ω x₁ x₂ ≤ c₂) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => Fθ c t ω θ₁ θ₂ c₃ ≤ ε) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => 0 ≤ dq1 c.f t ω θ₁ θ₂)

/-- (5.20): `0 ≤ σ₃ ≤ c₁`, `h ≤ c₂`, `F̄(t, c₃) ≤ ε`, `b₂ − b₃σ₂/σ₃ ≥ −ε` (with `σ₃ ≠ 0`),
uniformly. -/
def Cond520 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => 0 ≤ dq3 c.σ t ω θ₁ θ₂ ∧ dq3 c.σ t ω θ₁ θ₂ ≤ c₁) ∧
    UnifTerm P (fun ω x₁ x₂ => htil c ω x₁ x₂ ≤ c₂) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => Fθ c t ω θ₁ θ₂ c₃ ≤ ε) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0 ∧ -ε ≤ alpha3 c t ω θ₁ θ₂)

/-- (5.21): `σ₃ ≥ −c₁`, `0 ≥ h ≥ −c₂`, `F̲(t, −c₃) ≥ −ε`, `f₁ ≤ 0`, uniformly. -/
def Cond521 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => -c₁ ≤ dq3 c.σ t ω θ₁ θ₂) ∧
    UnifTerm P (fun ω x₁ x₂ => -c₂ ≤ htil c ω x₁ x₂ ∧ htil c ω x₁ x₂ ≤ 0) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => -ε ≤ Fθ c t ω θ₁ θ₂ (-c₃)) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq1 c.f t ω θ₁ θ₂ ≤ 0)

/-- (5.22): `0 ≥ σ₃ ≥ −c₁`, `h ≥ −c₂`, `F̲(t, −c₃) ≥ −ε`, `b₂ − b₃σ₂/σ₃ ≤ ε` (with `σ₃ ≠ 0`),
uniformly. -/
def Cond522 (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) (ε c₁ c₂ c₃ : ℝ) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => -c₁ ≤ dq3 c.σ t ω θ₁ θ₂ ∧ dq3 c.σ t ω θ₁ θ₂ ≤ 0) ∧
    UnifTerm P (fun ω x₁ x₂ => -c₂ ≤ htil c ω x₁ x₂) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => -ε ≤ Fθ c t ω θ₁ θ₂ (-c₃)) ∧
    UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0 ∧ alpha3 c t ω θ₁ θ₂ ≤ ε)

/-- The heading `σ₃ ≠ 0` of Tables 2 and 3, uniformly: `σ̃₃(t, θ₁, θ₂) ≠ 0`. -/
def SigmaNonzero (c : Coeffs Ω) (P : Measure Ω) (T : ℝ≥0) : Prop :=
  UnifCoef P T (fun t ω θ₁ θ₂ => dq3 c.σ t ω θ₁ θ₂ ≠ 0)

/-- The difference quotient `(u(t, x₁) − u(t, x₂))/(x₁ − x₂)` of a random field `u`. -/
noncomputable def dqU (u : ℝ≥0 → ℝ → Ω → ℝ) (t : ℝ≥0) (x₁ x₂ : ℝ) (ω : Ω) : ℝ :=
  (u t x₁ ω - u t x₂ ω) / (x₁ - x₂)

/-- The quotient of `u` satisfies the bound `p t q`: for every `t ∈ [0, T]` and every `x₁ ≠ x₂`,
almost surely, `p t ((u(t, x₁) − u(t, x₂))/(x₁ − x₂))`. -/
def QuotBound (P : Measure Ω) (T : ℝ≥0) (u : ℝ≥0 → ℝ → Ω → ℝ) (p : ℝ≥0 → ℝ → Prop) : Prop :=
  ∀ t ≤ T, ∀ x₁ x₂ : ℝ, x₁ ≠ x₂ → ∀ᵐ ω ∂P, p t (dqU u t x₁ x₂ ω)

/-- The conclusions (i)–(iii) of Theorem 6.1 on `[0, T]`, with the band (6.2) replaced by a
general relation `band (y̲_t) (ȳ_t)`: (i) for every `x` the FBSDE (1.1) has a unique solution in
`𝕃²`; (ii) the ODEs (3.13) have solutions `ȳ, y̲` with `band (y̲_t) (ȳ_t)` for all `t ∈ [0, T]`;
(iii) there is a random field `u` with `Y_t = u(t, X_t)` a.s. for all `t ∈ [0, T]` along every
solution from every `x`, and `y̲_t ≤ (u(t, x₁) − u(t, x₂))/(x₁ − x₂) ≤ ȳ_t` (6.3). -/
def SmallTimeConclusion (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) (B : ℝ≥0 → Ω → Fin 1 → ℝ)
    (c : Coeffs Ω) (T : ℝ≥0) (band : ℝ → ℝ → Prop) : Prop :=
  (∀ x : ℝ, HasUniqueSolution 𝓕 P B c T x) ∧
    ∃ ybar yund : ℝ → ℝ, SolvesUpperODE c P T ybar ∧ SolvesLowerODE c P T yund ∧
      (∀ t ∈ Icc (0 : ℝ) T, band (yund t) (ybar t)) ∧
      ∃ u : ℝ≥0 → ℝ → Ω → ℝ,
        (∀ (x : ℝ) (X Y Z : ℝ≥0 → Ω → ℝ), SolvesFBSDE 𝓕 P B c T x X Y Z →
          ∀ t ≤ T, ∀ᵐ ω ∂P, Y t ω = u t (X t ω) ω) ∧
        QuotBound P T u (fun t q => yund t ≤ q ∧ q ≤ ybar t)

end UnifiedFBSDE.Main


