-- Prove2me | Definitions.Def_TwoSidedPD_Baseline_Setting
-- name    : TwoSidedPD_Baseline_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:28.318353+00:00
-- url     : https://prove2.me/theorems/59c1679d-73e3-4fb7-bfdd-3d08fe251297
-- title:
--   §3, App. A.2, pp. 3343–3352 — two-sided platform with linear demands: inverse demands (3), (5), profits (4), (6), optima, surpluses, welfare, Assumption 1, b̂
-- statement:
--   This file sets up the baseline model of de Cornière, Mantovani and Shekhar: a monopoly platform intermediates between a mass one of buyers and two categories of sellers, $L$ and $H$, each of mass one.
--
--   **Parameters.** A buyer obtains a stand-alone value $v$ from the platform and an extra benefit $b$ for each seller on it. A seller of type $j\in\{L,H\}$ earns a variable profit $\theta_j$ per buyer on the platform. All outside options are uniform on $[0,1]$, so if $N_B$ buyers participate and the type-$j$ fee is $f_j$, the type-$j$ seller demand is $D_j=\theta_jN_B-f_j$, and the buyer demand at price $p$ with $N_S$ sellers is $D_B=v+bN_S-p$.
--
--   **Assumption 1** (p. 3343, as printed): (i) $0<v<4-(b+\theta_L)^2-(b+\theta_H)^2$; (ii) $\frac{\theta_H-3\theta_L}{2}<b$.
--
--   **Uniform pricing** ($f_L=f_H$). The platform chooses $(N_B,N_S)\in\mathbb R^2$; the inverse demands (3) and the profit (4) are
--   $$P^U(N_B,N_S)=v+bN_S-N_B,\qquad F^U(N_B,N_S)=\frac{(\theta_L+\theta_H)N_B-N_S}{2},$$
--   $$\Pi^U(N_B,N_S)=N_BP^U(N_B,N_S)+N_SF^U(N_B,N_S).$$
--   A uniform-pricing equilibrium is a global maximizer of $\Pi^U$ over $\mathbb R^2$. At $(N_B,N_S)$ the participation of type-$j$ sellers is their demand at the common fee, $N^U_j=\theta_jN_B-F^U(N_B,N_S)$ (footnote 14); note $N^U_H+N^U_L=N_S$.
--
--   **Price discrimination.** The platform chooses $(N_B,N_L,N_H)\in\mathbb R^3$; the inverse demands (5) and the profit (6) are
--   $$P^D=v+b(N_L+N_H)-N_B,\quad F^D_H=\theta_HN_B-N_H,\quad F^D_L=\theta_LN_B-N_L,$$
--   $$\Pi^D(N_B,N_L,N_H)=N_BP^D+N_LF^D_L+N_HF^D_H.$$
--   A discrimination equilibrium is a global maximizer of $\Pi^D$ over $\mathbb R^3$.
--
--   **Surpluses and welfare** (App. A.2, p. 3352), at an arbitrary allocation. The participant with outside option $k$ joins and obtains its net utility minus $k$:
--   $$CS^U=\int_0^{N_B}\big(v+b(N^U_H+N^U_L)-P^U-k\big)\,dk,\qquad DS^U_j=\int_0^{N^U_j}\big(\theta_jN_B-F^U-k\big)\,dk,$$
--   $$CS^D=\int_0^{N_B}\big(v+b(N_H+N_L)-P^D-k\big)\,dk,\qquad DS^D_j=\int_0^{N_j}\big(\theta_jN_B-F^D_j-k\big)\,dk,$$
--   and total welfare is $SW=CS+\Pi+DS_L+DS_H$ in each regime.
--
--   **Threshold and abbreviations.** $\hat b(\theta_H,\theta_L)=\big(\sqrt{32-7(\theta_H-\theta_L)^2}-3\theta_H-\theta_L\big)/4$ (Proposition 2); $U=8-(2b+\theta_H+\theta_L)^2$ and $D=4-2b^2-\theta_H^2-\theta_L^2-2b(\theta_H+\theta_L)$ are the denominators of (12) and (13)–(15); $\lambda$ is the quartic of App. A.2(ii), p. 3352:
--   $$\lambda=32-24b^4-7\theta_H^4+2\theta_H^3\theta_L+28\theta_L^2-7\theta_L^4-48b^3(\theta_H+\theta_L)-2\theta_L\theta_H(12-\theta_L^2)+14\theta_H^2(2-\theta_L^2)+2b(\theta_H+\theta_L)(16-13\theta_H^2+2\theta_H\theta_L-13\theta_L^2)+2b^2(16-25\theta_H^2-22\theta_L\theta_H-25\theta_L^2).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** A uniform allocation is a pair $x=(N_B,N_S)$, a discriminatory one a triple $y=(N_B,N_L,N_H)$ (low type before high type, the order of the arguments of $\Pi^D$ in (6)). The optima are maximizers over all real participation levels, the object the paper's first-order conditions (7)–(11) solve; no $[0,1]$ box is imposed. Assumption 1 is transcribed as printed, with $v<4-(b+\theta_L)^2-(b+\theta_H)^2$ in (i) (the bound $\bar b$ on p. 3344 corresponds to $2v<\dots$; see the goal's note). Surpluses are Lean interval integrals of affine integrands, not their closed forms. The buyer-surplus function under discrimination takes $\theta_H,\theta_L$ as (unused) arguments for a uniform signature. $\sqrt{\cdot}$ is `Real.sqrt`, which returns $0$ on negative input; on the parameter region of the mission its argument is positive.
-- source:
--   de Cornière, Mantovani & Shekhar, Third-Degree Price Discrimination in Two-Sided Markets, Management Science 71(4) (2025), pp. 3343–3344, §3.1–§3.4, (1), (3)–(6), Assumption 1; p. 3346, Proposition 2 (b̂); p. 3352, App. A.2.1–A.2.2 and A.2(ii) (λ); p. 3355, footnote 14

import Mathlib

namespace TwoSidedPD.Baseline

/-- Assumption 1 (p. 3343), exactly as printed:
(i) `0 < v < 4 - (b + θL)^2 - (b + θH)^2`; (ii) `(θH - 3 θL)/2 < b`. -/
def Assumption1 (v b θH θL : ℝ) : Prop :=
  (0 < v ∧ v < 4 - (b + θL) ^ 2 - (b + θH) ^ 2) ∧ (θH - 3 * θL) / 2 < b

/-- Uniform pricing, inverse demand of buyers, display (3): `P^U(N_B, N_S) = v + b N_S - N_B`. -/
def PU (v b NB NS : ℝ) : ℝ := v + b * NS - NB

/-- Uniform pricing, inverse demand of sellers (common fee), display (3):
`F^U(N_B, N_S) = ((θL + θH) N_B - N_S)/2`. -/
noncomputable def FU (θH θL NB NS : ℝ) : ℝ := ((θL + θH) * NB - NS) / 2

/-- Platform profit under uniform pricing, display (4), at the allocation `x = (N_B, N_S)`. -/
noncomputable def profitU (v b θH θL : ℝ) (x : ℝ × ℝ) : ℝ :=
  x.1 * PU v b x.1 x.2 + x.2 * FU θH θL x.1 x.2

/-- Price discrimination, inverse demand of buyers, display (5):
`P^D(N_B, N_L, N_H) = v + b (N_L + N_H) - N_B`. -/
def PD (v b NB NL NH : ℝ) : ℝ := v + b * (NL + NH) - NB

/-- Price discrimination, fee of high-type sellers, display (5): `F^D_H(N_B, N_H) = θH N_B - N_H`. -/
def FDH (θH NB NH : ℝ) : ℝ := θH * NB - NH

/-- Price discrimination, fee of low-type sellers, display (5): `F^D_L(N_B, N_L) = θL N_B - N_L`. -/
def FDL (θL NB NL : ℝ) : ℝ := θL * NB - NL

/-- Platform profit under price discrimination, display (6), at the allocation
`y = (N_B, N_L, N_H)`: `y.1 = N_B`, `y.2.1 = N_L` (low type), `y.2.2 = N_H` (high type). -/
def profitD (v b θH θL : ℝ) (y : ℝ × ℝ × ℝ) : ℝ :=
  y.1 * PD v b y.1 y.2.1 y.2.2 + y.2.1 * FDL θL y.1 y.2.1 + y.2.2 * FDH θH y.1 y.2.2

/-- `x = (N_B, N_S)` is a uniform-pricing equilibrium: a global maximizer of `Π^U` over `ℝ × ℝ`. -/
def IsUniformOpt (v b θH θL : ℝ) (x : ℝ × ℝ) : Prop :=
  ∀ x' : ℝ × ℝ, profitU v b θH θL x' ≤ profitU v b θH θL x

/-- `y = (N_B, N_L, N_H)` is a price-discrimination equilibrium: a global maximizer of `Π^D`
over `ℝ × ℝ × ℝ`. -/
def IsDiscrOpt (v b θH θL : ℝ) (y : ℝ × ℝ × ℝ) : Prop :=
  ∀ y' : ℝ × ℝ × ℝ, profitD v b θH θL y' ≤ profitD v b θH θL y

/-- Participation of sellers of type `θ ∈ {θH, θL}` under uniform pricing at `x = (N_B, N_S)`:
the demand `D_j(N_B, f) = θ N_B - f` at the common fee `f = F^U(N_B, N_S)` (§3.1, footnote 14). -/
noncomputable def sellerU (θ θH θL : ℝ) (x : ℝ × ℝ) : ℝ := θ * x.1 - FU θH θL x.1 x.2

/-- Buyer surplus under uniform pricing (App. A.2.1):
`CS^U = ∫_0^{N_B} (v + b (N^U_H + N^U_L) - p^U - k) dk`. -/
noncomputable def buyerSurplusU (v b θH θL : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ k in (0:ℝ)..x.1,
    (v + b * (sellerU θH θH θL x + sellerU θL θH θL x) - PU v b x.1 x.2 - k)

/-- Surplus of sellers of type `θ` under uniform pricing (App. A.2.1):
`DS^U_j = ∫_0^{N^U_j} (θ_j N_B - f^U - k) dk`. -/
noncomputable def sellerSurplusU (θ θH θL : ℝ) (x : ℝ × ℝ) : ℝ :=
  ∫ k in (0:ℝ)..(sellerU θ θH θL x), (θ * x.1 - FU θH θL x.1 x.2 - k)

/-- Total welfare under uniform pricing (App. A.2.1): `SW^U = CS^U + Π^U + DS^U_H + DS^U_L`. -/
noncomputable def welfareU (v b θH θL : ℝ) (x : ℝ × ℝ) : ℝ :=
  buyerSurplusU v b θH θL x + profitU v b θH θL x +
    sellerSurplusU θH θH θL x + sellerSurplusU θL θH θL x

/-- Buyer surplus under price discrimination (App. A.2.2, (A.6)):
`CS^D = ∫_0^{N_B} (v + b (N_H + N_L) - p^D - k) dk`. -/
noncomputable def buyerSurplusD (v b θH θL : ℝ) (y : ℝ × ℝ × ℝ) : ℝ :=
  ∫ k in (0:ℝ)..y.1, (v + b * (y.2.2 + y.2.1) - PD v b y.1 y.2.1 y.2.2 - k)

/-- Surplus of high-type sellers under price discrimination (App. A.2.2, (A.7)):
`DS^D_H = ∫_0^{N_H} (θH N_B - f^D_H - k) dk`. -/
noncomputable def sellerSurplusDH (θH : ℝ) (y : ℝ × ℝ × ℝ) : ℝ :=
  ∫ k in (0:ℝ)..y.2.2, (θH * y.1 - FDH θH y.1 y.2.2 - k)

/-- Surplus of low-type sellers under price discrimination (App. A.2.2, (A.7)):
`DS^D_L = ∫_0^{N_L} (θL N_B - f^D_L - k) dk`. -/
noncomputable def sellerSurplusDL (θL : ℝ) (y : ℝ × ℝ × ℝ) : ℝ :=
  ∫ k in (0:ℝ)..y.2.1, (θL * y.1 - FDL θL y.1 y.2.1 - k)

/-- Total welfare under price discrimination (App. A.2.2, (A.8)):
`SW^D = CS^D + Π^D + DS^D_L + DS^D_H`. -/
noncomputable def welfareD (v b θH θL : ℝ) (y : ℝ × ℝ × ℝ) : ℝ :=
  buyerSurplusD v b θH θL y + profitD v b θH θL y + sellerSurplusDL θL y + sellerSurplusDH θH y

/-- The threshold of Proposition 2(iii) (p. 3346):
`b̂(θH, θL) = (√(32 - 7(θH - θL)^2) - 3θH - θL)/4`. -/
noncomputable def bhat (θH θL : ℝ) : ℝ :=
  (Real.sqrt (32 - 7 * (θH - θL) ^ 2) - 3 * θH - θL) / 4

/-- The denominator of the uniform-pricing closed forms (12): `8 - (2b + θH + θL)^2`. -/
def Uden (b θH θL : ℝ) : ℝ := 8 - (2 * b + θH + θL) ^ 2

/-- The denominator of the price-discrimination closed forms (13)–(15):
`4 - 2b^2 - θH^2 - θL^2 - 2b(θH + θL)`. -/
def Dden (b θH θL : ℝ) : ℝ := 4 - 2 * b ^ 2 - θH ^ 2 - θL ^ 2 - 2 * b * (θH + θL)

/-- The quartic `λ` of App. A.2(ii) (p. 3352), term by term as printed. -/
def lam (b θH θL : ℝ) : ℝ :=
  32 - 24 * b ^ 4 - 7 * θH ^ 4 + 2 * θH ^ 3 * θL + 28 * θL ^ 2 - 7 * θL ^ 4
    - 48 * b ^ 3 * (θH + θL) - 2 * θL * θH * (12 - θL ^ 2) + 14 * θH ^ 2 * (2 - θL ^ 2)
    + 2 * b * (θH + θL) * (16 - 13 * θH ^ 2 + 2 * θH * θL - 13 * θL ^ 2)
    + 2 * b ^ 2 * (16 - 25 * θH ^ 2 - 22 * θL * θH - 25 * θL ^ 2)

end TwoSidedPD.Baseline


