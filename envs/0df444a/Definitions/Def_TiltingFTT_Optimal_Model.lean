-- Prove2me | Definitions.Def_TiltingFTT_Optimal_Model
-- name    : TiltingFTT_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:53.977285+00:00
-- url     : https://prove2.me/theorems/09cf7e2f-6cd9-4aa4-a2ae-56270ce1d55a
-- title:
--   §2–§5, pp. 9–29 — firm values (1)–(3), (23), prices, participation and IC constraints, separating and pooling equilibria, welfare W, T̄_L, τ*, τ_0
-- statement:
--   This file sets up the asset-trade signaling model of Dieler, Biswas, Calzolari and Castiglionesi.
--
--   **Parameters.** The state of the world is $\omega\in\{L,H\}$, with $\Pr(H)=\beta$. A single informed trader (discount factor $\delta_I$) observes $\omega$ and buys a quantity $T\in[0,1]$ of the firm's stock from a unit mass of competitive uninformed traders (discount factor $\delta_U$). The buyer pays a financial transaction tax (FTT) $\tau\ge 0$ proportional to the purchase value. Firm values are: $F_\omega$ when the manager invests knowing $\omega$; $\bar F_\omega$ when she invests on the prior; $F^{-\omega}_\omega$ when she invests as if the state were $-\omega$. The ex-ante value under prior investment is $\bar F=\beta\bar F_H+(1-\beta)\bar F_L$.
--
--   **Standing assumptions** (`Standing`): condition (1) $F_\omega\ge\bar F_\omega\ge F^{-\omega}_\omega$ in both states; condition (3) $F^L_H>F_L$ and $F^H_L>0$; $F_H>F_L$, $\bar F_H>\bar F_L$, $\delta_U<\delta_I$; and $\delta_U>0$, $0<\beta<1$. **Specification (23)** (`Spec23`): $F_\omega=V_\omega+v$, $\bar F_\omega=V_\omega$, $F^{-\omega}_\omega=V_\omega-v$ with $V_H>V_L>0$.
--
--   **Equilibria.** A *separating equilibrium* (beliefs (11)) is a pair $T_H\ne T_L$ in $[0,1]$ with prices $P_\omega=\delta_UF_\omega$ (13), satisfying participation (14) $-(1+\tau)P_\omega T_\omega+\delta_IT_\omega F_\omega\ge 0$, the incentive constraints (16) against mimicking the other type, and (31) against every other quantity $T'\in[0,1]$, which is priced at $P_H$ and yields $F^H_\omega$. A *pooling equilibrium* (beliefs (18)) is a common trade $T_P\in(0,1]$ at price $P_P=\delta_U\bar F$ with firm value $\bar F_\omega$, satisfying participation (20) and the constraint (21) against every other $T'\in[0,1]$, priced at $\delta_UF_H$.
--
--   **Closed forms.**
--   $$\bar T_L=\frac{(\delta_I-(1+\tau)\delta_U)F_H}{\delta_IF^L_H-(1+\tau)\delta_UF_L},\quad \underline T_L=\frac{\delta_IF^H_L-(1+\tau)\delta_UF_H}{(\delta_I-(1+\tau)\delta_U)F_L},\quad \underline T_P=\frac{(\delta_I-(1+\tau)\delta_U)F_H}{\delta_I\bar F_H-(1+\tau)\delta_U\bar F},$$
--   $$\tau^*=\frac{\delta_I}{\delta_U}\frac{\bar F_L}{\bar F}-1,\qquad \tau_{FB}=\frac{\delta_I}{\delta_U}-1,$$
--   $$\tau_0=\frac{(1-\beta)(\delta_I-\delta_U)F_L\big(\delta_I(F_H-F^L_H)-\delta_U(F_H-F_L)\big)+\delta_I(\delta_IF^L_H-\delta_UF_L)v}{\delta_UF_L\big((1-\beta)(\delta_I-\delta_U)(F_H-F_L)+\delta_Iv\big)}.$$
--
--   **Welfare.** The welfare of a trade profile is the bracket of (8), $\sum_\omega\Pr(\omega)[-(1+\tau)P_\omega T_\omega+\delta_IT_\omega x_\omega+P_\omega T_\omega+\delta_U(1-T_\omega)x_\omega+\tau P_\omega T_\omega]$, evaluated at the realized firm value $x_\omega$ ($F_\omega$ when separating, $\bar F_\omega$ when pooling). $W^*=\delta_I(\beta F_H+(1-\beta)F_L)$, and $W_S(\tau)=W^*-(1-\beta)(\delta_I-\delta_U)(1-\bar T_L(\tau))F_L$ is separating welfare at the Pareto-optimal trade $T_H=1$, $T_L=\bar T_L(\tau)$.
--
--   **Formalization Note.** Every ratio condition of the paper ((7)/(15), (17), (22), Proposition 4) is stored cross-multiplied (`Cond15`, `Cond17`, `Cond22`, `Coexist`), so that no division by zero enters; where the paper's denominator $F_H-\bar F_H$ or $F_H-F^L_H$ vanishes it reads the fraction as arbitrarily large, which is exactly what the cross-multiplied form says. The readings $\delta_U>0$ and $0<\beta<1$ are not printed but are implicit in "discount factor" and in the two states having probabilities $\beta$ and $1-\beta$.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), §2–§5 and Appendix A, pp. 9–29 and 41–47: (1)–(3), (8), (11), (13)–(16), (18)–(21), (23), (24), (31), (32), T̲_P (p. 45), τ_0 (p. 47), τ_FB (p. 14), τ* (Proposition 6)

import Mathlib

namespace TiltingFTT.Optimal

/-- The parameters of the economy (§2, pp. 9–11). There are two states, `L` and `H`; the
`H`-state has prior probability `β`.
* `δI`, `δU`: discount factors of the informed trader and of the uninformed traders;
* `FH`, `FL`: firm value `F_ω` when the manager invests knowing the state `ω`;
* `FbH`, `FbL`: firm value `F̄_ω` when the manager invests on the prior `β`;
* `FLH`: `F^L_H`, value in state `H` when the manager invested as if the state were `L`;
* `FHL`: `F^H_L`, value in state `L` when the manager invested as if the state were `H`. -/
structure Firm where
  β : ℝ
  δI : ℝ
  δU : ℝ
  FH : ℝ
  FL : ℝ
  FbH : ℝ
  FbL : ℝ
  FLH : ℝ
  FHL : ℝ

/-- Ex-ante expected firm value under prior investment, `F̄ = β F̄_H + (1 − β) F̄_L` (p. 10). -/
def Fbar (P : Firm) : ℝ := P.β * P.FbH + (1 - P.β) * P.FbL

/-- Standing assumptions of §2: condition (1) `F_ω ≥ F̄_ω ≥ F^{−ω}_ω` for both states,
condition (3) `F^L_H > F_L`, `F^H_L > 0`, `F_H > F_L`, `F̄_H > F̄_L`, `δ_U < δ_I`, together with
the readings `0 < δ_U` (a discount factor) and `0 < β < 1` (both states occur). -/
def Standing (P : Firm) : Prop :=
  P.FbH ≤ P.FH ∧ P.FLH ≤ P.FbH ∧ P.FbL ≤ P.FL ∧ P.FHL ≤ P.FbL ∧
  P.FL < P.FLH ∧ 0 < P.FHL ∧
  P.FL < P.FH ∧ P.FbL < P.FbH ∧ P.δU < P.δI ∧
  0 < P.δU ∧ 0 < P.β ∧ P.β < 1

/-- The specification (23) of §5 (p. 23): `F_ω = V_ω + v`, `F̄_ω = V_ω`, `F^{−ω}_ω = V_ω − v`,
with `V_H > V_L > 0`. -/
def Spec23 (P : Firm) (VH VL v : ℝ) : Prop :=
  VL < VH ∧ 0 < VL ∧ P.FH = VH + v ∧ P.FL = VL + v ∧ P.FbH = VH ∧ P.FbL = VL ∧
  P.FLH = VH - v ∧ P.FHL = VL - v

/-- Conditions (7)/(15), `δ_I / (δ_U (1 + τ)) ≥ 1`, cross-multiplied. -/
def Cond15 (P : Firm) (τ : ℝ) : Prop := (1 + τ) * P.δU ≤ P.δI

/-- Condition (17), `(F_H − F_L)/(F_H − F^L_H) ≥ δ_I / (δ_U (1 + τ))`, cross-multiplied. -/
def Cond17 (P : Firm) (τ : ℝ) : Prop :=
  P.δI * (P.FH - P.FLH) ≤ (1 + τ) * P.δU * (P.FH - P.FL)

/-- Condition (22), `(F_H − F̄)/(F_H − F̄_H) ≥ δ_I / (δ_U (1 + τ)) ≥ F̄ / F̄_L`, both inequalities
cross-multiplied. -/
def Cond22 (P : Firm) (τ : ℝ) : Prop :=
  P.δI * (P.FH - P.FbH) ≤ (1 + τ) * P.δU * (P.FH - Fbar P) ∧
  (1 + τ) * P.δU * Fbar P ≤ P.δI * P.FbL

/-- The coexistence region of Proposition 4 (ii),
`F̄/F̄_L < δ_I/(δ_U(1+τ)) ≤ min{(F_H − F̄)/(F_H − F̄_H), (F_H − F_L)/(F_H − F^L_H)}`,
every inequality cross-multiplied. -/
def Coexist (P : Firm) (τ : ℝ) : Prop :=
  (1 + τ) * P.δU * Fbar P < P.δI * P.FbL ∧
  P.δI * (P.FH - P.FbH) ≤ (1 + τ) * P.δU * (P.FH - Fbar P) ∧
  Cond17 P τ

/-- Upper bound of (32), `T̄_L := (δ_I − (1+τ)δ_U) F_H / (δ_I F^L_H − (1+τ) δ_U F_L)`. -/
noncomputable def Tbar (P : Firm) (τ : ℝ) : ℝ :=
  (P.δI - (1 + τ) * P.δU) * P.FH / (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)

/-- Lower bound of (32), `T̲_L := (δ_I F^H_L − (1+τ)δ_U F_H) / ((δ_I − (1+τ)δ_U) F_L)`. -/
noncomputable def Tlow (P : Firm) (τ : ℝ) : ℝ :=
  (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) / ((P.δI - (1 + τ) * P.δU) * P.FL)

/-- Lower bound of pooling trade (proof of Proposition 3, p. 45),
`T̲_P := (δ_I − (1+τ)δ_U) F_H / (δ_I F̄_H − (1+τ) δ_U F̄)`. -/
noncomputable def TlowP (P : Firm) (τ : ℝ) : ℝ :=
  (P.δI - (1 + τ) * P.δU) * P.FH / (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P)

/-- `τ* = (δ_I/δ_U)(F̄_L/F̄) − 1` (Proposition 6). -/
noncomputable def tauStar (P : Firm) : ℝ := P.δI / P.δU * (P.FbL / Fbar P) - 1

/-- `τ_FB = δ_I/δ_U − 1` (p. 14). -/
noncomputable def tauFB (P : Firm) : ℝ := P.δI / P.δU - 1

/-- `τ_0` (proof of Proposition 6, p. 47):
`τ_0 = [(1−β)(δ_I−δ_U)F_L(δ_I(F_H−F^L_H) − δ_U(F_H−F_L)) + δ_I(δ_I F^L_H − δ_U F_L)v]
       / [δ_U F_L((1−β)(δ_I−δ_U)(F_H−F_L) + δ_I v)]`. -/
noncomputable def tau0 (P : Firm) (v : ℝ) : ℝ :=
  ((1 - P.β) * (P.δI - P.δU) * P.FL * (P.δI * (P.FH - P.FLH) - P.δU * (P.FH - P.FL)) +
      P.δI * (P.δI * P.FLH - P.δU * P.FL) * v) /
    (P.δU * P.FL * ((1 - P.β) * (P.δI - P.δU) * (P.FH - P.FL) + P.δI * v))

/-- First-best welfare (8), `W* = δ_I (β F_H + (1 − β) F_L)`. -/
def Wstar (P : Firm) : ℝ := P.δI * (P.β * P.FH + (1 - P.β) * P.FL)

/-- Separating welfare (24) at the Pareto-optimal trade `T_H = 1`, `T_L = T̄_L(τ)`:
`W_S(τ) = W* − (1 − β)(δ_I − δ_U)(1 − T̄_L(τ)) F_L`. -/
noncomputable def WS (P : Firm) (τ : ℝ) : ℝ :=
  Wstar P - (1 - P.β) * (P.δI - P.δU) * (1 - Tbar P τ) * P.FL

/-- Welfare of a trade profile, the bracket of (8): with prices `pH`, `pL`, trades `TH`, `TL` and
realized firm values `xH`, `xL`,
`Σ_ω Pr(ω)[−(1+τ)P_ω T_ω + δ_I T_ω x_ω + P_ω T_ω + δ_U (1 − T_ω) x_ω + τ P_ω T_ω]`. -/
def welfare (P : Firm) (τ pH pL TH TL xH xL : ℝ) : ℝ :=
  P.β * (-(1 + τ) * pH * TH + P.δI * TH * xH + pH * TH + P.δU * (1 - TH) * xH + τ * pH * TH) +
  (1 - P.β) * (-(1 + τ) * pL * TL + P.δI * TL * xL + pL * TL + P.δU * (1 - TL) * xL + τ * pL * TL)

/-- Welfare of a separating profile: prices `P_ω = δ_U F_ω` (13), firm value `F_ω`. -/
def sepWelfare (P : Firm) (τ TH TL : ℝ) : ℝ :=
  welfare P τ (P.δU * P.FH) (P.δU * P.FL) TH TL P.FH P.FL

/-- Welfare of a pooling profile: price `P_P = δ_U F̄` (p. 20), firm value `F̄_ω`. -/
def poolWelfare (P : Firm) (τ TP : ℝ) : ℝ :=
  welfare P τ (P.δU * Fbar P) (P.δU * Fbar P) TP TP P.FbH P.FbL

/-- Separating equilibrium with the off-path beliefs (11): trades `T_H ≠ T_L` in `[0,1]`, prices
`P_ω = δ_U F_ω` (13); participation (14) in both states; incentive constraints (16) against the
other type's trade; and (31) against every other quantity `T' ∈ [0,1]`, which is priced at
`P_H = δ_U F_H` and yields firm value `F^H_ω` (`F^H_H = F_H`). -/
def IsSeparatingEq (P : Firm) (τ TH TL : ℝ) : Prop :=
  TH ∈ Set.Icc (0 : ℝ) 1 ∧ TL ∈ Set.Icc (0 : ℝ) 1 ∧ TH ≠ TL ∧
  0 ≤ -(1 + τ) * (P.δU * P.FH) * TH + P.δI * TH * P.FH ∧
  0 ≤ -(1 + τ) * (P.δU * P.FL) * TL + P.δI * TL * P.FL ∧
  -(1 + τ) * (P.δU * P.FL) * TL + P.δI * TL * P.FLH ≤
    -(1 + τ) * (P.δU * P.FH) * TH + P.δI * TH * P.FH ∧
  -(1 + τ) * (P.δU * P.FH) * TH + P.δI * TH * P.FHL ≤
    -(1 + τ) * (P.δU * P.FL) * TL + P.δI * TL * P.FL ∧
  ∀ T' ∈ Set.Icc (0 : ℝ) 1, T' ≠ TH → T' ≠ TL →
    (P.δI * P.FH - (1 + τ) * P.δU * P.FH) * T' ≤ (P.δI - (1 + τ) * P.δU) * TH * P.FH ∧
    (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * T' ≤ (P.δI - (1 + τ) * P.δU) * TL * P.FL

/-- Pooling equilibrium with the off-path beliefs (18): a common trade `T_P ∈ (0,1]` (no-trade
excluded, p. 22), price `P_P = δ_U F̄`, firm value `F̄_ω`; participation (20) in both states; and
(21) against every other quantity `T' ∈ [0,1]`, which is priced at `P' = δ_U F_H` and yields
firm value `F^H_ω` (`F^H_H = F_H`). -/
def IsPoolingEq (P : Firm) (τ TP : ℝ) : Prop :=
  TP ∈ Set.Ioc (0 : ℝ) 1 ∧
  0 ≤ (-(1 + τ) * P.δU * Fbar P + P.δI * P.FbH) * TP ∧
  0 ≤ (-(1 + τ) * P.δU * Fbar P + P.δI * P.FbL) * TP ∧
  ∀ T' ∈ Set.Icc (0 : ℝ) 1, T' ≠ TP →
    (P.δI * P.FH - (1 + τ) * P.δU * P.FH) * T' ≤
      (P.δI * P.FbH - (1 + τ) * P.δU * Fbar P) * TP ∧
    (P.δI * P.FHL - (1 + τ) * P.δU * P.FH) * T' ≤
      (P.δI * P.FbL - (1 + τ) * P.δU * Fbar P) * TP

end TiltingFTT.Optimal


