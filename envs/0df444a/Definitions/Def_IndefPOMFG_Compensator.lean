-- Prove2me | Definitions.Def_IndefPOMFG_Compensator
-- name    : IndefPOMFG_Compensator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:19.065398+00:00
-- url     : https://prove2.me/theorems/85436358-1878-4c54-aef4-0f154f3c59a4
-- title:
--   Relaxed compensators: Υ([0,T];𝕊ⁿ), (23), J^P_i (24), Condition (PD), Definition 4.6, Condition (RC), and 𝒥^P_i (p.17) (corrected: M^P, Q̂^P, S̃^P, R̃^P)
-- statement:
--   $\Upsilon([0,T];\mathbb S^n)$ is the set of symmetric-matrix functions $P_t=P_0+\int_0^t\dot P_sds$. For such $P$ the **compensated weights** (23) are
--
--   $$Q^P=Q+\dot P+PA+A^\top P+D^\top PD,\qquad S^P=S+PB+D^\top PF,\qquad R^P=R+F^\top PF,\qquad L^P_T=L_T-P_T,$$
--
--   together with the inhomogeneous terms $q^P,r^P,M^P,l^P_T,m^P_T$, and the compensated limiting cost $J^P_i$ of (24). $P$ is a **relaxed compensator** (Definition 4.6) if $(Q^P,S^P,R^P,L^P_T)$ satisfies **Condition (PD)**:
--
--   $$\begin{pmatrix}Q^P_t&S^P_t\\(S^P_t)^\top&R^P_t\end{pmatrix}\ge0\ \ (t\in[0,T]),\qquad R^P\gg0,\qquad L^P_T\ge0.$$
--
--   **Condition (RC)**, (26), asks $Q^P_t-S^P_t(R^P_t)^{-1}(S^P_t)^\top\ge0$ for $t\in[0,T]$, $P_T\le L_T$ and $R+F^\top PF\gg0$. The compensated $N$-player cost $\mathcal J^P_i$ of p.17 is built from twelve abbreviations $\tilde Q^P,\bar Q^P,\tilde q^P,\bar q^P,\hat Q^P,\tilde S^P,\tilde R^P,\tilde r^P,\bar r^P,\hat q^P,\hat r^P,\tilde M^P$.
--
--   These objects turn the indefinite cost into an equivalent one whose weights satisfy the usual positivity conditions; they are the paper's main device.
--
--   **Formalization Note** The regularity of $\dot P$ is not printed; it is read as integrable. "$\ge0$" for time-dependent matrices is a nonnegative quadratic form at every $t\in[0,T]$. Itô corrections printed $\sigma^\top P\sigma$ are traces. Corrections, each checked against Itô's formula: (23)/App. B omit $2\langle\bar D^\top P\bar F u^0,x^0\rangle$ in $M^P$ (without it (25) fails: $\bar D=\bar F=R=1$, $P\equiv1$, $x^0\equiv u^0\equiv1$, $u=0$, other data $0$ give $J_i=0$ but $J^P_i+\frac12\langle P_0x,x\rangle=-T$); on p.17 $\hat Q^P=-\beta_2S+\dots$ and $\tilde S^P=\bar F^\top P\bar D+\dots$ are ill-typed for $m\ne n$ (here $-\beta_2S^\top$ and $\bar D^\top P\bar F$), and $\tilde R^P=\beta_1R+\dots$ should be $\beta_1^2R+\dots$ (with $P=0$, $R=1$, $\beta_1=2$, $N=1$ the printed $\mathcal J^P_i$ has the opposite sign of $\mathcal J_i$).
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, Υ and (23)–(24) p.10, Definition 4.6, Condition (PD), Condition (RC) (26) p.11, 𝒥^P_i p.17

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

namespace IndefPOMFG

variable {n m d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- `P ∈ Υ([0, T]; 𝕊ⁿ)` (p.10) with derivative `Ṗ`: `P` is `𝕊ⁿ`-valued on `[0, T]` and
`P_t = P_0 + ∫₀ᵗ Ṗ_s ds`.

**Formalization Note** The paper prints no regularity of `Ṗ`; it is read as Lebesgue
integrable (`P` absolutely continuous), the weakest reading. -/
def IsUpsilon (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsACMat c.T P Pdot ∧ ∀ t ≤ c.T, (P t).IsSymm

/-- `Q^P = Q + Ṗ + PA + AᵀP + DᵀPD` of (23), p.10. -/
def QPm (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin n) ℝ :=
  c.Q t + Pdot t + P t * c.A t + (c.A t)ᵀ * P t + (c.D t)ᵀ * P t * c.D t

/-- `S^P = S + PB + DᵀPF` of (23), p.10. -/
def SPm (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin m) ℝ :=
  c.S t + P t * c.B t + (c.D t)ᵀ * P t * c.F t

/-- `R^P = R + FᵀPF` of (23), p.10. -/
def RPm (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin m) (Fin m) ℝ :=
  c.R t + (c.F t)ᵀ * P t * c.F t

/-- Condition (PD) (p.11) for the compensated quadruple `(Q^P, S^P, R^P, L^P_T)`:
`[Q^P S^P; (S^P)ᵀ R^P] ≥ 0` for every `t ∈ [0, T]`, `R^P ≫ 0`, `L^P_T = L_T − P_T ≥ 0`. -/
def PDcond (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ t ≤ c.T, QNonneg (Matrix.fromBlocks (QPm c P Pdot t) (SPm c P t) (SPm c P t)ᵀ (RPm c P t)))
    ∧ UnifPD c.T (RPm c P) ∧ QNonneg (c.LT - P c.T)

/-- `P` is a relaxed compensator for Problem (MFD), Definition 4.6 (p.11): `P ∈ Υ([0, T]; 𝕊ⁿ)`
and `(Q^P, S^P, R^P, L^P_T)` satisfies Condition (PD). -/
def IsRelaxedCompensator (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Pdot, IsUpsilon c P Pdot ∧ PDcond c P Pdot

/-- The inequalities (26) of Condition (RC) (p.11), for every `t ∈ [0, T]`:
`Ṗ + PA + AᵀP + DᵀPD + Q − (S + PB + DᵀPF)(R + FᵀPF)⁻¹(S + PB + DᵀPF)ᵀ ≥ 0`, `P_T ≤ L_T`,
`R + FᵀPF ≫ 0`. -/
def RCcond (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ t ≤ c.T, QNonneg (QPm c P Pdot t - SPm c P t * (RPm c P t)⁻¹ * (SPm c P t)ᵀ)) ∧
    QNonneg (c.LT - P c.T) ∧ UnifPD c.T (RPm c P)

/-- `P ∈ Υ([0, T]; 𝕊ⁿ)` satisfies Condition (RC), (26), p.11. -/
def CondRC (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Pdot, IsUpsilon c P Pdot ∧ RCcond c P Pdot

/-- `q^P = q + Pb + DᵀPb̄ + (PĀ + DᵀPD̄ − α₁Q)x⁰ + (PB̄ + DᵀPF̄ − β₂S)u⁰` of (23), at the values
`x⁰ = x0`, `u⁰ = u0`. -/
def qPv (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) (x0 : Fin n → ℝ)
    (u0 : Fin m → ℝ) : Fin n → ℝ :=
  c.q t + P t *ᵥ c.b t + (c.D t)ᵀ *ᵥ (P t *ᵥ c.bb t)
    + (P t * c.Ab t + (c.D t)ᵀ * P t * c.Db t - c.α₁ • c.Q t) *ᵥ x0
    + (P t * c.Bb t + (c.D t)ᵀ * P t * c.Fb t - c.β₂ • c.S t) *ᵥ u0

/-- `r^P = r + FᵀPb̄ + (FᵀPD̄ − α₂Sᵀ)x⁰ + (FᵀPF̄ − β₁R)u⁰` of (23). -/
def rPv (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) (x0 : Fin n → ℝ)
    (u0 : Fin m → ℝ) : Fin m → ℝ :=
  c.r t + (c.F t)ᵀ *ᵥ (P t *ᵥ c.bb t)
    + ((c.F t)ᵀ * P t * c.Db t - c.α₂ • (c.S t)ᵀ) *ᵥ x0
    + ((c.F t)ᵀ * P t * c.Fb t - c.β₁ • c.R t) *ᵥ u0

/-- `M^P` of (23), corrected:
`⟨(α₁²Q + D̄ᵀPD̄)x⁰ + 2D̄ᵀPb̄ − 2α₁q, x⁰⟩ + 2α₂β₂⟨Su⁰, x⁰⟩ + b̄ᵀPb̄ + tr(σᵀPσ) + tr(σ̄ᵀPσ̄)
 + ⟨(β₁²R + F̄ᵀPF̄)u⁰ + 2F̄ᵀPb̄ − 2β₁r, u⁰⟩ + 2⟨D̄ᵀPF̄u⁰, x⁰⟩`.

**Formalization Note** (23) prints `σᵀPσ + σ̄ᵀPσ̄` for `σ, σ̄ ∈ ℝ^{n×d}`; the Itô correction is
the trace. (23) and App. B (p.22) omit the cross term `2⟨D̄ᵀPF̄u⁰, x⁰⟩` of `⟨P c, c⟩` with
`c = D̄x⁰ + F̄u⁰ + b̄`, without which (25) fails (scalar example: `D̄ = F̄ = 1`, `P ≡ 1`,
`x⁰ ≡ u⁰ ≡ 1`, other data `0`, `R = 1`, `u = 0`: `J_i = 0` but printed `J^P_i + ½⟨P₀x, x⟩ = −T`). -/
def MPv (c : Coeffs n m d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) (x0 : Fin n → ℝ)
    (u0 : Fin m → ℝ) : ℝ :=
  ((c.α₁ ^ 2 • c.Q t + (c.Db t)ᵀ * P t * c.Db t) *ᵥ x0 + (2 : ℝ) • ((c.Db t)ᵀ *ᵥ (P t *ᵥ c.bb t))
      - (2 * c.α₁) • c.q t) ⬝ᵥ x0
    + 2 * c.α₂ * c.β₂ * ((c.S t *ᵥ u0) ⬝ᵥ x0)
    + c.bb t ⬝ᵥ (P t *ᵥ c.bb t)
    + Matrix.trace ((c.σ t)ᵀ * P t * c.σ t) + Matrix.trace ((c.σb t)ᵀ * P t * c.σb t)
    + ((c.β₁ ^ 2 • c.R t + (c.Fb t)ᵀ * P t * c.Fb t) *ᵥ u0
        + (2 : ℝ) • ((c.Fb t)ᵀ *ᵥ (P t *ᵥ c.bb t)) - (2 * c.β₁) • c.r t) ⬝ᵥ u0
    + 2 * ((((c.Db t)ᵀ * P t * c.Fb t) *ᵥ u0) ⬝ᵥ x0)

/-- The compensated cost `J^P_i(u)` of (24), p.10, along a limiting state `X` (a solution of (10)
under `u`), with the coefficients (23) (corrected `M^P`, see `MPv`):
`½ E[∫₀ᵀ {⟨Q^P X + 2q^P, X⟩ + 2⟨S^P u, X⟩ + M^P + ⟨R^P u + 2r^P, u⟩} dt + ⟨L^P_T X_T + 2l^P_T, X_T⟩ + m^P_T]`,
`L^P_T = L_T − P_T`, `l^P_T = l_T − α₃L_Tx⁰_T`, `m^P_T = ⟨α₃²L_Tx⁰_T − 2α₃l_T, x⁰_T⟩`. -/
noncomputable def JP (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (Pr : Measure Ω) (X : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ)
    (x0 : ℝ≥0 → Ω → Fin n → ℝ) (u0 : ℝ≥0 → Ω → Fin m → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ ω, ((∫ s in Icc (0 : ℝ) c.T,
      ((QPm c P Pdot s.toNNReal *ᵥ X s.toNNReal ω
          + (2 : ℝ) • qPv c P s.toNNReal (x0 s.toNNReal ω) (u0 s.toNNReal ω)) ⬝ᵥ X s.toNNReal ω
        + 2 * ((SPm c P s.toNNReal *ᵥ u s.toNNReal ω) ⬝ᵥ X s.toNNReal ω)
        + MPv c P s.toNNReal (x0 s.toNNReal ω) (u0 s.toNNReal ω)
        + (RPm c P s.toNNReal *ᵥ u s.toNNReal ω
            + (2 : ℝ) • rPv c P s.toNNReal (x0 s.toNNReal ω) (u0 s.toNNReal ω)) ⬝ᵥ u s.toNNReal ω))
      + ((c.LT - P c.T) *ᵥ X c.T ω + (2 : ℝ) • (c.lT - c.α₃ • (c.LT *ᵥ x0 c.T ω))) ⬝ᵥ X c.T ω
      + (c.α₃ ^ 2 • (c.LT *ᵥ x0 c.T ω) - (2 * c.α₃) • c.lT) ⬝ᵥ x0 c.T ω) ∂Pr

/-- The running integrand of the compensated `N`-player cost `𝒥^P_i` (p.17) at time `t`, for the
values `x = xⁱ_t`, `u = uⁱ_t`, `xN = x⁽ᴺ⁾_t`, `uN = u⁽ᴺ⁾_t`:
`⟨Q^P x + 2q̃^P + 2S^P u, x⟩ + ⟨R^P u + 2r̃^P, u⟩ + ⟨Q̃^P xN, xN⟩ + 2⟨Q̄^P x + r̄^P u + q̄^P, xN⟩
 + ⟨R̃^P uN, uN⟩ + 2⟨Q̂^P x + r̂^P u + q̂^P, uN⟩ + M̃^P + 2⟨S̃^P uN, xN⟩`, with
`Q̃^P = α₁²Q + D̄ᵀPD̄`, `Q̄^P = −α₁Q + ĀᵀP + D̄ᵀPD`, `q̃^P = q + Pb + DᵀPb̄`, `q̄^P = −α₁q + D̄ᵀPb̄`,
`Q̂^P = −β₂Sᵀ + B̄ᵀP + F̄ᵀPD`, `S̃^P = D̄ᵀPF̄ + α₂β₂S`, `R̃^P = β₁²R + F̄ᵀPF̄`, `r̃^P = r + FᵀPb̄`,
`r̄^P = −α₂S + D̄ᵀPF`, `q̂^P = F̄ᵀPb̄ − β₁r`, `r̂^P = F̄ᵀPF − β₁R`,
`M̃^P = b̄ᵀPb̄ + tr(σᵀPσ) + tr(σ̄ᵀPσ̄)`.

**Formalization Note** Three printed abbreviations are corrected. `Q̂^P = −β₂S + …` and
`S̃^P = F̄ᵀPD̄ + α₂β₂S` are ill-typed for `m ≠ n` (`S ∈ ℝ^{n×m}`, `F̄ᵀPD̄ ∈ ℝ^{m×n}`); the Itô
expansion gives `−β₂Sᵀ` and `D̄ᵀPF̄`. `R̃^P = β₁R + F̄ᵀPF̄` is printed with `β₁` where the cost (5)
contributes `β₁²R` (scalar example: `P = 0`, `R = 1`, `β₁ = 2`, `N = 1`, other data `0`: (5) gives
`½E∫u²`, the printed `𝒥^P_i` gives `−½E∫u²`). `q̄^P = −α₁q + b̄ᵀPD̄` is the row form of `−α₁q + D̄ᵀPb̄`;
the traces are the Itô corrections printed `σᵀPσ`, `σ̄ᵀPσ̄`. -/
def NPRate (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0)
    (x : Fin n → ℝ) (u : Fin m → ℝ) (xN : Fin n → ℝ) (uN : Fin m → ℝ) : ℝ :=
  let Pt := P t
  let Qtil := c.α₁ ^ 2 • c.Q t + (c.Db t)ᵀ * Pt * c.Db t
  let Qbar := -(c.α₁ • c.Q t) + (c.Ab t)ᵀ * Pt + (c.Db t)ᵀ * Pt * c.D t
  let qtil := c.q t + Pt *ᵥ c.b t + (c.D t)ᵀ *ᵥ (Pt *ᵥ c.bb t)
  let qbar := -(c.α₁ • c.q t) + (c.Db t)ᵀ *ᵥ (Pt *ᵥ c.bb t)
  let Qhat := -(c.β₂ • (c.S t)ᵀ) + (c.Bb t)ᵀ * Pt + (c.Fb t)ᵀ * Pt * c.D t
  let Stil := (c.Db t)ᵀ * Pt * c.Fb t + (c.α₂ * c.β₂) • c.S t
  let Rtil := c.β₁ ^ 2 • c.R t + (c.Fb t)ᵀ * Pt * c.Fb t
  let rtil := c.r t + (c.F t)ᵀ *ᵥ (Pt *ᵥ c.bb t)
  let rbar := -(c.α₂ • c.S t) + (c.Db t)ᵀ * Pt * c.F t
  let qhat := (c.Fb t)ᵀ *ᵥ (Pt *ᵥ c.bb t) - c.β₁ • c.r t
  let rhat := (c.Fb t)ᵀ * Pt * c.F t - c.β₁ • c.R t
  let Mtil := c.bb t ⬝ᵥ (Pt *ᵥ c.bb t) + Matrix.trace ((c.σ t)ᵀ * Pt * c.σ t)
    + Matrix.trace ((c.σb t)ᵀ * Pt * c.σb t)
  (QPm c P Pdot t *ᵥ x + (2 : ℝ) • qtil + (2 : ℝ) • (SPm c P t *ᵥ u)) ⬝ᵥ x
    + (RPm c P t *ᵥ u + (2 : ℝ) • rtil) ⬝ᵥ u
    + (Qtil *ᵥ xN) ⬝ᵥ xN
    + 2 * ((Qbar *ᵥ x + rbar *ᵥ u + qbar) ⬝ᵥ xN)
    + (Rtil *ᵥ uN) ⬝ᵥ uN
    + 2 * ((Qhat *ᵥ x + rhat *ᵥ u + qhat) ⬝ᵥ uN)
    + Mtil
    + 2 * ((Stil *ᵥ uN) ⬝ᵥ xN)

/-- The compensated `N`-player cost `𝒥^P_i(uⁱ, u⁻ⁱ)` (p.17) along the states `x` of the profile `u`:
`½ E[∫₀ᵀ NPRate dt + ⟨L^P_T xⁱ_T + 2l_T, xⁱ_T⟩ − 2α₃⟨L_T xⁱ_T + l_T, x⁽ᴺ⁾_T⟩ + α₃²⟨L_T x⁽ᴺ⁾_T, x⁽ᴺ⁾_T⟩]`. -/
noncomputable def NCostP (c : Coeffs n m d) (P Pdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (Pr : Measure Ω) (x : Fin N → ℝ≥0 → Ω → Fin n → ℝ) (u : Fin N → ℝ≥0 → Ω → Fin m → ℝ)
    (i : Fin N) : ℝ :=
  (1 / 2 : ℝ) * ∫ ω, ((∫ s in Icc (0 : ℝ) c.T,
      NPRate c P Pdot s.toNNReal (x i s.toNNReal ω) (u i s.toNNReal ω) (avg x s.toNNReal ω)
        (avg u s.toNNReal ω))
      + ((c.LT - P c.T) *ᵥ x i c.T ω + (2 : ℝ) • c.lT) ⬝ᵥ x i c.T ω
      - 2 * c.α₃ * ((c.LT *ᵥ x i c.T ω + c.lT) ⬝ᵥ avg x c.T ω)
      + c.α₃ ^ 2 * ((c.LT *ᵥ avg x c.T ω) ⬝ᵥ avg x c.T ω)) ∂Pr

end IndefPOMFG


