-- Prove2me | Definitions.Def_IndefPOMFG_Riccati
-- name    : IndefPOMFG_Riccati
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:14:22.297017+00:00
-- url     : https://prove2.me/theorems/881694d8-a75d-4f69-93e6-2faa2e1cda4d
-- title:
--   Riccati equations (34)–(35), ODE (36), the limit SDE (38), u⁰ (59), feedback (37) and SDE (39) (corrected: Σ̄, (39))
-- statement:
--   With $\mathcal R=R+F^\top\Pi F$ and $\tilde\Pi=\Pi B+D^\top\Pi F+S$, the **Riccati equation (34)** is
--
--   $$\dot\Pi_t+\Pi_tA_t+A_t^\top\Pi_t+D_t^\top\Pi_tD_t+Q_t-\tilde\Pi_t\mathcal R_t^{-1}\tilde\Pi_t^\top=0,\qquad\Pi_T=L_T,\qquad\mathcal R\gg0.$$
--
--   With $\tilde{\mathcal R}=(1-\beta_1)R+F^\top\Sigma(F+\bar F)$, $\tilde\Sigma=\Sigma(B+\bar B)+D^\top\Sigma(F+\bar F)+(1-\beta_2)S$ and $\bar\Sigma$ with $\bar\Sigma^\top=B^\top\Sigma+F^\top\Sigma(D+\bar D)+(1-\alpha_2)S^\top$, the asymmetric **Riccati equation (35)** is
--
--   $$\dot\Sigma_t+\Sigma_t(A_t+\bar A_t)+A_t^\top\Sigma_t+D_t^\top\Sigma_t(D_t+\bar D_t)-\tilde\Sigma_t\tilde{\mathcal R}_t^{-1}\bar\Sigma_t^\top+(1-\alpha_1)Q_t=0,\qquad\Sigma_T=(1-\alpha_3)L_T,\qquad\tilde{\mathcal R}+\tilde{\mathcal R}^\top\gg0,$$
--
--   and (36) is the linear ODE $\dot\rho+A^\top\rho-\tilde\Sigma\tilde{\mathcal R}^{-1}\tilde\rho+\Sigma b+D^\top\Sigma\bar b+q=0$, $\rho_T=l_T$, with $\tilde\rho=B^\top\rho+F^\top\Sigma\bar b+r$. The **limit SDE (38)** is
--
--   $$dx^0_t=\{[A_t+\bar A_t-(B_t+\bar B_t)\tilde{\mathcal R}_t^{-1}\bar\Sigma_t^\top]x^0_t-(B_t+\bar B_t)\tilde{\mathcal R}_t^{-1}\tilde\rho_t+b_t\}dt+\{[D_t+\bar D_t-(F_t+\bar F_t)\tilde{\mathcal R}_t^{-1}\bar\Sigma_t^\top]x^0_t-(F_t+\bar F_t)\tilde{\mathcal R}_t^{-1}\tilde\rho_t+\bar b_t\}dW^0_t,\quad x^0_0=x,$$
--
--   and $u^0_t=-\tilde{\mathcal R}_t^{-1}(\bar\Sigma_t^\top x^0_t+\tilde\rho_t)$ is (59). The module also defines the feedback (37) $-\mathcal R^{-1}\tilde\Pi^\top(\hat{\bar X}-x^0)-\tilde{\mathcal R}^{-1}(\bar\Sigma^\top x^0+\tilde\rho)$ and the SDE (39) of the optimal state.
--
--   **Formalization Note** Solutions of (34)–(36) are absolutely continuous and satisfy the equation for a.e. $t$ (App. C, p.23, calls them absolutely continuous; with bounded measurable coefficients a $C^1$ solution need not exist). p.13 prints $\bar\Sigma=\Sigma B+(D+\bar D)^\top\Sigma F+(1-\alpha_2)S$; App. C's derivation of (59) from (18) produces $B^\top\Sigma x^0+F^\top\Sigma(D+\bar D)x^0$, i.e. the transpose used here, which agrees with the printed form when $\Sigma$ is symmetric. The $dW^0$-coefficient of $x^0$ in (39) is printed with $\bar F$ (ill-typed) and is $\bar D$ here.
-- source:
--   Chen, Nie & Wu, Indefinite Linear-Quadratic Partially Observed Mean-Field Game, arXiv:2508.01568v1, (34)–(36) p.13, Theorem 4.12 (37)–(39) pp.13–14, (55)–(59) p.23

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_IndefPOMFG_Coeffs
import Definitions.Def_IndefPOMFG_Space
import Definitions.Def_IndefPOMFG_NPlayer
import Definitions.Def_IndefPOMFG_Limiting

open MeasureTheory Set Peng1990.SMP
open scoped NNReal ENNReal Matrix

namespace IndefPOMFG

variable {n m d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- `𝓡 = R + FᵀΠF` (p.13). -/
def calR (c : Coeffs n m d) (Pm : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin m) (Fin m) ℝ :=
  c.R t + (c.F t)ᵀ * Pm t * c.F t

/-- `Π̃ = ΠB + DᵀΠF + S` (p.13). -/
def tilPi (c : Coeffs n m d) (Pm : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin m) ℝ :=
  Pm t * c.B t + (c.D t)ᵀ * Pm t * c.F t + c.S t

/-- The left side of the Riccati equation (34) (p.13) at time `t`:
`Π̇ + ΠA + AᵀΠ + DᵀΠD + Q − Π̃𝓡⁻¹Π̃ᵀ`. -/
noncomputable def ric34 (c : Coeffs n m d) (Pm Pmdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin n) ℝ :=
  Pmdot t + Pm t * c.A t + (c.A t)ᵀ * Pm t + (c.D t)ᵀ * Pm t * c.D t + c.Q t
    - tilPi c Pm t * (calR c Pm t)⁻¹ * (tilPi c Pm t)ᵀ

/-- `Π` solves the Riccati equation (34) (p.13): `Π` is `𝕊ⁿ`-valued and absolutely continuous on
`[0, T]`, `Π̇ + ΠA + AᵀΠ + DᵀΠD + Q − Π̃𝓡⁻¹Π̃ᵀ = 0` for a.e. `t ∈ [0, T]`, `Π_T = L_T`, and
`𝓡 ≫ 0`.

**Formalization Note** The paper asks for `Π ∈ C([0, T]; 𝕊ⁿ)` (`Π̇` continuous, p.5), which bounded
measurable coefficients do not allow in general; solutions are read as absolutely continuous,
as App. C states for (56) (p.23), with the equation holding almost everywhere. -/
def Solves34 (c : Coeffs n m d) (Pm : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Pmdot, IsACMat c.T Pm Pmdot ∧ (∀ t ≤ c.T, (Pm t).IsSymm) ∧ Pm c.T = c.LT ∧
    UnifPD c.T (calR c Pm) ∧
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) c.T)), ric34 c Pm Pmdot s.toNNReal = 0

/-- `𝓡̃ = (1 − β₁)R + FᵀΣ(F + F̄)` (p.13). -/
def calRt (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin m) (Fin m) ℝ :=
  (1 - c.β₁) • c.R t + (c.F t)ᵀ * Sg t * (c.F t + c.Fb t)

/-- `Σ̃ = Σ(B + B̄) + DᵀΣ(F + F̄) + (1 − β₂)S` (p.13). -/
def tilSg (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin m) ℝ :=
  Sg t * (c.B t + c.Bb t) + (c.D t)ᵀ * Sg t * (c.F t + c.Fb t) + (1 - c.β₂) • c.S t

/-- `Σ̄`, corrected: `Σ̄ = ΣᵀB + (D + D̄)ᵀΣᵀF + (1 − α₂)S`, i.e. `Σ̄ᵀ = BᵀΣ + FᵀΣ(D + D̄) + (1 − α₂)Sᵀ`.

**Formalization Note** p.13 prints `Σ̄ = ΣB + (D + D̄)ᵀΣF + (1 − α₂)S`. App. C (p.23) derives `u⁰` by
substituting `φ = Π(X̄ − x⁰) + Σx⁰ + ρ` and (58) into (18), which produces `BᵀΣx⁰ + FᵀΣ(D + D̄)x⁰`,
i.e. the transpose used here. The two agree whenever `Σ` is symmetric (as (56) types it); (35)
is asymmetric (Remark 4.13(ii)) and Theorem 4.12 takes `Σ ∈ ℝ^{n×n}`. -/
def barSg (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin m) ℝ :=
  (Sg t)ᵀ * c.B t + (c.D t + c.Db t)ᵀ * (Sg t)ᵀ * c.F t + (1 - c.α₂) • c.S t

/-- The left side of the Riccati equation (35) (p.13) at time `t`:
`Σ̇ + Σ(A + Ā) + AᵀΣ + DᵀΣ(D + D̄) − Σ̃𝓡̃⁻¹Σ̄ᵀ + (1 − α₁)Q`. -/
noncomputable def ric35 (c : Coeffs n m d) (Sg Sgdot : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (t : ℝ≥0) :
    Matrix (Fin n) (Fin n) ℝ :=
  Sgdot t + Sg t * (c.A t + c.Ab t) + (c.A t)ᵀ * Sg t + (c.D t)ᵀ * Sg t * (c.D t + c.Db t)
    - tilSg c Sg t * (calRt c Sg t)⁻¹ * (barSg c Sg t)ᵀ + (1 - c.α₁) • c.Q t

/-- `Σ` solves the Riccati equation (35) (p.13): `Σ` is `ℝ^{n×n}`-valued and absolutely continuous on
`[0, T]`, (35) holds for a.e. `t`, `Σ_T = (1 − α₃)L_T`, and `𝓡̃ + 𝓡̃ᵀ ≫ 0` (reading as in
`Solves34`; `Σ̄` corrected as in `barSg`). -/
def Solves35 (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Sgdot, IsACMat c.T Sg Sgdot ∧ Sg c.T = (1 - c.α₃) • c.LT ∧
    UnifPD c.T (fun t => calRt c Sg t + (calRt c Sg t)ᵀ) ∧
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) c.T)), ric35 c Sg Sgdot s.toNNReal = 0

/-- "Riccati equation (35) admits a unique solution `Σ`" (Theorem 4.12, p.13): a solution exists,
and any two solutions coincide on `[0, T]`. -/
def UniqSolv35 (c : Coeffs n m d) : Prop :=
  ∃ Sg, Solves35 c Sg ∧ ∀ Sg', Solves35 c Sg' → ∀ t ≤ c.T, Sg' t = Sg t

/-- `ρ̃ = Bᵀρ + FᵀΣb̄ + r` (p.13). -/
def tilRho (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ≥0 → Fin n → ℝ)
    (t : ℝ≥0) : Fin m → ℝ :=
  (c.B t)ᵀ *ᵥ ρ t + (c.F t)ᵀ *ᵥ (Sg t *ᵥ c.bb t) + c.r t

/-- The left side of the ODE (36) (p.13): `ρ̇ + Aᵀρ − Σ̃𝓡̃⁻¹ρ̃ + Σb + DᵀΣb̄ + q`. -/
noncomputable def ode36 (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (ρ ρdot : ℝ≥0 → Fin n → ℝ)
    (t : ℝ≥0) : Fin n → ℝ :=
  ρdot t + (c.A t)ᵀ *ᵥ ρ t - tilSg c Sg t *ᵥ ((calRt c Sg t)⁻¹ *ᵥ tilRho c Sg ρ t)
    + Sg t *ᵥ c.b t + (c.D t)ᵀ *ᵥ (Sg t *ᵥ c.bb t) + c.q t

/-- `ρ` solves the ODE (36) (p.13): absolutely continuous on `[0, T]`, (36) for a.e. `t`,
`ρ_T = l_T`. -/
def Solves36 (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ≥0 → Fin n → ℝ) : Prop :=
  ∃ ρdot, IsACRep c.T ρ ρdot ∧ ρ c.T = c.lT ∧
    ∀ᵐ s ∂(volume.restrict (Icc (0 : ℝ) c.T)), ode36 c Sg ρ ρdot s.toNNReal = 0

/-- `u⁰_t = −𝓡̃_t⁻¹(Σ̄_tᵀx⁰_t + ρ̃_t)`, (59), p.23. -/
noncomputable def u0Of (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ≥0 → Fin n → ℝ) (x0 : ℝ≥0 → Ω → Fin n → ℝ) : ℝ≥0 → Ω → Fin m → ℝ :=
  fun t ω => -((calRt c Sg t)⁻¹ *ᵥ ((barSg c Sg t)ᵀ *ᵥ x0 t ω + tilRho c Sg ρ t))

/-- `x⁰` solves the SDE (38) (p.14):
`dx⁰ = {[A + Ā − (B + B̄)𝓡̃⁻¹Σ̄ᵀ]x⁰ − (B + B̄)𝓡̃⁻¹ρ̃ + b} dt
 + {[D + D̄ − (F + F̄)𝓡̃⁻¹Σ̄ᵀ]x⁰ − (F + F̄)𝓡̃⁻¹ρ̃ + b̄} dW⁰`, `x⁰_0 = x`. -/
def Solves38 (c : Coeffs n m d) (Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ≥0 → Fin n → ℝ)
    (Sp : Space N d Ω) (x0 : ℝ≥0 → Ω → Fin n → ℝ) : Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B c.x
    (fun s _ z => (c.A s + c.Ab s - (c.B s + c.Bb s) * (calRt c Sg s)⁻¹ * (barSg c Sg s)ᵀ) *ᵥ z
      - (c.B s + c.Bb s) *ᵥ ((calRt c Sg s)⁻¹ *ᵥ tilRho c Sg ρ s) + c.b s)
    (w0Diff (fun s _ z =>
      (c.D s + c.Db s - (c.F s + c.Fb s) * (calRt c Sg s)⁻¹ * (barSg c Sg s)ᵀ) *ᵥ z
        - (c.F s + c.Fb s) *ᵥ ((calRt c Sg s)⁻¹ *ᵥ tilRho c Sg ρ s) + c.bb s)) x0

/-- The filter `X̂_t = E[X̄_t | 𝓕^{Ȳ}_t]` of (17) (p.8). -/
noncomputable def filterHat (Sp : Space N d Ω) (θ : ℝ≥0 → Ω → Fin 1 → ℝ)
    (Yb Xb : ℝ≥0 → Ω → Fin n → ℝ) : ℝ≥0 → Ω → Fin n → ℝ :=
  fun t => condExp (obsOne Sp θ Yb t) Sp.P (Xb t)

/-- The right side of the feedback representation (37) (p.13):
`−𝓡⁻¹Π̃ᵀ(X̂ − x⁰) − 𝓡̃⁻¹(Σ̄ᵀx⁰ + ρ̃)`, with `X̂ = Xh`. -/
noncomputable def feedback37 (c : Coeffs n m d) (Pm Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ≥0 → Fin n → ℝ) (Xh x0 : ℝ≥0 → Ω → Fin n → ℝ) : ℝ≥0 → Ω → Fin m → ℝ :=
  fun t ω => -((calR c Pm t)⁻¹ *ᵥ ((tilPi c Pm t)ᵀ *ᵥ (Xh t ω - x0 t ω)))
    - (calRt c Sg t)⁻¹ *ᵥ ((barSg c Sg t)ᵀ *ᵥ x0 t ω + tilRho c Sg ρ t)

/-- `X̄` solves the SDE (39) (p.14) of agent `i`, with `X̂ = Xh`:
`dX̄ = {AX̄ − B𝓡⁻¹Π̃ᵀX̂ + [Ā + B𝓡⁻¹Π̃ᵀ − (B + B̄)𝓡̃⁻¹Σ̄ᵀ]x⁰ + b − (B + B̄)𝓡̃⁻¹ρ̃} dt
 + {DX̄ − F𝓡⁻¹Π̃ᵀX̂ + [D̄ + F𝓡⁻¹Π̃ᵀ − (F + F̄)𝓡̃⁻¹Σ̄ᵀ]x⁰ − (F + F̄)𝓡̃⁻¹ρ̃ + b̄} dW⁰ + σ dWⁱ + σ̄ dW̄ⁱ`,
`X̄_0 = x`.

**Formalization Note** The `dW⁰` coefficient of `x⁰` is printed `[F̄ + F𝓡⁻¹Π̃ᵀ − …]`, ill-typed
(`F̄ ∈ ℝ^{n×m}`, `x⁰ ∈ ℝⁿ`); substituting (37) into (10) gives `D̄`, used here. -/
def Solves39 (c : Coeffs n m d) (Pm Sg : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (ρ : ℝ≥0 → Fin n → ℝ) (Sp : Space N d Ω) (i : Fin N) (Xh x0 Xb : ℝ≥0 → Ω → Fin n → ℝ) :
    Prop :=
  SolvesSDE Sp.filt Sp.P c.T Sp.B c.x
    (fun s ω z => c.A s *ᵥ z - (c.B s * (calR c Pm s)⁻¹ * (tilPi c Pm s)ᵀ) *ᵥ Xh s ω
      + (c.Ab s + c.B s * (calR c Pm s)⁻¹ * (tilPi c Pm s)ᵀ
          - (c.B s + c.Bb s) * (calRt c Sg s)⁻¹ * (barSg c Sg s)ᵀ) *ᵥ x0 s ω
      + c.b s - (c.B s + c.Bb s) *ᵥ ((calRt c Sg s)⁻¹ *ᵥ tilRho c Sg ρ s))
    (agentDiff i (fun s ω z => c.D s *ᵥ z - (c.F s * (calR c Pm s)⁻¹ * (tilPi c Pm s)ᵀ) *ᵥ Xh s ω
        + (c.Db s + c.F s * (calR c Pm s)⁻¹ * (tilPi c Pm s)ᵀ
            - (c.F s + c.Fb s) * (calRt c Sg s)⁻¹ * (barSg c Sg s)ᵀ) *ᵥ x0 s ω
        - (c.F s + c.Fb s) *ᵥ ((calRt c Sg s)⁻¹ *ᵥ tilRho c Sg ρ s) + c.bb s)
      (fun s _ => c.σ s) (fun s _ => c.σb s)) Xb

end IndefPOMFG


