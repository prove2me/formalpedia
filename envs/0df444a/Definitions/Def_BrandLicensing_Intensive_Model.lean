-- Prove2me | Definitions.Def_BrandLicensing_Intensive_Model
-- name    : BrandLicensing_Intensive_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:33:27.3914+00:00
-- url     : https://prove2.me/theorems/a13cc6ce-1cd3-4e9c-b704-c6609794c0a1
-- title:
--   §3–§4, pp. 3185–3188 — brand extension: in-house development vs royalty licensing with a reciprocal effect, subgame-perfect equilibria
-- statement:
--   This file sets up the baseline model of brand extension of Bacchiega, Colucci, Denicolò and Magnani.
--
--   **Parameters.** A model is a tuple $(\alpha,\theta,\mu,\rho,\lambda,\varepsilon)$: the perceived distance $\alpha$ between the core and the extension product, the technological distance $\theta$ (the brand owner's cost disadvantage outside its core business), the size $\mu$ of the core market, the size $\rho$ of the extension market, the magnitude $\lambda$ of the reciprocal effect and the benchmark quality $\varepsilon$. The cost-of-effort parameter $\beta$ is normalized to $1$. The standing assumptions are those of Table 1 together with $\rho<1$:
--   $$0\le\alpha\le1,\quad \theta\ge1,\quad \mu>0,\quad 0\le\rho<1,\quad 0\le\lambda\le1,\quad \varepsilon>0.$$
--
--   **Demand and profits.** Efforts $e_C$ (core) and $e_E$ (extension) are perceived qualities. Extension demand at price $p$ is $q=\rho[e_E+(1-\alpha)e_C-p]$ (1), and the core product sells to $\mu$ consumers at their willingness to pay $v_C=e_C+\lambda(1-\alpha)(e_E-\varepsilon)$ (3). The seller of the extension, paying a royalty $s$ per unit, earns $(p-s)\max(q,0)$; at the monopoly price $p^M=[e_E+(1-\alpha)e_C+s]/2$ (4) this is
--   $$\pi^M=\rho\,\frac{\max\{e_E+(1-\alpha)e_C-s,\,0\}^2}{4}\qquad(6).$$
--   The brand owner's profit is $\pi_B=\mu v_C+\pi^M|_{s=0}-\tfrac12\theta e_E^2-\tfrac12e_C^2$ under in-house development (7); the licensee's profit is $\pi_L=\pi^M-\tfrac12e_E^2$ (10); the brand owner's profit under licensing is $\pi_B=\mu v_C+s\,q^M-\tfrac12e_C^2$ with $q^M=\rho\max\{(1-\alpha)e_C+e_E-s,0\}/2$ (14); without extension it is $\mu e_C-\tfrac12e_C^2$.
--
--   **Equilibria.** An *in-house equilibrium* is a pair $(e_C,e_E)$ maximizing (7) over $e_C,e_E\ge0$. A *licensing profile* consists of a licensee effort rule $\sigma_E(e_C,s)$, a royalty rule $\sigma_s(e_C)$ and a core effort $e_C$; it is a *subgame-perfect equilibrium* when, for every $e_C\ge0$ and $s\ge0$, $\sigma_E(e_C,s)\ge0$ maximizes (10) over $e_E\ge0$; for every $e_C\ge0$, $\sigma_s(e_C)\ge0$ maximizes (14) over $s\ge0$ given $\sigma_E$; and $e_C\ge0$ maximizes the resulting profit over $e_C\ge0$. Its outcome is $s^L=\sigma_s(e_C)$ and $e^L_E=\sigma_E(e_C,s^L)$.
--
--   **Closed forms.** The file also records the paper's closed-form expressions, with $\Xi=\theta[2-(1-\alpha)^2\rho]-\rho$ and $D=4-[3-(2-\alpha)\alpha]\rho$: the in-house efforts and profit (A.1)–(A.3), the licensee's reaction (12), the royalty rule (13), the licensing efforts, royalty and profit (15), (B.1)–(B.3), and $\theta_I$ of (F.2) as the quotient of its numerator and denominator.
--
--   These objects are shared by every statement of the mission: the milestones identify the equilibria with the closed forms, and Proposition 3 compares the equilibria themselves.
--
--   **Formalization Note** The positive parts in $\pi^M$ and $q^M$ encode "otherwise nothing is sold"; the paper uses (6) only where the margin is non-negative. All efforts and royalties range over $[0,\infty)$. The licensee's accept/reject decision is not modelled: with a pure royalty, $e_E=0$ guarantees $\pi_L\ge0$, so participation never binds. The core profit is $\mu v_C$ as on the page, also where $v_C<0$. The closed forms are used only by milestones; the goal theorem does not mention them.
-- source:
--   Bacchiega, Colucci, Denicolò & Magnani, Only the Ugly Face? A Theoretical Model of Brand Dilution, Management Science 70(5) (2024), pp. 3185–3188 (PDF 5–8), §3, §4, Table 1, eqs. (1)–(15); pp. 3195–3196 (PDF 15–16), (A.1)–(A.3), (B.1)–(B.3), (F.2)

import Mathlib

namespace BrandLicensing.Intensive

noncomputable section

/-- The parameters of the baseline model (Table 1, p. 3186), with β normalized to 1 (p. 3187):
perceived distance `α`, technological distance `θ`, core market size `μ`, extension market size
`ρ`, magnitude of the reciprocal effect `lam` (the paper's λ), benchmark quality `ε`. -/
structure Params where
  α : ℝ
  θ : ℝ
  μ : ℝ
  ρ : ℝ
  lam : ℝ
  ε : ℝ

/-- Standing assumptions (Table 1, p. 3186; p. 3187 "ρ < 1 to ensure concavity"):
`α ∈ [0,1]`, `θ ≥ 1`, `μ > 0`, `ρ ∈ [0,1)`, `λ ∈ [0,1]`, `ε > 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 ≤ P.α ∧ P.α ≤ 1 ∧ 1 ≤ P.θ ∧ 0 < P.μ ∧ 0 ≤ P.ρ ∧ P.ρ < 1 ∧
    0 ≤ P.lam ∧ P.lam ≤ 1 ∧ 0 < P.ε

/-- (3), p. 3186: consumers' willingness to pay for the core product,
`v_C = e_C + λ(1 − α)(e_E − ε)`. -/
def vC (P : Params) (eC eE : ℝ) : ℝ := eC + P.lam * (1 - P.α) * (eE - P.ε)

/-- (1), p. 3185: demand for the extension product at price `p`,
`q = ρ[e_E + (1 − α)e_C − p]`. -/
def demand (P : Params) (eC eE p : ℝ) : ℝ := P.ρ * (eE + (1 - P.α) * eC - p)

/-- The extension seller's profit at price `p` when it pays the royalty `s` per unit
(variable costs normalized to zero, p. 3185); sales are never negative. -/
def extProfitAt (P : Params) (eC eE s p : ℝ) : ℝ := (p - s) * max (demand P eC eE p) 0

/-- (4), p. 3187: the monopoly price `p^M = [e_E + (1 − α)e_C + s]/2`. -/
def pM (P : Params) (eC eE s : ℝ) : ℝ := (eE + (1 - P.α) * eC + s) / 2

/-- (6), p. 3187: the extension seller's profit at the monopoly price,
`π^M = ρ[e_E + (1 − α)e_C − s]²/4`, and `0` when the margin `e_E + (1 − α)e_C − s` is negative
(then nothing is sold). -/
def piM (P : Params) (eC eE s : ℝ) : ℝ := P.ρ * (max (eE + (1 - P.α) * eC - s) 0) ^ 2 / 4

/-- (7), p. 3187, with β = 1: the brand owner's profit under in-house development,
`μ v_C + π^M|_{s=0} − θ e_E²/2 − e_C²/2`. -/
def piInHouse (P : Params) (eC eE : ℝ) : ℝ :=
  P.μ * vC P eC eE + piM P eC eE 0 - P.θ * eE ^ 2 / 2 - eC ^ 2 / 2

/-- (10), p. 3187: the licensee's profit `π^M − e_E²/2` at royalty `s`. -/
def piLicensee (P : Params) (eC s eE : ℝ) : ℝ := piM P eC eE s - eE ^ 2 / 2

/-- (14), p. 3188: the brand owner's profit under licensing, `μ v_C + s q^M − e_C²/2`, where the
licensing revenue is `s q^M` with `q^M = ρ·max((1 − α)e_C + e_E − s, 0)/2` (5). -/
def piOwnerLic (P : Params) (eC s eE : ℝ) : ℝ :=
  P.μ * vC P eC eE + s * (P.ρ * max ((1 - P.α) * eC + eE - s) 0 / 2) - eC ^ 2 / 2

/-- §4.2.3, p. 3188: the brand owner's profit without brand extension, `μ e_C − e_C²/2`. -/
def piNoExt (P : Params) (eC : ℝ) : ℝ := P.μ * eC - eC ^ 2 / 2

/-- In-house equilibrium (§4.2.1): `(e_C, e_E)` maximizes (7) over the non-negative quadrant. -/
def IsInHouseEq (P : Params) (eC eE : ℝ) : Prop :=
  0 ≤ eC ∧ 0 ≤ eE ∧ ∀ c, 0 ≤ c → ∀ e, 0 ≤ e → piInHouse P c e ≤ piInHouse P eC eE

/-- A strategy profile of the licensing game (§3.4, Figure 1): the licensee's effort rule
`σE e_C s`, the brand owner's royalty rule `σs e_C`, and the brand owner's core effort `eC`. -/
structure LicProfile where
  σE : ℝ → ℝ → ℝ
  σs : ℝ → ℝ
  eC : ℝ

/-- Subgame-perfect equilibrium of the licensing game (§3.4, p. 3187 "we solve the model
backward"): the licensee's effort is optimal in every subgame `(e_C, s)`, the royalty is optimal
in every subgame `e_C` given the licensee's rule, and the core effort is optimal given both rules.
Efforts and royalties are non-negative. -/
def IsLicensingSPE (P : Params) (σ : LicProfile) : Prop :=
  (∀ c, 0 ≤ c → ∀ s, 0 ≤ s → 0 ≤ σ.σE c s ∧
      ∀ e, 0 ≤ e → piLicensee P c s e ≤ piLicensee P c s (σ.σE c s)) ∧
  (∀ c, 0 ≤ c → 0 ≤ σ.σs c ∧
      ∀ s, 0 ≤ s → piOwnerLic P c s (σ.σE c s) ≤ piOwnerLic P c (σ.σs c) (σ.σE c (σ.σs c))) ∧
  0 ≤ σ.eC ∧
  ∀ c, 0 ≤ c → piOwnerLic P c (σ.σs c) (σ.σE c (σ.σs c))
      ≤ piOwnerLic P σ.eC (σ.σs σ.eC) (σ.σE σ.eC (σ.σs σ.eC))

/-- The equilibrium-path royalty `s^L` of a licensing profile. -/
def LicProfile.sL (σ : LicProfile) : ℝ := σ.σs σ.eC

/-- The equilibrium-path licensee effort `e^L_E` of a licensing profile. -/
def LicProfile.eEL (σ : LicProfile) : ℝ := σ.σE σ.eC (σ.σs σ.eC)

/-! ### Closed forms reported by the paper (β = 1) -/

/-- `Ξ = θ[2 − (1 − α)²ρ] − ρ` (p. 3195). -/
def Xi (P : Params) : ℝ := P.θ * (2 - (1 - P.α) ^ 2 * P.ρ) - P.ρ

/-- `D = 4 − [3 − (2 − α)α]ρ`, the denominator of (15), (B.1)–(B.3). -/
def Dlic (P : Params) : ℝ := 4 - (3 - (2 - P.α) * P.α) * P.ρ

/-- (A.1), p. 3195. -/
def eCH_cf (P : Params) : ℝ :=
  P.μ * (2 * P.θ - P.ρ * (1 - (1 - P.α) ^ 2 * P.lam)) / Xi P

/-- (A.2), p. 3195. -/
def eEH_cf (P : Params) : ℝ :=
  (1 - P.α) * P.μ * (P.lam * (2 - (1 - P.α) ^ 2 * P.ρ) + P.ρ) / Xi P

/-- (A.3), p. 3195. -/
def piH_cf (P : Params) : ℝ :=
  P.μ ^ 2 * (2 * P.θ + 2 * (1 - P.α) ^ 2 * P.lam ^ 2 - P.ρ * (1 - (1 - P.α) ^ 2 * P.lam) ^ 2)
      / (2 * Xi P) - (1 - P.α) * P.ε * P.lam * P.μ

/-- (12), p. 3188: the licensee's effort `ρ/(2 − ρ)·[(1 − α)e_C − s]` if `s < (1 − α)e_C`, else `0`. -/
def eE12 (P : Params) (eC s : ℝ) : ℝ := P.ρ / (2 - P.ρ) * max ((1 - P.α) * eC - s) 0

/-- (13), p. 3188: `s = ½(1 − α)(e_C − λμ)`. -/
def s13 (P : Params) (eC : ℝ) : ℝ := (1 - P.α) * (eC - P.lam * P.μ) / 2

/-- (15), p. 3188. -/
def eCL_cf (P : Params) : ℝ :=
  P.μ * (4 - P.ρ * (2 - P.lam * (1 - P.α) ^ 2)) / (4 - P.ρ * (3 - P.α * (2 - P.α)))

/-- (B.1), p. 3195. -/
def sL_cf (P : Params) : ℝ :=
  (1 - P.α) * P.μ * (2 - P.ρ - P.lam * (2 - P.ρ * (2 - (2 - P.α) * P.α))) / Dlic P

/-- (B.2), p. 3195. -/
def eEL_cf (P : Params) : ℝ := (1 - P.α) * (P.lam + 1) * P.μ * P.ρ / Dlic P

/-- (B.3), p. 3195. -/
def piL_cf (P : Params) : ℝ :=
  P.μ * (P.μ * (4 + (1 - P.α) ^ 2 * P.lam * (2 + P.lam) * P.ρ - 2 * P.ρ)
      - 2 * (1 - P.α) * P.lam * P.ε * Dlic P) / (2 * Dlic P)

/-- Numerator of (F.2), p. 3196. -/
def thetaI_num (P : Params) : ℝ :=
  2 * P.lam * P.ρ * ((5 - 3 * (2 - P.α) * P.α) * P.lam - 4) - 8 * P.lam ^ 2
    - P.ρ ^ 2 * ((2 - (2 - P.α) * P.α) * P.lam - 1) ^ 2

/-- Denominator of (F.2), p. 3196. -/
def thetaI_den (P : Params) : ℝ :=
  P.ρ * (P.lam * (P.lam + 2) * ((1 - P.α) ^ 2 * P.ρ - 2) - 2 * P.ρ + 2)

/-- (F.2), p. 3196: the value `θ_I` of `θ` at which `π^H_B = π^L_B`. -/
def thetaI (P : Params) : ℝ := thetaI_num P / thetaI_den P

end

end BrandLicensing.Intensive


