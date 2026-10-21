-- Prove2me | Definitions.Def_PandemicInfo_Inequality_Reduced
-- name    : PandemicInfo_Inequality_Reduced
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:16.260597+00:00
-- url     : https://prove2.me/theorems/ec31df2c-ba74-4999-b7e0-929fa9ef483b
-- title:
--   §3, App. A — c⋆(µ), reduced costs (9)–(11), K̃_λ, envelope k_λ, G_h, G_ℓ, G_1, G_2 (23)–(25), thresholds λ1–λ4 (19)–(22), cutoffs (26), µ^DP_λ, µ^EX_λ (13)–(16), regimes (29)–(35)
-- statement:
--   The objects of Appendix A and §3 of de Véricourt, Gurkan and Wang that the analysis of the optimal policy is written in.
--
--   1. The equilibrium threshold $c^\star(\mu)=\dfrac{\mu\kappa(\theta+\sigma\sqrt3)}{\sigma2\sqrt3+\mu\kappa}$.
--   2. The reduced costs, for $c$ uniform on $\mathcal C$ (9)–(11): $K_e(x)=\mathbb E_c[c\,\mathbb 1\{c\le x\}]$, $K_h(x)=x\,\mathbb E_c[\mathbb 1\{c\ge x\}]$, $K_\lambda(x)=\lambda K_e(x)+(1-\lambda)K_h(x)$, and $\tilde K_\lambda(\mu)=K_\lambda(c^\star(\mu))$.
--   3. The lower convex envelope $k_\lambda$ of $\tilde K_\lambda$ on $[\omega_\ell,\omega_h]$ (the published definition `BiconvexProg.BranchBound.convexEnvelope`).
--   4. The functions (23)–(25):
--   $$G_h(\lambda)=\frac{1-\frac{5\lambda}4}{\omega_h(\frac12-\lambda)},\quad G_\ell(\lambda)=\frac{1-\frac{5\lambda}4}{\omega_\ell(\frac12-\lambda)},$$
--   $$G_1(\lambda)=\sqrt{\tfrac{5\lambda-4}{2(2\lambda-1)\omega_h\omega_\ell}+\Big(\tfrac{2(1-\lambda)\omega_h+\lambda\omega_\ell}{4(2\lambda-1)\omega_h\omega_\ell}\Big)^2}-\tfrac{2(1-\lambda)\omega_h+\lambda\omega_\ell}{4(2\lambda-1)\omega_h\omega_\ell},$$
--   $$G_2(\lambda)=\sqrt{\tfrac{4-5\lambda}{2(1-2\lambda)\omega_h\omega_\ell}+\Big(\tfrac{\lambda\omega_h+2(1-\lambda)\omega_\ell}{4(1-2\lambda)\omega_h\omega_\ell}\Big)^2}+\tfrac{\lambda\omega_h+2(1-\lambda)\omega_\ell}{4(1-2\lambda)\omega_h\omega_\ell}.$$
--   5. The thresholds (19)–(22), $\lambda_1=G_\ell^{-1}(\kappa/\gamma)$, $\lambda_2=G_2^{-1}(\kappa/\gamma)$ (on $[0,1/2)$), $\lambda_3=G_1^{-1}(\kappa/\gamma)$, $\lambda_4=G_h^{-1}(\kappa/\gamma)$ (on $[4/5,1]$), and the cutoffs (26) $\bar\kappa_0=\gamma G_\ell(0)$, $\underline\kappa_0=\gamma G_2(0)$, $\bar\kappa_1=\gamma G_1(1)$, $\underline\kappa_1=\gamma G_h(1)$.
--   6. The posterior thresholds (13)–(16): $\mu^{DP}_\lambda=\rho^{DP}_\lambda(\omega_h-\omega_\ell)+\omega_\ell$ and $\mu^{EX}_\lambda=\rho^{EX}_\lambda(\omega_h-\omega_\ell)+\omega_\ell$ with
--   $$\rho^{DP}_\lambda=\frac{\gamma^2(5\lambda-4)-2\kappa^2\omega_\ell\omega_h(2\lambda-1)-\gamma\kappa(2(1-\lambda)\omega_h+\lambda\omega_\ell)}{\kappa(\omega_h-\omega_\ell)(2\kappa\omega_h(2\lambda-1)+\gamma\lambda)},\qquad \rho^{EX}_\lambda=\frac{(2\kappa\omega_\ell(1-2\lambda)-\gamma(4-5\lambda))(\kappa\omega_\ell+\gamma)}{\kappa(\omega_h-\omega_\ell)(2\kappa\omega_\ell(2\lambda-1)+\gamma\lambda)}.$$
--   7. The regimes (29)–(35): $\mathrm{FD}_1:\lambda\in[1/2,4/5]$; $\mathrm{FD}_2:\lambda\in(4/5,1]\wedge\kappa/\gamma\ge G_1(\lambda)$; $\mathrm{FD}_3:\lambda\in[0,1/2)\wedge G_2(\lambda)\ge\kappa/\gamma$; $\mathrm{ND}_1:\lambda\in[0,1/2)\wedge\kappa/\gamma\ge G_\ell(\lambda)$; $\mathrm{ND}_2:\lambda\in(4/5,1]\wedge G_h(\lambda)\ge\kappa/\gamma$; $\mathrm{DP}:\lambda\in(4/5,1]\wedge G_1(\lambda)>\kappa/\gamma>G_h(\lambda)$; $\mathrm{EX}:\lambda\in[0,1/2)\wedge G_\ell(\lambda)>\kappa/\gamma>G_2(\lambda)$.
--
--   **Formalization Note** $K_e$ and $K_h$ are defined by the integrals (9)–(10), not by closed forms; the closed form of $\tilde K_\lambda$ is the theorem (39). The paper defines $\lambda_1=\max(-\epsilon,G_\ell^{-1}(\kappa/\gamma))$ and so on, an inverse that need not exist. Lean uses a sentinel form: $\lambda_1=\sup\big(\{-1\}\cup\{\lambda\in[0,\tfrac12):G_\ell(\lambda)\le\kappa/\gamma\}\big)$, likewise $\lambda_2$ with $G_2$, and $\lambda_3=\inf\big(\{2\}\cup\{\lambda\in[\tfrac45,1]:\kappa/\gamma\le G_1(\lambda)\}\big)$, likewise $\lambda_4$ with $G_h$. Every set is nonempty and bounded, so no junk value arises. Since the $G$'s are increasing (Lemma 1), for $\lambda\in[0,1]$ this gives the paper's regimes exactly: $\lambda\le\lambda_1\iff\mathrm{ND}_1$, $\lambda\ge\lambda_2\iff\mathrm{FD}_3$ for $\lambda<1/2$, $\lambda\le\lambda_3\iff\mathrm{FD}_2$ and $\lambda\ge\lambda_4\iff\mathrm{ND}_2$ for $\lambda>4/5$; the paper's $-\epsilon$ and $1+\epsilon$ play the role of the sentinels. Note that $\lambda_1,\dots,\lambda_4$ depend on $\kappa$ and $\gamma$ only through $\kappa/\gamma$.
-- source:
--   de Véricourt, Gurkan, Wang, Informing the Public about a Pandemic, ESMT Working Paper 20-03 (Dec. 15, 2020), p. 9 (PDF 10), (9)–(11); pp. 16–17 (PDF 17–18), App. A, c⋆(µ) and (13)–(26); p. 18 (PDF 19), K̃_λ; pp. 18–19 (PDF 19–20), (29)–(35); p. 19 (PDF 20), Lemma 4 (k_λ)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope
import Definitions.Def_PandemicInfo_Inequality_Model

namespace PandemicInfo.Inequality

namespace Params

variable (P : Params)

/-- The equilibrium threshold `c⋆(µ) = µκ(θ + σ√3)/(σ2√3 + µκ)` (Appendix A, p. 16). -/
noncomputable def cStar (μ : ℝ) : ℝ :=
  μ * P.κ * (P.θ + P.σ * Real.sqrt 3) / (P.σ * 2 * Real.sqrt 3 + μ * P.κ)

/-- (9): `K_e(x) = E_c[c 1{c ≤ x}]`. -/
noncomputable def Ke (x : ℝ) : ℝ := P.Ec (fun c => if c ≤ x then c else 0)

/-- (10): `K_h(x) = x E_c[1{c ≥ x}]`. -/
noncomputable def Kh (x : ℝ) : ℝ := x * P.Ec (fun c => if x ≤ c then 1 else 0)

/-- (11): `K_λ(x) = λK_e(x) + (1 − λ)K_h(x)`. -/
noncomputable def Klam (lam x : ℝ) : ℝ := lam * P.Ke x + (1 - lam) * P.Kh x

/-- `K̃_λ(µ) = K_λ(c⋆(µ))` (proof of Theorem 1, p. 18). -/
noncomputable def Ktil (lam μ : ℝ) : ℝ := P.Klam lam (P.cStar μ)

/-- The lower convex envelope `k_λ` of `K̃_λ` over `[ω_ℓ, ω_h]`. -/
noncomputable def kEnv (lam μ : ℝ) : ℝ :=
  BiconvexProg.BranchBound.convexEnvelope (Set.Icc P.ωl P.ωh) (P.Ktil lam) μ

/-- (23): `G_h(λ) = (1 − 5λ/4)/(ω_h(1/2 − λ))`. -/
noncomputable def Gh (lam : ℝ) : ℝ := (1 - 5 * lam / 4) / (P.ωh * (1 / 2 - lam))

/-- (23): `G_ℓ(λ) = (1 − 5λ/4)/(ω_ℓ(1/2 − λ))`. -/
noncomputable def Gl (lam : ℝ) : ℝ := (1 - 5 * lam / 4) / (P.ωl * (1 / 2 - lam))

/-- (24), for `λ ∈ (4/5, ∞)`. -/
noncomputable def G1 (lam : ℝ) : ℝ :=
  Real.sqrt ((5 * lam - 4) / (2 * (2 * lam - 1) * P.ωh * P.ωl) +
      ((2 * (1 - lam) * P.ωh + lam * P.ωl) / (4 * (2 * lam - 1) * P.ωh * P.ωl)) ^ 2) -
    (2 * (1 - lam) * P.ωh + lam * P.ωl) / (4 * (2 * lam - 1) * P.ωh * P.ωl)

/-- (25), for `λ ∈ (−∞, 1/2)`. -/
noncomputable def G2 (lam : ℝ) : ℝ :=
  Real.sqrt ((4 - 5 * lam) / (2 * (1 - 2 * lam) * P.ωh * P.ωl) +
      ((lam * P.ωh + 2 * (1 - lam) * P.ωl) / (4 * (1 - 2 * lam) * P.ωh * P.ωl)) ^ 2) +
    (lam * P.ωh + 2 * (1 - lam) * P.ωl) / (4 * (1 - 2 * lam) * P.ωh * P.ωl)

/-- (19), sentinel form: `λ1 = sup {λ ∈ [0, 1/2) : G_ℓ(λ) ≤ κ/γ}`, or `−1` if that set is
empty. -/
noncomputable def lam1 : ℝ :=
  sSup (insert (-1) {l | l ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.Gl l ≤ P.κ / P.γ})

/-- (20), sentinel form: `λ2 = sup {λ ∈ [0, 1/2) : G_2(λ) ≤ κ/γ}`, or `−1` if that set is
empty. -/
noncomputable def lam2 : ℝ :=
  sSup (insert (-1) {l | l ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.G2 l ≤ P.κ / P.γ})

/-- (21), sentinel form: `λ3 = inf {λ ∈ [4/5, 1] : κ/γ ≤ G_1(λ)}`, or `2` if that set is
empty. -/
noncomputable def lam3 : ℝ :=
  sInf (insert 2 {l | l ∈ Set.Icc (4 / 5 : ℝ) 1 ∧ P.κ / P.γ ≤ P.G1 l})

/-- (22), sentinel form: `λ4 = inf {λ ∈ [4/5, 1] : κ/γ ≤ G_h(λ)}`, or `2` if that set is
empty. -/
noncomputable def lam4 : ℝ :=
  sInf (insert 2 {l | l ∈ Set.Icc (4 / 5 : ℝ) 1 ∧ P.κ / P.γ ≤ P.Gh l})

/-- (26): `κ̄0 = γG_ℓ(0)`. -/
noncomputable def kap0bar : ℝ := P.γ * P.Gl 0

/-- (26): `κ_0 = γG_2(0)`. -/
noncomputable def kap0 : ℝ := P.γ * P.G2 0

/-- (26): `κ̄1 = γG_1(1)`. -/
noncomputable def kap1bar : ℝ := P.γ * P.G1 1

/-- (26): `κ_1 = γG_h(1)`. -/
noncomputable def kap1 : ℝ := P.γ * P.Gh 1

/-- (15). -/
noncomputable def ρDP (lam : ℝ) : ℝ :=
  (P.γ ^ 2 * (5 * lam - 4) - 2 * P.κ ^ 2 * P.ωl * P.ωh * (2 * lam - 1) -
      P.γ * P.κ * (2 * (1 - lam) * P.ωh + lam * P.ωl)) /
    (P.κ * (P.ωh - P.ωl) * (2 * P.κ * P.ωh * (2 * lam - 1) + P.γ * lam))

/-- (16). -/
noncomputable def ρEX (lam : ℝ) : ℝ :=
  ((2 * P.κ * P.ωl * (1 - 2 * lam) - P.γ * (4 - 5 * lam)) * (P.κ * P.ωl + P.γ)) /
    (P.κ * (P.ωh - P.ωl) * (2 * P.κ * P.ωl * (2 * lam - 1) + P.γ * lam))

/-- (13): `µ^DP_λ = ρ^DP_λ(ω_h − ω_ℓ) + ω_ℓ`. -/
noncomputable def μDP (lam : ℝ) : ℝ := P.ρDP lam * (P.ωh - P.ωl) + P.ωl

/-- (14): `µ^EX_λ = ρ^EX_λ(ω_h − ω_ℓ) + ω_ℓ`. -/
noncomputable def μEX (lam : ℝ) : ℝ := P.ρEX lam * (P.ωh - P.ωl) + P.ωl

/-- (29) `FD₁ : λ ∈ [1/2, 4/5]` (it does not involve the other parameters). -/
@[nolint unusedArguments]
def FD1 (_P : Params) (lam : ℝ) : Prop := lam ∈ Set.Icc (1 / 2 : ℝ) (4 / 5)

/-- (30) `FD₂ : λ ∈ (4/5, 1] ∧ κ/γ ≥ G_1(λ)`. -/
def FD2 (lam : ℝ) : Prop := lam ∈ Set.Ioc (4 / 5 : ℝ) 1 ∧ P.G1 lam ≤ P.κ / P.γ

/-- (31) `FD₃ : λ ∈ [0, 1/2) ∧ G_2(λ) ≥ κ/γ`. -/
def FD3 (lam : ℝ) : Prop := lam ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.κ / P.γ ≤ P.G2 lam

/-- (32) `ND₁ : λ ∈ [0, 1/2) ∧ κ/γ ≥ G_ℓ(λ)`. -/
def ND1 (lam : ℝ) : Prop := lam ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.Gl lam ≤ P.κ / P.γ

/-- (33) `ND₂ : λ ∈ (4/5, 1] ∧ G_h(λ) ≥ κ/γ`. -/
def ND2 (lam : ℝ) : Prop := lam ∈ Set.Ioc (4 / 5 : ℝ) 1 ∧ P.κ / P.γ ≤ P.Gh lam

/-- (34) `DP : λ ∈ (4/5, 1] ∧ G_1(λ) > κ/γ > G_h(λ)`. -/
def DP (lam : ℝ) : Prop :=
  lam ∈ Set.Ioc (4 / 5 : ℝ) 1 ∧ P.κ / P.γ < P.G1 lam ∧ P.Gh lam < P.κ / P.γ

/-- (35) `EX : λ ∈ [0, 1/2) ∧ G_ℓ(λ) > κ/γ > G_2(λ)`. -/
def EX (lam : ℝ) : Prop :=
  lam ∈ Set.Ico (0 : ℝ) (1 / 2) ∧ P.κ / P.γ < P.Gl lam ∧ P.G2 lam < P.κ / P.γ

end Params

end PandemicInfo.Inequality


