-- Prove2me | Definitions.Def_PlatformQualReg_ExclSubsid_Model
-- name    : PlatformQualReg_ExclSubsid_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:24.420094+00:00
-- url     : https://prove2.me/theorems/7cd58f5f-d6fe-46e4-acdd-bbed0b133484
-- title:
--   Sections 3–5: two-sided platform exclusion and subsidization model at μ = 0
-- statement:
--   A platform serves consumers and two types of application developer. A fraction $\lambda$ of developers produce quality $q_h>0$; the remaining fraction produce quality zero. The parameter record contains consumer and developer differentiation widths $\theta_c,\theta_d$, cross-side effects $\alpha_c,\alpha_{dh},\alpha_{dl}$, congestion $b$, total-quality preference $\beta$, operating-cost coefficient $\eta$, and base consumer value $w$.
--
--   An exclusion outcome records access fees $p_d,p_c$ and network sizes $m,n$. A subsidization outcome also records a nonnegative payment $\gamma$ to each high-quality developer. Its high- and low-quality counts are $n_h$ and $n_l$, with $n=n_h+n_l$. The equations defining consistent outcomes are the paper's demand equations at $\mu=0$; platform profit is
--
--   $$
--   \Pi^E=p_dn+p_cm-\eta mn,\qquad
--   \Pi^S=p_dn+p_cm-\eta mn-\gamma n_h.
--   $$
--
--   Feasible outcomes have nonnegative network sizes; subsidization also requires $\gamma,n_h,n_l\ge0$. An optimal outcome has profit at least as large as every feasible outcome. The model also names the paper's composite constants $\bar\alpha_d,\xi,\xi_1,\rho,t,\tau$ and the closed-form quantities used in the exclusion and subsidy milestones.
--
--   **Formalization Note** The model fixes $\mu=0$ throughout. Developer counts use the paper's untruncated linear formulas, with nonnegativity enforced in feasibility. Consumer demand under subsidy uses $q_hn_h$ for total quality. The parameter condition strengthens $\lambda\in[0,1]$ to $0<\lambda<1$ because inverse exclusion demand divides by $\lambda$. Strict concavity is named separately for each profit problem; it strengthens the paper's joint concavity assumption to match its unique-optimum claims.
-- source:
--   Huang, Lyu & Xu, Quality regulation on two-sided platforms: exclusion, subsidization, and first-party applications, SSRN 3948778, pp. 6–8, 11–12, 14–17, 26 (PDF 7–9, 12–13, 15–18, 27), §3, §4.1, §4.2, §5.1.1, equations (1), (5)–(13), Proposition 4

import Mathlib

namespace PlatformQualReg.ExclSubsid

noncomputable section

/-- Parameters of the two-sided market in the paper's `μ = 0` regime. -/
structure Params where
  lam : ℝ
  qh : ℝ
  thc : ℝ
  thd : ℝ
  adh : ℝ
  adl : ℝ
  ac : ℝ
  b : ℝ
  β : ℝ
  η : ℝ
  w : ℝ

/-- The standing sign and type assumptions of Sections 3–5. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.lam ∧ P.lam < 1 ∧ 0 < P.qh ∧ 0 < P.thc ∧ 0 < P.thd ∧
  P.adl ≤ P.adh ∧ 0 < P.b ∧ 0 ≤ P.β ∧ 0 < P.w

def abar (P : Params) : ℝ := P.lam * P.adh + (1 - P.lam) * P.adl
def xi (P : Params) : ℝ := abar P + P.ac + P.β * P.lam * P.qh - P.η
def xi1 (P : Params) : ℝ := P.adh + P.ac + P.β * P.qh - P.η
def rho (P : Params) : ℝ := P.lam * (1 - P.lam) * (P.adh - P.adl) / P.thd
def t (P : Params) : ℝ := P.lam * (1 - P.lam) / P.thd
def tau (P : Params) : ℝ :=
  P.lam * (1 - P.lam) * (P.thd + P.b) * (P.β * P.qh + P.adh - P.adl) ^ 2 / P.thd

/-- Posted fees and realized network sizes under exclusion. -/
structure OutcomeE where
  pd : ℝ
  pc : ℝ
  m : ℝ
  n : ℝ

def ConsistentE (P : Params) (x : OutcomeE) : Prop :=
  x.n = P.lam * (P.adh * x.m - x.pd) / (P.thd + P.lam * P.b) ∧
  x.m = (P.w + P.ac * x.n + P.β * P.qh * x.n - x.pc) / P.thc

def FeasibleE (P : Params) (x : OutcomeE) : Prop :=
  ConsistentE P x ∧ 0 ≤ x.m ∧ 0 ≤ x.n

def profitE (P : Params) (x : OutcomeE) : ℝ :=
  x.pd * x.n + x.pc * x.m - P.η * x.m * x.n

def IsOptE (P : Params) (x : OutcomeE) : Prop :=
  FeasibleE P x ∧ ∀ y : OutcomeE, FeasibleE P y → profitE P y ≤ profitE P x

/-- The exclusion inverse demands (6), (8), at `μ = 0`. -/
def outE (P : Params) (m n : ℝ) : OutcomeE :=
  ⟨P.adh * m - n * (P.thd + P.lam * P.b) / P.lam,
   P.w + P.ac * n + P.β * P.qh * n - m * P.thc, m, n⟩

/-- Posted fees, subsidy, and realized network sizes under subsidization. -/
structure OutcomeS where
  pd : ℝ
  pc : ℝ
  γ : ℝ
  m : ℝ
  n : ℝ

def nl (P : Params) (x : OutcomeS) : ℝ :=
  (1 - P.lam) * (P.adl * x.m - P.b * x.n - x.pd) / P.thd

def nh (P : Params) (x : OutcomeS) : ℝ :=
  P.lam * (P.adh * x.m - P.b * x.n + x.γ - x.pd) / P.thd

def ConsistentS (P : Params) (x : OutcomeS) : Prop :=
  x.n = nl P x + nh P x ∧
  x.m = (P.w + P.ac * x.n + P.β * P.qh * nh P x - x.pc) / P.thc

def FeasibleS (P : Params) (x : OutcomeS) : Prop :=
  ConsistentS P x ∧ 0 ≤ x.m ∧ 0 ≤ x.n ∧ 0 ≤ x.γ ∧ 0 ≤ nl P x ∧ 0 ≤ nh P x

def profitS (P : Params) (x : OutcomeS) : ℝ :=
  x.pd * x.n + x.pc * x.m - P.η * x.m * x.n - x.γ * nh P x

def IsOptS (P : Params) (x : OutcomeS) : Prop :=
  FeasibleS P x ∧ ∀ y : OutcomeS, FeasibleS P y → profitS P y ≤ profitS P x

/-- The subsidization inverse demands (10), (13), at `μ = 0`. -/
def outS (P : Params) (m n γ : ℝ) : OutcomeS :=
  ⟨abar P * m + P.lam * γ - (P.thd + P.b) * n,
   P.w + P.ac * n + P.β * P.qh * (P.lam * n + rho P * m + t P * γ) - m * P.thc,
   γ, m, n⟩

def avgQualityS (P : Params) (x : OutcomeS) : ℝ := nh P x * P.qh / x.n

def ConcaveE (P : Params) : Prop :=
  StrictConcaveOn ℝ Set.univ (fun z : ℝ × ℝ => profitE P (outE P z.1 z.2))

def ConcaveS (P : Params) : Prop :=
  StrictConcaveOn ℝ Set.univ
    (fun z : ℝ × ℝ × ℝ => profitS P (outS P z.1 z.2.1 z.2.2))

/-- Exclusion closed-form denominator at `μ = 0`. -/
def denomE (P : Params) : ℝ :=
  4 * (P.thd + P.lam * P.b) * P.thc - P.lam * (xi1 P) ^ 2
def optME (P : Params) : ℝ := 2 * (P.thd + P.lam * P.b) * P.w / denomE P
def optNE (P : Params) : ℝ := P.lam * xi1 P * P.w / denomE P
def optProfitE (P : Params) : ℝ := (P.thd + P.lam * P.b) * P.w ^ 2 / denomE P

/-- Subsidization closed-form denominator at `μ = 0`. -/
def denomS (P : Params) : ℝ :=
  4 * (P.thd + P.b) * P.thc - (xi P) ^ 2 - tau P
def optMS (P : Params) : ℝ := 2 * (P.thd + P.b) * P.w / denomS P
def optNS (P : Params) : ℝ := xi P * P.w / denomS P
def optGammaS (P : Params) : ℝ :=
  (P.thd + P.b) * P.w * (P.β * P.qh - (P.adh - P.adl)) / denomS P
def optProfitS (P : Params) : ℝ := (P.thd + P.b) * P.w ^ 2 / denomS P

end
end PlatformQualReg.ExclSubsid


