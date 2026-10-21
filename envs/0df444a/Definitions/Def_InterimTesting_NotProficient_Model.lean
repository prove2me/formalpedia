-- Prove2me | Definitions.Def_InterimTesting_NotProficient_Model
-- name    : InterimTesting_NotProficient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:14:57.911388+00:00
-- url     : https://prove2.me/theorems/6a6fff9b-c3b8-48eb-8ab2-24435bee3fc5
-- title:
--   §3, pp. 7–11, (1)–(18) — two-period teacher-incentive model: effort-driven proficiency chain, formative vs interim midyear signal, teachers' DP, district's budget-constrained optimum
-- statement:
--   A school's proficiency state is $\beta_t\in\{P,N\}$ (proficient / not proficient) at the beginning ($t=0$), middle ($t=1$) and end ($t=2$) of the school year. At the start of each half-year teachers choose an effort $e_t\in[0,1]$, unobserved by the district, at cost $e_t$ (Assumption 3 with $\gamma$ normalized to $1$).
--
--   **Dynamics** (Assumption 1, (1)). From $P$ the school is proficient at the end of the period with probability $1-\delta(e)=Ae+B$; from $N$ it moves to $P$ with probability $\alpha(e)=\mu(Ae+B)$. Write $m(e_0,S_0)$ for the first of these with $S_0=\beta_0$, (13).
--
--   **Midyear information** (2), (5). Without an interim assessment ($z_I=0$) teachers see only the formative result $X_1$, with
--   $$\Pr[X_1=P\mid\beta_1=P]=\phi_{P|P},\qquad \Pr[X_1=P\mid\beta_1=N]=\phi_{P|N}.$$
--   The free interim assessment ($z_I=1$) reveals $\beta_1$; it is the case $\phi_{P|P}=1$, $\phi_{P|N}=0$ (p. 12). The posterior $\Pr[\beta_1=P\mid S_1]$ at $S_1=(X_1,e_0,S_0)$ is given by Bayes' rule, (12).
--
--   **Teachers' problem** (7)–(8). Under the contract (3) teachers receive $\pi\ge0$ if $\beta_2=P$. In the second period they maximize $\pi\Pr[\beta_2=P\mid S_1]-e_1$ over $e_1\in[0,1]$, where $\Pr[\beta_2=P\mid S_1]=p(Ae_1+B)+(1-p)\mu(Ae_1+B)$ with $p$ the posterior, (A3); this gives $e_1^*$ and the profit-to-go $J_1$. In the first period they maximize the expected $J_1$ over the midyear observation minus $e_0$, giving $e_0^*$. When several efforts are optimal, teachers take the largest ("maximum effort if the incentives are at or above this threshold").
--
--   **District's problem** (9)–(10). $\Pr^*_{z_I}[S_2=P\mid S_0]$ (for fixed $\pi$ and $z_I$) is the probability that $\beta_2=P$ under $(e_0^*,e_1^*)$. For a budget $M$, the district's value for fixed $z_I$ is
--   $$\Pr\nolimits^*_{z_I}(M)=\sup\{\Pr^*_{z_I}[S_2=P\mid S_0](\pi)\;:\;\pi\ge0,\ \pi\,\Pr^*_{z_I}[S_2=P\mid S_0](\pi)\le M\},$$
--   and it invests in the interim assessment only if this makes the value strictly larger (p. 15).
--
--   **Constants.** $\mathcal T_1(S_1)=1/(A((1-\mu)\Pr[\beta_1=P\mid S_1]+\mu))$ (11); $\mathcal T_0(N)=1/(\mu(1-\mu)A(A+B))$ (A57);
--   $$\mathcal H_1(\mu)=\Big(1+\frac{B(1+(1-\mu)B)}{A(B\phi_{P|P}+\phi_{P|N}(1-\mu B))}\Big)(\phi_{P|P}\mu B+\phi_{P|N}(1-\mu B))\ (15),\qquad \mathcal H^I_1(\mu)=\mu B\,\frac{A+1+(1-\mu)B}{A}\ (16),$$
--   $$\mathcal H_2(\mu)=\mu(A+B)(1+(1-\mu)B)\,\mathcal T_1(N,0,N)\ (\text{A155}),\qquad \mathcal H^I_2(\mu)=\frac{(A+B)(1+(1-\mu)B)}{A}\ (\text{A213}),$$
--   $$\mu_0(B)=\frac1B-\frac{1-\phi_{P|P}}{\phi_{P|N}}\ (18),\qquad M_L=\min\{\mathcal H_1(\mu),\mathcal H^I_1(\mu)\},\qquad M_U=\frac{1+(1-\mu)B}{(1-\mu)A}+1 .$$
--
--   **Standing assumptions.** $0<A$, $0\le B$, $A+B\le1$, $0<\mu<1$ (Assumption 1, tightened) and $1>\phi_{P|P}\ge\phi_{P|N}>0$ (Assumption 2). Condition (14) is $\frac{(1-\phi_{P|P})\phi_{P|N}}{\phi_{P|P}-\phi_{P|N}}\le\frac{(1-(A+B))B}{A}$.
--
--   **Formalization Note** `Params` bundles $(A,B,\mu,\phi_{P|P},\phi_{P|N})$ as `A, B, μ, φPP, φPN`; `Params.Standing` adds $A>0$ and $0<\mu<1$ to Assumption 1 (the thresholds divide by $A$, $\mu$ and $1-\mu$). `Cond14` is (14) cross-multiplied, so that it is not vacuously true at $\phi_{P|P}=\phi_{P|N}$. The decision $z_I$ is a `Bool`; `acc θ zI` is the signal accuracy, $(1,0)$ for the interim assessment. `post` is Bayes' rule with Lean's $0/0=0$ on a null observation, which only enters multiplied by that null probability. `e1Star`, `e0Star` are the greatest maximizers over $[0,1]$ (`sSup` of the argmax set); `e1Star` depends on $S_1$ only through the posterior, as in (A11). `PrStar` is the probability of $\beta_2=P$ summed over the joint law of $(\beta_1,X_1,\beta_2)$, not a closed form; `optProb` is the supremum above; `investsInterim` is the strict comparison; `IsOptIncentive` says $\pi$ is affordable and attains `optProb`. `H2` is (A155), a product with $\mathcal T_1(N,0,N)$; the printed (17) divides by it, a misprint. All quantities are real numbers.
-- source:
--   Virudachalam, Savin & Steinberg, Too Much Information: When Does Additional Testing Benefit Schools?, SSRN 3884543 (version of November 3, 2022), pp. 7–16 (PDF 7–16), §3, (1)–(13), Assumptions 1–3, (14)–(18); p. A10 (PDF 36), (A57); p. A23 (PDF 49), (A155); p. A32 (PDF 58), (A213)

import Mathlib

namespace InterimTesting.NotProficient

/-- The proficiency state of the school, `P` (proficient) or `N` (not proficient), p. 7. -/
inductive Prof
  | P
  | N
  deriving DecidableEq

/-- Model parameters, §3, pp. 8–9: `A` (response-to-effort parameter), `B` (baseline proficiency
factor), `μ` (improvement potential factor), `φPP` = ϕ_{P|P} (true positive rate of the formative
assessment) and `φPN` = ϕ_{P|N} (false positive rate). The cost of effort is `γ e` with `γ`
normalized to `1` (Assumption 3, p. 10). -/
structure Params where
  A : ℝ
  B : ℝ
  μ : ℝ
  φPP : ℝ
  φPN : ℝ

/-- Standing assumptions: Assumption 1 (p. 8: `0 ≤ A, B`, `A + B ≤ 1`, `0 ≤ μ ≤ 1`), tightened to
`0 < A` and `0 < μ < 1` (disclosed additions: the thresholds (11), (A57) and `M_U` divide by
`A`, `μ`, `1 − μ`), and Assumption 2 (p. 9: `1 > ϕ_{P|P} ≥ ϕ_{P|N} > 0`). -/
def Params.Standing (θ : Params) : Prop :=
  0 < θ.A ∧ 0 ≤ θ.B ∧ θ.A + θ.B ≤ 1 ∧ 0 < θ.μ ∧ θ.μ < 1 ∧
    0 < θ.φPN ∧ θ.φPN ≤ θ.φPP ∧ θ.φPP < 1

/-- Condition (14) (= (A26)), p. 13, cross-multiplied:
`(1 − ϕ_{P|P}) ϕ_{P|N} / (ϕ_{P|P} − ϕ_{P|N}) ≤ (1 − (A + B)) B / A`. -/
def Cond14 (θ : Params) : Prop :=
  (1 - θ.φPP) * θ.φPN * θ.A ≤ (1 - (θ.A + θ.B)) * θ.B * (θ.φPP - θ.φPN)

/-- Probability of being proficient at the end of a period that starts in state `s` with effort
`e`, Assumption 1, (1): `1 − δ(e) = A e + B` from `P`, `α(e) = μ (A e + B)` from `N`.
`m(e0, S0)` of (13) is `toP θ S0 e0`. -/
def toP (θ : Params) : Prof → ℝ → ℝ
  | .P, e => θ.A * e + θ.B
  | .N, e => θ.μ * (θ.A * e + θ.B)

/-- Signal accuracy `(Pr[X1 = P | β1 = P], Pr[X1 = P | β1 = N])` of the midyear observation.
Without the interim assessment (`zI = false`) it is the formative assessment, (2):
`(ϕ_{P|P}, ϕ_{P|N})`. With it (`zI = true`) the midyear state is revealed, i.e. the case
`ϕ_{P|P} = 1`, `ϕ_{P|N} = 0` (p. 12, p. A4). -/
def acc (θ : Params) (zI : Bool) : ℝ × ℝ :=
  if zI then (1, 0) else (θ.φPP, θ.φPN)

/-- `Pr[X1 = x | β1 = b]`. -/
def sig (θ : Params) (zI : Bool) : Prof → Prof → ℝ
  | .P, .P => (acc θ zI).1
  | .P, .N => 1 - (acc θ zI).1
  | .N, .P => (acc θ zI).2
  | .N, .N => 1 - (acc θ zI).2

/-- `Pr[β1 = b, X1 = x]` given the first-period effort `e0` and starting state `S0`. -/
def joint (θ : Params) (zI : Bool) (S0 : Prof) (e0 : ℝ) (b x : Prof) : ℝ :=
  (match b with
    | .P => toP θ S0 e0
    | .N => 1 - toP θ S0 e0) * sig θ zI b x

/-- `Pr[X1 = x]` given `e0` and `S0`. -/
def obsProb (θ : Params) (zI : Bool) (S0 : Prof) (e0 : ℝ) (x : Prof) : ℝ :=
  joint θ zI S0 e0 .P x + joint θ zI S0 e0 .N x

/-- Posterior `Pr[β1 = P | S1]` at `S1 = (x, e0, S0)`, by Bayes' rule (the definition behind
(12)). On an observation of probability `0` Lean's `0 / 0 = 0` is used; every quantity below
multiplies it by that probability `0`. -/
noncomputable def post (θ : Params) (zI : Bool) (S0 : Prof) (e0 : ℝ) (x : Prof) : ℝ :=
  joint θ zI S0 e0 .P x / obsProb θ zI S0 e0 x

/-- `Pr[β2 = P]` when `Pr[β1 = P] = p` and the second-period effort is `e1`, (A3). -/
def finalP (θ : Params) (p e1 : ℝ) : ℝ :=
  p * toP θ .P e1 + (1 - p) * toP θ .N e1

/-- Second-period objective of (7) at `t = 1` with `J2` of (8) and `γ = 1`, cf. (A11). -/
def obj1 (θ : Params) (π p e1 : ℝ) : ℝ :=
  π * finalP θ p e1 - e1

/-- Teachers' optimal second-period effort: the greatest maximizer of `obj1` over `[0, 1]`. -/
noncomputable def e1Star (θ : Params) (π p : ℝ) : ℝ :=
  sSup {e | e ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e' ∈ Set.Icc (0 : ℝ) 1, obj1 θ π p e' ≤ obj1 θ π p e}

/-- Second-period profit-to-go `J1(S1)`, (A9)/(A11), as a function of the posterior. -/
noncomputable def J1 (θ : Params) (π p : ℝ) : ℝ :=
  obj1 θ π p (e1Star θ π p)

/-- First-period objective of (7) at `t = 0`: expected profit-to-go over the midyear observation,
minus the cost of effort. -/
noncomputable def obj0 (θ : Params) (zI : Bool) (S0 : Prof) (π e0 : ℝ) : ℝ :=
  obsProb θ zI S0 e0 .P * J1 θ π (post θ zI S0 e0 .P)
    + obsProb θ zI S0 e0 .N * J1 θ π (post θ zI S0 e0 .N) - e0

/-- Teachers' optimal first-period effort: the greatest maximizer of `obj0` over `[0, 1]`. -/
noncomputable def e0Star (θ : Params) (zI : Bool) (S0 : Prof) (π : ℝ) : ℝ :=
  sSup {e | e ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ e' ∈ Set.Icc (0 : ℝ) 1, obj0 θ zI S0 π e' ≤ obj0 θ zI S0 π e}

/-- Contribution of the midyear observation `x` to `Pr[β2 = P]` when the first-period effort is
`e0` and teachers respond optimally in the second period. -/
noncomputable def finalContrib (θ : Params) (zI : Bool) (S0 : Prof) (π e0 : ℝ) (x : Prof) : ℝ :=
  let e1 := e1Star θ π (post θ zI S0 e0 x)
  joint θ zI S0 e0 .P x * toP θ .P e1 + joint θ zI S0 e0 .N x * toP θ .N e1

/-- `Pr*[S2 = P | S0]` for fixed `π` and `zI`: the probability that the school is proficient at
`t = 2` under the teachers' optimal policy `(e0*, e1*)`, p. 11. -/
noncomputable def PrStar (θ : Params) (zI : Bool) (S0 : Prof) (π : ℝ) : ℝ :=
  finalContrib θ zI S0 π (e0Star θ zI S0 π) .P + finalContrib θ zI S0 π (e0Star θ zI S0 π) .N

/-- `Pr*_{zI}[S2 = P | S0]`: the value of the district's problem (9)–(10) for fixed `zI`, the
supremum of `Pr*` over incentives `π ≥ 0` meeting the budget `π · Pr* ≤ M`. -/
noncomputable def optProb (θ : Params) (zI : Bool) (S0 : Prof) (M : ℝ) : ℝ :=
  sSup {q | ∃ π : ℝ, 0 ≤ π ∧ π * PrStar θ zI S0 π ≤ M ∧ q = PrStar θ zI S0 π}

/-- The district invests in the (free) interim assessment only if this makes the optimal
probability strictly greater, p. 15. -/
def investsInterim (θ : Params) (S0 : Prof) (M : ℝ) : Prop :=
  optProb θ false S0 M < optProb θ true S0 M

/-- `π` is an optimal incentive for fixed `zI`: affordable and attaining `optProb`. -/
def IsOptIncentive (θ : Params) (zI : Bool) (S0 : Prof) (M π : ℝ) : Prop :=
  0 ≤ π ∧ π * PrStar θ zI S0 π ≤ M ∧ PrStar θ zI S0 π = optProb θ zI S0 M

/-- `𝒯1` of (11) as a function of the posterior `p = Pr[β1 = P | S1]`. -/
noncomputable def T1p (θ : Params) (p : ℝ) : ℝ :=
  1 / (θ.A * ((1 - θ.μ) * p + θ.μ))

/-- `𝒯1(x, e0, S0)`, (11)–(13). -/
noncomputable def T1 (θ : Params) (zI : Bool) (S0 : Prof) (e0 : ℝ) (x : Prof) : ℝ :=
  T1p θ (post θ zI S0 e0 x)

/-- `𝒯0(N) = 1 / (μ (1 − μ) A (A + B))`, (A57). -/
noncomputable def T0N (θ : Params) : ℝ :=
  1 / (θ.μ * (1 - θ.μ) * θ.A * (θ.A + θ.B))

/-- `ℋ1(μ)`, (15). -/
noncomputable def H1 (θ : Params) : ℝ :=
  (1 + θ.B * (1 + (1 - θ.μ) * θ.B) /
      (θ.A * (θ.B * θ.φPP + θ.φPN * (1 - θ.μ * θ.B)))) *
    (θ.φPP * θ.μ * θ.B + θ.φPN * (1 - θ.μ * θ.B))

/-- `ℋ^I_1(μ) = μ B (A + 1 + (1 − μ) B) / A`, (16) = (A200). -/
noncomputable def HI1 (θ : Params) : ℝ :=
  θ.μ * θ.B * ((θ.A + 1 + (1 - θ.μ) * θ.B) / θ.A)

/-- `ℋ2(μ) = μ (A + B)(1 + (1 − μ) B) · 𝒯1(N, 0, N)`, (A155) (the printed (17) has a quotient). -/
noncomputable def H2 (θ : Params) : ℝ :=
  θ.μ * (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) * T1 θ false .N 0 .N

/-- `ℋ^I_2(μ) = (A + B)(1 + (1 − μ) B) / A`, (A213). -/
noncomputable def HI2 (θ : Params) : ℝ :=
  (θ.A + θ.B) * (1 + (1 - θ.μ) * θ.B) / θ.A

/-- `μ0(B) = 1/B − (1 − ϕ_{P|P}) / ϕ_{P|N}`, (18). -/
noncomputable def mu0 (θ : Params) : ℝ :=
  1 / θ.B - (1 - θ.φPP) / θ.φPN

/-- `M_L = min{ℋ1(μ), ℋ^I_1(μ)}`, Proposition 1 b). -/
noncomputable def ML (θ : Params) : ℝ :=
  min (H1 θ) (HI1 θ)

/-- `M_U = (1 + (1 − μ) B) / ((1 − μ) A) + 1`, Proposition 1 b). -/
noncomputable def MU (θ : Params) : ℝ :=
  (1 + (1 - θ.μ) * θ.B) / ((1 - θ.μ) * θ.A) + 1

end InterimTesting.NotProficient


