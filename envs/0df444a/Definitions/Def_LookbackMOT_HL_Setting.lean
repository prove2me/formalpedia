-- Prove2me | Definitions.Def_LookbackMOT_HL_Setting
-- name    : LookbackMOT_HL_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:33:10.907989+00:00
-- url     : https://prove2.me/theorems/86949984-15b4-47f1-a82b-fc29560caef1
-- title:
--   §2.1, (3.1)–(3.25), pp. 4–15 — Brownian setting, 𝒯_∞, J, u^λ, Λ^μ_0, U^μ, c, b, μ^HL, τ*, λ*, Ψ^λ, v^ψ, φ
-- statement:
--   This file fixes the objects of Section 3 of Galichon, Henry-Labordère and Touzi: the robust superhedging problem for a lookback payoff $g(X^*_T)$ when the law $\mu$ of the terminal value of the underlying is known, in its reduced form (3.7) as an optimal stopping problem for Brownian motion with a Lagrange multiplier $\lambda$.
--
--   **The process.** On a probability space $(\Omega,\mathcal F,P)$ with a filtration $(\mathcal F_t)_{t\ge 0}$, $B$ is an $(\mathcal F_t)$-Brownian motion: a real Brownian motion with continuous paths, $B_0=0$, adapted to the filtration, whose increments $B_t-B_s$ ($s\le t$) are independent of $\mathcal F_s$. For a starting point $x\in\mathbb R$ write $X^x_t=x+B_t$, and $X=X^{X_0}$. For a random time $\tau$, $X^*_\tau=\max_{t\le\tau}X_t$ is the running maximum, and $X_\tau$ the stopped value.
--
--   **Admissible stopping times.** $\mathcal T_\infty$ is the set of stopping times $\tau$ such that the stopped process $(X_{t\wedge\tau})_{t\ge0}$ is a uniformly integrable martingale (p. 10).
--
--   **Expectations of payoffs.** For a payoff $\varphi$, $\mathbb E[\varphi]=\mathbb E[\varphi^+]-\mathbb E[\varphi^-]\in[-\infty,+\infty]$, with the convention $(+\infty)-(+\infty)=-\infty$.
--
--   **The reduced problem (3.7)–(3.8).** For $g:\mathbb R\to\mathbb R_+$ and a multiplier $\lambda:\mathbb R\to\mathbb R$,
--   $$J(\lambda,\tau)=\mathbb E\big[g(X^*_\tau)-\lambda(X_\tau)\big],\qquad u^\lambda(x,m)=\sup_{\tau\in\mathcal T_\infty}\mathbb E\big[g(m\vee \max_{t\le\tau}X^x_t)-\lambda(X^x_\tau)\big]\quad (x\le m),$$
--   $$\Lambda^\mu_0=\Big\{\lambda\in\mathbb L^1(\mu):\ \sup_{\tau\in\mathcal T_\infty}\mathbb E[\lambda(X_\tau)^-]<\infty\Big\},\qquad \hat\Lambda^\mu_0=\{\lambda\in\Lambda^\mu_0:\lambda\text{ convex}\},$$
--   $$U^\mu(\xi)=\inf_{\lambda\in\Lambda^\mu_0}\big\{\mu(\lambda)+u^\lambda(X_0,X_0)\big\},\qquad \mu(\lambda)=\int\lambda\,d\mu .$$
--
--   **Objects of the marginal.** The call price $c(x)=\int(y-x)^+\mu(dy)$, $c_0(x)=(X_0-x)^+$, and $\varphi(x,m)=\big(c(x)-c_0(x)\mathbf 1_{m<X_0}\big)/(m-x)$ (3.25). The barycenter function (3.9) is $b(x)=\int_{[x,\infty)}y\,\mu(dy)/\mu([x,\infty))$ when $\mu((x,\infty))>0$ (that is, $x<r^\mu$) and $b(x)=x$ otherwise. The Hardy–Littlewood transform $\mu^{HL}$ (3.12) is the probability measure with
--   $$\mu^{HL}([y,\infty))=\inf_{\xi<y}\frac{c(\xi)}{y-\xi}\qquad\text{for all }y .$$
--   The right-continuous inverse of $b$ is $b^{-1}(m)=\sup\{\xi:b(\xi)\le m\}$; on $(X_0,r^\mu)$ it is Hobson's function $\beta$ of Remark 3.1.
--
--   **Convex multipliers.** $\lambda'$ denotes the right derivative and $\lambda''$ the second-derivative measure, $\lambda''((s,t])=\lambda'(t)-\lambda'(s)$. The set $\Psi^\lambda$ (3.22) consists of right-continuous $\psi$ with $\psi(m)<m$ for all $m$ satisfying the weak ODE (3.21), $\int_{\psi(B)}\lambda''(dy)=\int_B \frac{g'(m)}{m-\psi(m)}\,dm$. Peskir's candidate (3.18) is $v^\psi(x,m)=g(m)-\lambda(x\wedge\psi(m))-\lambda'(\psi(m))(x-x\wedge\psi(m))$.
--
--   **The Azéma–Yor solution.** $\tau^*=\inf\{t>0:X^*_t\ge b(X_t)\}$ (3.13) and
--   $$\lambda^*(x)=\int_{\ell^\mu}^{x}\!\int_{\ell^\mu}^{y} g'(b(\xi))\,\frac{b(d\xi)}{b(\xi)-\xi}\,dy\qquad(3.14),$$
--   taken in the form the proof of Lemma 3.3 uses ("by definition, $\lambda^*$ satisfies the ODE (3.21) with $\psi=b^{-1}$"): after the change of variables $m=b(\xi)$,
--   $$\lambda^*(x)=\int_{X_0<m<r^\mu}\frac{g'(m)\,(x-b^{-1}(m))^+}{m-b^{-1}(m)}\,dm .$$
--
--   These are the objects in which Theorem 3.1 and the lemmas of its proof are stated.
--
--   **Formalization Note** The Brownian motion lives on an arbitrary filtered probability space rather than the canonical Wiener space; that is the paper's setting as a special case. Every $\tau\in\mathcal T_\infty$ is in addition required to be a.s. finite (implied by uniform integrability of the stopped Brownian motion) so that $X_\tau$ is meaningful. $\Lambda^\mu_0$ also requires $\lambda$ to be measurable, so that $\lambda(X_\tau)$ is a random variable. Payoff expectations are taken in the extended reals as $\mathbb E[\varphi^+]-\mathbb E[\varphi^-]$, never as a Bochner integral. The barycenter, $\mu^{HL}$ and $\lambda^*$ are given on all of $\mathbb R$ (the paper writes them for $x\ge0$ while taking $\mu\in M(\mathbb R)$). The numerator in (3.12) is $c(\xi)$; the page prints $c(y)$, which would make every tail $0$. $\lambda^*$ is written through $b^{-1}$, as the solution of (3.21) with $\psi=b^{-1}$ that the proof of Lemma 3.3 says it is: this is the page's Fubini form $\int_{\ell^\mu}^x g'(b(\xi))\frac{x-\xi}{b(\xi)-\xi}\,b(d\xi)$ after the substitution $m=b(\xi)$, and the two agree whenever $b$ is continuous. Where $\mu$ has atoms, $b$ jumps, and the Lebesgue–Stieltjes reading of (3.14) puts the weight $g'(b(\xi))/(b(\xi)-\xi)$ at the left end of each jump instead of $\int g'(m)/(m-\xi)\,dm$ across it; with infinitely many atoms and a suitable $C^1$ $g$ that reading is not $\mu$-integrable even though $\mu^{HL}(g)<\infty$, and Theorem 3.1 fails for it. $\lambda^*$ is computed in $[0,\infty]$ (the page notes $\lambda^*\in[0,\infty]$) and converted to a real number; the conversion is exact for $x<r^\mu$, and values at $x>r^\mu$ are never charged by $\mu$ or by $X_{\tau^*}$. The weak ODE (3.21) is recorded in the two forms the paper's proofs use it in: as a change of variables ($\lambda''$ is the image of $g'(m)/(m-\psi(m))\,dm$ under $\psi$, "in the distribution sense", proof of Lemma 3.2) and on intervals $B=(y_1,y_2]$ with $\psi(B)$ read as $(\psi(y_1),\psi(y_2)]$, i.e. $\lambda'(\psi(y_2))=\lambda'(\psi(y_1))+\int_{y_1}^{y_2}g'(m)/(m-\psi(m))\,dm$ (the display of Remark 3.2). The literal form, which constrains $\lambda''$ only on images $\psi(B)$, leaves $\lambda''$ free off the range of $\psi$, and the lemmas can fail under it. The measures $\mu^{HL}$ and $\lambda''$ enter as measures satisfying their defining identities; each exists and is unique.
-- source:
--   Galichon, Henry-Labordère & Touzi, A stochastic control approach to no-arbitrage bounds given marginals, with an application to lookback options, arXiv:1401.3921v1, p. 4 (§2.1), p. 7 (§2.4, mean condition), pp. 10–15, (3.1)–(3.3), (3.7)–(3.14), (3.16), (3.18), (3.21)–(3.22), (3.25)

import Mathlib

namespace LookbackMOT.HL

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The Brownian setting of §2.1 (p. 4), on an arbitrary filtered probability space: `B` is a real
Brownian motion with everywhere-continuous paths, `B₀ = 0`, adapted to `ℱ`, and with increments
`B t - B s` (`s ≤ t`) independent of `ℱ s`. -/
structure IsFBrownian (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (B : ℝ≥0 → Ω → ℝ) : Prop where
  brownian : IsBrownianReal B P
  cont : ∀ ω, Continuous fun t => B t ω
  zero : ∀ ω, B 0 ω = 0
  adapted : Adapted ℱ B
  indep : ∀ s t : ℝ≥0, s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) P

/-- The process started at `x`: `X^x_t = x + B_t` (p. 10, (3.3)); `X = shift X₀ B` (p. 4). -/
def shift (x : ℝ) (B : ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ := fun t ω => x + B t ω

/-- The running maximum `X*_τ = max_{t ≤ τ} X_t` (p. 10, (3.1)); with `τ ≡ t` it is `X*_t`. -/
noncomputable def runMaxUpTo (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ s : {s : ℝ≥0 // (s : WithTop ℝ≥0) ≤ τ ω}, X s ω

/-- `τ ∈ 𝒯_∞` (p. 10): `τ` is an `ℱ`-stopping time, a.s. finite, and the stopped process
`(X_{t∧τ})_{t ≥ 0}` is a uniformly integrable martingale. -/
def IsUIStop (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : Prop :=
  IsStoppingTime ℱ τ ∧ (∀ᵐ ω ∂P, τ ω ≠ ⊤) ∧
    Martingale (stoppedProcess X τ) ℱ P ∧ UniformIntegrable (stoppedProcess X τ) 1 P

/-- The expectation of a payoff in `EReal`: `E[φ⁺] − E[φ⁻]`, which is `⊥` when both parts are
infinite (`⊤ − ⊤ = ⊥` in `EReal`). -/
noncomputable def expect (P : Measure Ω) (φ : Ω → ℝ) : EReal :=
  ((∫⁻ ω, ENNReal.ofReal (φ ω) ∂P : ℝ≥0∞) : EReal) -
    ((∫⁻ ω, ENNReal.ofReal (-φ ω) ∂P : ℝ≥0∞) : EReal)

/-- The value of the stopping problem started at `(x, m) ∈ Δ` (Proposition 3.1, p. 10):
`u^λ(x, m) = sup_{τ ∈ 𝒯_∞} E[g(M^{x,m}_τ) − λ(X^x_τ)]` with `M^{x,m}_τ = m ∨ max_{t ≤ τ} X^x_t`. -/
noncomputable def stopValue (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (B : ℝ≥0 → Ω → ℝ) (g lam : ℝ → ℝ) (x m : ℝ) : EReal :=
  ⨆ τ : Ω → WithTop ℝ≥0, ⨆ (_ : IsUIStop P ℱ (shift x B) τ),
    expect P (fun ω => g (max m (runMaxUpTo (shift x B) τ ω)) -
      lam (stoppedValue (shift x B) τ ω))

/-- `J(λ, τ) = E[g(X*_τ) − λ(X_τ)]` (p. 11), with `X = X₀ + B`. -/
noncomputable def J (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X₀ : ℝ) (g lam : ℝ → ℝ)
    (τ : Ω → WithTop ℝ≥0) : EReal :=
  expect P (fun ω => g (runMaxUpTo (shift X₀ B) τ ω) - lam (stoppedValue (shift X₀ B) τ ω))

/-- `λ ∈ Λ^μ_0` (3.8): `λ` is measurable, `μ`-integrable, and
`sup_{τ ∈ 𝒯_∞} E[λ(X_τ)⁻] < ∞`. -/
def InLambda0 (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ)
    (X₀ : ℝ) (μ : Measure ℝ) (lam : ℝ → ℝ) : Prop :=
  Measurable lam ∧ Integrable lam μ ∧
    (⨆ τ : Ω → WithTop ℝ≥0, ⨆ (_ : IsUIStop P ℱ (shift X₀ B) τ),
      ∫⁻ ω, ENNReal.ofReal (-(lam (stoppedValue (shift X₀ B) τ ω))) ∂P) < ⊤

/-- `λ ∈ Λ̂^μ_0` (3.16): `λ ∈ Λ^μ_0` and `λ` is convex. -/
def InLambda0Hat (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ)
    (X₀ : ℝ) (μ : Measure ℝ) (lam : ℝ → ℝ) : Prop :=
  InLambda0 P ℱ B X₀ μ lam ∧ ConvexOn ℝ Set.univ lam

/-- The reduced problem (3.7): `U^μ(ξ) = inf_{λ ∈ Λ^μ_0} {μ(λ) + u^λ(X₀, X₀)}`. -/
noncomputable def U (P : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (B : ℝ≥0 → Ω → ℝ)
    (X₀ : ℝ) (μ : Measure ℝ) (g : ℝ → ℝ) : EReal :=
  ⨅ lam : ℝ → ℝ, ⨅ (_ : InLambda0 P ℱ B X₀ μ lam),
    ((∫ x, lam x ∂μ : ℝ) : EReal) + stopValue P ℱ B g lam X₀ X₀

/-- The call price `c(x) = ∫ (y − x)⁺ μ(dy)` (Remark 3.1, (3.25)). -/
noncomputable def callPrice (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, max (y - x) 0 ∂μ

/-- `c₀(x) = (X₀ − x)⁺` (3.25). -/
noncomputable def c0 (X₀ x : ℝ) : ℝ := max (X₀ - x) 0

/-- `φ(x, m) = (c(x) − c₀(x) 1_{m < X₀}) / (m − x)` (3.25). -/
noncomputable def phi (μ : Measure ℝ) (X₀ x m : ℝ) : ℝ :=
  (callPrice μ x - c0 X₀ x * (if m < X₀ then 1 else 0)) / (m - x)

/-- The barycenter function (3.9): `b(x) = ∫_{[x,∞)} y μ(dy) / μ([x,∞))` for `x < r^μ`
(equivalently `μ((x,∞)) > 0`) and `b(x) = x` otherwise; on all of `ℝ`. -/
noncomputable def barycenter (μ : Measure ℝ) (x : ℝ) : ℝ :=
  if 0 < μ (Set.Ioi x) then (∫ y in Set.Ici x, y ∂μ) / (μ (Set.Ici x)).toReal else x

/-- `ν = μ^HL` (3.12), with the numerator `c(ξ)`: `ν` is a probability measure with
`ν([y, ∞)) = inf_{ξ < y} c(ξ) / (y − ξ)` for every `y`. -/
def IsHLTransform (μ ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧
    ∀ y : ℝ, ν (Set.Ici y) = ENNReal.ofReal (⨅ ξ : Set.Iio y, callPrice μ ξ / (y - ξ))

/-- The right derivative `λ′(x) = λ′(x+)`. -/
noncomputable def rDeriv (lam : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin lam (Set.Ioi x) x

/-- `ν₂ = λ″`, the second-derivative measure of a convex `λ`: the Stieltjes measure of the
right-continuous `λ′`, `ν₂((s, t]) = λ′(t) − λ′(s)`. -/
def IsSecondDerivMeasure (lam : ℝ → ℝ) (ν₂ : Measure ℝ) : Prop :=
  ∀ s t : ℝ, s ≤ t → ν₂ (Set.Ioc s t) = ENNReal.ofReal (rDeriv lam t - rDeriv lam s)

/-- `ψ ∈ Ψ^λ` (3.22) with the weak ODE (3.21): `ψ` is right-continuous with `ψ(m) < m`, and
(3.21) holds in two forms: as a change of variables (`λ″` is the image of
`g′(m)/(m − ψ(m)) dm` under `ψ`), and on half-open intervals `B = (y₁, y₂]` with `ψ(B)` read as
`(ψ(y₁), ψ(y₂)]`, i.e. `λ′(ψ(y₂)) = λ′(ψ(y₁)) + ∫_{y₁}^{y₂} g′(m)/(m − ψ(m)) dm`. -/
def InPsi (g lam : ℝ → ℝ) (ν₂ : Measure ℝ) (ψ : ℝ → ℝ) : Prop :=
  (∀ m, ψ m < m) ∧ (∀ m, ContinuousWithinAt ψ (Set.Ici m) m) ∧
    (∀ A : Set ℝ, MeasurableSet A →
      ν₂ A = ∫⁻ m in ψ ⁻¹' A, ENNReal.ofReal (deriv g m / (m - ψ m))) ∧
    (∀ y₁ y₂ : ℝ, y₁ ≤ y₂ → rDeriv lam (ψ y₁) ≤ rDeriv lam (ψ y₂) ∧
      ENNReal.ofReal (rDeriv lam (ψ y₂) - rDeriv lam (ψ y₁)) =
        ∫⁻ m in Set.Ioc y₁ y₂, ENNReal.ofReal (deriv g m / (m - ψ m)))

/-- Peskir's guess (3.18): `v^ψ(x, m) = g(m) − λ(x ∧ ψ(m)) − λ′(ψ(m))(x − x ∧ ψ(m))`. -/
noncomputable def vpsi (g lam ψ : ℝ → ℝ) (x m : ℝ) : ℝ :=
  g m - lam (min x (ψ m)) - rDeriv lam (ψ m) * (x - min x (ψ m))

/-- The Azéma–Yor stopping time (3.13): `τ* = inf{t > 0 : X*_t ≥ b(X_t)}`, `⊤` if the set is
empty. -/
noncomputable def tauStar (B : ℝ≥0 → Ω → ℝ) (X₀ : ℝ) (μ : Measure ℝ) (ω : Ω) : WithTop ℝ≥0 :=
  let S : Set ℝ≥0 := {t | 0 < t ∧
    barycenter μ (X₀ + B t ω) ≤ runMaxUpTo (shift X₀ B) (fun _ => (t : WithTop ℝ≥0)) ω}
  open Classical in if S.Nonempty then ((sInf S : ℝ≥0) : WithTop ℝ≥0) else ⊤

/-- `b⁻¹`, the right-continuous inverse of the barycenter function (Remark 3.1, proof of Lemma 3.3
step (2)): `b⁻¹(m) = sup{ξ : b(ξ) ≤ m}`. It is used only for `X₀ < m < r^μ`, where the set is
nonempty (`b(ξ) → X₀` as `ξ → −∞`) and bounded above by `m` (`b(ξ) > ξ` for `ξ < r^μ`, `b(ξ) = ξ`
beyond), so `sSup` is a real number with `b⁻¹(m) < m`. -/
noncomputable def baryInv (μ : Measure ℝ) (m : ℝ) : ℝ := sSup {ξ : ℝ | barycenter μ ξ ≤ m}

/-- The optimal multiplier λ* (3.14), in the form the proof of Lemma 3.3, step (2), uses: λ* is
the convex function with `λ*(x) = 0` for `x ≤ ℓ^μ` that solves the weak ODE (3.21) with
`ψ = b⁻¹`, i.e. `(λ*)″` is the image of `g′(m)/(m − b⁻¹(m)) dm` on `(X₀, r^μ)` under `b⁻¹`:
`λ*(x) = ∫_{X₀ < m < r^μ} g′(m) (x − b⁻¹(m))⁺ / (m − b⁻¹(m)) dm`, computed in `[0, ∞]`.
This is the page's Fubini form `∫_{ℓ^μ}^x g′(b(ξ)) (x − ξ)/(b(ξ) − ξ) b(dξ)` after the change of
variables `m = b(ξ)`; the two agree when `b` is continuous, and where `b` jumps (atoms of `μ`)
the change-of-variables form is the solution of (3.21) that the proof uses. -/
noncomputable def lamStar (μ : Measure ℝ) (X₀ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫⁻ m in {m : ℝ | X₀ < m ∧ 0 < μ (Set.Ioi m)},
    ENNReal.ofReal (deriv g m * max (x - baryInv μ m) 0 / (m - baryInv μ m))).toReal

end LookbackMOT.HL


