-- Prove2me | Definitions.Def_MartOT_Var_Setting
-- name    : MartOT_Var_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:10:37.311095+00:00
-- url     : https://prove2.me/theorems/e0ac9c9a-5608-44db-b705-6ca03c33f01c
-- title:
--   §1–§4, pp. 1–31 — 𝓜, Π_M via (4), sufficient integrability, E_π[c], C_M, ⪯C (Def. 2.1), ⪯E (Def. 4.3), shadows (Lemma 4.6), left-monotone (Def. 1.4), π_lc (Thm 4.18), competitors (Def. 1.10), u_µ
-- statement:
--   This file fixes the vocabulary of the martingale optimal transport problem on the real line, as set up by Beiglböck and Juillet.
--
--   1. **Finite measures with a first moment.** $\mathcal M$ is the set of finite Borel measures $\mu$ on $\mathbb R$ with $\int |x|\,d\mu(x)<\infty$.
--   2. **Extended integral.** For a measure $\mu$ and a real function $f$, $\int f\,d\mu\in[-\infty,+\infty]$ is $\int f^+\,d\mu-\int f^-\,d\mu$, with the convention $(+\infty)-(+\infty)=-\infty$.
--   3. **Convex order (Definition 2.1).** For $\mu,\nu\in\mathcal M$, $\mu\preceq_C\nu$ means $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every convex $\varphi:\mathbb R\to\mathbb R$. **Extended convex order (Definition 4.3):** $\mu\preceq_E\nu$ asks this only for nonnegative convex $\varphi$.
--   4. **Transport plans.** $\Pi(\mu,\nu)$ is the set of measures $\pi$ on $\mathbb R\times\mathbb R$ with first marginal $\mu$ and second marginal $\nu$. A plan is a **martingale transport plan**, $\pi\in\Pi_M(\mu,\nu)$, if $y-x$ is $\pi$-integrable and
--   $$\int\rho(x)\,(y-x)\,d\pi(x,y)=0\quad\text{for every bounded Borel }\rho:\mathbb R\to\mathbb R .$$
--   5. **Costs.** A cost $c:\mathbb R^2\to\mathbb R$ satisfies the **sufficient integrability condition** if $c(x,y)\ge a(x)+b(y)$ with $a\in L^1(\mu)$, $b\in L^1(\nu)$. The cost of a plan is $E_\pi[c]=\int c\,d\pi\in(-\infty,+\infty]$, the value of the problem is $C_M(\mu,\nu)=\inf\{E_\pi[c]:\pi\in\Pi_M(\mu,\nu)\}$, and $\pi$ is **optimal** if it lies in $\Pi_M(\mu,\nu)$ and attains this infimum.
--   6. **Shadows (Lemma 4.6).** $\eta$ is the shadow $S^\nu(\mu)$ of $\mu$ in $\nu$ if $\eta\le\nu$, $\mu\preceq_C\eta$, and $\eta\preceq_C\eta'$ for every $\eta'\le\nu$ with $\mu\preceq_C\eta'$. With $\nu^\pi_t$ the second marginal of $\pi$ restricted to $(-\infty,t]\times\mathbb R$, $\pi$ is a **left-curtain coupling** (Theorem 4.18) if it is finite and, for every $x$, it carries $\mu|_{(-\infty,x]}$ to $S^\nu(\mu|_{(-\infty,x]})$.
--   7. **Left-monotone plans (Definition 1.4).** $\pi$ is concentrated on a Borel set $\Gamma$ containing no three points $(x,y^-),(x,y^+),(x',y')$ with $x<x'$ and $y^-<y'<y^+$.
--   8. **Competitors (Definition 1.10).** A measure $\alpha'$ on $\mathbb R^2$ is a competitor of $\alpha$ if both have the same two marginals, $y$ is integrable for both, and $\int\rho(x)\,y\,d\alpha=\int\rho(x)\,y\,d\alpha'$ for every bounded Borel $\rho$; that is, $\alpha$ and $\alpha'$ have the same conditional barycentres $\int y\,d\alpha_x(y)=\int y\,d\alpha'_x(y)$ for almost every $x$.
--   9. **Potential function (§4.1).** $u_\mu(x)=\int|y-x|\,d\mu(y)$.
--
--   Every theorem of the mission is stated in these terms.
--
--   **Formalization Note** The martingale condition "$\int y\,d\pi_x(y)=x$ for $\mu$-a.e. $x$" is encoded through the paper's equivalent characterization (4) (p. 10), and the competitor condition of Definition 1.10 through the same device with test functions $\rho(x)$; this avoids disintegrations. The extended integral is the published `ModelRiskOT.Duality.extIntegral`, with values in `EReal`. Shadows and left-curtain couplings are predicates, not functions: their existence and uniqueness are theorems of the paper. Only items 1–5 and 8 are used in this mission; the rest is the shared layer of the series.
-- source:
--   arXiv:1208.1509v2, §1.1 (pp. 1–2), §2.1–2.2 (pp. 10–11, eq. (4)), §4.1–4.4, Definitions 1.4 (p. 5), 1.10 (p. 8), 2.1 (p. 11), 4.3 (p. 21), Lemma 4.6 (p. 23), Theorem 4.18 (p. 31)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral

namespace MartOT.Var

open MeasureTheory

/-- `𝓜` (§2.1, p. 10): a finite measure on `ℝ` with finite first moment. -/
def InM (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧ Integrable (fun x : ℝ => x) μ

/-- The integral `∫ f dμ ∈ [−∞, +∞]` of a real function, as `∫ f⁺ − ∫ f⁻`
(`ModelRiskOT.Duality.extIntegral`); it is the paper's `∫ c dπ ∈ ]−∞, +∞]` under the sufficient
integrability condition and `∫ ϕ dμ` for a convex `ϕ` and `μ ∈ 𝓜`. -/
noncomputable def integralE {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : EReal :=
  ModelRiskOT.Duality.extIntegral μ (fun x => (f x : EReal))

/-- **Definition 2.1** (p. 11): `μ ⪯C ν`, the convex order on `𝓜`. -/
def ConvexLE (μ ν : Measure ℝ) : Prop :=
  InM μ ∧ InM ν ∧ ∀ ϕ : ℝ → ℝ, ConvexOn ℝ Set.univ ϕ → integralE μ ϕ ≤ integralE ν ϕ

/-- **Definition 4.3** (p. 21): `μ ⪯E ν`, the extended convex order on `𝓜`. -/
def ExtConvexLE (μ ν : Measure ℝ) : Prop :=
  InM μ ∧ InM ν ∧ ∀ ϕ : ℝ → ℝ, ConvexOn ℝ Set.univ ϕ → (∀ x, 0 ≤ ϕ x) →
    ∫⁻ x, ENNReal.ofReal (ϕ x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (ϕ x) ∂ν

/-- Transport plans `Π(μ, ν)` (p. 2, p. 10): measures on `ℝ × ℝ` with marginals `μ` and `ν`. -/
def IsPlan (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) : Prop :=
  π.map Prod.fst = μ ∧ π.map Prod.snd = ν

/-- Martingale transport plans `Π_M(μ, ν)` (p. 2, p. 10), through the paper's characterization (4):
`∫ ρ(x)(y − x) dπ(x, y) = 0` for every bounded measurable `ρ`. -/
def IsMartingalePlan (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) : Prop :=
  IsPlan μ ν π ∧ Integrable (fun p : ℝ × ℝ => p.2 - p.1) π ∧
    ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * (p.2 - p.1) ∂π = 0

/-- The sufficient integrability condition (p. 1): `c(x, y) ≥ a(x) + b(y)` with `a ∈ L¹(μ)`,
`b ∈ L¹(ν)`. -/
def SuffIntegrable (μ ν : Measure ℝ) (c : ℝ → ℝ → ℝ) : Prop :=
  ∃ a b : ℝ → ℝ, Integrable a μ ∧ Integrable b ν ∧ ∀ x y, a x + b y ≤ c x y

/-- `E_π[c] = ∫∫ c(x, y) dπ(x, y)` (2). -/
noncomputable def cost (c : ℝ → ℝ → ℝ) (π : Measure (ℝ × ℝ)) : EReal :=
  integralE π (fun p => c p.1 p.2)

/-- `C_M(μ, ν) = inf {E_π[c] : π ∈ Π_M(μ, ν)}` (p. 2). -/
noncomputable def CM (c : ℝ → ℝ → ℝ) (μ ν : Measure ℝ) : EReal :=
  ⨅ (π : Measure (ℝ × ℝ)) (_ : IsMartingalePlan μ ν π), cost c π

/-- `π` is an optimal martingale transport plan: a minimizer of (2). -/
def IsOptimal (c : ℝ → ℝ → ℝ) (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) : Prop :=
  IsMartingalePlan μ ν π ∧ ∀ π', IsMartingalePlan μ ν π' → cost c π ≤ cost c π'

/-- `ν^π_t = proj^y_# π|_{]−∞,t]×ℝ}` (p. 7). -/
noncomputable def targetUpTo (π : Measure (ℝ × ℝ)) (t : ℝ) : Measure ℝ :=
  (π.restrict (Set.Iic t ×ˢ Set.univ)).map Prod.snd

/-- **Lemma 4.6** (p. 23), properties (i)–(iii): `η` is the shadow `S^ν(μ)` of `μ` in `ν`. -/
def IsShadow (ν μ η : Measure ℝ) : Prop :=
  η ≤ ν ∧ ConvexLE μ η ∧ ∀ η', η' ≤ ν → ConvexLE μ η' → ConvexLE η η'

/-- **Definition 1.4** (p. 5): `π` is (left-)monotone, with a Borel monotonicity set `Γ`. -/
def IsLeftMonotone (π : Measure (ℝ × ℝ)) : Prop :=
  ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
    ∀ x x' ym yp y' : ℝ, (x, ym) ∈ Γ → (x, yp) ∈ Γ → (x', y') ∈ Γ →
      ¬ (x < x' ∧ ym < y' ∧ y' < yp)

/-- **Theorem 4.18** (p. 31), defining property of `π_lc`: `π` transports `μ|]−∞,x]` to
`S^ν(μ|]−∞,x])` for every `x`. The page asks for a probability measure because its `μ`, `ν` are
probabilities; a finite `π` keeps Theorem 6.3's finite measures in scope. -/
def IsLeftCurtain (μ ν : Measure ℝ) (π : Measure (ℝ × ℝ)) : Prop :=
  IsFiniteMeasure π ∧
    ∀ x : ℝ, (π.restrict (Set.Iic x ×ˢ Set.univ)).map Prod.fst = μ.restrict (Set.Iic x) ∧
      IsShadow ν (μ.restrict (Set.Iic x)) (targetUpTo π x)

/-- **Definition 1.10** (p. 8) for the finitely supported `α` of Lemma 1.11: `α'` has the marginals of
`α` and the same conditional barycentres, `∫ ρ(x) y dα = ∫ ρ(x) y dα'` for bounded measurable `ρ`. -/
def IsCompetitor (α α' : Measure (ℝ × ℝ)) : Prop :=
  α.map Prod.fst = α'.map Prod.fst ∧ α.map Prod.snd = α'.map Prod.snd ∧
    Integrable (fun p : ℝ × ℝ => p.2) α ∧ Integrable (fun p : ℝ × ℝ => p.2) α' ∧
    ∀ ρ : ℝ → ℝ, Measurable ρ → (∃ C, ∀ x, |ρ x| ≤ C) →
      ∫ p, ρ p.1 * p.2 ∂α = ∫ p, ρ p.1 * p.2 ∂α'

/-- The potential function `u_μ(x) = ∫ |y − x| dμ(y)` (§4.1, p. 20). -/
noncomputable def potential (μ : Measure ℝ) (x : ℝ) : ℝ := ∫ y, |y - x| ∂μ

end MartOT.Var


