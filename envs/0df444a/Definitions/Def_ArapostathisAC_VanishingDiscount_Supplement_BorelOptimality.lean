-- Prove2me | Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelOptimality
-- name    : ArapostathisAC_VanishingDiscount_Supplement_BorelOptimality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T18:00:30.847597+00:00
-- url     : https://prove2.me/theorems/5ff684cc-30d3-403a-a4a0-0681bc1ac103
-- title:
--   Borel ACOE (6.1), the fixed-state and infimum-normalized differential values, Assumptions 6.8–6.11 and the ACOI (6.12)
-- statement:
--   On a Borel controlled Markov process:
--
--   1. $(\rho,h)$ **solves the ACOE (6.1)** if $\rho,h\in\mathcal M(S)$ are measurable real functions, $h$ is $P(\cdot\mid x,a)$-integrable for every admissible pair, and for every $x$
--   $$\rho(x)+h(x)=\inf_{a\in U(x)}\Big\{c(x,a)+\int_S h(y)\,P(dy\mid x,a)\Big\};$$
--   $f\in\Pi_{SD}$ attains the infimum if $c(x,f(x))+\int h\,dP(\cdot\mid x,f(x))=\rho(x)+h(x)$ for every $x$.
--   2. $h_\beta(x)=J^*_\beta(x)-J^*_\beta(x_0)$ for a fixed state $x_0$, and $\underline h_\beta(x)=J^*_\beta(x)-\inf_{y\in S}J^*_\beta(y)$.
--   3. **Assumption 6.8**: there are $x_0$, a nonnegative $b\in\mathcal M(S)$, $M\ge0$ and $\beta_n\in(0,1)$, $\beta_n\uparrow1$, with $-M\le h_{\beta_n}(x)\le b(x)$ and $\int b(y)P(dy\mid x,a)<\infty$ for all $x$ and $a\in U(x)$. **Assumption 6.9**: $J(\hat x,\pi)<\infty$ for some $\pi$ and $\hat x$. **Assumption 6.10**: for some $\beta'\in(0,1)$, $\sup_{\beta\in(\beta',1)}\underline h_\beta(x)<\infty$ for every $x$. **Assumption 6.11**: $a\mapsto\int u\,dP(\cdot\mid x,a)$ is continuous on $U(x)$ for every bounded measurable $u$ and every $x$.
--   4. The **ACOI (6.12)**: for every $x$ the minimum below is attained and
--   $$\rho^*+h(x)\ge\min_{a\in U(x)}\Big\{c(x,a)+\int_S h(y)\,P(dy\mid x,a)\Big\};$$
--   $f\in\Pi_{SD}$ realizes the minimum if $f(x)$ is a minimizer for every $x$.
--
--   **Formalization Note** $h_\beta$ and $\underline h_\beta$ are computed in $\mathrm{EReal}$ from $J^*_\beta\in[0,\infty]$. The two-sided bound of Assumption 6.8 fails when $J^*_{\beta_n}(x)$ or $J^*_{\beta_n}(x_0)$ is infinite ($\top-\top=\bot$ in Mathlib), so it carries the finiteness the paper's $h_\beta$ presupposes. In (6.12), $h$ is bounded below, so $\int h\,dP$ is a well-defined element of $(-\infty,\infty]$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 315, (6.1); p. 322, Lemma 6.3 (h_β with fixed x₀); p. 323, Assumptions 6.8–6.11 and (6.12)

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalTriplet_CMP
import Definitions.Def_ArapostathisAC_VanishingDiscount_Supplement_BorelCriteria

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.VanishingDiscount.Supplement

open ArapostathisAC.CanonicalTriplet

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- `(ρ, h)` is a solution of the ACOE (6.1) on a Borel state space (p. 315): `ρ, h ∈ 𝓜(S)` are
measurable real functions, `h` is `P(· | x, a)`-integrable for every admissible pair, and
`ρ(x) + h(x) = inf_{a ∈ U(x)} {c(x, a) + ∫ h(y) P(dy | x, a)}` for every `x` (the infimum need not
be attained; `IsGLB` is the exact greatest lower bound). -/
def BorelACOE (M : BorelCMP S A) (ρ h : S → ℝ) : Prop :=
  Measurable ρ ∧ Measurable h ∧
    ∀ x, (∀ a ∈ M.U x, Integrable h (M.P (x, a))) ∧
      IsGLB ((fun a => M.c (x, a) + ∫ y, h y ∂(M.P (x, a))) '' M.U x) (ρ x + h x)

/-- `f ∈ Π_SD` attains the infimum in (6.1) at every state:
`c(x, f(x)) + ∫ h(y) P(dy | x, f(x)) = ρ(x) + h(x)`. -/
def AttainsACOE (M : BorelCMP S A) (ρ h : S → ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ x, M.c (x, f.1 x) + ∫ y, h y ∂(M.P (x, f.1 x)) = ρ x + h x

/-- The fixed-state differential discounted value `h_β(x) = J*_β(x) − J*_β(x₀)` (p. 322 and
Assumption 6.8, p. 323), computed in `EReal`. When both values are `+∞` the difference is `⊥`,
when only `J*_β(x)` is infinite it is `⊤`, and when only `J*_β(x₀)` is infinite it is `⊥`. -/
noncomputable def hRelB (M : BorelCMP S A) (β : ℝ) (x₀ x : S) : EReal :=
  (discValue M β x : EReal) - (discValue M β x₀ : EReal)

/-- The infimum-normalized differential discounted value of Assumption 6.10 (p. 323):
`h̲_β(x) = J*_β(x) − inf_{y ∈ S} J*_β(y)`, computed in `EReal`. -/
noncomputable def hLowRel (M : BorelCMP S A) (β : ℝ) (x : S) : EReal :=
  (discValue M β x : EReal) - ((⨅ y, discValue M β y : ℝ≥0∞) : EReal)

/-- Assumption 6.8 (p. 323): there are a reference state `x₀` (the fixed state of `h_β`), a
nonnegative `b ∈ 𝓜(S)`, a constant `M ≥ 0` and a sequence `β_n ∈ (0, 1)`, `β_n ↑ 1`, such that for
all `x ∈ S` (i) `−M ≤ h_{β_n}(x) ≤ b(x)` and (ii) `∫ b(y) P(dy | x, a) < ∞` for all `a ∈ U(x)`. -/
def Assumption68 (M : BorelCMP S A) : Prop :=
  ∃ x₀ : S, ∃ b : S → ℝ, ∃ Mc : ℝ, ∃ βs : ℕ → ℝ,
    Measurable b ∧ (∀ x, 0 ≤ b x) ∧ 0 ≤ Mc ∧ (∀ n, βs n ∈ Set.Ioo (0 : ℝ) 1) ∧ Monotone βs ∧
      Tendsto βs atTop (𝓝 1) ∧
      (∀ n x, ((-Mc : ℝ) : EReal) ≤ hRelB M (βs n) x₀ x ∧ hRelB M (βs n) x₀ x ≤ (b x : EReal)) ∧
      ∀ x, ∀ a ∈ M.U x, ∫⁻ y, ENNReal.ofReal (b y) ∂(M.P (x, a)) < ⊤

/-- Assumption 6.9 (p. 323): some policy `π` and initial state `x̂` have `J(x̂, π) < ∞`. -/
def Assumption69 (M : BorelCMP S A) : Prop :=
  ∃ π : Policy M, ∃ x : S, avgCost M π x < ⊤

/-- Assumption 6.10 (p. 323): there is `β' ∈ (0, 1)` with `sup_{β ∈ (β', 1)} h̲_β(x) < ∞` for
every `x ∈ S`. -/
def Assumption610 (M : BorelCMP S A) : Prop :=
  ∃ β' ∈ Set.Ioo (0 : ℝ) 1, ∀ x, (⨆ β ∈ Set.Ioo β' 1, hLowRel M β x) < ⊤

/-- Assumption 6.11 (p. 323): `P(· | x, a)` is strongly continuous in `a` for each `x`: for every
bounded measurable `u`, `a ↦ ∫ u(y) P(dy | x, a)` is continuous on `U(x)`. -/
def Assumption611 (M : BorelCMP S A) : Prop :=
  ∀ x, ∀ u : S → ℝ, Measurable u → (∃ C, ∀ y, |u y| ≤ C) →
    ContinuousOn (fun a => ∫ y, u y ∂(M.P (x, a))) (M.U x)

/-- The right-hand side of (6.12) before minimization, `c(x, a) + ∫ h(y) P(dy | x, a)`, for `h`
bounded below, in `(-∞, +∞]`. -/
noncomputable def acoiTerm (M : BorelCMP S A) (h : S → ℝ) (x : S) (a : A) : EReal :=
  (M.c (x, a) : EReal) + extIntegral (M.P (x, a)) (fun y => (h y : EReal))

/-- The average cost optimality inequality (6.12) (p. 323), with its minimum attained:
for every `x`, some `a ∈ U(x)` minimizes `c(x, ·) + ∫ h dP(· | x, ·)` over `U(x)`, and
`ρ* + h(x) ≥ min_{a ∈ U(x)} {c(x, a) + ∫ h(y) P(dy | x, a)}`. -/
def ACOI (M : BorelCMP S A) (ρs : ℝ) (h : S → ℝ) : Prop :=
  ∀ x, ∃ a ∈ M.U x, (∀ a' ∈ M.U x, acoiTerm M h x a ≤ acoiTerm M h x a') ∧
    acoiTerm M h x a ≤ ((ρs + h x : ℝ) : EReal)

/-- `f ∈ Π_SD` realizes the minimum on the right-hand side of (6.12) at every state. -/
def RealizesACOIMin (M : BorelCMP S A) (h : S → ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ x, ∀ a ∈ M.U x, acoiTerm M h x (f.1 x) ≤ acoiTerm M h x a

end ArapostathisAC.VanishingDiscount.Supplement


