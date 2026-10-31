-- Prove2me | Definitions.Def_SalesforceComp_Model
-- name    : SalesforceComp_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:24:41.361717+00:00
-- url     : https://prove2.me/theorems/d50a0758-ff53-4bfc-a4fd-3eced22d1824
-- title:
--   §2–§4, pp. 6–13 — salesforce model: $K=C\circ E$, $D$, $S$, $M$, problems (PCD), (PCS), (PDD), (PDS), system (1), Conditions (D), (S), $V^*$, the menus of Props 3 and 5
-- statement:
--   This module defines the model of Song, Lai and Xiao's analysis of salesforce compensation with inventory, and the four contracting problems it compares.
--
--   **Setting** (§2, pp. 6–8). A risk-neutral firm sells through a risk-neutral sales agent at unit price $p>0$. The agent privately observes the market condition $\Theta=\theta\in[\underline\theta,\bar\theta]$, which has density $f>0$ on $[\underline\theta,\bar\theta]$, distribution function $F(\theta)=\int_{\underline\theta}^{\theta}f$ and inverse hazard rate $H(\theta)=(1-F(\theta))/f(\theta)$, assumed decreasing. A $\theta$-type agent who chooses output $r$ pays the cost $K(r,\theta)=C(E(r,\theta))$, where $C$ is the cost of effort and $E(r,\theta)$ the effort needed for output $r$. Demand is $d(r,\varepsilon)$, with a shock $\varepsilon\sim G$, $G$ a probability measure with a density. Inventory $Q$ costs the firm $c$ and the agent $h$ per unit; sales are $\min\{d,Q\}$. The data satisfy Assumption 1 (p. 7): $C$, $d$, $E$ are three times continuously differentiable and, writing numbered subscripts for partial derivatives,
--
--   1. $C_1>0$, $C_{11}>0$, $C_{111}\ge0$;
--   2. $d_1>0$, $d_2>0$, $d_{11}\le0$;
--   3. $E_1>0$, $E_2<0$, $E_{11}\ge0$, $E_{12}\le0$, $E_{22}\ge0$, $E_{112}\le0$, $E_{122}\ge0$.
--
--   **Derived quantities.** Expected demand $D(r)=\mathbb E_\varepsilon[d(r,\varepsilon)]$ and expected sales $S(r,Q)=\mathbb E_\varepsilon[\min\{d(r,\varepsilon),Q\}]$ (p. 8); the virtual surplus (proof of Proposition 1, p. 22)
--   $$M(r,Q,\theta)=pS(r,Q)-(c+h)Q-K(r,\theta)+K_2(r,\theta)H(\theta);$$
--   and $\mathbb E_\Theta[\varphi(\Theta)]=\int_{\underline\theta}^{\bar\theta}\varphi f$.
--
--   **The four problems** (§3, p. 9; §4, p. 12). A direct mechanism for the control setting is a payment $T(\cdot,\hat\theta)$ on realized demand (CD) or on realized sales (CS), an inventory $Q(\hat\theta)$ set by the firm, and the output $r(\theta)$ it expects. The $\theta$-type agent who reports $\hat\theta$ and produces $x$ earns
--   $$\mathbb E_\varepsilon[T(d(x,\varepsilon),\hat\theta)]-hQ(\hat\theta)-K(x,\theta)\quad\text{(CD)},\qquad \mathbb E_\varepsilon[T(\min\{d(x,\varepsilon),Q(\hat\theta)\},\hat\theta)]-hQ(\hat\theta)-K(x,\theta)\quad\text{(CS)}.$$
--   In the delegation setting the payment $T(\cdot,q,\hat\theta)$ also depends on the inventory $q$ the agent requests, the agent pays $hq$, and the mechanism names both the expected output $r(\theta)$ and the expected request $Q(\theta)$ (DD on demand, DS on sales). A mechanism is feasible when (IC) truthful reporting with the expected actions is optimal against every report $\hat\theta\in[\underline\theta,\bar\theta]$ and every output $x\ge0$ (and every request $q\ge0$), (IR) the truthful payoff $\pi(\theta)$ is nonnegative, and the expectations involved exist. The firm's profit is
--   $$\Pi=\mathbb E_{\Theta,\varepsilon}\big[pS(r(\Theta),Q(\Theta))-cQ(\Theta)-T(\cdot)\big],$$
--   with the payment evaluated at the truthful report and actions. For each problem the set of attainable profits ranges over **all** feasible direct mechanisms.
--
--   **The second-best outcome.** System (1) of Proposition 1 (p. 9) at type $\theta$ reads
--   $$pS_1(r,Q)-K_1(r,\theta)+K_{12}(r,\theta)H(\theta)=0,\qquad pS_2(r,Q)-c-h=0.$$
--   For a nonnegative solution $(r^*,Q^*)$ of (1) on $[\underline\theta,\bar\theta]$: Condition (D) says $K_1(r^*(\theta),\theta)/D_1(r^*(\theta))$ is nondecreasing on $[\underline\theta,\bar\theta]$, Condition (S) says $K_1(r^*(\theta),\theta)/S_1(r^*(\theta),Q^*(\theta))$ is, and $V^*=\mathbb E_\Theta[M(r^*(\Theta),Q^*(\Theta),\Theta)]$.
--
--   **The menus of linear contracts** (Propositions 3 and 5, pp. 11, 13). With $B(\theta)=\int_{\underline\theta}^{\theta}K_2(r^*(z),z)\,dz$:
--
--   1. $T_{CD}(d,\theta)=\alpha_{CD}(\theta)d+\beta_{CD}(\theta)$, $\alpha_{CD}=K_1(r^*,\theta)/D_1(r^*)$, $\beta_{CD}=-\alpha_{CD}D(r^*)+K(r^*,\theta)+hQ^*-B$;
--   2. $T_{CS}(s,\theta)=\alpha_{CS}(\theta)s+\beta_{CS}(\theta)$, $\alpha_{CS}=K_1(r^*,\theta)/S_1(r^*,Q^*)$, $\beta_{CS}=-\alpha_{CS}S(r^*,Q^*)+K(r^*,\theta)+hQ^*-B$;
--   3. $T_{DD}(d,Q,\theta)=\alpha_{CD}(\theta)d+\beta_{DD}(\theta)+\gamma_{DD}(\theta)Q-Q^2$, $\gamma_{DD}=2Q^*+h$, $\beta_{DD}=-\alpha_{CD}D(r^*)+K(r^*,\theta)+hQ^*-B-\gamma_{DD}Q^*+(Q^*)^2$;
--   4. $T_{DS}(s,Q,\theta)=\alpha_{CS}(\theta)s+\beta_{DS}(\theta)-\gamma_{DS}(\theta)Q$, $\gamma_{DS}=\alpha_{CS}(c+h)/p-h$, $\beta_{DS}=-\alpha_{CS}S(r^*,Q^*)+K(r^*,\theta)+hQ^*-B+\gamma_{DS}Q^*$.
--
--   These objects carry every statement of the mission: the envelope identity (Lemma 2), the common upper bound (Propositions 1 and 4), the optimality of the menus (Propositions 2, 3 and 5) and the equality of the four optimal profits (Proposition 6).
--
--   **Formalization Note** The model is the structure `Model`; $\underline\theta,\bar\theta$ are the fields `θlo`, `θhi`. Partial derivatives are derivatives of one-variable slices (`pd1`, `pd2`, so $K_{12}$ is `pd2 (pd1 K)`). The functions are $C^3$ on $\mathbb R$ and $\mathbb R^2$; the sign conditions of Assumption 1 are required on the domain of the model only: $E$ at outputs $r\ge0$ and types $\theta\in[\underline\theta,\bar\theta]$, $C$ at the efforts $E(r,\theta)$ these reach, $d$ at outputs $r\ge0$ and for $G$-almost every $\varepsilon$. $E$ is a primitive; the output function $R$ of p. 7 does not appear. $G$ is any probability measure absolutely continuous with respect to Lebesgue measure, and $\varepsilon\mapsto d(r,\varepsilon)$ is $G$-integrable for each $r\ge0$. "Increasing hazard rate" is $H$ antitone on $[\underline\theta,\bar\theta]$; $f>0$ there, so $H$ never divides by zero on the support. Feasibility is the obedience form of (IC): each mechanism names the actions it expects, since the agent's best response need not be unique. The paper prints the delegated profit without the inventory argument of $T$; it is restored. Conditions (D) and (S) are the monotone forms of the paper's nonnegative-derivative conditions. $\alpha_{CD}$ divides by $D_1>0$; $\alpha_{CS}$ divides by $S_1(r^*,Q^*)$, which (1) makes positive.
-- source:
--   Song–Lai–Xiao, Optimal Salesforce Compensation, MSOM (2024), doi:10.1287/msom.2022.0400, §2 pp. 6–8 and Assumption 1 p. 7; §3 pp. 8–9 (π(θ, θ̂), (IC), (IR), Π(T, Q), (PCD), (PCS)); Proposition 1 and (1) p. 9; Conditions (D), (S) p. 10; Proposition 3 p. 11; §4 p. 12 (delegation payoffs, Π(T), (PDD), (PDS)); Proposition 5 p. 13; Appendix A, proof of Proposition 1, p. 22 (M(r, Q, θ))

import Mathlib

open MeasureTheory

namespace SalesforceComp

/-- First partial derivative of a function of two real variables: `pd1 g x y = ∂g/∂x (x, y)`.
Song–Lai–Xiao, *Optimal Salesforce Compensation with General Demand and Operational
Considerations*, MSOM (2024), doi:10.1287/msom.2022.0400, §2, p. 7: "the numbered subscripts
applied to multivariate functions denote partial derivatives relative to the respective
variables". So `g₁ = pd1 g`, `g₁₂ = pd2 (pd1 g)`, `g₁₁₂ = pd2 (pd1 (pd1 g))`, and so on.

**Formalization Note.** `deriv` of a slice. `K`, `E` and `d` are C³ on `ℝ²`. `D` and `S` are
differentiable at every `r > 0` (`d` is concave in `r` there, and `G` has no atoms). At `r = 0` the
two-sided `deriv` also looks at `r < 0`; system (1) forces `S₁ > 0`, so a solution of (1) never
sees the junk value `0` of `deriv` there. -/
noncomputable def pd1 (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun x' => g x' y) x

/-- Second partial derivative of a function of two real variables: `pd2 g x y = ∂g/∂y (x, y)`.
MSOM (2024), §2, p. 7 (numbered subscripts are partial derivatives). -/
noncomputable def pd2 (g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => deriv (fun y' => g x y') y

/-- **The model of §2 with its standing assumptions**, Song–Lai–Xiao, MSOM (2024),
doi:10.1287/msom.2022.0400, §2, pp. 6–8, and Assumption 1, p. 7.

* `p`, `c`, `h`: unit price, the firm's unit production cost, the agent's unit hassle cost (p. 8).
* `θlo`, `θhi`: the endpoints `θ̲`, `θ̄` of the support of the market condition `Θ` (p. 6–7).
* `f`: the density of `Θ`; `F θ = ∫_{θ̲}^θ f`, `H = (1 − F)/f` (p. 7).
* `G`: the law of the demand shock `ε` (p. 7).
* `d r ε`: the demand at output level `r` and shock `ε` (p. 7).
* `C`: the cost of effort; `E r θ`: the effort a `θ`-type agent needs to reach output `r`, so the
  output cost is `K(r, θ) = C(E(r, θ))` (p. 7; the reformulated model "will be our focus
  throughout the paper").

**Formalization Note.**
1. `θlo`, `θhi` stand for `θ̲`, `θ̄`.
2. `C`, `d`, `E` are three times continuously differentiable on `ℝ`, `ℝ²`, `ℝ²`; partial
   derivatives are the `deriv` slices `pd1`, `pd2`. The sign conditions of Assumption 1 are required
   only on the domain of the model: `E` at outputs `r ≥ 0` (the agent's action set, p. 9) and types
   `θ ∈ [θ̲, θ̄]`, `C` at the efforts `E(r, θ)` these reach, `d` at outputs `r ≥ 0` and for
   `G`-almost every shock `ε`.
3. `p > 0` (a unit price) is implicit in the paper; `c`, `h` carry no sign assumption.
4. `G` is a probability measure on `ℝ` absolutely continuous w.r.t. Lebesgue measure ("with
   density `g`"); no smoothness of `g` is assumed.
5. `f` is measurable, integrable on `[θ̲, θ̄]` with total mass `1`, and positive on `[θ̲, θ̄]`, so
   `H` never divides by zero there.
6. "Increasing hazard rate, i.e., `H` decreases in `θ`" is `H` antitone (weakly decreasing) on
   `[θ̲, θ̄]`.
7. `ε ↦ d(r, ε)` is `G`-integrable for every `r ≥ 0`, so that `D(r) = E_ε[d(r, ε)]` (p. 8)
   exists. -/
structure Model where
  p : ℝ
  c : ℝ
  h : ℝ
  θlo : ℝ
  θhi : ℝ
  f : ℝ → ℝ
  G : Measure ℝ
  d : ℝ → ℝ → ℝ
  C : ℝ → ℝ
  E : ℝ → ℝ → ℝ
  p_pos : 0 < p
  θlo_lt_θhi : θlo < θhi
  f_measurable : Measurable f
  f_pos : ∀ θ ∈ Set.Icc θlo θhi, 0 < f θ
  f_intervalIntegrable : IntervalIntegrable f volume θlo θhi
  f_total : ∫ θ in θlo..θhi, f θ = 1
  /-- Increasing hazard rate: `H(θ) = (1 − F(θ))/f(θ)` decreases in `θ` (p. 7). -/
  hazard_antitone :
    AntitoneOn (fun θ => (1 - ∫ t in θlo..θ, f t) / f θ) (Set.Icc θlo θhi)
  G_prob : IsProbabilityMeasure G
  G_ac : G ≪ volume
  d_integrable : ∀ r, 0 ≤ r → Integrable (fun ε => d r ε) G
  /-- Assumption 1: all functions are three times continuously differentiable. -/
  d_contDiff : ContDiff ℝ 3 (fun x : ℝ × ℝ => d x.1 x.2)
  C_contDiff : ContDiff ℝ 3 C
  E_contDiff : ContDiff ℝ 3 (fun x : ℝ × ℝ => E x.1 x.2)
  /-- Assumption 1(C): `C₁ > 0`, `C₁₁ > 0`, `C₁₁₁ ≥ 0`, at the efforts `e = E(r, θ)` of the model. -/
  C1_pos : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 < deriv C (E r θ)
  C11_pos : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 < deriv (deriv C) (E r θ)
  C111_nonneg : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 ≤ deriv (deriv (deriv C)) (E r θ)
  /-- Assumption 1(D): `d₁ > 0`, `d₂ > 0`, `d₁₁ ≤ 0`, at outputs `r ≥ 0`, for `G`-a.e. `ε`. -/
  d1_pos : ∀ᵐ ε ∂G, ∀ r, 0 ≤ r → 0 < pd1 d r ε
  d2_pos : ∀ᵐ ε ∂G, ∀ r, 0 ≤ r → 0 < pd2 d r ε
  d11_nonpos : ∀ᵐ ε ∂G, ∀ r, 0 ≤ r → pd1 (pd1 d) r ε ≤ 0
  /-- Assumption 1(E): `E₁ > 0`, `E₂ < 0`, `E₁₁ ≥ 0`, `E₁₂ ≤ 0`, `E₂₂ ≥ 0`, `E₁₁₂ ≤ 0`,
  `E₁₂₂ ≥ 0`, at outputs `r ≥ 0` and types `θ ∈ [θ̲, θ̄]`. -/
  E1_pos : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 < pd1 E r θ
  E2_neg : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → pd2 E r θ < 0
  E11_nonneg : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 ≤ pd1 (pd1 E) r θ
  E12_nonpos : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → pd2 (pd1 E) r θ ≤ 0
  E22_nonneg : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 ≤ pd2 (pd2 E) r θ
  E112_nonpos : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → pd2 (pd1 (pd1 E)) r θ ≤ 0
  E122_nonneg : ∀ r θ, 0 ≤ r → θ ∈ Set.Icc θlo θhi → 0 ≤ pd2 (pd2 (pd1 E)) r θ

/-- A direct mechanism for the control setting with demand-based payment (CD), MSOM (2024), §3,
pp. 8–9: a payment `T(d, θ̂)` (realized demand, reported type), the inventory `Q(θ̂)` the firm
stocks, and the output `r(θ)` the mechanism expects of a truthful `θ`-type.

**Formalization Note.** The mechanism names the output it expects (obedience form): the paper's
"let `r(θ, θ̂)` be the maximizer" need not be unique for a general `T`. -/
structure MechCD where
  T : ℝ → ℝ → ℝ
  Q : ℝ → ℝ
  r : ℝ → ℝ

/-- A direct mechanism for the control setting with sales-based payment (CS), MSOM (2024), §3,
p. 9 ("replacing demand with sales"): a payment `T(s, θ̂)` on realized sales, the inventory
`Q(θ̂)` and the expected output `r(θ)`. -/
structure MechCS where
  T : ℝ → ℝ → ℝ
  Q : ℝ → ℝ
  r : ℝ → ℝ

/-- A direct mechanism for the delegation setting with demand-based payment (DD), MSOM (2024),
§4, pp. 11–12: a payment `T(d, Q, θ̂)` (realized demand, requested inventory, reported type), the
output `r(θ)` and the inventory request `Q(θ)` the mechanism expects of a truthful `θ`-type. -/
structure MechDD where
  T : ℝ → ℝ → ℝ → ℝ
  r : ℝ → ℝ
  Q : ℝ → ℝ

/-- A direct mechanism for the delegation setting with sales-based payment (DS), MSOM (2024),
§4, p. 12: a payment `T(s, Q, θ̂)` on realized sales, the expected output `r(θ)` and the expected
inventory request `Q(θ)`. -/
structure MechDS where
  T : ℝ → ℝ → ℝ → ℝ
  r : ℝ → ℝ
  Q : ℝ → ℝ

namespace Model

variable (M : Model)

/-- The type support `[θ̲, θ̄]`, MSOM (2024), §2, p. 7. -/
def I : Set ℝ := Set.Icc M.θlo M.θhi

/-- The distribution function `F(θ) = ∫_{θ̲}^θ f`, MSOM (2024), §2, p. 6. -/
noncomputable def F (θ : ℝ) : ℝ := ∫ t in M.θlo..θ, M.f t

/-- The inverse hazard rate `H(θ) = (1 − F(θ))/f(θ)`, MSOM (2024), §2, p. 7.

**Formalization Note.** `f > 0` on `[θ̲, θ̄]` (a field of `Model`), so on the support this is a
genuine quotient; it is only ever evaluated at `θ ∈ [θ̲, θ̄]`. -/
noncomputable def H (θ : ℝ) : ℝ := (1 - M.F θ) / M.f θ

/-- Expectation over the type, `E_Θ[φ(Θ)] = ∫_{θ̲}^{θ̄} φ(θ) f(θ) dθ`, MSOM (2024), §3, p. 9. -/
noncomputable def expect (φ : ℝ → ℝ) : ℝ := ∫ θ in M.θlo..M.θhi, φ θ * M.f θ

/-- The output cost `K(r, θ) = C(E(r, θ))`, MSOM (2024), §2, p. 7. -/
noncomputable def K (r θ : ℝ) : ℝ := M.C (M.E r θ)

/-- Expected demand `D(r) = E_ε[d(r, ε)]`, MSOM (2024), §2, p. 8. -/
noncomputable def D (r : ℝ) : ℝ := ∫ ε, M.d r ε ∂M.G

/-- Expected realized sales `S(r, Q) = E_ε[min{d(r, ε), Q}]`, MSOM (2024), §2, p. 8. -/
noncomputable def S (r Q : ℝ) : ℝ := ∫ ε, min (M.d r ε) Q ∂M.G

/-- The virtual surplus `M(r, Q, θ) = pS(r, Q) − (c + h)Q − K(r, θ) + K₂(r, θ)H(θ)`, MSOM (2024),
Appendix A, proof of Proposition 1, p. 22. -/
noncomputable def virtSurplus (r Q θ : ℝ) : ℝ :=
  M.p * M.S r Q - (M.c + M.h) * Q - M.K r θ + pd2 M.K r θ * M.H θ

/-! ### Control setting, demand-based payment (CD), §3, pp. 8–9 -/

/-- The payoff of a `θ`-type agent who reports `θ̂` and chooses output `x` under a CD mechanism:
`E_ε[T(d(x, ε), θ̂)] − hQ(θ̂) − K(x, θ)`, MSOM (2024), §3, p. 9 (the maximand of `π(θ, θ̂)`). -/
noncomputable def payoffCD (m : MechCD) (θ θ' x : ℝ) : ℝ :=
  ∫ ε, m.T (M.d x ε) θ' ∂M.G - M.h * m.Q θ' - M.K x θ

/-- The truthful, obedient payoff `π(θ)` under a CD mechanism, MSOM (2024), §3, p. 9. -/
noncomputable def rentCD (m : MechCD) (θ : ℝ) : ℝ := M.payoffCD m θ θ (m.r θ)

/-- The firm's expected profit under a CD mechanism,
`Π = E_{Θ,ε}[pS(r(Θ), Q(Θ)) − cQ(Θ) − T(d(r(Θ), ε), Θ)]`, MSOM (2024), §3, p. 9. -/
noncomputable def profitCD (m : MechCD) : ℝ :=
  M.expect fun θ => M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ - ∫ ε, m.T (M.d (m.r θ) ε) θ ∂M.G

/-- Feasibility of a CD mechanism for problem (PCD), MSOM (2024), §3, p. 9: (IC) and (IR).

**Formalization Note.** (IC) is in obedience form: for all `θ, θ̂ ∈ [θ̲, θ̄]` and every output
`x ≥ 0`, reporting `θ̂` and producing `x` pays no more than reporting `θ` and producing the
expected `r(θ)`. The paper's expectations are assumed to exist: the payment is `G`-integrable at
every report and output, and the firm's profit integrand is integrable over `[θ̲, θ̄]`. -/
structure FeasibleCD (m : MechCD) : Prop where
  nonneg : ∀ θ ∈ M.I, 0 ≤ m.Q θ ∧ 0 ≤ m.r θ
  integrable : ∀ θ' ∈ M.I, ∀ x, 0 ≤ x → Integrable (fun ε => m.T (M.d x ε) θ') M.G
  ic : ∀ θ ∈ M.I, ∀ θ' ∈ M.I, ∀ x, 0 ≤ x → M.payoffCD m θ θ' x ≤ M.rentCD m θ
  ir : ∀ θ ∈ M.I, 0 ≤ M.rentCD m θ
  profit_integrable : IntervalIntegrable
    (fun θ => (M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ - ∫ ε, m.T (M.d (m.r θ) ε) θ ∂M.G) *
      M.f θ) volume M.θlo M.θhi

/-- The set of profits the firm can attain in (PCD), over **all** feasible direct mechanisms. -/
def profitsCD : Set ℝ := {v | ∃ m : MechCD, M.FeasibleCD m ∧ M.profitCD m = v}

/-! ### Control setting, sales-based payment (CS), §3, p. 9 -/

/-- The payoff of a `θ`-type agent who reports `θ̂` and chooses output `x` under a CS mechanism:
`E_ε[T(min{d(x, ε), Q(θ̂)}, θ̂)] − hQ(θ̂) − K(x, θ)`, MSOM (2024), §3, p. 9. -/
noncomputable def payoffCS (m : MechCS) (θ θ' x : ℝ) : ℝ :=
  ∫ ε, m.T (min (M.d x ε) (m.Q θ')) θ' ∂M.G - M.h * m.Q θ' - M.K x θ

/-- The truthful, obedient payoff `π(θ)` under a CS mechanism. -/
noncomputable def rentCS (m : MechCS) (θ : ℝ) : ℝ := M.payoffCS m θ θ (m.r θ)

/-- The firm's expected profit under a CS mechanism,
`E_{Θ,ε}[pS(r(Θ), Q(Θ)) − cQ(Θ) − T(min{d(r(Θ), ε), Q(Θ)}, Θ)]`, MSOM (2024), §3, p. 9. -/
noncomputable def profitCS (m : MechCS) : ℝ :=
  M.expect fun θ =>
    M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ - ∫ ε, m.T (min (M.d (m.r θ) ε) (m.Q θ)) θ ∂M.G

/-- Feasibility of a CS mechanism for problem (PCS), MSOM (2024), §3, p. 9; same conventions as
`FeasibleCD`. -/
structure FeasibleCS (m : MechCS) : Prop where
  nonneg : ∀ θ ∈ M.I, 0 ≤ m.Q θ ∧ 0 ≤ m.r θ
  integrable : ∀ θ' ∈ M.I, ∀ x, 0 ≤ x →
    Integrable (fun ε => m.T (min (M.d x ε) (m.Q θ')) θ') M.G
  ic : ∀ θ ∈ M.I, ∀ θ' ∈ M.I, ∀ x, 0 ≤ x → M.payoffCS m θ θ' x ≤ M.rentCS m θ
  ir : ∀ θ ∈ M.I, 0 ≤ M.rentCS m θ
  profit_integrable : IntervalIntegrable
    (fun θ => (M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ -
      ∫ ε, m.T (min (M.d (m.r θ) ε) (m.Q θ)) θ ∂M.G) * M.f θ) volume M.θlo M.θhi

/-- The set of profits the firm can attain in (PCS), over all feasible direct mechanisms. -/
def profitsCS : Set ℝ := {v | ∃ m : MechCS, M.FeasibleCS m ∧ M.profitCS m = v}

/-! ### Delegation setting, demand-based payment (DD), §4, pp. 11–12 -/

/-- The payoff of a `θ`-type agent who reports `θ̂`, chooses output `x` and requests inventory `q`
under a DD mechanism: `E_ε[T(d(x, ε), q, θ̂)] − hq − K(x, θ)`, MSOM (2024), §4, p. 12. -/
noncomputable def payoffDD (m : MechDD) (θ θ' x q : ℝ) : ℝ :=
  ∫ ε, m.T (M.d x ε) q θ' ∂M.G - M.h * q - M.K x θ

/-- The truthful, obedient payoff `π(θ)` under a DD mechanism. -/
noncomputable def rentDD (m : MechDD) (θ : ℝ) : ℝ := M.payoffDD m θ θ (m.r θ) (m.Q θ)

/-- The firm's expected profit under a DD mechanism,
`E_{Θ,ε}[pS(r(Θ), Q(Θ)) − cQ(Θ) − T(d(r(Θ), ε), Q(Θ), Θ)]`, MSOM (2024), §4, p. 12.

**Formalization Note.** The printed formula omits the inventory argument of `T`; it is restored. -/
noncomputable def profitDD (m : MechDD) : ℝ :=
  M.expect fun θ =>
    M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ - ∫ ε, m.T (M.d (m.r θ) ε) (m.Q θ) θ ∂M.G

/-- Feasibility of a DD mechanism for problem (PDD), MSOM (2024), §4, p. 12: obedient (IC) over
every report `θ̂ ∈ [θ̲, θ̄]`, output `x ≥ 0` and inventory request `q ≥ 0`; (IR); integrability of
the payment and of the firm's profit integrand. -/
structure FeasibleDD (m : MechDD) : Prop where
  nonneg : ∀ θ ∈ M.I, 0 ≤ m.Q θ ∧ 0 ≤ m.r θ
  integrable : ∀ θ' ∈ M.I, ∀ x q, 0 ≤ x → 0 ≤ q →
    Integrable (fun ε => m.T (M.d x ε) q θ') M.G
  ic : ∀ θ ∈ M.I, ∀ θ' ∈ M.I, ∀ x q, 0 ≤ x → 0 ≤ q → M.payoffDD m θ θ' x q ≤ M.rentDD m θ
  ir : ∀ θ ∈ M.I, 0 ≤ M.rentDD m θ
  profit_integrable : IntervalIntegrable
    (fun θ => (M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ -
      ∫ ε, m.T (M.d (m.r θ) ε) (m.Q θ) θ ∂M.G) * M.f θ) volume M.θlo M.θhi

/-- The set of profits the firm can attain in (PDD), over all feasible direct mechanisms. -/
def profitsDD : Set ℝ := {v | ∃ m : MechDD, M.FeasibleDD m ∧ M.profitDD m = v}

/-! ### Delegation setting, sales-based payment (DS), §4, p. 12 -/

/-- The payoff of a `θ`-type agent who reports `θ̂`, chooses output `x` and requests inventory `q`
under a DS mechanism: `E_ε[T(min{d(x, ε), q}, q, θ̂)] − hq − K(x, θ)`, MSOM (2024), §4, p. 12. -/
noncomputable def payoffDS (m : MechDS) (θ θ' x q : ℝ) : ℝ :=
  ∫ ε, m.T (min (M.d x ε) q) q θ' ∂M.G - M.h * q - M.K x θ

/-- The truthful, obedient payoff `π(θ)` under a DS mechanism. -/
noncomputable def rentDS (m : MechDS) (θ : ℝ) : ℝ := M.payoffDS m θ θ (m.r θ) (m.Q θ)

/-- The firm's expected profit under a DS mechanism,
`E_{Θ,ε}[pS(r(Θ), Q(Θ)) − cQ(Θ) − T(min{d(r(Θ), ε), Q(Θ)}, Q(Θ), Θ)]`, MSOM (2024), §4, p. 12. -/
noncomputable def profitDS (m : MechDS) : ℝ :=
  M.expect fun θ =>
    M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ -
      ∫ ε, m.T (min (M.d (m.r θ) ε) (m.Q θ)) (m.Q θ) θ ∂M.G

/-- Feasibility of a DS mechanism for problem (PDS), MSOM (2024), §4, p. 12; same conventions as
`FeasibleDD`. -/
structure FeasibleDS (m : MechDS) : Prop where
  nonneg : ∀ θ ∈ M.I, 0 ≤ m.Q θ ∧ 0 ≤ m.r θ
  integrable : ∀ θ' ∈ M.I, ∀ x q, 0 ≤ x → 0 ≤ q →
    Integrable (fun ε => m.T (min (M.d x ε) q) q θ') M.G
  ic : ∀ θ ∈ M.I, ∀ θ' ∈ M.I, ∀ x q, 0 ≤ x → 0 ≤ q → M.payoffDS m θ θ' x q ≤ M.rentDS m θ
  ir : ∀ θ ∈ M.I, 0 ≤ M.rentDS m θ
  profit_integrable : IntervalIntegrable
    (fun θ => (M.p * M.S (m.r θ) (m.Q θ) - M.c * m.Q θ -
      ∫ ε, m.T (min (M.d (m.r θ) ε) (m.Q θ)) (m.Q θ) θ ∂M.G) * M.f θ) volume M.θlo M.θhi

/-- The set of profits the firm can attain in (PDS), over all feasible direct mechanisms. -/
def profitsDS : Set ℝ := {v | ∃ m : MechDS, M.FeasibleDS m ∧ M.profitDS m = v}

/-! ### The second-best outcome and Conditions (D), (S) -/

/-- System (1) at type `θ`, MSOM (2024), Proposition 1, p. 9:
`pS₁(r, Q) − K₁(r, θ) + K₁₂(r, θ)H(θ) = 0` and `pS₂(r, Q) − c − h = 0`. -/
def FOC (r Q θ : ℝ) : Prop :=
  M.p * pd1 M.S r Q - pd1 M.K r θ + pd2 (pd1 M.K) r θ * M.H θ = 0 ∧
    M.p * pd2 M.S r Q - M.c - M.h = 0

/-- `(r*, Q*)` is a second-best outcome: for every `θ ∈ [θ̲, θ̄]`, `r*(θ) ≥ 0`, `Q*(θ) ≥ 0` and
`(r*(θ), Q*(θ))` solves system (1), MSOM (2024), Proposition 1, p. 9.

**Formalization Note.** The paper presupposes a solution of (1); here it is a hypothesis.
Uniqueness is not assumed: (1) can have a whole interval of solutions `Q` at a given `θ`. -/
def SolvesFOC (rs Qs : ℝ → ℝ) : Prop :=
  ∀ θ ∈ M.I, 0 ≤ rs θ ∧ 0 ≤ Qs θ ∧ M.FOC (rs θ) (Qs θ) θ

/-- Condition (D), MSOM (2024), Proposition 2, p. 10: `θ ↦ K₁(r*(θ), θ)/D₁(r*(θ))` is
nondecreasing on `[θ̲, θ̄]`.

**Formalization Note.** The paper writes `d/dθ [K₁(r*(θ), θ)/D₁(r*(θ))] ≥ 0`; the monotone form
is implied by it and needs no differentiability of `r*`. -/
def CondD (rs : ℝ → ℝ) : Prop :=
  MonotoneOn (fun θ => pd1 M.K (rs θ) θ / deriv M.D (rs θ)) M.I

/-- Condition (S), MSOM (2024), Proposition 2, p. 10: `θ ↦ K₁(r*(θ), θ)/S₁(r*(θ), Q*(θ))` is
nondecreasing on `[θ̲, θ̄]` (monotone form of `d/dθ[…] ≥ 0`). -/
def CondS (rs Qs : ℝ → ℝ) : Prop :=
  MonotoneOn (fun θ => pd1 M.K (rs θ) θ / pd1 M.S (rs θ) (Qs θ)) M.I

/-- The common upper bound `V* = E_Θ[M(r*(Θ), Q*(Θ), Θ)]`, MSOM (2024), Proposition 1, p. 9, and
proof, p. 22. -/
noncomputable def Vstar (rs Qs : ℝ → ℝ) : ℝ :=
  M.expect fun θ => M.virtSurplus (rs θ) (Qs θ) θ

/-! ### The menus of linear contracts, Propositions 3 and 5 -/

/-- The information-rent integral `B(θ) = ∫_{θ̲}^θ K₂(r*(z), z) dz`, MSOM (2024), Propositions 3
and 5, pp. 11, 13. -/
noncomputable def B (rs : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ z in M.θlo..θ, pd2 M.K (rs z) z

/-- `α_CD(θ) = K₁(r*(θ), θ)/D₁(r*(θ))`, MSOM (2024), Proposition 3, p. 11. -/
noncomputable def alphaCD (rs : ℝ → ℝ) (θ : ℝ) : ℝ := pd1 M.K (rs θ) θ / deriv M.D (rs θ)

/-- `β_CD(θ) = −α_CD(θ)D(r*(θ)) + K(r*(θ), θ) + hQ*(θ) − ∫_{θ̲}^θ K₂(r*(z), z) dz`,
MSOM (2024), Proposition 3, p. 11. -/
noncomputable def betaCD (rs Qs : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -M.alphaCD rs θ * M.D (rs θ) + M.K (rs θ) θ + M.h * Qs θ - M.B rs θ

/-- The CD menu of linear contracts `T_CD(d, θ) = α_CD(θ)d + β_CD(θ)` with inventory `Q*` and
expected output `r*`, MSOM (2024), Proposition 3, p. 11. -/
noncomputable def mechCD (rs Qs : ℝ → ℝ) : MechCD where
  T := fun dem θ => M.alphaCD rs θ * dem + M.betaCD rs Qs θ
  Q := Qs
  r := rs

/-- `α_CS(θ) = K₁(r*(θ), θ)/S₁(r*(θ), Q*(θ))`, MSOM (2024), Proposition 3, p. 11. -/
noncomputable def alphaCS (rs Qs : ℝ → ℝ) (θ : ℝ) : ℝ :=
  pd1 M.K (rs θ) θ / pd1 M.S (rs θ) (Qs θ)

/-- `β_CS(θ) = −α_CS(θ)S(r*(θ), Q*(θ)) + K(r*(θ), θ) + hQ*(θ) − ∫_{θ̲}^θ K₂(r*(z), z) dz`,
MSOM (2024), Proposition 3, p. 11. -/
noncomputable def betaCS (rs Qs : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -M.alphaCS rs Qs θ * M.S (rs θ) (Qs θ) + M.K (rs θ) θ + M.h * Qs θ - M.B rs θ

/-- The CS menu `T_CS(s, θ) = α_CS(θ)s + β_CS(θ)` with inventory `Q*` and expected output `r*`,
MSOM (2024), Proposition 3, p. 11. -/
noncomputable def mechCS (rs Qs : ℝ → ℝ) : MechCS where
  T := fun s θ => M.alphaCS rs Qs θ * s + M.betaCS rs Qs θ
  Q := Qs
  r := rs

/-- `γ_DD(θ) = 2Q*(θ) + h`, MSOM (2024), Proposition 5, p. 13. -/
noncomputable def gammaDD (Qs : ℝ → ℝ) (θ : ℝ) : ℝ := 2 * Qs θ + M.h

/-- `β_DD(θ) = −α_DD(θ)D(r*(θ)) + K(r*(θ), θ) + hQ*(θ) − ∫_{θ̲}^θ K₂(r*(z), z) dz
− γ_DD(θ)Q*(θ) + Q*(θ)²`, with `α_DD = α_CD`, MSOM (2024), Proposition 5, p. 13. -/
noncomputable def betaDD (rs Qs : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -M.alphaCD rs θ * M.D (rs θ) + M.K (rs θ) θ + M.h * Qs θ - M.B rs θ -
    M.gammaDD Qs θ * Qs θ + Qs θ ^ 2

/-- The DD menu `T_DD(d, Q, θ) = α_DD(θ)d + β_DD(θ) + γ_DD(θ)Q − Q²` with expected output `r*`
and expected inventory request `Q*`, MSOM (2024), Proposition 5, p. 13. -/
noncomputable def mechDD (rs Qs : ℝ → ℝ) : MechDD where
  T := fun dem q θ => M.alphaCD rs θ * dem + M.betaDD rs Qs θ + M.gammaDD Qs θ * q - q ^ 2
  r := rs
  Q := Qs

/-- `γ_DS(θ) = α_DS(θ)(c + h)/p − h`, with `α_DS = α_CS`, MSOM (2024), Proposition 5, p. 13. -/
noncomputable def gammaDS (rs Qs : ℝ → ℝ) (θ : ℝ) : ℝ :=
  M.alphaCS rs Qs θ * (M.c + M.h) / M.p - M.h

/-- `β_DS(θ) = −α_DS(θ)S(r*(θ), Q*(θ)) + K(r*(θ), θ) + hQ*(θ) − ∫_{θ̲}^θ K₂(r*(z), z) dz
+ γ_DS(θ)Q*(θ)`, MSOM (2024), Proposition 5, p. 13. -/
noncomputable def betaDS (rs Qs : ℝ → ℝ) (θ : ℝ) : ℝ :=
  -M.alphaCS rs Qs θ * M.S (rs θ) (Qs θ) + M.K (rs θ) θ + M.h * Qs θ - M.B rs θ +
    M.gammaDS rs Qs θ * Qs θ

/-- The DS menu `T_DS(s, Q, θ) = α_DS(θ)s + β_DS(θ) − γ_DS(θ)Q` with expected output `r*` and
expected inventory request `Q*`, MSOM (2024), Proposition 5, p. 13. -/
noncomputable def mechDS (rs Qs : ℝ → ℝ) : MechDS where
  T := fun s q θ => M.alphaCS rs Qs θ * s + M.betaDS rs Qs θ - M.gammaDS rs Qs θ * q
  r := rs
  Q := Qs

end Model

end SalesforceComp


