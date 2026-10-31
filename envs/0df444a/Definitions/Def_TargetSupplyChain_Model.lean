-- Prove2me | Definitions.Def_TargetSupplyChain_Model
-- name    : TargetSupplyChain_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:20:53.649735+00:00
-- url     : https://prove2.me/theorems/c8aa27f3-b1aa-4e1d-b6e0-f3550c61c62c
-- title:
--   Supplier–retailer newsvendor game with uniform demand: profits, risk-neutral and target-oriented best responses, Stackelberg outcomes
-- statement:
--   A supplier with marginal cost $c$ sells to a retailer at wholesale price $w$; the retailer sells at the fixed retail price $p$ and faces demand $D\sim U[a,a+b]$. Unsatisfied demand is lost and leftovers have no salvage value.
--
--   **Parameters.** $(p,c,a,b)$ with the standing assumptions $0<c<p$, $0\le a$, $0<b$; the critical fractile is $\xi^c=(p-c)/p$. The retailer's target coefficient $\alpha^r$ ranges over $\{\alpha^r:\ 0<\alpha^r,\ a\le\alpha^r<a+b\}$.
--
--   **Profits.** For an order $y\ge0$ the retailer's random profit is $V(y;D)=p\min\{D,y\}-wy$. The supplier earns $\pi^s=(w-c)y$, the retailer's expected profit is $\pi^r=p\,\mathbb E[\min(D,y)]-wy$, the total is $\Pi=\pi^s+\pi^r$, and the centralized profit (8) is
--   $$\Pi^c_{nn}(y)=p\,\mathbb E[\min(y,D)]-cy.$$
--
--   **Retailer's problems.** A risk-neutral retailer solves (6), $\max_{y\ge0}\mathbb E[V(y;D)]$. A target-oriented retailer with target $\tau^r=\alpha^r(p-w)$ solves (7), $\max_{y\ge0}\rho_{\tau^r}(V(y;D))$, with $\rho$ the CVaR-satisficing measure. A best response is any maximizer.
--
--   **Supplier and outcomes.** The supplier (Stackelberg leader) maximizes $(w-c)y$ over $w$ given the retailer's best response (4). Let $v$ be the least upper bound of $(w-c)y$ over $w\in[c,p)$ and best responses $y$ to $w$. An **outcome** $(w^*,y^*)$ is a limit of pairs $(w_n,y_n)$ with $w_n\in[c,p)$, $y_n$ a best response to $w_n$, and $(w_n-c)y_n\to v$. "NN" outcomes use the risk-neutral retailer, "NT" outcomes the target-oriented one.
--
--   These primitives carry every statement of the mission; none of the paper's closed-form solutions is used as a definition.
--
--   **Formalization Note** The paper writes the supplier's solution as $w^*=p-\epsilon$, $y^*=\alpha^r-\epsilon$ with $\epsilon$ "an infinitely small positive number" (p.12). At $w=p$ every $y\in[0,a]$ is a best response, and the supplier's supremum over $w<p$ is not always attained, so outcomes are limits over $w\in[c,p)$; when the supremum is attained, the maximizer is an outcome. Requiring $v$ to be a least upper bound means an empty or unbounded profit set has no outcome. Profits at an outcome are evaluated at the limit pair. The standing assumptions $0<c<p$, $0\le a$, $0<b$ are a separate predicate `Params.Standing`; $\alpha^r=a+b$ is excluded because there every order has CSM $-1$ and the NT outcome is undefined.
-- source:
--   Chen–Tang, Supply Chain Performance with Target-Oriented Firms, SSRN 3533746 (version of July 6, 2021), §3 (pp.9–11): V(y; D) p.10, supplier's problem (4) p.10, retailer's problems (6)–(7) p.11; §4.1 centralized problem (8) and ξᶜ, p.11; uniform demand and τʳ = αʳ(p − w), p.12; ε convention pp.12–13; Π* = πˢ* + πʳ*, p.18

import Mathlib
import Definitions.Def_TargetSupplyChain_CVaRSatisficing

open MeasureTheory Filter Topology Classical

namespace TargetSupplyChain

/-- The parameters of the supply chain of Chen–Tang, *Supply Chain Performance with
Target-Oriented Firms*, SSRN 3533746 (version of July 6, 2021), §3, p.10 and §4.1, p.11:
the retail price `p`, the supplier's marginal cost `c`, and the bounds `a`, `b` of the uniform
demand `D ~ U[a, a + b]`. The retailer's target coefficient `α = αʳ` is a separate argument. -/
structure Params where
  p : ℝ
  c : ℝ
  a : ℝ
  b : ℝ

/-- The standing assumptions `0 < c < p`, `0 ≤ a`, `0 < b` (pp.10–11).

**Formalization Note** The paper assumes `c ≤ w ≤ p` (p.10), "a and b are non-negative"
(p.11) and a continuous demand with a density, which forces `b > 0`; `c < p` makes the
critical fractile `ξᶜ` positive, and `c > 0` is used by the paper's proofs (they divide by `c`). -/
def Params.Standing (P : Params) : Prop :=
  0 < P.c ∧ P.c < P.p ∧ 0 ≤ P.a ∧ 0 < P.b

/-- The critical fractile (system profit margin) `ξᶜ = (p − c)/p`, §4.1, p.11. -/
noncomputable def Params.xi (P : Params) : ℝ := (P.p - P.c) / P.p

/-- The domain of the retailer's target coefficient: `0 < αʳ` (p.9, "α is a positive number")
and `a ≤ αʳ < a + b`.

**Formalization Note** The paper writes `αʳ ∈ [a, a + b]` (Proposition 2, p.13). The endpoint
`αʳ = a + b` is excluded: there the target `(a + b)(p − w)` exceeds the retailer's profit almost
surely for every order, the CVaR-satisficing measure is `−1` for every order and the
Stackelberg outcome is undefined. -/
def Params.InDom (P : Params) (α : ℝ) : Prop :=
  0 < α ∧ P.a ≤ α ∧ α < P.a + P.b

/-- The law of the demand `D ~ U[a, a + b]` (p.11, p.12): `(1/b) · Lebesgue` restricted to
`[a, a + b]`, a probability measure on `ℝ` when `b > 0`. -/
noncomputable def demandLaw (P : Params) : Measure ℝ :=
  ENNReal.ofReal (1 / P.b) • (volume.restrict (Set.Icc P.a (P.a + P.b)))

/-- The expected sales `E[min(y, D)]` (pp.11–12). -/
noncomputable def expSales (P : Params) (y : ℝ) : ℝ :=
  ∫ d, min d y ∂(demandLaw P)

/-- The law of the retailer's random profit `V(y; D) = p · min{D, y} − w y` (p.10), the
image of the demand law under `d ↦ p · min{d, y} − w y`. -/
noncomputable def profitLaw (P : Params) (w y : ℝ) : Measure ℝ :=
  (demandLaw P).map (fun d => P.p * min d y - w * y)

/-- The risk-neutral retailer's expected profit `E[V(y; D)] = E[p · min{D, y} − w y]` (6), p.11. -/
noncomputable def expProfit (P : Params) (w y : ℝ) : ℝ :=
  ∫ d, (P.p * min d y - w * y) ∂(demandLaw P)

/-- `y` solves the risk-neutral retailer's problem (6), p.11, at wholesale price `w`:
`y ≥ 0` maximizes `E[V(y; D)]` over `y ≥ 0`. -/
def IsRNBestResponse (P : Params) (w y : ℝ) : Prop :=
  0 ≤ y ∧ ∀ y' : ℝ, 0 ≤ y' → expProfit P w y' ≤ expProfit P w y

/-- `y` solves the target-oriented retailer's problem (7), p.11, at wholesale price `w`, with
the linear target `τʳ = αʳ(p − w)` (p.9, p.12): `y ≥ 0` maximizes the CSM
`ρ_{τʳ}(V(y; D))` over `y ≥ 0`. -/
def IsTOBestResponse (P : Params) (α w y : ℝ) : Prop :=
  0 ≤ y ∧ ∀ y' : ℝ, 0 ≤ y' →
    csm (profitLaw P w y') (α * (P.p - w)) ≤ csm (profitLaw P w y) (α * (P.p - w))

/-- A Stackelberg outcome `(w*, y*)` of the supplier's problem (4), p.10, against the retailer's
best-response relation `BR`. Let `v` be the least upper bound of the supplier's profits
`(w − c) y` over wholesale prices `w ∈ [c, p)` and best responses `y` to `w`. Then `(w*, y*)` is
an outcome when it is the limit of a sequence `(wₙ, yₙ)` with `wₙ ∈ [c, p)`, `yₙ` a best
response to `wₙ`, and supplier profits `(wₙ − c) yₙ → v`.

**Formalization Note** The paper writes the solution as `w* = p − ε`, `y* = αʳ − ε` with
"ε an infinitely small positive number" (p.12), and notes that the supplier "will avert from
setting the wholesale price to be equal to the retail price" (p.13): at `w = p` every
`y ∈ [0, a]` is a best response. The supplier's set is therefore `[c, p)`, and an outcome is
a limit point of supplier-optimal sequences; when the supremum is attained the constant
sequence at the maximizer is one. `v` is required to be the least upper bound (`IsLUB`), so an
empty or unbounded profit set has no outcome rather than a junk one. Profits at an outcome are
evaluated at the limit pair. -/
def IsOutcome (P : Params) (BR : ℝ → ℝ → Prop) (w y : ℝ) : Prop :=
  ∃ v : ℝ,
    IsLUB {π : ℝ | ∃ w' y' : ℝ, w' ∈ Set.Ico P.c P.p ∧ BR w' y' ∧ π = (w' - P.c) * y'} v ∧
    ∃ ws ys : ℕ → ℝ, (∀ n, ws n ∈ Set.Ico P.c P.p ∧ BR (ws n) (ys n)) ∧
      Tendsto (fun n => (ws n - P.c) * ys n) atTop (𝓝 v) ∧
      Tendsto ws atTop (𝓝 w) ∧ Tendsto ys atTop (𝓝 y)

/-- An outcome of the "NN" game (risk-neutral supplier and retailer), §4.1, p.12. -/
def nnOutcome (P : Params) (w y : ℝ) : Prop :=
  IsOutcome P (IsRNBestResponse P) w y

/-- An outcome of the "NT" game (risk-neutral supplier, target-oriented retailer with target
coefficient `α`), §4.2, pp.12–13. -/
def ntOutcome (P : Params) (α w y : ℝ) : Prop :=
  IsOutcome P (IsTOBestResponse P α) w y

/-- The supplier's profit `πˢ = (w − c) y` (4), p.10. -/
def supplierProfit (P : Params) (w y : ℝ) : ℝ := (w - P.c) * y

/-- The retailer's expected profit `πʳ = p E[min(D, y)] − w y` (6), p.11. -/
noncomputable def retailerProfit (P : Params) (w y : ℝ) : ℝ := P.p * expSales P y - w * y

/-- The total supply-chain profit `Π* = πˢ + πʳ` at a decision pair `(w, y)` (p.18). -/
noncomputable def totalProfit (P : Params) (w y : ℝ) : ℝ :=
  supplierProfit P w y + retailerProfit P w y

/-- The centralized supply-chain profit `Πᶜ_nn(y) = p E[min(y, D)] − c y` (8), p.11. -/
noncomputable def centralProfit (P : Params) (y : ℝ) : ℝ := P.p * expSales P y - P.c * y

end TargetSupplyChain


