-- Prove2me | Definitions.Def_XinGoldbergTBS_Asymptotic_SingleSource
-- name    : XinGoldbergTBS_Asymptotic_SingleSource
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T01:20:38.043624+00:00
-- url     : https://prove2.me/theorems/e5a99068-114c-42e3-b79f-c72cd0e7f403
-- title:
--   Single-source discounted backlog problem: $V^n_\alpha(r,x)$, $V^\infty_\alpha(r,x)$, $S^\infty_\alpha(r)$, $\bar S_\alpha(r)$
-- statement:
--   The single-sourcing backlog inventory problem of Section 3.1.3 (p. 443): holding cost $h$, backorder cost $b$, zero ordering cost, discount factor $\alpha \in (0,1)$, i.i.d. demand distributed as $D - r$ (possibly negative), lead time $L_0$, and initial inventory position $x \in \mathbb R$.
--
--   A policy $\pi \in \bar\Pi$ orders, in period $i$, a nonnegative quantity that is a measurable function of the demands realized in periods $1, \dots, i-1$; the inventory position is raised from $x_i$ to $y_i \ge x_i$ and then moves to $x_{i+1} = y_i - (D_i - r)$, with $x_1 = x$. The cost incurred in period $i + L_0$ is
--   $$C^\pi_i(r,x) = G\Big(y_i - \sum_{k=i}^{i+L_0}(D_k - r)\Big).$$
--   Then
--   $$V^n_\alpha(r,x) = \inf_{\pi\in\bar\Pi}\mathbb E\Big[\sum_{i=1}^n \alpha^{i-1}C^\pi_i(r,x)\Big] \quad (5), \qquad V^\infty_\alpha(r,x) = \inf_{\pi\in\bar\Pi}\mathbb E\Big[\sum_{i=1}^\infty \alpha^{i-1}C^\pi_i(r,x)\Big] \quad (6),$$
--   $V^0_\alpha = 0$, and $V^n_\alpha(r,-\infty) = \inf_{x} V^n_\alpha(r,x)$. $S^\infty_\alpha(r)$ is the supremum of the set of minimizers in $x$ of $V^\infty_\alpha(r,x)$, and (p. 444)
--   $$\bar S_\alpha(r) = 4(L_0+1)\frac{\max(b,h)}{\min(b,h)}(|r| + \mathbb E[D])(1-\alpha)^{-2}.$$
--   A policy is *stationary Markov* with rule $f$ if it orders $f(x_i)$ in every period, and the *base-stock* rule with level $S$ orders $\max(0, S - x_i)$.
--
--   These value functions carry the lower bound on $\mathrm{OPT}(L)$ (Lemma 2 onwards).
--
--   **Formalization Note** The paper defines $\bar\Pi$ as "all feasible nonanticipative policies ... as it is typically defined; see Zipkin 2000". Here it is read as deterministic, time-dependent, nonnegative orders that are Borel functions of the past demands. Randomized policies are not included; they do not lower a discounted-cost infimum. $V^n_\alpha$ and $V^\infty_\alpha$ are $[0,\infty]$-valued and are defined by (5) and (6), not by a Bellman recursion (the recursion is Lemma 3). $S^\infty_\alpha(r)$ is a real supremum; Lemma 4 asserts that the minimizer set is nonempty and bounded.
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 443, Section 3.1.3, Eqs. (5)-(6); p. 444, definition of S̄_α(r) and Lemma 4

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model

/-!
# The single-source backlog problem behind Lemmas 2–4 (p. 443, eqs. (5)–(6))

Single-sourcing backlog inventory problem: holding cost `h`, backorder cost `b`, zero
ordering cost, lead time `L₀`, i.i.d. demand distributed as `D - r` (possibly negative),
initial inventory position `x`. On the i.i.d. path (coordinate `n` is `D_{n+1}`), in period
`n + 1` (0-based index `n`) the controller sees the realized demands of periods `1, …, n` and
orders a quantity `u_n ≥ 0`, raising the inventory position from `x_n` to `y_n = x_n + u_n`;
then `x_{n+1} = y_n - (D_{n+1} - r)`, and the cost charged in period `n + 1 + L₀` is
`C_{n+1}(r, x) = G(y_n - ∑_{k=n+1}^{n+1+L₀}(D_k - r))`.

The class `Π̄` of "feasible nonanticipative policies" (the paper defers to Zipkin 2000) is
read as: deterministic, time-dependent order quantities that are nonnegative and Borel
measurable functions of the past demands. `V^n_α` and `V^∞_α` are `ℝ≥0∞`-valued infima of
expected discounted costs; they are defined by (5)–(6), not by a Bellman recursion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- A policy in `Π̄`: in (0-based) period `n`, a nonnegative order that is a measurable
function of the demands of the `n` earlier periods. -/
structure SSPolicy where
  order : (n : ℕ) → (Fin n → ℝ) → ℝ≥0
  measurable_order : ∀ n, Measurable (order n)

/-- Order placed by `π` in (0-based) period `n` on the demand path `d`. -/
def ssOrder (π : SSPolicy) (d : Path) (n : ℕ) : ℝ := π.order n (fun i => d i)

/-- Inventory position before ordering in (0-based) period `n`: `x_0 = x`,
`x_{n+1} = x_n + u_n - (D_{n+1} - r)`. -/
def ssPosition (π : SSPolicy) (r x : ℝ) (d : Path) : ℕ → ℝ
  | 0 => x
  | n + 1 => ssPosition π r x d n + ssOrder π d n - (d n - r)

/-- Order-up-to level `y_n = x_n + u_n`. -/
def ssOrderUpTo (π : SSPolicy) (r x : ℝ) (d : Path) (n : ℕ) : ℝ :=
  ssPosition π r x d n + ssOrder π d n

/-- `C^π_{n+1}(r, x) = G(y_n - ∑_{k=n+1}^{n+1+L₀}(D_k - r))`. -/
def ssCost (κ : Costs) (L₀ : ℕ) (π : SSPolicy) (r x : ℝ) (d : Path) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (G κ (ssOrderUpTo π r x d n - ∑ k ∈ Finset.range (L₀ + 1), (d (n + k) - r)))

/-- Infinite-horizon discounted cost `∑_{i ≥ 1} α^{i-1} C^π_i(r, x)` on a path. -/
def ssDiscCost (κ : Costs) (L₀ : ℕ) (α : ℝ) (π : SSPolicy) (r x : ℝ) (d : Path) : ℝ≥0∞ :=
  ∑' i : ℕ, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i

/-- `V^n_α(r, x) = inf_{π ∈ Π̄} 𝔼[∑_{i=1}^n α^{i-1} C^π_i(r, x)]` (5); `V^0_α = 0`. -/
def Vn (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (n : ℕ) (r x : ℝ) : ℝ≥0∞ :=
  ⨅ π : SSPolicy,
    ∫⁻ d, ∑ i ∈ Finset.range n, ENNReal.ofReal (α ^ i) * ssCost κ L₀ π r x d i ∂pathLaw μ

/-- `V^∞_α(r, x) = inf_{π ∈ Π̄} 𝔼[∑_{i=1}^∞ α^{i-1} C^π_i(r, x)]` (6). -/
def Vinf (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (r x : ℝ) : ℝ≥0∞ :=
  ⨅ π : SSPolicy, ∫⁻ d, ssDiscCost κ L₀ α π r x d ∂pathLaw μ

/-- `V^n_α(r, -∞) = inf_{x ∈ ℝ} V^n_α(r, x)`. -/
def VnNegInf (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α : ℝ) (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ⨅ x : ℝ, Vn μ κ L₀ α n r x

/-- The set of minimizers in `x` of `V^∞_α(r, x)`. -/
def VinfMinimizers (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) : Set ℝ :=
  {x : ℝ | Vinf μ κ L₀ α r x = ⨅ x' : ℝ, Vinf μ κ L₀ α r x'}

/-- `S^∞_α(r)`: the supremum of the set of minimizers in `x` of `V^∞_α(r, x)` (a real `sSup`;
Lemma 4 asserts that this set is nonempty and bounded). -/
def Sinf (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) : ℝ :=
  sSup (VinfMinimizers μ κ L₀ α r)

/-- `S̄_α(r) = 4(L₀ + 1)(max(b, h)/min(b, h))(|r| + 𝔼[D])(1 - α)^{-2}` (p. 444). -/
def Sbar (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) (α r : ℝ) : ℝ :=
  4 * ((L₀ : ℝ) + 1) * (max κ.b κ.h / min κ.b κ.h) * (|r| + μ.mean) * ((1 - α) ^ 2)⁻¹

/-- `π` acts, from initial position `x`, as the stationary Markov policy `f`: in every period
it orders `f(x_n)`, a measurable function of the current inventory position only. -/
def IsStationaryMarkov (π : SSPolicy) (f : ℝ → ℝ≥0) (r x : ℝ) : Prop :=
  Measurable f ∧ ∀ (n : ℕ) (d : Path), ssOrder π d n = f (ssPosition π r x d n)

/-- The base-stock rule with order-up-to level `S`: order `max(0, S - x)`. -/
def baseStockRule (S : ℝ) : ℝ → ℝ≥0 := fun y => (S - y).toNNReal

end XinGoldbergTBS.Asymptotic


