-- Prove2me | Definitions.Def_BlockchainMarketPower_Model
-- name    : BlockchainMarketPower_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:25:53.335371+00:00
-- url     : https://prove2.me/theorems/a09fd923-fb1b-47ce-86d6-db20d837a4b0
-- title:
--   The supply chain game of §3: parameters, Bayes demand, supplier stage, random profit, $\mathcal M_r$, $\Omega$, SPNE; and $f$, $\Lambda$
-- statement:
--   There are $N\ge 1$ homogeneous suppliers, one manufacturer with type $q\in\{A,B\}$ and a unit mass of consumers. The parameters are the signal accuracy $\alpha\in(\tfrac12,1)$, the information share $\delta\in(0,1]$, the risk aversion $\gamma\in(0,1)$ and the outside option $v_0\ge 1$. The regimes are NB (no blockchain) and B (blockchain), with signal accuracy $a(\mathrm{NB})=\alpha$ and $a(\mathrm B)=\alpha+\delta(1-\alpha)$.
--
--   **Consumers.** A consumer of type $t\in\{A,B\}$ values the good at $V(q,t)=v_0+I(q=t)-I(q\ne t)$. The types $q,t$ are uniform and independent, and a signal $\tilde q$ equals $q$ with probability $a$. The conditional expected utility $E_a[V\mid t,\tilde q]$ is the Bayes quotient on this finite joint law, and demand at type $q$ and price $P$ is
--
--   $$
--   s_r(q,P)=\sum_{t}\sum_{\tilde q}\tfrac12\,L_a(\tilde q\mid q)\,I\bigl(E_a[V\mid t,\tilde q]-P\ge v_0\bigr).
--   $$
--
--   **Suppliers.** Effort $e$ has defect probability $\rho(e)=1-\sqrt e$. In an order of size $n$, with own effort $e_j$ and effort $e$ of the others, the no-recall probabilities are
--
--   $$
--   \pi_{\mathrm{NB}}=(1-\rho(e_j))(1-\rho(e))^{n-1},\qquad \pi_{\mathrm B}=1-\rho(e_j),
--   $$
--
--   and the profit per unit is $u_r(n,\Psi;e_j,e)=\pi_r\Psi-e_j/2$. A **symmetric effort** is $e\in[0,1]$ maximizing $e'\mapsto u_r(n,\Psi;e',e)$ on $[0,1]$. The supplier **accepts** when $u_r(n,\Psi;e,e)>0$.
--
--   **Manufacturer.** An order is $(P,\Psi,\Xi)$ with $P,\Psi\ge 0$ and $\Xi$ a set of suppliers. With $\Gamma=\Xi$ if the effort is accepted and $\Gamma=\emptyset$ otherwise, and batches independent and good with probability $\sqrt e$, the random profit is
--
--   $$
--   \Pi_r=\sum_{j\in\Gamma}(P-\Psi)\,\frac{s_r(q,P)}{|\Xi|}\,\xi_{r,j},
--   $$
--
--   where $\xi_{\mathrm B,j}$ says that batch $j$ is good and $\xi_{\mathrm{NB},j}$ says that every batch of $\Gamma$ is good. The utility is $\mathcal M_r=\mathbb E[\Pi_r]-\frac\gamma2\mathrm{Var}[\Pi_r]$, and $\Omega=\mathcal M_{\mathrm B}-\mathcal M_{\mathrm{NB}}$ at the two orders of a strategy.
--
--   **Equilibrium.** A strategy $\sigma$ gives a symmetric effort after each history $(r,P,\Psi,\Xi)$, an order in each regime and an adoption decision. It is an SPNE at cost $\chi$ when (1) the effort is a symmetric effort after every history with $P,\Psi\ge0$, $\Xi\ne\emptyset$; (2) the order of each regime is valid and maximizes $\mathcal M_r$ over all valid orders, for both types; and (3) blockchain is adopted if and only if $\Omega\ge\chi$, for both types.
--
--   **Used by the milestones only.** The printed effort selection, the prices $P^\star_r=2a(r)-1$, and
--
--   $$
--   f(P,\Psi;\gamma')=\tfrac12(P-\Psi)\Psi-\tfrac{\gamma'}{8}(P-\Psi)^2\Psi(1-\Psi),\qquad
--   \Lambda(\Psi,P,N)=\tfrac12(P-2\Psi)-\tfrac{\gamma}{8N}(P-\Psi)\bigl(4\Psi^2-(2P+3)\Psi+P\bigr).
--   $$
--
--   None of these enters the definition of the equilibrium.
--
--   This is the model on which every statement of the mission is made.
--
--   **Formalization Note** Types and signals are `Bool`, suppliers are `Fin N`, and $v_\Delta=1$ is the paper's normalization. The cost $\chi$ is an argument of the equilibrium, not a parameter. Consumers condition on $(t,\tilde q)$, demand is the purchase probability of a generic consumer, the supplier objective is per unit, the supplier stage is the symmetric fixed point of the proof (which assumes that all of $\Xi$ produce), batches are independent, and the manufacturer's strategy does not depend on its type. In $\pi_{\mathrm{NB}}$ the convention $(1-\rho(e))^0=1$ applies at $n=1$, including at $e=0$. With $\Xi=\emptyset$ the sum is empty and the profit is $0$.
-- source:
--   Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, §3, (1)–(12), pp.11–17; §3.4, p.17; the fixed-point problems, pp.32, 36; (15), p.35; Λ, p.19

import Mathlib
import Definitions.Def_BlockchainMarketPower_BernoulliProduct

namespace BlockchainMarketPower

/-- The parameters of the model, for `N` suppliers.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, §3, pp.11–17: `N ∈ ℕ` suppliers (p.11), signal accuracy
`α` (p.14), the share `δ ∈ (0, 1]` of unknown information that blockchain reveals (p.14), risk
aversion `γ ∈ (0, 1)` (p.16), outside option `v₀ ≥ 1` (p.14).

**Formalization Note.** `v_Δ = 1` is the paper's normalization (p.14). `N ≥ 1` is what `N ∈ ℕ` means
on p.11: with no suppliers nothing can be ordered. The paper's `α ∈ [α̲, ᾱ]` with
`1/2 < α̲ < ᾱ < 1` describes the same set of `α` as `1/2 < α < 1`. The adoption cost `χ` is not a
parameter here, because Proposition 4.1 fixes `Ω⋆` before `χ`. Assumption 1 is not a hypothesis. -/
structure Params (N : ℕ) where
  α : ℝ
  δ : ℝ
  γ : ℝ
  v₀ : ℝ
  N_pos : 0 < N
  half_lt_α : 1 / 2 < α
  α_lt_one : α < 1
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  γ_pos : 0 < γ
  γ_lt_one : γ < 1
  one_le_v₀ : 1 ≤ v₀

/-- The two regimes: blockchain not adopted (`NB`) and adopted (`B`). -/
inductive Regime
  | NB
  | B
  deriving DecidableEq

/-- The accuracy of a consumer's signal in each regime: `α`, or `α + δ(1 - α)`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (5), (6), p.14. -/
def Params.accuracy {N : ℕ} (p : Params N) : Regime → ℝ
  | .NB => p.α
  | .B => p.α + p.δ * (1 - p.α)

/-- The realized utility `V(q, t) = v₀ + I(q = t) - I(q ≠ t)` of a consumer of type `t` from the good
of a manufacturer of type `q`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (4), p.13, with
`v_Δ = 1` (p.14).

**Formalization Note.** The types `{A, B}` of consumers and manufacturer and the signals are
encoded by `Bool`. -/
def consumerValue (v₀ : ℝ) (q t : Bool) : ℝ :=
  v₀ + (if q = t then 1 else 0) - (if q ≠ t then 1 else 0)

/-- The signal law `L_a(q̃ | q)`: `a` if `q̃ = q`, and `1 - a` otherwise.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (5), (6), p.14. -/
def signalLaw (a : ℝ) (sig q : Bool) : ℝ :=
  if sig = q then a else 1 - a

/-- The joint weight of `(q, t, q̃)`: `q` and `t` are uniform and independent, and the signal `q̃`
depends only on `q`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.13–14, 16. -/
noncomputable def jointWeight (a : ℝ) (q _t sig : Bool) : ℝ :=
  1 / 2 * (1 / 2) * signalLaw a sig q

/-- The conditional expected utility `E_a[V | t, q̃]`, by Bayes on the finite joint law `jointWeight`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (7), p.15, as conditioned in the proof, p.31.

**Formalization Note.** (7) prints `E[V_k - P | q̃_k, P]`; without `t_k` this would be `v₀ - P` for
every consumer. The proof (p.31) conditions on `(t_k, q̃_k)`, and so does this definition. `P` carries
no information about `q`, as stated on p.15. -/
noncomputable def condExpectedValue (v₀ a : ℝ) (t sig : Bool) : ℝ :=
  (∑ q : Bool, jointWeight a q t sig * consumerValue v₀ q t) / ∑ q : Bool, jointWeight a q t sig

/-- Demand at signal accuracy `a`: the probability that a generic consumer buys, given the manufacturer's
type `q`, i.e. `s(q, P) = Σ_t Σ_q̃ (1/2) L_a(q̃ | q) I(E_a[V | t, q̃] - P ≥ v₀)`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (8), p.15.

**Formalization Note.** (8) integrates over `k ∈ [0, 1]`, and p.15 appeals to independence across a
continuum, for which the integral is not literally definable; the purchase probability of a generic
consumer is the value the paper assigns to it. -/
noncomputable def demandAt (v₀ a : ℝ) (q : Bool) (P : ℝ) : ℝ :=
  open Classical in
  ∑ t : Bool, ∑ sig : Bool,
    1 / 2 * signalLaw a sig q * (if v₀ ≤ condExpectedValue v₀ a t sig - P then 1 else 0)

/-- Consumer demand `s_r(q, P)` in regime `r`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (8), p.15. -/
noncomputable def Params.demand {N : ℕ} (p : Params N) (r : Regime) (q : Bool) (P : ℝ) : ℝ :=
  demandAt p.v₀ (p.accuracy r) q P

/-- The defect probability `ρ(e) = 1 - √e`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.13. -/
noncomputable def rho (e : ℝ) : ℝ :=
  1 - Real.sqrt e

/-- The probability `π_r` that a supplier's batch is not recalled, with own effort `eⱼ`, when the
order has size `n` and every other supplier in the order exerts effort `e`:
`π_NB = (1 - ρ(eⱼ)) (1 - ρ(e))^(n-1)`, `π_B = 1 - ρ(eⱼ)`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (2), p.12, (3), p.13, and the fixed-point problem, p.32.

**Formalization Note.** §3.1 lets (2) depend on the accepting set `Γ`; the proof on p.32 uses the
exponent `|Ξ| - 1`, i.e. assumes all of `Ξ` produce, and this definition follows the proof. `n` is at
least `1` wherever this is used, so `n - 1` is not truncated, and `(1 - ρ(e))^0 = 1` at `n = 1`,
including at `e = 0`. -/
noncomputable def noRecallProb : Regime → ℕ → ℝ → ℝ → ℝ
  | .NB, n, eⱼ, e => (1 - rho eⱼ) * (1 - rho e) ^ (n - 1)
  | .B, _, eⱼ, _ => 1 - rho eⱼ

/-- A supplier's profit per unit, `u_r(n, Ψ; eⱼ, e) = π_r · Ψ - eⱼ/2`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (1), p.12, divided by `Q`.

**Formalization Note.** When demand is zero, `Q = 0` and (1) vanishes identically, so every effort would
be a maximizer. The proof drops `Q` (p.32); this per-unit objective does the same, for every
non-empty order. Nothing changes when `Q > 0`. -/
noncomputable def supplierProfit (r : Regime) (n : ℕ) (Ψ eⱼ e : ℝ) : ℝ :=
  noRecallProb r n eⱼ e * Ψ - eⱼ / 2

/-- `e` is a symmetric supplier effort: `e ∈ [0, 1]` and `e` maximizes `e' ↦ u_r(n, Ψ; e', e)` on
`[0, 1]`, the fixed-point problem. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.32, p.36. -/
def IsSymEffort (r : Regime) (n : ℕ) (Ψ e : ℝ) : Prop :=
  e ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e' ∈ Set.Icc (0 : ℝ) 1, supplierProfit r n Ψ e' e ≤ supplierProfit r n Ψ e e

/-- The accept decision: a supplier accepts when its profit at the symmetric effort is strictly
above the zero pay-off. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.12, and `θ` on pp.32, 37. -/
def Accepts (r : Regime) (n : ℕ) (Ψ e : ℝ) : Prop :=
  0 < supplierProfit r n Ψ e e

/-- An order `(P, Ψ, Ξ)`: consumer price, one supplier price, and the set of suppliers receiving an
order, each for quantity `s/|Ξ|`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.16; one price for all
suppliers, §3.4, p.17. -/
structure Order (N : ℕ) where
  P : ℝ
  Ψ : ℝ
  Ξ : Finset (Fin N)

/-- An order is valid when `P ≥ 0` and `Ψ ≥ 0`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.16. -/
def Order.Valid {N : ℕ} (x : Order N) : Prop :=
  0 ≤ x.P ∧ 0 ≤ x.Ψ

/-- The no-recall indicator `ξ_r,j` of supplier `j` when `Γ` produces, at the outcome `b` (`b i = true`:
batch `i` is good): without blockchain every batch of `Γ` must be good, with blockchain only `j`'s.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.11, 17. -/
noncomputable def noRecall {N : ℕ} (r : Regime) (Γ : Finset (Fin N)) (j : Fin N)
    (b : Fin N → Bool) : ℝ :=
  match r with
  | .NB => if ∀ i ∈ Γ, b i = true then 1 else 0
  | .B => if b j = true then 1 else 0

/-- The manufacturer's random profit `Π_r = Σ_{j ∈ Γ} (P - Ψ) (s_r(q, P)/|Ξ|) ξ_r,j`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (11), p.17.

**Formalization Note.** With `Ξ = ∅` the accepting set `Γ ⊆ Ξ` is empty, so the sum is empty and the
profit is `0`, which is the case p.17 sets aside. -/
noncomputable def Params.profit {N : ℕ} (p : Params N) (r : Regime) (q : Bool) (x : Order N)
    (Γ : Finset (Fin N)) (b : Fin N → Bool) : ℝ :=
  ∑ j ∈ Γ, (x.P - x.Ψ) * (p.demand r q x.P / (x.Ξ.card : ℝ)) * noRecall r Γ j b

/-- A symmetric strategy profile, for fixed parameters: the suppliers' symmetric effort after each
history `(r, P, Ψ, Ξ)`, the manufacturer's order in each regime, and the adoption decision.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, §3.4, p.17.

**Formalization Note.** The manufacturer's choices do not depend on its type: p.15 says that the
manufacturer selects the same price irrespective of its type, and the solution models no
type-dependent price and no off-path beliefs. -/
structure Strategy (N : ℕ) where
  effort : Regime → ℝ → ℝ → Finset (Fin N) → ℝ
  order : Regime → Order N
  adopt : Prop

/-- The effort of `σ` after the order `x` in regime `r`. -/
def Strategy.effortAt {N : ℕ} (σ : Strategy N) (r : Regime) (x : Order N) : ℝ :=
  σ.effort r x.P x.Ψ x.Ξ

/-- The set `Γ ⊆ Ξ` of suppliers who receive and accept the order `x`: all of `Ξ` when the effort of
`σ` is accepted, nobody otherwise (`Γ⋆` on pp.33, 37).
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.16. -/
noncomputable def Strategy.accepted {N : ℕ} (σ : Strategy N) (r : Regime) (x : Order N) :
    Finset (Fin N) :=
  open Classical in
  if Accepts r x.Ξ.card x.Ψ (σ.effortAt r x) then x.Ξ else ∅

/-- The manufacturer's utility `𝓜_r = E[Π_r] - (γ/2) Var[Π_r]` of type `q` at the order `x` in
regime `r`, given the effort and acceptance that `σ` induces. The batches are independent, each good
with probability `1 - ρ(e) = √e`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (10), p.16, (11), p.17.

**Formalization Note.** The sample space has `N` coordinates and `Γ` uses only `|Γ|` of them; the
others marginalize out. -/
noncomputable def Params.util {N : ℕ} (p : Params N) (σ : Strategy N) (r : Regime) (q : Bool)
    (x : Order N) : ℝ :=
  meanVariance p.γ (1 - rho (σ.effortAt r x)) (p.profit r q x (σ.accepted r x))

/-- The manufacturer's incremental welfare `Ω = 𝓜_B - 𝓜_NB` of type `q` at the two orders of `σ`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (12), p.17. -/
noncomputable def Params.Omega {N : ℕ} (p : Params N) (σ : Strategy N) (q : Bool) : ℝ :=
  p.util σ .B q (σ.order .B) - p.util σ .NB q (σ.order .NB)

/-- Suppliers play a symmetric effort after every history with `P, Ψ ≥ 0` and `Ξ ≠ ∅`, on and off the
equilibrium path. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.32, 36. -/
def Strategy.SuppliersRespond {N : ℕ} (σ : Strategy N) : Prop :=
  ∀ (r : Regime) (P Ψ : ℝ) (Ξ : Finset (Fin N)), 0 ≤ P → 0 ≤ Ψ → Ξ.Nonempty →
    IsSymEffort r Ξ.card Ψ (σ.effort r P Ψ Ξ)

/-- `x` is a valid order and maximizes the utility of both manufacturer types over all valid orders in
regime `r`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.33–34, 37. -/
def Params.IsOptimalOrder {N : ℕ} (p : Params N) (σ : Strategy N) (r : Regime) (x : Order N) : Prop :=
  x.Valid ∧ ∀ (q : Bool) (y : Order N), y.Valid → p.util σ r q y ≤ p.util σ r q x

/-- `σ` is a symmetric subgame perfect Nash equilibrium at adoption cost `χ`: suppliers respond
after every history, the manufacturer's order is optimal in both regimes, and blockchain is
adopted if and only if `Ω ≥ χ`, for each type. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, §3.4,
p.17, and (12), p.17.

**Formalization Note.** The supplier stage is solved as in the proof (pp.32, 36): the symmetric fixed
point assuming all of `Ξ` produce, then acceptance at that effort. This is the paper's concept, and
not a Nash equilibrium of the simultaneous accept/effort game for `|Ξ| ≥ 2`. Nothing here refers to
the printed effort formula, the printed `Ψ⋆` or `f`: those are conclusions. -/
def Params.IsSPNE {N : ℕ} (p : Params N) (χ : ℝ) (σ : Strategy N) : Prop :=
  σ.SuppliersRespond ∧
    (∀ r : Regime, p.IsOptimalOrder σ r (σ.order r)) ∧
    ∀ q : Bool, σ.adopt ↔ χ ≤ p.Omega σ q

/-- The printed effort of Proposition 3.1 part 2: `min{Ψ², 1}` with blockchain, and without it
`min{Ψ², 1}` if `|Ξ| = 1`, `0` if `|Ξ| > 1`. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.18.
This is a selection, used only by milestones, and it is not part of `IsSPNE`. -/
noncomputable def printedEffort (r : Regime) (n : ℕ) (Ψ : ℝ) : ℝ :=
  match r with
  | .NB => if n = 1 then min (Ψ ^ 2) 1 else 0
  | .B => min (Ψ ^ 2) 1

/-- The function `f(P, Ψ; γ') = (1/2)(P - Ψ)Ψ - (γ'/8)(P - Ψ)²Ψ(1 - Ψ)`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, (15), p.35. Used by the milestones only. -/
noncomputable def f (P Ψ γ' : ℝ) : ℝ :=
  1 / 2 * (P - Ψ) * Ψ - γ' / 8 * (P - Ψ) ^ 2 * Ψ * (1 - Ψ)

/-- The function `Λ(Ψ, P, N) = (1/2)(P - 2Ψ) - (γ/(8N))(P - Ψ)(4Ψ² - (2P + 3)Ψ + P)`.
Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.19. Used by the milestones only. -/
noncomputable def Lam (γ Ψ P : ℝ) (N : ℕ) : ℝ :=
  1 / 2 * (P - 2 * Ψ) - γ / (8 * (N : ℝ)) * (P - Ψ) * (4 * Ψ ^ 2 - (2 * P + 3) * Ψ + P)

/-- The equilibrium consumer price `P⋆_r = 2 a(r) - 1`, i.e. `2α - 1` without blockchain and
`2(α + δ(1 - α)) - 1` with it. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, p.18. Used by the
milestones only. -/
def Params.priceStar {N : ℕ} (p : Params N) (r : Regime) : ℝ :=
  2 * p.accuracy r - 1

/-- `Ψ` is a root of `Λ(·, P, n)` in the open interval `(0, P)`, where the proof locates the
supplier price. Iyengar–Saleh–Sethuraman–Wang, SSRN 3950580, pp.35–36, 39. Used by the milestones
only. -/
def IsInteriorRoot (γ : ℝ) (n : ℕ) (P Ψ : ℝ) : Prop :=
  0 < Ψ ∧ Ψ < P ∧ Lam γ Ψ P n = 0

end BlockchainMarketPower


