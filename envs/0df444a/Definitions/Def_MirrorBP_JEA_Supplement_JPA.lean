-- Prove2me | Definitions.Def_MirrorBP_JEA_Supplement_JPA
-- name    : MirrorBP_JEA_Supplement_JPA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:47:20.037039+00:00
-- url     : https://prove2.me/theorems/8af5638f-0f58-431e-9af4-9275b61b337f
-- title:
--   §5.2, pp. 23–25, and Appendix E.1 — joint pricing-assignment model, Condition 2, Algorithm 2, SPP (49)–(51), W*_T, W*, W^π
-- statement:
--   Objects of the joint pricing-assignment (JPA) setting of §5.2. The nodes $V$ ($m=|V|$), types $\mathcal T$, neighbourhoods $P(\tau),D(\tau)$ and states $q\in\Omega_K$ are those of the published base model; the type distribution $\varphi$ is stationary and buffers are infinite.
--
--   1. **Control and payoff.** In each period, after seeing the type $\tau$, the platform posts a price $p\in[p^{\min}_\tau,p^{\max}_\tau]$ and chooses a decision: one pair $(j,k)\in P(\tau)\times D(\tau)$ with $q_j>0$, or none (25). The customer buys with probability $1-F_\tau(p)$, $F_\tau$ the willingness-to-pay distribution function. On a purchase with decision $(j,k)$ a unit moves from $j$ to $k$ and the platform earns $p-c_{j\tau k}$; otherwise nothing moves and nothing is earned. Controls may randomize and use the whole history (states, types, decisions, prices, purchase outcomes).
--   2. **Inverse demand and revenue.** $p_\tau(\mu)=F_\tau^{-1}(1-\mu)$ is the price realizing a fraction $\mu\in[0,1]$ of demand, and $r_\tau(\mu)=\mu\,p_\tau(\mu)$.
--   3. **Condition 2.** For every $\tau$: (1) $F_\tau(p^{\min}_\tau)=0$, $F_\tau(p^{\max}_\tau)=1$; (2) the willingness to pay is non-atomic with support $[p^{\min}_\tau,p^{\max}_\tau]$ and positive density on it; (3) $r_\tau$ is concave and twice continuously differentiable on $[0,1]$.
--   4. **Scaling.** $\max_\tau p^{\max}_\tau+\max_{j,k,\tau}|c_{j\tau k}|=1$.
--   5. **Algorithm 2.** With $\bar q$ from (9) and $f$ from (8): $(j^*,k^*)\in\arg\max_{P(\tau)\times D(\tau)}\{-c_{j\tau k}+f(\bar q_j)-f(\bar q_k)\}$; if $q_{j^*}>0$, take $\mu_\tau\in\arg\max_{\mu\in[0,1]}\{r_\tau(\mu)+\mu(-c_{j^*\tau k^*}+f(\bar q_{j^*})-f(\bar q_{k^*}))\}$, post $p_\tau(\mu_\tau)$ and serve a buying customer with $(j^*,k^*)$; otherwise drop the customer.
--   6. **Static planning problem (49)–(51).**
--   $$W^{\rm SPP}=\max_x\ \sum_\tau\varphi_\tau\Big[r_\tau\Big(\sum_{j\in P(\tau),k\in D(\tau)}x_{j\tau k}\Big)-\sum_{j\in P(\tau),k\in D(\tau)}c_{j\tau k}x_{j\tau k}\Big]$$
--   subject to flow balance $\sum_\tau\varphi_\tau\sum_{j,k}x_{j\tau k}(e_j-e_k)=0$ and $\sum_{j,k}x_{j\tau k}\le1$, $x\ge0$.
--   7. **Payoff benchmarks (4)–(5).** $W^*_T=\sup_\pi\max_{q\in\Omega_K}\frac1T\sum_{t<T}\mathbb E[v^\pi[t]\mid q[0]=q]$, $W^*=\limsup_TW^*_T$; $W^\pi_T=\min_{q\in\Omega_K}\frac1T\sum_{t<T}\mathbb E[v^\pi[t]\mid q[0]=q]$, $W^\pi=\liminf_TW^\pi_T$.
--
--   These are the objects of Proposition 5 and Theorem 3.
--
--   **Formalization Note** Randomized controls draw from finitely supported distributions over (decision, price); this class contains every deterministic history-dependent control. Expected payoffs are a finite recursion. $p_\tau(\mu)$ is written as $\sup\{p\in[p^{\min}_\tau,p^{\max}_\tau]:F_\tau(p)\le1-\mu\}$, which is the inverse under Condition 2. Condition 2(2) is encoded as: $F_\tau$ monotone and continuous, $0$ on $(-\infty,p^{\min}_\tau]$, $1$ on $[p^{\max}_\tau,\infty)$, with a positive derivative at every interior point. Algorithm 2 prints $p_\tau\leftarrow F_\tau^{-1}(\mu_\tau)$ and a queue update without the purchase indicator; following p. 24 ($p_\tau(\mu)$ realizes the fraction $\mu$) and item (2) of p. 23, the posted price is $p_\tau(\mu_\tau)$ and the unit moves only on a purchase. A dropped customer is posted $p^{\max}_\tau$, which affects nothing.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, pp. 23–25, §5.2, (25), (26), Condition 2, Algorithm 2; p. 10, (4)–(5); Appendix E.1, appendix p. 16 (PDF 49), (49)–(51)

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP
import Definitions.Def_MirrorBP_JEA_SPP

namespace MirrorBP.JEA.Supplement

open Finset

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- A history of the joint pricing-assignment (JPA) setting (§5.2, pp. 23–25): the list of past
(state, type, decision, posted price, purchase indicator) records, in chronological order. -/
abbrev JHistory (V Ty : Type) := List ((V → ℕ) × Ty × Decision V × ℝ × Bool)

/-- A (possibly randomized, history- and time-dependent) control of the JPA setting (§5.2, p. 23): in
period `t`, after history `h`, at state `q`, for an arriving customer of type `τ`, the platform draws a pair
(decision, price) from the finitely supported probability distribution `act t h q τ`. Admissibility
(prices in `[p_τ^min, p_τ^max]`, constraint (25) and no underflow) is the separate predicate
`AdmissibleJ`. -/
structure JPolicy (V Ty : Type) where
  act : ℕ → JHistory V Ty → (V → ℕ) → Ty → (Decision V × ℝ) →₀ ℝ
  nonneg : ∀ t h q τ x, 0 ≤ act t h q τ x
  sum_one : ∀ t h q τ, (act t h q τ).sum (fun _ a => a) = 1

/-- Admissibility of a JPA control (p. 23): every (decision, price) pair it can draw has a price in
`[p_τ^min, p_τ^max]` and a decision satisfying (25) (one pair `(j, k) ∈ P(τ) × D(τ)` or none) and the
no-underflow constraint (`x_{jτk} = 0` if `q_j = 0`). -/
def AdmissibleJ (P D : Ty → Finset V) (pmin pmax : Ty → ℝ) (π : JPolicy V Ty) : Prop :=
  ∀ t h q τ x, x ∈ (π.act t h q τ).support →
    Feasible P D τ q x.1 ∧ x.2 ∈ Set.Icc (pmin τ) (pmax τ)

/-- The JPA payoff of a purchased service (p. 23, item (2)): `p − c_{jτk}` when the customer is served
with `(j, k)` at price `p`, and `0` when the customer is dropped. -/
def payJ (c : V → Ty → V → ℝ) (τ : Ty) : Decision V → ℝ → ℝ
  | none, _ => 0
  | some (j, k), p => p - c j τ k

/-- Expected total JPA payoff over the next `n` periods, starting in period `t` with history `h` at state
`q`, under stationary type distribution `phi` (p. 23): the customer's type is `τ` with probability `phi τ`;
the control draws (decision `d`, price `p`) with probability `π.act t h q τ (d, p)`; the customer buys with
probability `1 − F_τ(p)` (item (1), p. 23), in which case the platform collects `payJ c τ d p` and the
supply unit moves (`step q d`); otherwise (probability `F_τ(p)`) nothing is collected and the state is
unchanged (item (2)). -/
noncomputable def expPayoffFromJ (c : V → Ty → V → ℝ) (F : Ty → ℝ → ℝ) (phi : Ty → ℝ)
    (π : JPolicy V Ty) : ℕ → ℕ → JHistory V Ty → (V → ℕ) → ℝ
  | 0, _, _, _ => 0
  | n + 1, t, h, q =>
      ∑ τ, phi τ * (π.act t h q τ).sum (fun x a => a *
        ((1 - F τ x.2) * (payJ c τ x.1 x.2 +
            expPayoffFromJ c F phi π n (t + 1) (h ++ [(q, τ, x.1, x.2, true)]) (step q x.1)) +
          F τ x.2 * expPayoffFromJ c F phi π n (t + 1) (h ++ [(q, τ, x.1, x.2, false)]) q))

/-- `∑_{t=0}^{T−1} E[v^π[t] | q[0] = q]` in the JPA setting (periods numbered from `0`). -/
noncomputable def expPayoffJ (c : V → Ty → V → ℝ) (F : Ty → ℝ → ℝ) (phi : Ty → ℝ)
    (π : JPolicy V Ty) (T : ℕ) (q : V → ℕ) : ℝ :=
  expPayoffFromJ c F phi π T 0 [] q

/-- The price that realizes a fraction `μ ∈ [0, 1]` of type-`τ` demand (p. 24): `p_τ(μ) = F_τ^{−1}(1 − μ)`,
written as `sup {p ∈ [p_τ^min, p_τ^max] : F_τ(p) ≤ 1 − μ}`. Under Condition 2 (`F_τ` continuous and strictly
increasing on `[p_τ^min, p_τ^max]` from `0` to `1`) the set is the interval `[p_τ^min, F_τ^{−1}(1 − μ)]`, so
this is the inverse, with `1 − F_τ(p_τ(μ)) = μ`. -/
noncomputable def pPrice (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ) (τ : Ty) (μ : ℝ) : ℝ :=
  sSup {p | p ∈ Set.Icc (pmin τ) (pmax τ) ∧ F τ p ≤ 1 - μ}

/-- The revenue function `r_τ(μ) = μ · p_τ(μ)` of Condition 2, part 3 (p. 24). -/
noncomputable def revJ (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ) (τ : Ty) (μ : ℝ) : ℝ :=
  μ * pPrice F pmin pmax τ μ

/-- **Condition 2** (pp. 23–24) for every type `τ`, the willingness-to-pay distribution function `F_τ` and
the price interval `[p_τ^min, p_τ^max]`:
1. `F_τ(p_τ^min) = 0` and `F_τ(p_τ^max) = 1` (stated as: `F_τ = 0` on `(−∞, p_τ^min]` and `F_τ = 1` on
   `[p_τ^max, ∞)`, since `F_τ` is a distribution function);
2. the willingness to pay is non-atomic (`F_τ` monotone and continuous) with support `[p_τ^min, p_τ^max]`
   (`p_τ^min < p_τ^max`) and positive density everywhere on the support (`F_τ` has a positive derivative at
   every point of `(p_τ^min, p_τ^max)`);
3. the revenue function `r_τ(μ) = μ p_τ(μ)` is concave and twice continuously differentiable on `[0, 1]`. -/
def Condition2 (pmin pmax : Ty → ℝ) (F : Ty → ℝ → ℝ) : Prop :=
  ∀ τ, pmin τ < pmax τ ∧ Monotone (F τ) ∧ Continuous (F τ) ∧
    (∀ p, p ≤ pmin τ → F τ p = 0) ∧ (∀ p, pmax τ ≤ p → F τ p = 1) ∧
    (∀ p ∈ Set.Ioo (pmin τ) (pmax τ), ∃ d : ℝ, 0 < d ∧ HasDerivAt (F τ) d p) ∧
    ConcaveOn ℝ (Set.Icc 0 1) (revJ F pmin pmax τ) ∧
    ContDiffOn ℝ 2 (revJ F pmin pmax τ) (Set.Icc 0 1)

/-- The scaling `max_{τ ∈ 𝒯} p_τ^max + max_{j, k ∈ V, τ ∈ 𝒯} |c_{jτk}| = 1` (p. 24), with both maxima
written out as attained values. -/
def JPANormalized (pmax : Ty → ℝ) (c : V → Ty → V → ℝ) : Prop :=
  ∃ τ₀ : Ty, ∃ j₀ k₀ : V, ∃ τ₁ : Ty,
    (∀ τ, pmax τ ≤ pmax τ₀) ∧ (∀ j τ k, |c j τ k| ≤ |c j₀ τ₁ k₀|) ∧ pmax τ₀ + |c j₀ τ₁ k₀| = 1

/-- The JPA assignment score of Algorithm 2 (p. 25): `−c_{jτk} + f(q̄_j) − f(q̄_k)`, with `q̄` from (9). -/
noncomputable def scoreJ (c : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ) (q : V → ℕ) (τ : Ty) (j k : V) : ℝ :=
  -c j τ k + f (qbar K q j) - f (qbar K q k)

/-- A tie-breaking rule for the assignment argmax of Algorithm 2: `sel q τ ∈ P(τ) × D(τ)` maximizes
`scoreJ` over all of `P(τ) × D(τ)` (self-pairs allowed). -/
structure IsArgmaxPairJ (P D : Ty → Finset V) (c : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) : Prop where
  mem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ
  max : ∀ q τ, ∀ j ∈ P τ, ∀ k ∈ D τ, scoreJ c f K q τ j k ≤ scoreJ c f K q τ (sel q τ).1 (sel q τ).2

/-- A tie-breaking rule for the fraction argmax of Algorithm 2: `muSel q τ ∈ [0, 1]` maximizes
`r_τ(μ) + μ · s` over `μ ∈ [0, 1]`, where `s` is the score of the selected pair `sel q τ`. -/
def IsArgmaxMuJ (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ) (c : V → Ty → V → ℝ) (f : ℝ → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (muSel : (V → ℕ) → Ty → ℝ) : Prop :=
  ∀ q τ, muSel q τ ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ μ ∈ Set.Icc (0 : ℝ) 1,
    revJ F pmin pmax τ μ + μ * scoreJ c f K q τ (sel q τ).1 (sel q τ).2
      ≤ revJ F pmin pmax τ (muSel q τ) + muSel q τ * scoreJ c f K q τ (sel q τ).1 (sel q τ).2

/-- The decision and price of Algorithm 2 (p. 25) at state `q` for a type-`τ` customer: with
`(j*, k*) = sel q τ`, if `q_{j*} > 0` the platform posts `p_τ(μ_τ)` for `μ_τ = muSel q τ` and serves a buying
customer with `(j*, k*)`; otherwise it drops the customer (the posted price is then immaterial and is taken to
be `p_τ^max`). -/
noncomputable def mbpDecisionJ (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ)
    (sel : (V → ℕ) → Ty → V × V) (muSel : (V → ℕ) → Ty → ℝ) (q : V → ℕ) (τ : Ty) : Decision V × ℝ :=
  if 0 < q (sel q τ).1 then (some (sel q τ), pPrice F pmin pmax τ (muSel q τ)) else (none, pmax τ)

/-- The MBP policy for joint pricing-assignment, Algorithm 2 (p. 25), as a deterministic stationary
Markov JPA control. -/
noncomputable def mbpPolicyJ (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ)
    (sel : (V → ℕ) → Ty → V × V) (muSel : (V → ℕ) → Ty → ℝ) : JPolicy V Ty where
  act _ _ q τ := Finsupp.single (mbpDecisionJ F pmin pmax sel muSel q τ) 1
  nonneg _ _ q τ x := by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  sum_one _ _ q τ := by
    rw [Finsupp.sum_single_index]; rfl

/-- The objective (49) of the JPA static planning problem (Appendix E.1, appendix p. 16, PDF 49):
`∑_τ φ_τ [r_τ(∑_{j ∈ P(τ), k ∈ D(τ)} x_{jτk}) − ∑_{j ∈ P(τ), k ∈ D(τ)} c_{jτk} x_{jτk}]`. -/
noncomputable def sppObjJ (P D : Ty → Finset V) (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ)
    (c : V → Ty → V → ℝ) (phi : Ty → ℝ) (x : V → Ty → V → ℝ) : ℝ :=
  ∑ τ, phi τ * (revJ F pmin pmax τ (∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k)
    - ∑ j ∈ P τ, ∑ k ∈ D τ, c j τ k * x j τ k)

/-- `W^SPP` of the JPA setting: the optimal value of (49) subject to the flow balance (50) and the demand
constraint (51) (the constraints of `sppFeasX`). The feasible set is nonempty (`x = 0`) and the objective
is bounded on it (`0 ≤ x`, `∑ x ≤ 1` per type, and `p_τ(μ)` takes values in `[p_τ^min, p_τ^max]` or is `0`),
so this `sSup` is the optimal value. -/
noncomputable def WsppJ (P D : Ty → Finset V) (F : Ty → ℝ → ℝ) (pmin pmax : Ty → ℝ)
    (c : V → Ty → V → ℝ) (phi : Ty → ℝ) : ℝ :=
  sSup (sppObjJ P D F pmin pmax c phi '' {x | sppFeasX P D phi x})

/-- `W*_T` of the JPA setting, display (4) (p. 10) for admissible JPA controls: the supremum over admissible
controls `π` and initial states `q ∈ Ω_K` of `(1/T) ∑_{t<T} E[v^π[t] | q[0] = q]`. The set is nonempty (the
always-drop control) and, under Condition 2 and the scaling `JPANormalized`, bounded above by `1`. -/
noncomputable def WstarTJ (P D : Ty → Finset V) (pmin pmax : Ty → ℝ) (c : V → Ty → V → ℝ)
    (F : Ty → ℝ → ℝ) (phi : Ty → ℝ) (K T : ℕ) : ℝ :=
  sSup {x | ∃ π : JPolicy V Ty, AdmissibleJ P D pmin pmax π ∧
    ∃ q ∈ StateSpace V K, x = expPayoffJ c F phi π T q / T}

/-- `W* = limsup_{T → ∞} W*_T`, display (5) (p. 10), in the JPA setting (a bounded sequence under the
standing assumptions of §5.2). -/
noncomputable def WstarJ (P D : Ty → Finset V) (pmin pmax : Ty → ℝ) (c : V → Ty → V → ℝ)
    (F : Ty → ℝ → ℝ) (phi : Ty → ℝ) (K : ℕ) : ℝ :=
  Filter.limsup (fun T : ℕ => WstarTJ P D pmin pmax c F phi K T) Filter.atTop

/-- `W^π_T = min_{q ∈ Ω_K} (1/T) ∑_{t<T} E[v^π[t] | q[0] = q]`, display (4) (p. 10), in the JPA setting
(`Ω_K` is finite and nonempty, so the infimum is a minimum). -/
noncomputable def WpiTJ (c : V → Ty → V → ℝ) (F : Ty → ℝ → ℝ) (phi : Ty → ℝ) (π : JPolicy V Ty)
    (K T : ℕ) : ℝ :=
  sInf {x | ∃ q ∈ StateSpace V K, x = expPayoffJ c F phi π T q / T}

/-- `W^π = liminf_{T → ∞} W^π_T`, display (5) (p. 10), in the JPA setting. -/
noncomputable def WpiJ (c : V → Ty → V → ℝ) (F : Ty → ℝ → ℝ) (phi : Ty → ℝ) (π : JPolicy V Ty)
    (K : ℕ) : ℝ :=
  Filter.liminf (fun T : ℕ => WpiTJ c F phi π K T) Filter.atTop

end MirrorBP.JEA.Supplement


