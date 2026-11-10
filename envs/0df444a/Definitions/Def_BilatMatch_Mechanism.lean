-- Prove2me | Definitions.Def_BilatMatch_Mechanism
-- name    : BilatMatch_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:54.238025+00:00
-- url     : https://prove2.me/theorems/e6e8b4c7-4104-45b6-892a-edc349125818
-- title:
--   Direct mechanisms, interim utilities, BIC, IIR, admissibility, GFT and revenue
-- statement:
--   A **direct mechanism** $(x,p)$ on a market specifies, at every report profile $\theta$, a distribution over feasible matchings and a signed payment $p_u(\theta)$ for every agent $u\in B\sqcup S$ (positive payments go to the mechanism). The randomization is a uniform seed $\omega\in[0,1]$: the mechanism selects the matching $\mathrm{alloc}(\theta,\omega)\in\mathcal F$, and $x_{ij}(\theta)$ is the probability that the edge $(i,j)$ is selected. The agents' trade probabilities are $x_{B_i}=\sum_j x_{ij}$ and $x_{S_j}=\sum_i x_{ij}$.
--
--   Interim quantities average over the other agents' types with the agent's own report fixed. Buyer $i$ with value $t$ reporting $r$ has interim utility $t\,\bar x_{B_i}(r)-\bar p_i(r)$; seller $j$ with cost $t$ reporting $r$ has $-t\,\bar x_{S_j}(r)-\bar p_j(r)$. Given report domains $D_u\subseteq\mathbb R$:
--
--   1. **BIC on $D$**: for every agent and all $t,r\in D_u$, reporting $t$ is at least as good as reporting $r$;
--   2. **IIR on $D$**: every type $t\in D_u$ has nonnegative truthful interim utility;
--   3. **admissible** (footnote 1): total absolute payments and absolute realized gains have finite expectations, and every interim payment integrand is integrable.
--
--   Expected gains from trade and expected net revenue are
--   $$\mathrm{GFT}=\mathbb E\Big[\sum_{(i,j)\in E}(v_i-c_j)x_{ij}\Big],\qquad \mathrm{Rev}=\mathbb E\Big[\sum_{i\in B}p_i+\sum_{j\in S}p_j\Big].$$
--
--   **Formalization Note** Every realization of the allocation is feasible at every real profile, and trade events are jointly measurable in profile and seed; for a countable edge set every measurable distribution over feasible matchings arises this way. Payments are deterministic measurable functions of the report profile. The whole-line domain $D_u=\mathbb R$ is `wholeLine`.
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), §2, pp.5–6 (pdf pp.7–8), footnote 1 p.5, and p.7

import Mathlib
import Definitions.Def_BilatMatch_Market

open MeasureTheory

namespace BilatMatch

/-!
# Direct mechanisms, interim utilities, BIC, IIR, admissibility, GFT and revenue

Liu, Qin, Wang, *From Bilateral Trade to Matching Markets: Sharp Gains from Trade*,
arXiv:2609.30702 (held version, sha256 ff1490ad…), §2, pp.5–6 (pdf pp.7–8), footnote 1 (p.5),
and p.7 ("admissible BIC/IIR mechanisms").

**Formalization Note**
* **Randomization seed.** "A distribution over feasible matchings" is the law of
  `alloc θ ω` for a uniform seed `ω ∈ [0,1]` (`unitInterval` with Lebesgue measure). Every
  realization is feasible (`alloc θ ω ∈ F` for all `θ, ω`, not only on the support of the prior),
  and every event `{(θ, ω) | e ∈ alloc θ ω}` is measurable. Since `2^E` is standard Borel for a
  countable edge set, every measurable distribution over feasible matchings arises this way.
* **Payments** are deterministic signed functions of the report profile, positive payments going
  to the mechanism (p.5); they are measurable.
* `x e θ` is the probability that edge `e` trades at `θ`; `x_{B_i} = ∑_j x_{ij}`,
  `x_{S_j} = ∑_i x_{ij}` (p.5) as `tsum`s.
* **Interim quantities** are integrals over the whole product prior of the profile with one
  coordinate replaced; since the prior is a product, this averages over the other agents only.
* **Report domains.** BIC and IIR are taken relative to a report domain `D u ⊆ ℝ` for every agent
  `u` (types and reports in `D u`); the main theorem uses `D u = ℝ` (whole line, paper.md
  decision 5), the finite-market statements use the supports or bounded intervals (p.6, p.8).
* **Admissible** (footnote 1, p.5): total absolute payments and absolute realized gains have finite
  expectations, and every interim payment integrand (one agent's report replaced by any real) is
  integrable, so no Bochner integral below is a junk value.
-/

variable {B S : Type*}

/-- A direct mechanism `(x, p)` on the market `I` (p.5): a randomized feasible matching
`alloc θ ω ∈ F` driven by a uniform seed `ω`, and signed payments `pay θ u` to the mechanism for
every agent `u ∈ B ⊕ S` at every report profile `θ`. -/
structure Mechanism (I : Market B S) where
  /-- the matching selected at report profile `θ` and seed `ω` -/
  alloc : Profile B S → unitInterval → Set (B × S)
  /-- every realization is a feasible matching -/
  alloc_mem : ∀ θ ω, alloc θ ω ∈ I.family
  /-- the trade events are jointly measurable in the profile and the seed -/
  alloc_meas : ∀ e : B × S, MeasurableSet {p : Profile B S × unitInterval | e ∈ alloc p.1 p.2}
  /-- the signed payment of agent `u` to the mechanism at profile `θ` -/
  pay : Profile B S → B ⊕ S → ℝ
  /-- payments are measurable in the profile -/
  pay_meas : ∀ u, Measurable fun θ => pay θ u

namespace Mechanism

variable {I : Market B S} (A : Mechanism I)

/-- `x_e(θ)`: the probability that edge `e` trades at profile `θ`. -/
noncomputable def x (e : B × S) (θ : Profile B S) : ℝ :=
  (volume {ω : unitInterval | e ∈ A.alloc θ ω}).toReal

/-- Buyer `i`'s trade probability `x_{B_i}(θ) = ∑_j x_{ij}(θ)`. -/
noncomputable def xB (i : B) (θ : Profile B S) : ℝ := ∑' j : S, A.x (i, j) θ

/-- Seller `j`'s trade probability `x_{S_j}(θ) = ∑_i x_{ij}(θ)`. -/
noncomputable def xS (j : S) (θ : Profile B S) : ℝ := ∑' i : B, A.x (i, j) θ

/-- Buyer `i`'s interim trade probability at report `r`: `E_{θ_{-i}}[x_{B_i}(r, θ_{-i})]`. -/
noncomputable def interimXB (i : B) (r : ℝ) : ℝ :=
  ∫ θ, A.xB i (updateBuyer θ i r) ∂typeMeasure I

/-- Seller `j`'s interim trade probability at report `r`. -/
noncomputable def interimXS (j : S) (r : ℝ) : ℝ :=
  ∫ θ, A.xS j (updateSeller θ j r) ∂typeMeasure I

/-- Buyer `i`'s interim payment to the mechanism at report `r`. -/
noncomputable def interimPayB (i : B) (r : ℝ) : ℝ :=
  ∫ θ, A.pay (updateBuyer θ i r) (Sum.inl i) ∂typeMeasure I

/-- Seller `j`'s interim payment to the mechanism at report `r`. -/
noncomputable def interimPayS (j : S) (r : ℝ) : ℝ :=
  ∫ θ, A.pay (updateSeller θ j r) (Sum.inr j) ∂typeMeasure I

/-- Interim utility of buyer `i` with value `t` reporting `r` while the others report truthfully:
`t · x_{B_i}(r) − p_i(r)` (quasilinear, p.6). -/
noncomputable def utilB (i : B) (t r : ℝ) : ℝ := t * A.interimXB i r - A.interimPayB i r

/-- Interim utility of seller `j` with cost `t` reporting `r`: `−t · x_{S_j}(r) − p_j(r)` (p.6). -/
noncomputable def utilS (j : S) (t r : ℝ) : ℝ := -(t * A.interimXS j r) - A.interimPayS j r

/-- Admissibility (footnote 1, p.5): finite expected total absolute payment, finite expected
absolute realized gains, and integrable interim payment integrands at every own report. -/
def Admissible : Prop :=
  (∫⁻ θ, ∑' u : B ⊕ S, ENNReal.ofReal |A.pay θ u| ∂typeMeasure I) < ⊤ ∧
  (∫⁻ θ, ∑' e : I.edges, ENNReal.ofReal |(θ.1 e.1.1 - θ.2 e.1.2) * A.x e θ| ∂typeMeasure I) < ⊤ ∧
  (∀ i r, Integrable (fun θ => A.pay (updateBuyer θ i r) (Sum.inl i)) (typeMeasure I)) ∧
  (∀ j r, Integrable (fun θ => A.pay (updateSeller θ j r) (Sum.inr j)) (typeMeasure I))

/-- Bayesian incentive compatibility relative to report domains `D` (p.6): for every agent, every
type in its domain weakly prefers truthful reporting to every report in its domain. -/
def IsBICOn (D : B ⊕ S → Set ℝ) : Prop :=
  (∀ i, ∀ t ∈ D (Sum.inl i), ∀ r ∈ D (Sum.inl i), A.utilB i t r ≤ A.utilB i t t) ∧
  (∀ j, ∀ t ∈ D (Sum.inr j), ∀ r ∈ D (Sum.inr j), A.utilS j t r ≤ A.utilS j t t)

/-- Interim individual rationality relative to report domains `D` (p.6): every type in its domain
has nonnegative truthful interim utility. -/
def IsIIROn (D : B ⊕ S → Set ℝ) : Prop :=
  (∀ i, ∀ t ∈ D (Sum.inl i), 0 ≤ A.utilB i t t) ∧ (∀ j, ∀ t ∈ D (Sum.inr j), 0 ≤ A.utilS j t t)

/-- The realized gains from trade `∑_{(i,j) ∈ E} (v_i − c_j) x_{ij}(θ)` at a profile. -/
noncomputable def gftIntegrand (θ : Profile B S) : ℝ :=
  ∑' e : I.edges, (θ.1 e.1.1 - θ.2 e.1.2) * A.x e θ

/-- Expected gains from trade `GFT(M) = E[∑_{(i,j) ∈ E} (v_i − c_j) x_{ij}]` (p.6). -/
noncomputable def GFT : ℝ := ∫ θ, A.gftIntegrand θ ∂typeMeasure I

/-- Expected net revenue `Rev(M) = E[∑_{i ∈ B} p_i + ∑_{j ∈ S} p_j]` (p.6). -/
noncomputable def Rev : ℝ := ∫ θ, ∑' u : B ⊕ S, A.pay θ u ∂typeMeasure I

end Mechanism

/-- The whole-line report domain: every agent may report any real number. -/
def wholeLine (B S : Type*) : B ⊕ S → Set ℝ := fun _ => Set.univ

end BilatMatch


