-- Prove2me | Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model
-- name    : ConsumerUtilityApprox_UnitDemand_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:53:52.61648+00:00
-- url     : https://prove2.me/theorems/400151c4-6c4a-4fbb-801e-9290ab95f3f3
-- title:
--   Value laws, single-buyer mechanisms, deletion loss, OPT^{1,1}, posted prices, and the multi-buyer benchmark OPT^{n,m} (§2, §2.3, §3)
-- statement:
--   There are $n \ge 1$ buyers and $m \ge 1$ items, one copy of each. Buyer $i$'s value for item $j$ is a random variable $V_{ij} \ge 0$ with law $F_{ij}$ on $[0,\infty)$, with $0 < \mathbb E[V_{ij}] < \infty$ (atoms allowed); all $nm$ values are independent. An **instance** records the laws $F_{ij}$; $V_i = (V_{i1},\dots,V_{im})$ has the product law $\prod_j F_{ij}$ and the profile $V = (V_1,\dots,V_n)$ the product of all $nm$ marginals.
--
--   **Single-buyer mechanisms (§3).** A single-buyer mechanism is a pair $(x,p)$ defined on every report $b \in \mathbb R^m_+$: $x_j(b)$ is the probability that item $j$ is allocated and $p(b)$ the expected payment; the buyer of type $v$ reporting $b$ gets $v\cdot x(b) - p(b)$, and $u(v) = v\cdot x(v) - p(v)$. It is *truthful* if $u(v) \ge v\cdot x(b)-p(b)$ for all $v,b\in\mathbb R^m_+$, *individually rational* if $u \ge 0$, has *nonnegative payments* if $p \ge 0$, is *feasible* if $x(b)\in[0,1]^m$, and *unit-demand* if $\sum_j x_j(b) \le 1$. For a type law $\mu$ (independent coordinates), $q^{\mathrm{alloc}}_j = \mathbb E_\mu[x_j(V)]$ is the ex-ante allocation probability, $U = \mathbb E_\mu[u(V)]$ the expected utility, and
--   $$D_j = \mathbb E_V\big[u(V) - u(V_{-j},0)\big],\qquad D=\sum_j D_j$$
--   the **deletion loss** (3.2), where $(V_{-j},0)$ sets coordinate $j$ to $0$.
--
--   **Single-dimensional benchmark (2.3).** For $X\ge 0$ with law $\nu$, a single-dimensional mechanism $(a,\tau)$ has $a(z)\in[0,1]$, $\tau(z)\ge0$ for every report $z\ge0$, is BIC ($z a(z)-\tau(z)\ge z a(z')-\tau(z')$) and IR ($z a(z)-\tau(z)\ge 0$); $\mathrm{OPT}^{1,1}(X;q)$ is the supremum of $\mathbb E[Xa(X)-\tau(X)]$ over such mechanisms with $\mathbb E[a(X)]\le q$.
--
--   **Posted prices (Lemma 3, C.1).** A price $t\in[0,\infty]$ ($t=\infty$: no offer) gives surplus $(v-t)^+$ (zero if $t=\infty$); the item sells iff $v>t$. For independent price laws $\pi_j$, $U(M^1_j)=\mathbb E[(V_j-P_j)^+]$ and $\Pr(V_j>P_j)$ is the sale probability. Under $M^{UD}$ all prices are posted together and the buyer takes an item of largest positive surplus (ties uniform; no purchase when no surplus is positive); $U(M^{UD})$ and $q^{\mathrm{alloc}}_j(M^{UD})$ are its expected utility and allocation probabilities. Free lotteries use $\ell_j(h)=\min\{1,h/\lambda_j\}$ if $\lambda_j>0$ and $1$ if $\lambda_j=0$; the buyer's candidate items are those maximizing a positive $\ell_jv_j$.
--
--   **Multi-buyer mechanisms (§2).** A mechanism in reduced form $M=(x,p)$ gives, at each reported profile $v$, the probability $x_{ij}(v)$ that buyer $i$ receives item $j$ and $i$'s expected payment $p_i(v)$. With interim rules $\bar x_i(w)=\mathbb E_{V_{-i}}[x_i(w,V_{-i})]$, $\bar p_i(w)=\mathbb E_{V_{-i}}[p_i(w,V_{-i})]$, $M$ is **BIC** if $v\cdot\bar x_i(v)-\bar p_i(v)\ge v\cdot\bar x_i(w)-\bar p_i(w)$ for all $i$ and all $v,w\in\mathbb R^m_+$, and **interim IR** if $u_i(v)=v\cdot\bar x_i(v)-\bar p_i(v)\ge 0$. Its residual surplus is $U(M)=\sum_i\mathbb E[u_i(V_i)]$ and
--   $$\mathrm{OPT}^{n,m}=\sup\{U(M): M \text{ feasible, BIC, interim IR, } p\ge 0\}.$$
--   Feasible means a lottery over matchings; in reduced form, $x\ge0$ with every row and column sum at most $1$. $q^{\mathrm{alloc}}_{ij}(M)=\mathbb E[x_{ij}(V)]$; $M$ is ex-ante feasible if $\sum_i q^{\mathrm{alloc}}_{ij}\le 1$ for every $j$.
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note.** Values are `ℝ≥0`, laws are `ProbabilityMeasure ℝ≥0`; buyers and items are `Fin n`, `Fin m`. Single-buyer mechanisms are the published `MultiItemRev.BundlingOpt.Mechanism (Fin m)` with `IsFeasible`, `IsIC`, `IsIR`, `IsNPT` (not its `IsAdmissible`); `IsTruthfulIRNPT` adds Borel measurability of $x$ and $p$, the tacit convention that makes every expectation defined. `OPT11` is a real `sSup`; on the inputs used ($q\ge0$, finite mean) its set is nonempty and bounded by $\mathbb E[X]$. Feasibility of the benchmark is the doubly-substochastic reduced form (Birkhoff–von Neumann); `IsWellDefined` asks for measurable rules and finite interim payments, without which $U$ is undefined. `OPT` is a real `sSup` over a nonempty set bounded by $\sum_{i,j}\mathbb E[V_{ij}]$. $(v)_{-i}$ with $w$ in place of $v_i$ is `Function.update v i w`.
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), pp. 6–8 (§2, §2.2, §2.3), pp. 9–14 (§3), p. 22 (§5.1)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-!
Goldner, Lundy, Tsilivis, *A Constant-Factor Approximation to Multidimensional Consumer
Utility* (arXiv:2610.10516, version of November 3, 2026), §2, §2.2, §2.3, §3 and §5.1:
value laws, single-buyer mechanisms, deletion loss, the single-dimensional benchmark
`OPT^{1,1}`, posted prices, free lotteries, multi-buyer mechanisms in reduced form, BIC,
interim individual rationality, residual surplus `U` and the benchmark `OPT^{n,m}`.

Single-buyer mechanisms are the published `MultiItemRev.BundlingOpt.Mechanism (Fin m)`
(allocation `q b j`, payment `s b`, defined on every report `b ∈ ℝ^m_+`), with its predicates
`IsFeasible`, `IsIC`, `IsIR`, `IsNPT`; unit demand and measurability are added here.
-/

namespace ConsumerUtilityApprox.UnitDemand

open MultiItemRev.BundlingOpt

/-! ### Value laws and instances (§2, p. 6) -/

/-- A law on `[0, ∞)` has finite mean. -/
def HasFiniteMean (ν : ProbabilityMeasure ℝ≥0) : Prop :=
  Integrable (fun x : ℝ≥0 => (x : ℝ)) (ν : Measure ℝ≥0)

/-- The mean `E[X]` of a law on `[0, ∞)`. -/
noncomputable def mean (ν : ProbabilityMeasure ℝ≥0) : ℝ :=
  ∫ x, (x : ℝ) ∂(ν : Measure ℝ≥0)

/-- The standing assumption of §2: `0 < E[V] < ∞`. Atoms are allowed. -/
def IsValueLaw (ν : ProbabilityMeasure ℝ≥0) : Prop :=
  HasFiniteMean ν ∧ 0 < mean ν

/-- An instance (§2): `n` buyers, `m` items, buyer `i`'s value for item `j` has law `F i j`
on `[0, ∞)` with `0 < E[V_ij] < ∞`; values are independent across all pairs. -/
structure Instance (n m : ℕ) where
  F : Fin n → Fin m → ProbabilityMeasure ℝ≥0
  valueLaw : ∀ i j, IsValueLaw (F i j)

/-- The law of a vector `(V_1, …, V_m)` of independent values with laws `G j`. -/
noncomputable def vecLaw {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0) :
    Measure (Fin m → ℝ≥0) :=
  Measure.pi (fun j => (G j : Measure ℝ≥0))

instance {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0) : IsProbabilityMeasure (vecLaw G) := by
  unfold vecLaw; infer_instance

/-- A reported (or true) value profile `v = (v_1, …, v_n)`, `v i j = v_ij`. -/
abbrev Profile (n m : ℕ) := Fin n → Fin m → ℝ≥0

/-- Buyer `i`'s type law `V_i ∼ ∏_j F_ij`. -/
noncomputable def Instance.buyerLaw {n m : ℕ} (I : Instance n m) (i : Fin n) :
    Measure (Fin m → ℝ≥0) :=
  vecLaw (I.F i)

instance {n m : ℕ} (I : Instance n m) (i : Fin n) : IsProbabilityMeasure (I.buyerLaw i) := by
  unfold Instance.buyerLaw; infer_instance

/-- The law of the whole profile `V = (V_ij)`: the product of all `n m` marginals. -/
noncomputable def Instance.profileLaw {n m : ℕ} (I : Instance n m) : Measure (Profile n m) :=
  Measure.pi (fun i => I.buyerLaw i)

instance {n m : ℕ} (I : Instance n m) : IsProbabilityMeasure I.profileLaw := by
  unfold Instance.profileLaw; infer_instance

/-! ### Single-buyer mechanisms (§2.2, §3) -/

/-- Unit demand: the expected allocations of every report sum to at most one. -/
def IsUnitDemand {m : ℕ} (M : Mechanism (Fin m)) : Prop :=
  ∀ b, ∑ j, M.q b j ≤ 1

/-- Allocation and payment rules are Borel measurable, so that expectations are defined
(the standing convention behind every `E[·]` of the paper). -/
def IsMeasurableMech {m : ℕ} (M : Mechanism (Fin m)) : Prop :=
  (∀ j, Measurable fun b => M.q b j) ∧ Measurable M.s

/-- A truthful, individually rational single-buyer mechanism with nonnegative payments
(§3, p. 9): allocations in `[0,1]^m`, IC and IR for all types and reports in `ℝ^m_+`,
`p ≥ 0`, measurable rules. -/
def IsTruthfulIRNPT {m : ℕ} (M : Mechanism (Fin m)) : Prop :=
  IsFeasible M ∧ IsIC M ∧ IsIR M ∧ IsNPT M ∧ IsMeasurableMech M

/-- Ex-ante allocation probability `q^alloc_j = E_V[x_j(V)]` (§2.2). -/
noncomputable def qAlloc {m : ℕ} (μ : Measure (Fin m → ℝ≥0)) (M : Mechanism (Fin m))
    (j : Fin m) : ℝ :=
  ∫ b, M.q b j ∂μ

/-- Expected utility `U = E_V[u(V)]`, `u(v) = v · x(v) − p(v)`. -/
noncomputable def utility {m : ℕ} (μ : Measure (Fin m → ℝ≥0)) (M : Mechanism (Fin m)) : ℝ :=
  ∫ v, buyerPayoff M v ∂μ

/-- Expected deletion loss of item `j`, (3.2): `D_j = E_V[u(V) − u(V_{−j}, 0)]`. -/
noncomputable def deletionLoss {m : ℕ} (μ : Measure (Fin m → ℝ≥0)) (M : Mechanism (Fin m))
    (j : Fin m) : ℝ :=
  ∫ v, (buyerPayoff M v - buyerPayoff M (Function.update v j 0)) ∂μ

/-- Total deletion loss `D = Σ_j D_j`, (3.2). -/
noncomputable def totalDeletionLoss {m : ℕ} (μ : Measure (Fin m → ℝ≥0))
    (M : Mechanism (Fin m)) : ℝ :=
  ∑ j, deletionLoss μ M j

/-! ### The single-dimensional benchmark `OPT^{1,1}` (§2.3, (2.3)) -/

/-- A single-dimensional mechanism: allocation probability `a z` and expected payment `τ z`
for each report `z ≥ 0`. -/
structure SDMechanism where
  a : ℝ≥0 → ℝ
  τ : ℝ≥0 → ℝ

/-- `(a, τ)` has `a ∈ [0,1]`, `τ ≥ 0`, is BIC and IR for all values and reports `z ≥ 0`,
and has measurable rules. -/
def SDMechanism.IsAdmissible (M : SDMechanism) : Prop :=
  (∀ z, 0 ≤ M.a z ∧ M.a z ≤ 1) ∧ (∀ z, 0 ≤ M.τ z) ∧
  (∀ z z' : ℝ≥0, (z : ℝ) * M.a z' - M.τ z' ≤ (z : ℝ) * M.a z - M.τ z) ∧
  (∀ z : ℝ≥0, 0 ≤ (z : ℝ) * M.a z - M.τ z) ∧ Measurable M.a ∧ Measurable M.τ

/-- `E[X a(X) − τ(X)]` for `X ∼ ν`. -/
noncomputable def SDMechanism.utility (ν : ProbabilityMeasure ℝ≥0) (M : SDMechanism) : ℝ :=
  ∫ z, ((z : ℝ) * M.a z - M.τ z) ∂(ν : Measure ℝ≥0)

/-- `E[a(X)]` for `X ∼ ν`. -/
noncomputable def SDMechanism.alloc (ν : ProbabilityMeasure ℝ≥0) (M : SDMechanism) : ℝ :=
  ∫ z, M.a z ∂(ν : Measure ℝ≥0)

/-- `OPT^{1,1}(X; q)`, (2.3), written as a supremum (its attainment is a separate statement):
the largest expected utility of a BIC, IR single-dimensional mechanism with nonnegative
payments and `E[a(X)] ≤ q`. For `X` with finite mean and `q ≥ 0` the set is nonempty (the
mechanism that never allocates) and bounded above by `E[X]`. -/
noncomputable def OPT11 (ν : ProbabilityMeasure ℝ≥0) (q : ℝ) : ℝ :=
  sSup {u | ∃ M : SDMechanism, M.IsAdmissible ∧ M.alloc ν ≤ q ∧ M.utility ν = u}

/-! ### Posted prices (Lemma 3, Appendix C.1) -/

/-- The surplus `(v − t)^+` of value `v` at a posted price `t ∈ [0, ∞]`; `t = ∞` means the
item is not offered (surplus `0`). The item sells iff `v > t`. -/
noncomputable def surplus (v : ℝ≥0) (t : ℝ≥0∞) : ℝ :=
  if t = ⊤ then 0 else max ((v : ℝ) - t.toReal) 0

/-- Expected utility `U(M^1_j) = E[(V − P)^+]` of one item with value law `ν` sold at an
independent random price with law `π` on `[0, ∞]`. -/
noncomputable def postedUtility1 (ν : ProbabilityMeasure ℝ≥0) (π : Measure ℝ≥0∞) : ℝ :=
  ∫ t, ∫ v, surplus v t ∂(ν : Measure ℝ≥0) ∂π

/-- Probability of sale `Pr(V > P)` for `V ∼ ν` and an independent price `P ∼ π`. -/
noncomputable def saleProb1 (ν : ProbabilityMeasure ℝ≥0) (π : Measure ℝ≥0∞) : ℝ :=
  ∫ t, ((ν : Measure ℝ≥0) {v | t < (v : ℝ≥0∞)}).toReal ∂π

/-- The items a unit-demand buyer with values `v` facing prices `t` may choose: positive
surplus, and largest surplus among all items. -/
noncomputable def udCandidates {m : ℕ} (v : Fin m → ℝ≥0) (t : Fin m → ℝ≥0∞) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j =>
    0 < surplus (v j) (t j) ∧ ∀ k, surplus (v k) (t k) ≤ surplus (v j) (t j)

/-- Probability that the buyer takes item `j` under `M^UD` at prices `t`: ties among the
best items are broken uniformly at random; with no positive surplus the buyer does not
participate (ties with non-participation go to non-participation, p. 7). -/
noncomputable def udChoice {m : ℕ} (v : Fin m → ℝ≥0) (t : Fin m → ℝ≥0∞) (j : Fin m) : ℝ :=
  if j ∈ udCandidates v t then 1 / ((udCandidates v t).card : ℝ) else 0

/-- Expected utility `U(M^UD)` of posting independent prices with laws `π j` together to a
buyer with independent values of laws `G j`. -/
noncomputable def udUtility {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) : ℝ :=
  ∫ t, ∫ v, ∑ j, udChoice v t j * surplus (v j) (t j) ∂(vecLaw G) ∂(Measure.pi π)

/-- Ex-ante probability `q^alloc_j(M^UD)` that `M^UD` allocates item `j`. -/
noncomputable def udAlloc {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (π : Fin m → Measure ℝ≥0∞) (j : Fin m) : ℝ :=
  ∫ t, ∫ v, udChoice v t j ∂(vecLaw G) ∂(Measure.pi π)

/-! ### Free lotteries (§5.1, p. 22) -/

/-- `ℓ_j(h) = min{1, h/λ_j}` if `λ_j > 0`, and `1` if `λ_j = 0`. -/
noncomputable def lotteryProb {m : ℕ} (lam : Fin m → ℝ) (h : ℝ) (j : Fin m) : ℝ :=
  if 0 < lam j then min 1 (h / lam j) else 1

/-- The items a buyer with values `v` may choose among free lotteries `ℓ`: positive expected
utility `ℓ_j v_j`, and largest among all items. -/
noncomputable def lotCandidates {m : ℕ} (v : Fin m → ℝ≥0) (ℓ : Fin m → ℝ) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun j =>
    0 < ℓ j * (v j : ℝ) ∧ ∀ k, ℓ k * (v k : ℝ) ≤ ℓ j * (v j : ℝ)

/-! ### Multi-buyer mechanisms in reduced form (§2, pp. 6–7) -/

/-- A multi-buyer mechanism in reduced form `M = (x, p)`: `x v i j` is the probability that
buyer `i` receives item `j` and `p v i` buyer `i`'s expected payment at reported profile
`v`, averaging over the mechanism's internal randomness. -/
structure RMech (n m : ℕ) where
  x : Profile n m → Fin n → Fin m → ℝ
  p : Profile n m → Fin n → ℝ

namespace RMech

variable {n m : ℕ}

/-- Matching feasibility of a lottery over matchings, in reduced form: `x ≥ 0`, each buyer
receives at most one item and each item goes to at most one buyer in expectation
(doubly substochastic; by Birkhoff–von Neumann exactly the reduced forms of lotteries over
matchings). -/
def IsFeasible (M : RMech n m) : Prop :=
  ∀ v, (∀ i j, 0 ≤ M.x v i j) ∧ (∀ i, ∑ j, M.x v i j ≤ 1) ∧ (∀ j, ∑ i, M.x v i j ≤ 1)

/-- Nonnegative (expected) payments `p_i(v) ≥ 0`. -/
def HasNonnegPayments (M : RMech n m) : Prop :=
  ∀ v i, 0 ≤ M.p v i

/-- The rules are measurable and every interim payment is finite, so that the interim rules
and `U` are defined. -/
def IsWellDefined (I : Instance n m) (M : RMech n m) : Prop :=
  (∀ i j, Measurable fun v => M.x v i j) ∧ (∀ i, Measurable fun v => M.p v i) ∧
  ∀ i (w : Fin m → ℝ≥0), Integrable (fun v => M.p (Function.update v i w) i) I.profileLaw

/-- Interim allocation `x̄_ij(w) = E_{V_{−i}}[x_ij(w, V_{−i})]`. -/
noncomputable def interimAlloc (I : Instance n m) (M : RMech n m) (i : Fin n)
    (w : Fin m → ℝ≥0) (j : Fin m) : ℝ :=
  ∫ v, M.x (Function.update v i w) i j ∂I.profileLaw

/-- Interim payment `p̄_i(w) = E_{V_{−i}}[p_i(w, V_{−i})]`. -/
noncomputable def interimPay (I : Instance n m) (M : RMech n m) (i : Fin n)
    (w : Fin m → ℝ≥0) : ℝ :=
  ∫ v, M.p (Function.update v i w) i ∂I.profileLaw

/-- Interim utility `v · x̄_i(w) − p̄_i(w)` of buyer `i` of type `v` reporting `w`. -/
noncomputable def interimUtil (I : Instance n m) (M : RMech n m) (i : Fin n)
    (v w : Fin m → ℝ≥0) : ℝ :=
  ∑ j, (v j : ℝ) * interimAlloc I M i w j - interimPay I M i w

/-- Bayesian incentive compatibility, for every true type and report in `ℝ^m_+`. -/
def IsBIC (I : Instance n m) (M : RMech n m) : Prop :=
  ∀ i (v w : Fin m → ℝ≥0), interimUtil I M i v w ≤ interimUtil I M i v v

/-- Interim individual rationality, for every type in `ℝ^m_+`. -/
def IsInterimIR (I : Instance n m) (M : RMech n m) : Prop :=
  ∀ i (v : Fin m → ℝ≥0), 0 ≤ interimUtil I M i v v

/-- Residual surplus `U(M) = Σ_i E_{V_i}[u_i(V_i)]`. -/
noncomputable def U (I : Instance n m) (M : RMech n m) : ℝ :=
  ∑ i, ∫ v, interimUtil I M i v v ∂I.buyerLaw i

/-- Ex-ante allocation probability `q^alloc_ij(M) = E_V[x_ij(V)]`. -/
noncomputable def exAnteAlloc (I : Instance n m) (M : RMech n m) (i : Fin n) (j : Fin m) :
    ℝ :=
  ∫ v, M.x v i j ∂I.profileLaw

/-- Ex-ante feasibility: `Σ_i q^alloc_ij(M) ≤ 1` for every item. -/
def IsExAnteFeasible (I : Instance n m) (M : RMech n m) : Prop :=
  ∀ j, ∑ i, exAnteAlloc I M i j ≤ 1

/-- The class of the benchmark: feasible, BIC, interim IR, nonnegative payments. -/
def IsBenchmarkClass (I : Instance n m) (M : RMech n m) : Prop :=
  IsWellDefined I M ∧ IsFeasible M ∧ IsBIC I M ∧ IsInterimIR I M ∧ HasNonnegPayments M

end RMech

/-- `OPT^{n,m}` (p. 7): the supremum of `U` over all feasible, BIC, interim individually
rational mechanisms with nonnegative payments (nonempty: the mechanism that allocates
nothing; bounded above by `Σ_{i,j} E[V_ij]`). -/
noncomputable def OPT {n m : ℕ} (I : Instance n m) : ℝ :=
  sSup {u | ∃ M : RMech n m, M.IsBenchmarkClass I ∧ M.U I = u}

end ConsumerUtilityApprox.UnitDemand


