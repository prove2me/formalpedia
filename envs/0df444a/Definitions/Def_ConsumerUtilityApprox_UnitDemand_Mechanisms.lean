-- Prove2me | Definitions.Def_ConsumerUtilityApprox_UnitDemand_Mechanisms
-- name    : ConsumerUtilityApprox_UnitDemand_Mechanisms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:54:39.928567+00:00
-- url     : https://prove2.me/theorems/f4b3837d-02db-41b3-b0ee-ef170e57825b
-- title:
--   Randomized mechanisms with realized outcomes, M^UD, M^free, M^{1,m}_het, the cap program (5.4), bisection, fair contention and the mechanism description language (§5, App. C.3–C.5)
-- statement:
--   All internal randomness of the paper's mechanisms is finitely supported, so the law of a realized outcome is a probability mass function; "in every realized outcome" means "for every outcome of positive probability".
--
--   **Elementary choices.** A coin with $\Pr(\text{true})=p$ (clamped to $[0,1]$); a uniform element of a finite set (nothing if empty); independent draws.
--
--   **Two-point prices (§2.3, C.1).** A price drawn from at most two options, $p_1$ with probability $\theta$ and $p_2$ with probability $1-\theta$, $p_1,p_2\in[0,\infty]$ ($\infty$ = no offer). It *implements* $\mathrm{OPT}^{1,1}(X;q)$ if $\Pr(X>P)\le q$ and $\mathbb E[(X-P)^+]=\mathrm{OPT}^{1,1}(X;q)$.
--
--   **Single-buyer randomized mechanisms.** For each report $b\in\mathbb R^m_+$, a law of the realized outcome (item received or none, payment). Its reduced form is $x_j(b)=\Pr(\text{item } j)$, $p(b)=\mathbb E[\text{payment}]$; it is BIC if the reduced form is truthful, **ex-post IR** if for every type $v$ every realized outcome gives $v_{j}-\text{payment}\ge 0$ (value $0$ with no item), and has nonnegative payments if every realized payment is $\ge0$.
--
--   **Offers.** Posted-price offer $M^{UD}$: independent two-point prices, the buyer asks for an item of largest strictly positive surplus $v_j-P_j$ (ties uniform) and pays $P_j$. Free-lottery offer with $\ell\in[0,1]^m$: the buyer picks an item maximizing a positive $\ell_jv_j$ (ties uniform) and receives it free with probability $\ell_j$; $M^{\mathrm{free}}_h$ uses $\ell_j(h)$, $M^{\mathrm{free}}_0$ uses $\ell=0$. $M^{1,m}_{\mathrm{het}}$ runs $M^{UD}$ with probability $e/(3e-2)$ and the free-lottery offer otherwise, independently of the report.
--
--   **Cap program (5.4).** For demand weights $\lambda$, caps $q\ge0$ with $\sum_jq_j\le1$ have objective $\sum_j\big(\mathrm{OPT}^{1,1}(V_j;q_j)-\tfrac{e}{e-1}\lambda_jq_j\big)$, and $R_\lambda$ is its supremum.
--
--   **Bisection (C.3).** On $[a,b]=[0,1]$, with midpoint $c$, move $a$ to $c$ if $f(c)>2c$ and $b$ to $c$ otherwise; stop after $k=\lceil\log_2(1/\gamma)\rceil$ steps, the first $k$ with $b-a=2^{-k}\le\gamma$.
--
--   **Fair contention (§5.2, C.5).** With announced request probabilities $Q_{kj}$ and requester set $A_j$: nobody if $A_j=\emptyset$, the sole requester if $|A_j|=1$, otherwise requester $i$ with probability
--   $$\frac{1}{\sum_kQ_{kj}}\Big(\sum_{k\in A_j\setminus\{i\}}\frac{Q_{kj}}{|A_j|-1}+\sum_{k\notin A_j}\frac{Q_{kj}}{|A_j|}\Big)$$
--   (uniform if $\sum_kQ_{kj}=0$); $c_j=1$ if $\sum_kQ_{kj}=0$ and $c_j=(1-\prod_k(1-Q_{kj}))/\sum_kQ_{kj}$ otherwise.
--
--   **Multi-buyer randomized mechanisms.** For each reported profile, a law of the realized outcome (each buyer's item or none, payments); ex-post IR, matching feasibility (no item to two buyers) and nonnegative payments are required in every realized outcome; BIC and $U$ are those of the reduced form.
--
--   **Description language.** A description gives $T$ rounds, a participation probability $\rho$, for each buyer $i$ and round $t<T$ the probability $w_{it}$ of the pricing branch, two-point prices and lotteries, announced request probabilities $Q_{ij}$ and service probabilities $\sigma_j$. Its pre-contention mechanism $\bar M^{n,m}_{\mathrm{het}}$: each buyer independently participates with probability $\rho$, draws a uniform round, runs the pricing offer with probability $w_{it}$ and the lottery offer otherwise, and every request is granted. Its mechanism $M^{n,m}_{\mathrm{het}}$: the same requests, then for each item independently the fair rule selects a requester, who is served with probability $\sigma_j$, receives the item and pays the request's price; unserved requests pay nothing.
--
--   **Formalization Note.** Randomness is `PMF`; ex-post properties quantify over `PMF.support`. Out-of-range data in a description are clamped ($\theta,\ell,\rho,w,\sigma,Q$ to $[0,1]$; prices are in `ℝ≥0∞`), and the fair rule falls back to a uniform choice when its weights do not sum to one; neither happens for well-formed data. Rounds are $0,\dots,T-1$.
-- source:
--   Goldner, Lundy, Tsilivis, A Constant-Factor Approximation to Multidimensional Consumer Utility, arXiv:2610.10516 (version of November 3, 2026, sha256 94e0dd44…), p. 7 (§2), pp. 19–26 (§5), pp. 38–39 (C.1), pp. 43–44 (C.3), pp. 48–50 (C.5)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_ConsumerUtilityApprox_UnitDemand_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-!
Goldner, Lundy, Tsilivis, arXiv:2610.10516 (version of November 3, 2026), §2 (p. 7), §5
(pp. 19–26), Appendix C.3–C.5: randomized mechanisms with realized outcomes, the posted-price
and free-lottery single-buyer mechanisms, the mixture `M^{1,m}_het`, the cap program (5.4),
the bisection of C.3, the fair contention rule of Feige and Vondrák, and the description
language of the paper's mechanisms (rounds of posted-price / free-lottery offers, a
participation probability, and contention data) with its semantics `M^{n,m}_het` and the
pre-contention mechanism `M̄^{n,m}_het`.

All internal randomness is finitely supported and is written as a probability mass function
(`PMF`); "every realized outcome" is "every outcome in the support".
-/

namespace ConsumerUtilityApprox.UnitDemand

open MultiItemRev.BundlingOpt

/-! ### Elementary random choices -/

/-- `x` clamped to `[0, 1]`. -/
noncomputable def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

/-- A coin showing `true` with probability `p` (clamped to `[0, 1]`). -/
noncomputable def coin (p : ℝ) : PMF Bool :=
  PMF.ofFintype
    (fun b => if b then ((min (Real.toNNReal p) 1 : ℝ≥0) : ℝ≥0∞)
      else 1 - ((min (Real.toNNReal p) 1 : ℝ≥0) : ℝ≥0∞))
    (by
      rw [Fintype.sum_bool]
      simp only [if_true, Bool.false_eq_true, if_false]
      exact add_tsub_cancel_of_le (by exact_mod_cast min_le_right _ _))

/-- A uniformly random element of `s`, or `none` if `s` is empty. -/
noncomputable def uniformOn {α : Type} (s : Finset α) : PMF (Option α) :=
  if h : s.Nonempty then (PMF.uniformOfFinset s h).map some else PMF.pure none

/-- `k` independent draws, the `i`-th from `f i`. -/
noncomputable def indep {α : Type} : (k : ℕ) → (Fin k → PMF α) → PMF (Fin k → α)
  | 0, _ => PMF.pure (fun i => Fin.elim0 i)
  | k + 1, f => (f 0).bind fun a =>
      (indep k (fun i => f i.succ)).map (fun g => (Fin.cons a g : Fin (k + 1) → α))

/-! ### Two-point posted prices (§2.3, Appendix C.1) -/

/-- A random posted price drawn from at most two options: `p₁` with probability `θ`, `p₂`
with probability `1 − θ` (`θ` clamped to `[0,1]`); `⊤ = ∞` means no offer. -/
structure TwoPointPrice where
  p₁ : ℝ≥0∞
  p₂ : ℝ≥0∞
  θ : ℝ

/-- The law of a two-point price. -/
noncomputable def TwoPointPrice.law (P : TwoPointPrice) : PMF ℝ≥0∞ :=
  (coin P.θ).map fun b => if b then P.p₁ else P.p₂

/-- The two-point price `P` implements `OPT^{1,1}(X; q)` for `X ∼ ν`: its probability of sale
is at most `q` and its expected utility `E[(X − P)^+]` equals `OPT^{1,1}(X; q)`. -/
def IsImplementing (ν : ProbabilityMeasure ℝ≥0) (q : ℝ) (P : TwoPointPrice) : Prop :=
  saleProb1 ν P.law.toMeasure ≤ q ∧ postedUtility1 ν P.law.toMeasure = OPT11 ν q

/-! ### Single-buyer randomized mechanisms -/

/-- A realized single-buyer unit-demand outcome: the item received (if any) and the payment. -/
abbrev SBOutcome (m : ℕ) := Option (Fin m) × ℝ

/-- A randomized single-buyer unit-demand mechanism: the law of the realized outcome for
every report `b ∈ ℝ^m_+`. -/
abbrev SBRand (m : ℕ) := (Fin m → ℝ≥0) → PMF (SBOutcome m)

/-- Value of a realized assignment to a unit-demand buyer of type `v`. -/
def assignValue {m : ℕ} (v : Fin m → ℝ≥0) : Option (Fin m) → ℝ
  | none => 0
  | some j => (v j : ℝ)

namespace SBRand

variable {m : ℕ}

/-- Probability that report `b` receives item `j`. -/
noncomputable def alloc (M : SBRand m) (b : Fin m → ℝ≥0) (j : Fin m) : ℝ :=
  ((M b).toOuterMeasure {ω | ω.1 = some j}).toReal

/-- Expected payment of report `b`. -/
noncomputable def pay (M : SBRand m) (b : Fin m → ℝ≥0) : ℝ :=
  ∑' ω, ((M b) ω).toReal * ω.2

/-- The reduced form `(x, p)` of a randomized single-buyer mechanism. -/
noncomputable def reduced (M : SBRand m) : Mechanism (Fin m) :=
  ⟨fun b j => M.alloc b j, fun b => M.pay b⟩

/-- BIC (= truthful, for one buyer): IC of the reduced form for all types and reports. -/
def IsBIC (M : SBRand m) : Prop := IsIC M.reduced

/-- Ex-post individual rationality: truthful utility is nonnegative in every realized
outcome, for every type. -/
def IsExPostIR (M : SBRand m) : Prop :=
  ∀ v, ∀ ω ∈ (M v).support, 0 ≤ assignValue v ω.1 - ω.2

/-- Nonnegative payments in every realized outcome, for every report. -/
def HasNonnegPayments (M : SBRand m) : Prop :=
  ∀ b, ∀ ω ∈ (M b).support, 0 ≤ ω.2

end SBRand

/-! ### Offers: posted prices and free lotteries -/

/-- A request: the item a buyer asks for and the price charged if it is served. -/
abbrev Request (m : ℕ) := Option (Fin m × ℝ)

/-- Posted-price offer `M^UD`: prices are drawn independently from two-point laws; the buyer
(with values `v`) asks for an item of largest positive surplus, ties uniform, and for nothing
if no surplus is positive. -/
noncomputable def pricingRequest {m : ℕ} (pr : Fin m → TwoPointPrice) (v : Fin m → ℝ≥0) :
    PMF (Request m) :=
  (indep m (fun j => (pr j).law)).bind fun t =>
    (uniformOn (udCandidates v t)).map fun c => c.map fun j => (j, (t j).toReal)

/-- Free-lottery offer `M^free` with lotteries `ℓ` (clamped to `[0,1]`): the buyer picks an
item maximizing `ℓ_j v_j` if positive (ties uniform) and receives it free with probability
`ℓ_j`. -/
noncomputable def lotteryRequest {m : ℕ} (ℓ : Fin m → ℝ) (v : Fin m → ℝ≥0) :
    PMF (Request m) :=
  (uniformOn (lotCandidates v (fun j => clamp01 (ℓ j)))).bind fun c =>
    match c with
    | none => PMF.pure none
    | some j => (coin (clamp01 (ℓ j))).map fun s => if s then some (j, 0) else none

/-- The realized outcome of a request that is served. -/
def Request.toOutcome {m : ℕ} : Request m → SBOutcome m
  | none => (none, 0)
  | some (j, π) => (some j, π)

/-- The posted-price mechanism `M^UD` with two-point prices `pr`. -/
noncomputable def postedPriceMech {m : ℕ} (pr : Fin m → TwoPointPrice) : SBRand m :=
  fun v => (pricingRequest pr v).map Request.toOutcome

/-- The free-lottery mechanism with lotteries `ℓ`; `M^free_h` is
`freeLotteryMech (lotteryProb λ h)` and `M^free_0` is `freeLotteryMech 0`. -/
noncomputable def freeLotteryMech {m : ℕ} (ℓ : Fin m → ℝ) : SBRand m :=
  fun v => (lotteryRequest ℓ v).map Request.toOutcome

/-- The single-buyer mechanism `M^{1,m}_het` (p. 24): with probability `e/(3e − 2)` the
posted-price mechanism with prices `pr`, otherwise (probability `2(e − 1)/(3e − 2)`) the
free-lottery mechanism with lotteries `ℓ`, independently of the report. -/
noncomputable def hetMech {m : ℕ} (pr : Fin m → TwoPointPrice) (ℓ : Fin m → ℝ) : SBRand m :=
  fun v => (coin (Real.exp 1 / (3 * Real.exp 1 - 2))).bind fun b =>
    if b then postedPriceMech pr v else freeLotteryMech ℓ v

/-! ### The cap program (5.4) and the bisection of Appendix C.3 -/

/-- Caps `q_j ≥ 0` with `Σ_j q_j ≤ 1`. -/
def IsFeasibleCaps {m : ℕ} (q : Fin m → ℝ) : Prop :=
  (∀ j, 0 ≤ q j) ∧ ∑ j, q j ≤ 1

/-- The objective of the cap program (5.4):
`Σ_j (OPT^{1,1}(V_j; q_j) − (e/(e − 1)) λ_j q_j)`. -/
noncomputable def capObjective {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0)
    (lam q : Fin m → ℝ) : ℝ :=
  ∑ j, (OPT11 (G j) (q j) - Real.exp 1 / (Real.exp 1 - 1) * lam j * q j)

/-- The optimal value `R_λ` of the cap program (5.4). -/
noncomputable def capOpt {m : ℕ} (G : Fin m → ProbabilityMeasure ℝ≥0) (lam : Fin m → ℝ) : ℝ :=
  sSup {r | ∃ q, IsFeasibleCaps q ∧ capObjective G lam q = r}

/-- One bisection step on `[a, b]` (Appendix C.3): with midpoint `c`, move the lower endpoint
to `c` if `f c > 2c`, the upper endpoint otherwise. -/
noncomputable def bisectStep (f : ℝ → ℝ) (ab : ℝ × ℝ) : ℝ × ℝ :=
  if f ((ab.1 + ab.2) / 2) > 2 * ((ab.1 + ab.2) / 2) then ((ab.1 + ab.2) / 2, ab.2)
  else (ab.1, (ab.1 + ab.2) / 2)

/-- Number of bisection steps (one evaluation of `f` each) until `b − a ≤ γ`, starting from
`[0, 1]`: the least `k` with `2^{−k} ≤ γ`. -/
noncomputable def bisectSteps (γ : ℝ) : ℕ := ⌈Real.logb 2 (1 / γ)⌉₊

/-- The final interval `[a, b]` of the bisection on `[0, 1]` with tolerance `γ`. -/
noncomputable def bisect (f : ℝ → ℝ) (γ : ℝ) : ℝ × ℝ :=
  (bisectStep f)^[bisectSteps γ] (0, 1)

/-! ### Fair contention resolution (§5.2, Appendix C.5) -/

/-- The fair rule of Feige and Vondrák: the probability that requester `i` is selected for
item `j` when the set of requesters is `A`, using the announced request probabilities `Q`. -/
noncomputable def fairSelProb {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (A : Finset (Fin n)) (i : Fin n) : ℝ :=
  if i ∉ A then 0
  else if A.card = 1 then 1
  else if ∑ k, Q k j = 0 then 1 / (A.card : ℝ)
  else (1 / ∑ k, Q k j) *
    ((∑ k ∈ A.erase i, Q k j) / ((A.card : ℝ) - 1) +
      (∑ k ∈ Finset.univ \ A, Q k j) / (A.card : ℝ))

/-- `c_j` of (5.11). -/
noncomputable def selectionConst {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m) : ℝ :=
  if ∑ k, Q k j = 0 then 1 else (1 - ∏ k, (1 - Q k j)) / ∑ k, Q k j

/-- The fair rule as a random choice (`none` if there is no requester); if the weights do not
form a probability vector (ill-formed `Q`), a requester is chosen uniformly. -/
noncomputable def fairSelect {n m : ℕ} (Q : Fin n → Fin m → ℝ) (j : Fin m)
    (A : Finset (Fin n)) : PMF (Option (Fin n)) :=
  if h : ∑ i, ENNReal.ofReal (fairSelProb Q j A i) = 1 then
    (PMF.ofFintype (fun i => ENNReal.ofReal (fairSelProb Q j A i)) h).map some
  else uniformOn A

/-! ### Multi-buyer randomized mechanisms -/

/-- A realized outcome: an assignment (buyer `i` receives `a i`, at most one item) and
payments. -/
abbrev Outcome (n m : ℕ) := (Fin n → Option (Fin m)) × (Fin n → ℝ)

/-- A randomized multi-buyer mechanism: the law of the realized outcome for every reported
profile. -/
abbrev RandMech (n m : ℕ) := Profile n m → PMF (Outcome n m)

namespace RandMech

variable {n m : ℕ}

/-- The reduced form of a randomized mechanism. -/
noncomputable def reduced (M : RandMech n m) : RMech n m :=
  ⟨fun v i j => ((M v).toOuterMeasure {ω | ω.1 i = some j}).toReal,
   fun v i => ∑' ω, ((M v) ω).toReal * ω.2 i⟩

/-- BIC (of the reduced form). -/
def IsBIC (I : Instance n m) (M : RandMech n m) : Prop := M.reduced.IsBIC I

/-- Ex-post individual rationality: for every profile, truthful utility of every buyer is
nonnegative in every realized outcome. -/
def IsExPostIR (M : RandMech n m) : Prop :=
  ∀ v, ∀ ω ∈ (M v).support, ∀ i, 0 ≤ assignValue (v i) (ω.1 i) - ω.2 i

/-- Matching feasibility in every realized outcome: no item goes to two buyers (each buyer
receives at most one item by the type of outcomes). -/
def IsMatchingFeasible (M : RandMech n m) : Prop :=
  ∀ v, ∀ ω ∈ (M v).support, ∀ i i' j, ω.1 i = some j → ω.1 i' = some j → i = i'

/-- Nonnegative payments in every realized outcome. -/
def HasNonnegPayments (M : RandMech n m) : Prop :=
  ∀ v, ∀ ω ∈ (M v).support, ∀ i, 0 ≤ ω.2 i

/-- Residual surplus `U(M)` of the reduced form. -/
noncomputable def U (I : Instance n m) (M : RandMech n m) : ℝ := M.reduced.U I

end RandMech

/-! ### The description language of the paper's mechanisms -/

/-- A finite description of a mechanism of the paper's family (§5.1.1, §5.2, Appendix C.5):
`T` rounds; a participation probability `ρ`; for buyer `i` and round `t < T` the probability
`w i t` of the pricing branch, the two-point price laws `price i t j` and the free lotteries
`lottery i t j`; the announced request probabilities `Q i j` used by the fair contention rule;
and the service probabilities `σ j`. -/
structure MechDescription (n m : ℕ) where
  T : ℕ
  ρ : ℝ
  w : Fin n → ℕ → ℝ
  price : Fin n → ℕ → Fin m → TwoPointPrice
  lottery : Fin n → ℕ → Fin m → ℝ
  Q : Fin n → Fin m → ℝ
  σ : Fin m → ℝ

namespace MechDescription

variable {n m : ℕ}

/-- Buyer `i`'s request when reporting `v`: with probability `ρ` the buyer participates, draws
a uniform round `t < T`, and faces the pricing offer (probability `w i t`) or the free-lottery
offer of that round; otherwise (or if `T = 0`) no request. -/
noncomputable def request (D : MechDescription n m) (i : Fin n) (v : Fin m → ℝ≥0) :
    PMF (Request m) :=
  if h : (Finset.range D.T).Nonempty then
    (coin D.ρ).bind fun part =>
      if part then
        (PMF.uniformOfFinset (Finset.range D.T) h).bind fun t =>
          (coin (D.w i t)).bind fun br =>
            if br then pricingRequest (D.price i t) v else lotteryRequest (D.lottery i t) v
      else PMF.pure none
  else PMF.pure none

/-- The announced request probabilities, clamped to `[0,1]`. -/
noncomputable def Q' (D : MechDescription n m) : Fin n → Fin m → ℝ :=
  fun i j => clamp01 (D.Q i j)

/-- The buyers requesting item `j`. -/
noncomputable def requesters (req : Fin n → Request m) (j : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun i => (req i).map Prod.fst = some j

/-- `M^{n,m}_het`: buyers request independently; for each item independently the fair rule
selects one requester, who is served with probability `σ j` (independently), receives the
item and pays the price of the request; unserved requests pay nothing. -/
noncomputable def law (D : MechDescription n m) : RandMech n m := fun v =>
  (indep n (fun i => D.request i (v i))).bind fun req =>
    (indep m (fun j =>
        (fairSelect D.Q' j (requesters req j)).bind fun s =>
          (coin (D.σ j)).map fun serve => if serve then s else none)).map fun sel =>
      (fun i => match req i with
        | some (j, _) => if sel j = some i then some j else none
        | none => none,
       fun i => match req i with
        | some (j, π) => if sel j = some i then π else 0
        | none => 0)

/-- The pre-contention mechanism `M̄^{n,m}_het`: every request is granted. -/
noncomputable def preLaw (D : MechDescription n m) : RandMech n m := fun v =>
  (indep n (fun i => D.request i (v i))).map fun req =>
    (fun i => (req i).map Prod.fst, fun i => match req i with
      | some (_, π) => π
      | none => 0)

end MechDescription

end ConsumerUtilityApprox.UnitDemand


