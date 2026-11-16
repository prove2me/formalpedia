-- Prove2me | Definitions.Def_MoneyBurningSurplus_Harmonic_Supplement_Bayes
-- name    : MoneyBurningSurplus_Harmonic_Supplement_Bayes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:56:09.064445+00:00
-- url     : https://prove2.me/theorems/04fce55a-c04c-4f8f-ae7e-29a1ef453479
-- title:
--   App. C — finite product priors, interim values, assignment LP and the Bayesian harmonic-sampling mechanism
-- statement:
--   **Prior and algorithm.** Agent $i$ has a finite type set $T_i$; type $a\in T_i$ has a nonnegative valuation $a:O\to\mathbb R_{\ge0}$ and prior mass $f_i(a)>0$, with $\sum_a f_i(a)=1$; the prior is $D=\prod_iD_i$. An allocation algorithm $A$ (possibly randomized, not necessarily truthful) maps every report profile to a distribution $A(v)$ on $O$. Its welfare is $SW_A=\mathbb E_{v\sim D}\big[\sum_o A(v)(o)\sum_iv_i(o)\big]$ and its interim values are
--
--   $$G_i(a,b)=\mathbb E_{v_{-i}\sim D_{-i}}\Big[\sum_oA(b,v_{-i})(o)\,a(o)\Big],\qquad a,b\in T_i.\tag{6}$$
--
--   **LP.** At level $q$, the assignment LP (7) maximizes $\sum_{a,b}x_i(a,b)G_i(a,b)$ over $x_i\ge0$ with $\sum_bx_i(a,b)\le qf_i(a)$ and $\sum_ax_i(a,b)\le f_i(b)$; its dual (8) minimizes $q\sum_af_i(a)u_i(a)+\sum_bf_i(b)\pi_i(b)$ over $u_i,\pi_i\ge0$ with $u_i(a)+\pi_i(b)\ge G_i(a,b)$. An **admissible LP choice** fixes, for every $q\in(0,1)$ and agent $i$, an optimum $x_i^q$ of (7) with every row saturated ($\sum_bx_i^q(a,b)=qf_i(a)$) and an optimum $(u_i^q,\pi_i^q)$ of (8). At $q=0$ the convention is $\pi_i^0=0$, $u_i^0(a)=\max_bG_i(a,b)$. Write $U(q)=\sum_i\sum_af_i(a)u_i^q(a)$ and $g_n(q)=\sum_{k=0}^{n-1}(1-q)^k$.
--
--   **The mechanism $M_q$.** For $0<q<1$ set $K_i^q(a,b)=x_i^q(a,b)/(qf_i(a))$ and $\rho_i^q(b)=(f_i(b)-\sum_ax_i^q(a,b))/(1-q)$. On reports $b$: if $q=0$, choose an agent $I$ uniformly, give her the surrogate $\mathrm{sel}_I(b_I)\in\arg\max_cG_I(b_I,c)$ (a fixed rule), draw the others' surrogates from $D_{-I}$, draw $o\sim A(\tilde v)$, and charge nothing. If $q>0$, draw the active set $R$ with $\Pr[R=S]=q^{|S|}(1-q)^{n-|S|}/(1-(1-q)^n)$ for $S\neq\emptyset$, surrogates independently $\tilde v_i\sim K_i^q(b_i,\cdot)$ for $i\in R$ and $\tilde v_i\sim\rho_i^q$ for $i\notin R$, and $o\sim A(\tilde v)$; inactive agents pay $0$ and an active agent with report $a$ and surrogate $c$ pays
--
--   $$p_i=\begin{cases}\pi_i^q(c)\,a(o)/G_i(a,c),&G_i(a,c)>0,\\0,&G_i(a,c)=0.\end{cases}\tag{14}$$
--
--   **The mixture $M_{D,\varepsilon}$.** With $L=\lceil n/\varepsilon\rceil$, $q_j=j/L$ and $C_{n,L}=\frac1L\sum_{j=0}^{L-1}g_n(q_j)$, draw $J=j\in\{0,\dots,L-1\}$ with probability $g_n(q_j)/(LC_{n,L})$ and run $M_{q_J}$.
--
--   **Properties of a finite lottery.** For a mechanism given by seed probabilities at each report profile, a seed's outcome and its payments: the interim utility of agent $i$ with true type $a$ reporting $b$ is $\mathbb E_{v_{-i}\sim D_{-i}}\mathbb E[a(o)-p_i]$ with the others truthful; **BIC** means reporting the true type maximizes it; **EPIR** means every seed of positive probability at truthful reports gives every agent $v_i(o)-p_i\ge0$; **nonnegative payments** means every such seed charges $p_i\ge0$; the **expected residual surplus** is $\mathbb E_{v\sim D}\mathbb E\big[\sum_i(v_i(o)-p_i)\big]$.
--
--   **Formalization Note** Type sets are finite types `Ty i` with a valuation map `val i`; the paper's types are valuations themselves (the case of an injective map), and nothing requires injectivity. A seed of $M_q$ is a triple $(R,\tilde v,o)$, with $R=\{I\}$ at $q=0$; all expectations are finite sums. The LP data are fixed functions of the level, chosen before reports.
-- source:
--   Tomer Ezra, Money Burning Mechanism Design: From Welfare to Surplus, STOC 2027 submission #585 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/585.pdf, App. C.1 (prior, SW_A, interim values (6)), PDF p. 21 (printed p. 20); App. C.2 (LP (7), dual (8), q = 0 convention, (11), (12), (13), mechanism steps 1–4 and payment (14)), PDF pp. 22–23 (printed pp. 21–22); BIC and EPIR, §2 PDF p. 7 and App. C.1

import Mathlib

noncomputable section

namespace MoneyBurningSurplus.Harmonic.Supplement

open Finset

/-! Appendix C (PDF 21–25): finite-support product priors, interim values, the assignment LP
and its dual, and the Bayesian harmonic-sampling mechanism.

Agent `i`'s finite type set is the finite type `Ty i`; a type `a : Ty i` has the valuation
`val i a : O → ℝ` and prior mass `f i a`. A type profile is `(i : Fin n) → Ty i`. -/

section Prior

variable {n : ℕ} {O : Type*} [Fintype O]
variable {Ty : Fin n → Type*} [∀ i, Fintype (Ty i)] [∀ i, DecidableEq (Ty i)]

/-- A finite-support product prior over nonnegative valuations (App. C.1, PDF 21): every type's
valuation is nonnegative, every type has positive mass `f_i(a) > 0`, and each `f_i` sums to one. -/
def IsFiniteProductPrior (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ) :
    Prop :=
  (∀ i a o, 0 ≤ val i a o) ∧ (∀ i a, 0 < f i a) ∧ ∀ i, ∑ a, f i a = 1

/-- Prior probability `∏_i f_i(v_i)` of the type profile `v` under `D = ∏_i D_i`. -/
def priorWeight (f : (i : Fin n) → Ty i → ℝ) (v : (i : Fin n) → Ty i) : ℝ :=
  ∏ i, f i (v i)

/-- Probability `∏_{j ≠ i} f_j(v_j)` of the other agents' types under `D_{-i}`. -/
def othersWeight (f : (i : Fin n) → Ty i → ℝ) (i : Fin n) (v : (i : Fin n) → Ty i) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, f j (v j)

/-- A (possibly randomized) allocation algorithm, given by its outcome distribution `A(v)` at
every profile of reports: a probability vector on `O`. -/
def IsAllocAlgorithm (A : ((i : Fin n) → Ty i) → O → ℝ) : Prop :=
  ∀ v, (∀ o, 0 ≤ A v o) ∧ ∑ o, A v o = 1

/-- Interim value (6): `G_i(a, b) = E_{v_{-i} ∼ D_{-i}, r}[a(A^r(b, v_{-i}))]`, type `a`'s expected
value when agent `i` reports `b` to `A` and the others' reports follow `D_{-i}`. -/
def interimValue (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (i : Fin n) (a b : Ty i) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : (j : Fin n) → Ty j => v i = b),
    othersWeight f i v * ∑ o, A v o * val i a o

/-- `SW_A = E_{v ∼ D, r}[∑_i v_i(A^r(v))]` (App. C.1, PDF 21). -/
def expectedWelfareA (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ) : ℝ :=
  ∑ v, priorWeight f v * ∑ o, A v o * ∑ i, val i (v i) o

end Prior

section LP

variable {τ : Type*} [Fintype τ]

/-- Feasibility in the assignment LP (7) at level `q`: `x ≥ 0`, row sums `∑_b x(a,b) ≤ q f(a)`,
column sums `∑_a x(a,b) ≤ f(b)`. -/
def IsAssignFeasible (f : τ → ℝ) (q : ℝ) (x : τ → τ → ℝ) : Prop :=
  (∀ a b, 0 ≤ x a b) ∧ (∀ a, ∑ b, x a b ≤ q * f a) ∧ ∀ b, ∑ a, x a b ≤ f b

/-- Objective `∑_{a,b} x(a,b) G(a,b)` of the assignment LP (7). -/
def assignValue (G : τ → τ → ℝ) (x : τ → τ → ℝ) : ℝ :=
  ∑ a, ∑ b, x a b * G a b

/-- `x` is an optimum of (7) at level `q` with every row saturated, `∑_b x(a,b) = q f(a)`
(App. C.2, PDF 22). -/
def IsRowSaturatedOptimum (f : τ → ℝ) (G : τ → τ → ℝ) (q : ℝ) (x : τ → τ → ℝ) : Prop :=
  IsAssignFeasible f q x ∧ (∀ a, ∑ b, x a b = q * f a) ∧
    ∀ y, IsAssignFeasible f q y → assignValue G y ≤ assignValue G x

/-- Feasibility in the dual (8): `u, π ≥ 0` and `u(a) + π(b) ≥ G(a,b)`. -/
def IsDualFeasible (G : τ → τ → ℝ) (u π : τ → ℝ) : Prop :=
  (∀ a, 0 ≤ u a) ∧ (∀ b, 0 ≤ π b) ∧ ∀ a b, G a b ≤ u a + π b

/-- Objective `q ∑_a f(a) u(a) + ∑_b f(b) π(b)` of the dual (8). -/
def dualValue (f : τ → ℝ) (q : ℝ) (u π : τ → ℝ) : ℝ :=
  q * ∑ a, f a * u a + ∑ b, f b * π b

/-- `(u, π)` is an optimal solution of the dual (8) at level `q`. -/
def IsDualOptimum (f : τ → ℝ) (G : τ → τ → ℝ) (q : ℝ) (u π : τ → ℝ) : Prop :=
  IsDualFeasible G u π ∧
    ∀ u' π', IsDualFeasible G u' π' → dualValue f q u π ≤ dualValue f q u' π'

end LP

section Mechanism

variable {n : ℕ} {O : Type*} [Fintype O]
variable {Ty : Fin n → Type*} [∀ i, Fintype (Ty i)] [∀ i, DecidableEq (Ty i)]

/-- An admissible choice of LP solutions, one for every level `q ∈ (0,1)` and every agent
(App. C.2, PDF 22): `x q i` is a row-saturated optimum of (7) and `(u q i, π q i)` an optimum of
(8), both for the interim table `G_i`; the choice is fixed in advance, independent of reports. -/
def IsAdmissibleLPChoice (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ)
    (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (u π : ℝ → (i : Fin n) → Ty i → ℝ) : Prop :=
  ∀ q ∈ Set.Ioo (0 : ℝ) 1, ∀ i,
    IsRowSaturatedOptimum (f i) (interimValue val f A i) q (x q i) ∧
      IsDualOptimum (f i) (interimValue val f A i) q (u q i) (π q i)

/-- The level-zero convention (App. C.2, PDF 22): `π_i^0 = 0` and `u_i^0(a) = max_b G_i(a,b)`. -/
def IsLevelZeroConvention (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (u π : ℝ → (i : Fin n) → Ty i → ℝ) : Prop :=
  ∀ i, (∀ b, π 0 i b = 0) ∧ ∀ a, IsGreatest (Set.range (interimValue val f A i a)) (u 0 i a)

/-- A fixed rule choosing, for every true type `a` of agent `i`, a surrogate in
`argmax_b G_i(a, b)` (step 2 of `M_{D,ε}`, PDF 23). -/
def IsArgmaxRule (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (sel : (i : Fin n) → Ty i → Ty i) : Prop :=
  ∀ i a b, interimValue val f A i a b ≤ interimValue val f A i a (sel i a)

/-- `U(q) = ∑_i ∑_a f_i(a) u_i^q(a)` (App. C.2, PDF 22). -/
def dualUtility (f : (i : Fin n) → Ty i → ℝ) (u : ℝ → (i : Fin n) → Ty i → ℝ) (q : ℝ) : ℝ :=
  ∑ i, ∑ a, f i a * u q i a

/-- `g_n(q) = ∑_{k=0}^{n-1} (1 − q)^k` (12). -/
def gNorm (n : ℕ) (q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 - q) ^ k

/-- Law of the active set, Bernoulli-`q` conditioned on being nonempty (step 3, PDF 23):
`q^{|S|} (1 − q)^{n − |S|} / (1 − (1 − q)^n)` for `S ≠ ∅`, and `0` for `S = ∅`. -/
def activeSetProb (n : ℕ) (q : ℝ) (S : Finset (Fin n)) : ℝ :=
  if S.Nonempty then q ^ S.card * (1 - q) ^ (n - S.card) / (1 - (1 - q) ^ n) else 0

/-- Active surrogate law (11): `K_i^q(a, b) = x_i^q(a, b) / (q f_i(a))`. -/
def surrogateK (f : (i : Fin n) → Ty i → ℝ) (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (q : ℝ)
    (i : Fin n) (a b : Ty i) : ℝ :=
  x q i a b / (q * f i a)

/-- Inactive surrogate law (11): `ρ_i^q(b) = (f_i(b) − ∑_a x_i^q(a, b)) / (1 − q)`. -/
def surrogateRho (f : (i : Fin n) → Ty i → ℝ) (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (q : ℝ)
    (i : Fin n) (b : Ty i) : ℝ :=
  (f i b - ∑ a, x q i a b) / (1 - q)

/-- Internal randomness of the fixed-level mechanism `M_q`: a set of agents `R` (the active set
for `q > 0`, the singleton `{I}` of the chosen agent for `q = 0`), a surrogate profile `ṽ`, and
the outcome `o` drawn from `A(ṽ)`. -/
abbrev LevelSeed (n : ℕ) (O : Type*) (Ty : Fin n → Type*) :=
  Finset (Fin n) × ((i : Fin n) → Ty i) × O

/-- Probability of the seed `(R, ṽ, o)` in `M_q` at the reported type profile `b`
(steps 2–4, PDF 23). For `q = 0`: `R = {I}` with `I` uniform, `ṽ_I = sel_I(b_I)`, the other
surrogates drawn from `D_{-I}`. For `q > 0`: `R` the conditioned Bernoulli-`q` active set,
`ṽ_i ∼ K_i^q(b_i, ·)` for `i ∈ R` and `ṽ_i ∼ ρ_i^q` for `i ∉ R`, independently. In both cases
`o ∼ A(ṽ)`. -/
def levelProb (f : (i : Fin n) → Ty i → ℝ) (A : ((i : Fin n) → Ty i) → O → ℝ)
    (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (sel : (i : Fin n) → Ty i → Ty i) (q : ℝ)
    (b : (i : Fin n) → Ty i) (s : LevelSeed n O Ty) : ℝ :=
  if q = 0 then
    (if s.1.card = 1 then
      (1 / (n : ℝ)) * ∏ i, (if i ∈ s.1 then (if s.2.1 i = sel i (b i) then 1 else 0)
        else f i (s.2.1 i))
    else 0) * A s.2.1 s.2.2
  else
    activeSetProb n q s.1 *
      (∏ i, if i ∈ s.1 then surrogateK f x q i (b i) (s.2.1 i) else surrogateRho f x q i (s.2.1 i)) *
      A s.2.1 s.2.2

/-- Payment (14) of agent `i` in `M_q` at reports `b` and seed `(R, ṽ, o)`: zero for `q = 0`
and for inactive agents; an active agent with report `a = b_i` and surrogate `c = ṽ_i` pays
`π_i^q(c) a(o) / G_i(a, c)` if `G_i(a, c) > 0`, and `0` if `G_i(a, c) = 0`. -/
def levelPay (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (π : ℝ → (i : Fin n) → Ty i → ℝ) (q : ℝ)
    (b : (i : Fin n) → Ty i) (s : LevelSeed n O Ty) (i : Fin n) : ℝ :=
  if q = 0 then 0
  else if i ∈ s.1 then
    (if 0 < interimValue val f A i (b i) (s.2.1 i) then
      π q i (s.2.1 i) * val i (b i) s.2.2 / interimValue val f A i (b i) (s.2.1 i)
    else 0)
  else 0

end Mechanism

section Lottery

/-! Properties of a Bayesian mechanism presented as a finite lottery over internal seeds `σ`:
`prob b s` is the probability of seed `s` at the report profile `b`, `out s` the outcome and
`pay b s i` agent `i`'s payment. -/

variable {n : ℕ} {O : Type*}
variable {Ty : Fin n → Type*} [∀ i, Fintype (Ty i)] [∀ i, DecidableEq (Ty i)]
variable {σ : Type*} [Fintype σ]

/-- Interim expected utility of agent `i` with true type `a` who reports `b`, the others
reporting truthfully with types drawn from `D_{-i}`: the expectation over `v_{-i}` and the
mechanism's internal randomness of `a(o) − p_i`. -/
def lotteryInterimUtility (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (prob : ((i : Fin n) → Ty i) → σ → ℝ) (out : σ → O)
    (pay : ((i : Fin n) → Ty i) → σ → Fin n → ℝ) (i : Fin n) (a b : Ty i) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v : (j : Fin n) → Ty j => v i = b),
    othersWeight f i v * ∑ s, prob v s * (val i a (out s) - pay v s i)

/-- Bayesian incentive compatibility (App. C.1): for every agent, true type `a` and report `b`,
the interim utility of reporting `b` is at most that of reporting `a`. -/
def IsBIC (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (prob : ((i : Fin n) → Ty i) → σ → ℝ) (out : σ → O)
    (pay : ((i : Fin n) → Ty i) → σ → Fin n → ℝ) : Prop :=
  ∀ i (a b : Ty i),
    lotteryInterimUtility val f prob out pay i a b ≤ lotteryInterimUtility val f prob out pay i a a

/-- Ex-post individual rationality: at truthful reports `v`, every seed of positive probability
gives every agent `v_i(o) − p_i ≥ 0` (§2, PDF 7). -/
def IsLotteryEPIR (val : (i : Fin n) → Ty i → O → ℝ)
    (prob : ((i : Fin n) → Ty i) → σ → ℝ) (out : σ → O)
    (pay : ((i : Fin n) → Ty i) → σ → Fin n → ℝ) : Prop :=
  ∀ v s, 0 < prob v s → ∀ i, 0 ≤ val i (v i) (out s) - pay v s i

/-- Nonnegative payments: every seed of positive probability charges every agent `p_i ≥ 0`. -/
def HasLotteryNonnegPayments (prob : ((i : Fin n) → Ty i) → σ → ℝ)
    (pay : ((i : Fin n) → Ty i) → σ → Fin n → ℝ) : Prop :=
  ∀ v s, 0 < prob v s → ∀ i, 0 ≤ pay v s i

/-- Expected residual surplus `E_{v ∼ D, (o,p)}[∑_i (v_i(o) − p_i)]` under truthful reports. -/
def lotterySurplus (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (prob : ((i : Fin n) → Ty i) → σ → ℝ) (out : σ → O)
    (pay : ((i : Fin n) → Ty i) → σ → Fin n → ℝ) : ℝ :=
  ∑ v, priorWeight f v * ∑ s, prob v s * ∑ i, (val i (v i) (out s) - pay v s i)

end Lottery

section Mixture

variable {n : ℕ} {O : Type*} [Fintype O]
variable {Ty : Fin n → Type*} [∀ i, Fintype (Ty i)] [∀ i, DecidableEq (Ty i)]

/-- `L = ⌈n / ε⌉` levels (13). -/
def numLevels (n : ℕ) (ε : ℝ) : ℕ := ⌈(n : ℝ) / ε⌉₊

/-- Grid level `q_j = j / L` (13). -/
def gridLevel (L : ℕ) (j : ℕ) : ℝ := (j : ℝ) / (L : ℝ)

/-- `C_{n,L} = (1/L) ∑_{j=0}^{L-1} g_n(q_j)` (13). -/
def gridConst (n L : ℕ) : ℝ :=
  (1 / (L : ℝ)) * ∑ j ∈ Finset.range L, gNorm n (gridLevel L j)

/-- Mixing probability `Pr[J = j] = g_n(q_j) / (L C_{n,L})` (step 1, PDF 23). -/
def levelWeight (n L : ℕ) (j : ℕ) : ℝ :=
  gNorm n (gridLevel L j) / ((L : ℝ) * gridConst n L)

/-- Seed probabilities of `M_{D,ε}`: `J = j` with `Pr[J = j]`, then the seed of `M_{q_j}`. -/
def mixtureProb (f : (i : Fin n) → Ty i → ℝ) (A : ((i : Fin n) → Ty i) → O → ℝ)
    (x : ℝ → (i : Fin n) → Ty i → Ty i → ℝ) (sel : (i : Fin n) → Ty i → Ty i) (ε : ℝ)
    (b : (i : Fin n) → Ty i) (s : Fin (numLevels n ε) × LevelSeed n O Ty) : ℝ :=
  levelWeight n (numLevels n ε) s.1 *
    levelProb f A x sel (gridLevel (numLevels n ε) s.1) b s.2

/-- Payments of `M_{D,ε}`: those of `M_{q_J}`. -/
def mixturePay (val : (i : Fin n) → Ty i → O → ℝ) (f : (i : Fin n) → Ty i → ℝ)
    (A : ((i : Fin n) → Ty i) → O → ℝ) (π : ℝ → (i : Fin n) → Ty i → ℝ) (ε : ℝ)
    (b : (i : Fin n) → Ty i) (s : Fin (numLevels n ε) × LevelSeed n O Ty) (i : Fin n) : ℝ :=
  levelPay val f A π (gridLevel (numLevels n ε) s.1) b s.2 i

/-- Outcome of a seed of `M_q`. -/
def levelOut (s : LevelSeed n O Ty) : O := s.2.2

/-- Outcome of a seed of `M_{D,ε}`. -/
def mixtureOut (ε : ℝ) (s : Fin (numLevels n ε) × LevelSeed n O Ty) : O := s.2.2.2

end Mixture

end MoneyBurningSurplus.Harmonic.Supplement


