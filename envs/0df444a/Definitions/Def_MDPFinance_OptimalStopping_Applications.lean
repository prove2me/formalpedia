-- Prove2me | Definitions.Def_MDPFinance_OptimalStopping_Applications
-- name    : MDPFinance_OptimalStopping_Applications
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:44:45.723331+00:00
-- url     : https://prove2.me/theorems/8c597d92-ce3f-4551-b5e2-fa5673b9463d
-- title:
--   The house selling, secretary and Bayesian stopping problems of §10.3, with the likelihood ratio order and MTP2
-- statement:
--   The three worked problems of §10.3, each with the concrete data the book lists, so that
--   Theorems 10.3.1, 10.3.3, 10.3.4 and 10.3.6 and Proposition 10.3.2 are statements about those
--   problems rather than about free parameters.
--
--   **House selling** (§10.3.1, p. 316). Each week an offer arrives, i.i.d. with law $Q$ on $[m,M]$
--   where $0 < m < M$; rejecting costs $c > 0$ in maintenance. Data: $E := [m,M]$,
--   $Q^X(\cdot|x) := Q(\cdot)$, $c(x) \equiv -c$, $g(x) := x$. For the *unbounded horizon* version the
--   book requires $\beta \in (0,1)$ — strictly less than one, which is what makes Assumption (B) hold
--   (p. 317) — and that is stronger than the $\beta \in (0,1]$ of the general stationary problem.
--
--   **Secretary** (§10.3.2, p. 321). $N$ candidates are interviewed in random order, decisions are
--   irrevocable, and only relative ranks are observed. Data: $E := \{1,\dots,N,N+1\}$ where $x$ is the
--   time point at which a candidate is leading and $N+1$ is absorbing; $c(x) \equiv 0$;
--   $g(N+1) := 0$ and $g(x) := x/N$; $\beta := 1$; and the transition probabilities
--   $$ q^X(y|x) = \frac{x}{y(y-1)},\ 1 \le x < y \le N; \qquad q^X(N+1|x) = \frac{x}{N},\ 1 \le x \le N;
--   \qquad q^X(N+1|N+1) = 1 \tag{10.4} $$
--   with all others zero. The value functions satisfy $V_{N-1}(x) = x/N$ and
--   $V_n(x) = \max\{x/N,\ \sum_{y=x+1}^N \frac{x}{y(y-1)}V_{n+1}(y)\}$. Finally
--   $h(x) := \frac1x + \frac1{x+1} + \dots + \frac1{N-1}$ and
--   $$ k^* := \inf\{k \in \{1,\dots,N-2\} \mid h(k) > 1 \ge h(k+1)\} \tag{10.5} $$
--   (p. 322); $h$ is decreasing with $h(1) > 1 > h(N-1)$, which is what makes the set nonempty. Both
--   are indexed by the horizon $N$ as well, so that Theorem 10.3.3's $N \to \infty$ limit is
--   statable.
--
--   **Bayesian stopping** (§10.3.4-10.3.5, pp. 323-326). The offers are i.i.d. with a law $Q(\cdot|\theta)$
--   depending on an unknown $\theta \in \Theta \subseteq \mathbb{R}$ and density $q(z|\theta)$,
--   handled by §5.4's filtered Markov Decision Model. The state is $(x,i) \in \mathbb{R} \times I$ —
--   current offer and relevant information — with update $\hat\Phi(i,z)$, posterior
--   $\hat\mu(\cdot|i)$, cost $c$ of continuing, stopping reward $x$ and $\beta = 1$; the value
--   functions are $J_0(x,i) = x$ and $J_n(x,i) = \max\{x, c_n(i)\}$ with
--   $c_n(i) = -c + \iint J_{n-1}(z,\hat\Phi(i,z))Q(dz|\theta)\hat\mu(d\theta|i)$.
--
--   Two order-theoretic notions are restated locally, as §5.4 defines them. $\mu \le_{lr} \nu$, the
--   **likelihood ratio order**: the two have densities $f$, $g$ against a common reference measure with
--   $f(\theta')g(\theta) \le f(\theta)g(\theta')$ for $\theta \le \theta'$ — strictly stronger than
--   stochastic dominance. And $q$ is **$MTP_2$** in $z$ and $\theta$:
--   $q(z|\theta)q(z'|\theta') \le q(z \vee z'|\theta \vee \theta')q(z \wedge z'|\theta \wedge \theta')$.
--   The order on $I$ is $i \le i' :\Leftrightarrow \hat\mu(\cdot|i) \le_{lr} \hat\mu(\cdot|i')$ and on
--   $E = \mathbb{R} \times I$ it is $(x,i) \le (x',i')$ iff $x \le x'$ and $i \le i'$.
--
--   Example 10.3.5 (p. 325) is the conjugate instance Theorem 10.3.6 is about: $c = 0$, exponential
--   offers $q(z|\theta) = \theta^{-1}e^{-z/\theta}$, sufficient statistic $i = (s,n)$ with
--   $\hat\Phi((s,n),z) = (s+z,n+1)$, and an **Inverse Gamma** prior with $a > 1$, $b > 0$. The
--   posterior predictive is then the Second Order Beta law $\hat Q^Z(\cdot|s,n) = Be(1,a+n,s+b)$, with
--   density $(n+a)(s+b)^{n+a}/(z+s+b)^{n+a+1}$ on $z > 0$, and the prior is carried by its two
--   parameters rather than as an abstract measure: everything Theorem 10.3.6 speaks about is a
--   function of $a$ and $b$ through that closed form.
--
--   The sequence $\hat c_j$ of Theorem 10.3.6 is $\hat c_1 = 1/(N+a-2)$ and, with $k := N - j$,
--   $\hat c_{j+1} = \frac{1}{k+a-2}[(k+a-1)\hat c_j + ((1-\hat c_j)^+)^{k+a-1}]$ — the last term is a
--   **power** with exponent $k+a-1$, real since $a$ is a real shape parameter. And
--   $n^*(N) := \max\{k \in \{1,\dots,N\} \mid \hat c_{N-k+1} \ge 1\}$ with $\max\emptyset := 0$.
--
--   **Moderation note.** The general Bayesian stopping problem carried an arbitrary `Φ̂`, `μ̂` and `q` with no relation between them — not a Bayesian model, and Theorem 10.3.4 is false for such data; `q` was not required to be a density, the moment condition `sup_θ ∫ z Q(dz|θ) < ∞` of p. 324 was absent, and the value recursion used real integrals (junk). Now `μ̂(·|Φ̂(i,z))` is the Bayes update of `μ̂(·|i)` by `q(z|·)`, `q(·|θ)` integrates to `1`, the moment condition is a field, and `J_n`, `c_n` are `[-∞,∞]`-valued. House selling, secretary and the Inverse-Gamma instance are as drafted.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §10.3 pp. 316-326 (PDF 324-334)

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_StoppingProblem
import Definitions.Def_MDPFinance_OptimalStopping_Stationary

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.OptimalStopping

/-! ## The house selling problem (§10.3.1, p. 316) -/

/-- The **house selling problem** (p. 316): i.i.d. offers with law `Q` on `[m,M]`, `0 < m < M`,
maintenance cost `c > 0` per rejection; `E := [m,M]`, `Q^X(·|x) := Q`, `c(x) ≡ -c`, `g(x) := x`;
for the unbounded horizon `β ∈ (0,1)` (p. 317). -/
structure HouseSelling where
  m : ℝ
  M : ℝ
  Q : Measure ℝ
  c : ℝ
  beta : ℝ
  m_pos : 0 < m
  m_lt_M : m < M
  Q_prob : IsProbabilityMeasure Q
  Q_supp : Q {x : ℝ | x < m ∨ M < x} = 0
  c_pos : 0 < c
  beta_mem : beta ∈ Set.Ioo (0 : ℝ) 1

def HouseSelling.E (H : HouseSelling) : Set ℝ := Set.Icc H.m H.M

/-- `x ↦ (-c Q([m,x)) + ∫_x^∞ x' Q(dx')) / (1 − β Q([m,x)))` (Theorem 10.3.1). -/
noncomputable def HouseSelling.thresholdObjective (H : HouseSelling) (x : ℝ) : ℝ :=
  (-H.c * (H.Q (Set.Ico H.m x)).toReal + ∫ y in Set.Ici x, y ∂H.Q)
    / (1 - H.beta * (H.Q (Set.Ico H.m x)).toReal)

noncomputable def HouseSelling.toProblem (H : HouseSelling) : StationaryProblem ℝ where
  QX := fun _ => H.Q
  QX_prob := fun _ => H.Q_prob
  QX_meas := measurable_const
  c := fun _ => -H.c
  c_meas := measurable_const
  g := fun x => x
  g_meas := measurable_id
  beta := H.beta
  beta_mem := ⟨H.beta_mem.1, le_of_lt H.beta_mem.2⟩

/-! ## The secretary problem (§10.3.2, pp. 319-322) -/

/-- The **secretary problem** (p. 321) with `N > 2` candidates. -/
structure Secretary where
  N : ℕ
  N_ge : 3 ≤ N

/-- The transition probabilities **(10.4)**. -/
noncomputable def Secretary.q (S : Secretary) (x y : ℕ) : ℝ :=
  if x = S.N + 1 then (if y = S.N + 1 then 1 else 0)
  else if y = S.N + 1 then (x : ℝ) / (S.N : ℝ)
  else if x < y ∧ y ≤ S.N then (x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))
  else 0

/-- `g(N+1) = 0`, `g(x) = x/N` for `x = 1,…,N`. -/
noncomputable def Secretary.g (S : Secretary) (x : ℕ) : ℝ :=
  if x = S.N + 1 then 0 else (x : ℝ) / (S.N : ℝ)

/-- The value functions by periods still to run: `W 0 = V_{N-1}`, `W (j+1) (x) = max{x/N,
Σ_{y=x+1}^N (x/(y(y-1))) W j (y)}` (p. 321). -/
noncomputable def Secretary.W (S : Secretary) : ℕ → ℕ → ℝ
  | 0, x => (x : ℝ) / (S.N : ℝ)
  | (j + 1), x =>
      max ((x : ℝ) / (S.N : ℝ))
        (∑ y ∈ Finset.Icc (x + 1) S.N, ((x : ℝ) / ((y : ℝ) * ((y : ℝ) - 1))) * S.W j y)

/-- `V_n = W_{N-1-n}` for `n = 0,…,N-1`. -/
noncomputable def Secretary.V (S : Secretary) (n x : ℕ) : ℝ := S.W (S.N - 1 - n) x

/-- `h(x) := 1/x + … + 1/(N-1)` (p. 322), as a function of the horizon. -/
noncomputable def secretaryH (N x : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico x N, (1 : ℝ) / (j : ℝ)

/-- `k^*(N) := inf{k ∈ {1,…,N-2} | h(k) > 1 ≥ h(k+1)}` **(10.5)**. -/
noncomputable def secretaryKStar (N : ℕ) : ℕ :=
  sInf {k : ℕ | k ∈ Finset.Icc 1 (N - 2) ∧ 1 < secretaryH N k ∧ secretaryH N (k + 1) ≤ 1}

noncomputable def Secretary.h (S : Secretary) (x : ℕ) : ℝ := secretaryH S.N x

noncomputable def Secretary.kStar (S : Secretary) : ℕ := secretaryKStar S.N

/-! ### The general Bayesian stopping problem (§10.3.4, pp. 323-324) -/

/-- `μ ≤_lr ν`, the likelihood ratio order (Definition B.3.5): densities `f`, `g` against a
common reference measure with `f(θ')g(θ) ≤ f(θ)g(θ')` for `θ ≤ θ'`. -/
def LikelihoodRatioLe (mu nu : Measure ℝ) : Prop :=
  ∃ (lam : Measure ℝ) (f g : ℝ → ℝ),
    (∀ θ, 0 ≤ f θ) ∧ (∀ θ, 0 ≤ g θ) ∧ Measurable f ∧ Measurable g ∧
    mu = lam.withDensity (fun θ => ENNReal.ofReal (f θ)) ∧
    nu = lam.withDensity (fun θ => ENNReal.ofReal (g θ)) ∧
    ∀ θ θ' : ℝ, θ ≤ θ' → f θ' * g θ ≤ f θ * g θ'

/-- `q(z|θ)` is **`MTP_2`** in `z` and `θ`. -/
def IsMTP2 (q : ℝ → ℝ → ℝ) : Prop :=
  ∀ z z' θ θ' : ℝ, q z θ * q z' θ' ≤ q (max z z') (max θ θ') * q (min z z') (min θ θ')

/-- The **general Bayesian stopping problem** of §10.3.4 (pp. 323-324): i.i.d. offers with law
`Q(·|θ)` of Lebesgue density `q(·|θ)`, unknown `θ`; information `i ∈ I` with posterior
`μ̂(·|i)` and update `Φ̂(i,z)` — the *Bayes* update, `μ̂(·|Φ̂(i,z)) ∝ q(z|·) μ̂(·|i)` (§5.4);
`sup_θ ∫ z Q(dz|θ) < ∞` (for (B_N)); cost `c ≥ 0` of continuing; stopping reward the offer;
`β = 1`. -/
structure GenBayesStopping (I : Type*) [MeasurableSpace I] where
  q : ℝ → ℝ → ℝ
  q_nonneg : ∀ z θ, 0 ≤ q z θ
  q_meas : Measurable fun p : ℝ × ℝ => q p.1 p.2
  q_density : ∀ θ, ∫⁻ z, ENNReal.ofReal (q z θ) = 1
  hmom : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ θ, ∫⁻ z, ENNReal.ofReal z * ENNReal.ofReal (q z θ) ≤ K
  muhat : I → Measure ℝ
  muhat_prob : ∀ i, IsProbabilityMeasure (muhat i)
  Phi : I → ℝ → I
  /-- The Bayes update: wherever the predictive density is positive,
  `μ̂(·|Φ̂(i,z)) = q(z|·) μ̂(·|i) / ∫ q(z|θ) μ̂(dθ|i)`. -/
  hbayes : ∀ i z, 0 < ∫⁻ θ, ENNReal.ofReal (q z θ) ∂(muhat i) →
    muhat (Phi i z) = (∫⁻ θ, ENNReal.ofReal (q z θ) ∂(muhat i))⁻¹ •
      (muhat i).withDensity (fun θ => ENNReal.ofReal (q z θ))
  cost : ℝ
  cost_nonneg : 0 ≤ cost

variable {I : Type*} [MeasurableSpace I]

/-- `J_0(x,i) = x`, `J_n(x,i) = max{x, −c + ∫∫ J_{n-1}(z, Φ̂(i,z)) Q(dz|θ) μ̂(dθ|i)}` (p. 324), in
`[-∞,∞]` (the double integral is a genuine value in `[-∞,∞)` under the moment condition). -/
noncomputable def GenBayesStopping.J (M : GenBayesStopping I) : ℕ → ℝ → I → EReal
  | 0, x, _ => (x : EReal)
  | (k + 1), x, i =>
      max (x : EReal) (-(M.cost : EReal) + erealIntegral (M.muhat i)
        (fun θ => erealIntegral volume (fun z => M.J k z (M.Phi i z) * (M.q z θ : EReal))))

/-- `c_n(i) := −c + ∫∫ J_{n-1}(z, Φ̂(i,z)) Q(dz|θ) μ̂(dθ|i)`, `n ≥ 1`. -/
noncomputable def GenBayesStopping.cfun (M : GenBayesStopping I) (n : ℕ) (i : I) : EReal :=
  -(M.cost : EReal) + erealIntegral (M.muhat i)
    (fun θ => erealIntegral volume (fun z => M.J (n - 1) z (M.Phi i z) * (M.q z θ : EReal)))

/-- `i ≤ i' :⟺ μ̂(·|i) ≤_lr μ̂(·|i')` (p. 324). -/
def GenBayesStopping.Ile (M : GenBayesStopping I) (i i' : I) : Prop :=
  LikelihoodRatioLe (M.muhat i) (M.muhat i')

/-- `(x,i) ≤ (x',i') :⟺ x ≤ x'` and `i ≤ i'`. -/
def GenBayesStopping.Ele (M : GenBayesStopping I) (p p' : ℝ × I) : Prop :=
  p.1 ≤ p'.1 ∧ M.Ile p.2 p'.2

/-! ## The Bayesian stopping problem with exponential offers and Inverse Gamma prior
(Example 10.3.5, pp. 325-326) -/

/-- Example 10.3.5: `c = 0`, exponential offers with unknown mean `θ`, sufficient statistic
`i = (s,n)`, Inverse Gamma prior with `a > 1`, `b > 0`; posterior predictive
`Q̂^Z(·|s,n) = Be(1, a+n, s+b)`, density `(n+a)(s+b)^{n+a}/(z+s+b)^{n+a+1}` on `z > 0`. -/
structure BayesStopping where
  a : ℝ
  b : ℝ
  a_gt : 1 < a
  b_pos : 0 < b

noncomputable def BayesStopping.qZ (M : BayesStopping) (s : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  ((n : ℝ) + M.a) * (s + M.b) ^ ((n : ℝ) + M.a) / (z + s + M.b) ^ ((n : ℝ) + M.a + 1)

/-- `J_0(x,i) = x`, `J_k(x,(s,n)) = max{x, ∫ J_{k-1}(z,(s+z,n+1)) Q̂^Z(dz|s,n)}` (`c = 0`). -/
noncomputable def BayesStopping.J (M : BayesStopping) : ℕ → ℝ → ℝ → ℕ → ℝ
  | 0, x, _, _ => x
  | (k + 1), x, s, n =>
      max x (∫ z in Set.Ioi (0 : ℝ), M.J k z (s + z) (n + 1) * M.qZ s n z)

/-- `c_k((s,n)) := ∫ J_{k-1}(z,(s+z,n+1)) Q̂^Z(dz|s,n)`, `k ≥ 1`. -/
noncomputable def BayesStopping.cfun (M : BayesStopping) (k : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ), M.J (k - 1) z (s + z) (n + 1) * M.qZ s n z

/-- `ĉ_1 = 1/(N+a-2)` and, with `k := N - j`, `ĉ_{j+1} = (1/(k+a-2))[(k+a-1)ĉ_j +
((1-ĉ_j)^+)^{k+a-1}]` (Theorem 10.3.6 a)); `ĉ_0` unused. -/
noncomputable def BayesStopping.chat (M : BayesStopping) (N : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / ((N : ℝ) + M.a - 2)
  | (j + 2) =>
      let k : ℝ := (N : ℝ) - ((j : ℝ) + 1)
      (1 / (k + M.a - 2)) *
        ((k + M.a - 1) * M.chat N (j + 1)
          + Real.rpow (max (1 - M.chat N (j + 1)) 0) (k + M.a - 1))

/-- `n^*(N) := max{k ∈ {1,…,N} | ĉ_{N-k+1} ≥ 1}`, `max ∅ := 0`. -/
noncomputable def BayesStopping.nStar (M : BayesStopping) (N : ℕ) : ℕ :=
  sSup {k : ℕ | k ∈ Finset.Icc 1 N ∧ 1 ≤ M.chat N (N - k + 1)}

end MDPFinance.OptimalStopping


