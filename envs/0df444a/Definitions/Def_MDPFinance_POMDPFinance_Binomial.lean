-- Prove2me | Definitions.Def_MDPFinance_POMDPFinance_Binomial
-- name    : MDPFinance_POMDPFinance_Binomial
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:06.777411+00:00
-- url     : https://prove2.me/theorems/42fdaf35-7649-4702-9d9a-e92a69240124
-- title:
--   The binomial market's reachable posteriors and the one-step optimal-fraction problem
-- statement:
--   This definition specializes the chapter's general partial-observation apparatus to the specific
--   binomial market Bäuerle and Rieder analyze in detail: a single stock with unknown up-probability
--   $\theta \in \Theta = (0,1)$, prior density $p_0$. Writing $m$ for the number of observed up-moves
--   out of $n$ trials, Example 5.4.4's sufficient-statistic reduction gives the posterior density
--   $$
--   \hat p(\theta \mid m,n) \propto \theta^m(1-\theta)^{n-m}p_0(\theta),
--   $$
--   and $D_{Q_0} := \{\hat p(\cdot\mid m,n) \mid n \in \mathbb N_0, m \le n\}$ collects every
--   posterior reachable from the prior $p_0$.
--
--   The **likelihood ratio order** on densities, $f \le_{lr} g$ iff $f(t)g(s) \le f(s)g(t)$ for all
--   $s \le t$, is the comparison Lemma 6.1.4 and Theorem 6.1.5 use throughout; it is a ratio-of-
--   densities monotonicity condition, distinct from the weaker stochastic or increasing-concave
--   orders used elsewhere in this book's series.
--
--   Finally, for the one-step optimization problem (6.4)/(6.5) that determines the optimal invested
--   fraction $\alpha_n^*(\rho)$ at a binomial posterior, `IsOptimalFraction` characterizes $\alpha$ as
--   *a* maximizer of the relevant objective over $[0,1]$ (the short-selling-excluded admissible set),
--   rather than reconstructing the explicit closed form $\alpha^*(\lambda)$ the book's own proof
--   derives via a separate lemma (Lemma 4.2.9, from a different chunk's own machinery): Theorem
--   6.1.5's comparison inequality is a fact about any maximizer of this concave one-variable problem.
--
--   **Formalization Note.** The market is genuinely one-dimensional ($d=1$) throughout this
--   sub-model, matching the book's own "one stock" binomial example.
--
--   **Moderation note.** Four additions. `IsBinomialMarket` pins the market the binomial results are about (constant hidden parameter, returns $\bar u$ w.p. $\theta$ and $\bar d$ w.p. $1-\theta$); the draft's Lemma 6.1.4(b) and Theorem 6.1.5 quantified over an arbitrary `FilterMarket ℝ d`, for which the claims are false. `measureOfDensity` is normalized to a probability measure (the draft's unnormalized posteriors have masses that scale $d_k$ and break the comparison in Lemma 6.1.4(b)); `IsPriorDensity`, `rhobar`, `ubar`, `dbar` name the remaining data. `dBin` is the book's recursion (6.4) with $\tilde A=[0,1]$ (short-selling excluded, p. 179), which is the recursion whose maximizers are the fractions $\alpha^*_n(\rho)$ compared in Theorem 6.1.5; the draft used the general `dPow` over the full admissible set $\tilde A$ of (6.3), a different recursion (Lemma 6.1.4(b)'s proof needs $\alpha\ge 0$). `LRMeasure` is Definition B.3.5 on measures.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 179-180, model data preceding Lemma 6.1.4 and the proof of Theorem 6.1.5

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_PowerLogValue

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDPFinance

/-- The **likelihood ratio order** on real densities (Bäuerle–Rieder, Definition B.3.5, p. 360,
PDF 366, applied to two densities as the book itself writes `ρ ≤_{lr} ρ'` for two posteriors given
by their `Q_0`-densities — restated in this chunk's own namespace per the file-ownership boundary,
matching `MDPFinance.BayesianModels.LikelihoodRatioOrder` (chunk `05b`)'s definition exactly):
`f ≤_{lr} g` iff `f(t)g(s) ≤ f(s)g(t)` for all `s ≤ t`. -/
def LikelihoodRatioOrder (f g : ℝ → ℝ) : Prop :=
  ∀ s t : ℝ, s ≤ t → f t * g s ≤ f s * g t

/-- The binomial market's posterior density `\hat p(\theta \mid m,n) \propto θ^m(1-θ)^{n-m}
p_0(θ)`, `θ \in Θ = (0,1)`, given prior density `p_0` w.r.t. Lebesgue measure and sufficient
statistic `(m,n)` = (number of ups, number of trials) (Bäuerle–Rieder, p. 179, PDF 192, `\hat
μ(C\mid m,n) = \int_C θ^m(1-θ)^{n-m}Q_0(dθ) / \int_Θ θ'^m(1-θ')^{n-m}Q_0(dθ')`, restated as an
explicit density against `p_0`). -/
noncomputable def binomialPosteriorDensity (p0 : ℝ → ℝ) (m n : ℕ) (θ : ℝ) : ℝ :=
  θ ^ m * (1 - θ) ^ (n - m) * p0 θ

/-- `D_{Q_0} := \{\hat μ(\cdot\mid m,n) \mid n \in ℕ_0, m \le n\}`, the set of posterior densities
reachable from prior density `p_0` (Bäuerle–Rieder, p. 179, PDF 192), represented as the set of
functions `binomialPosteriorDensity p0 m n` ranging over admissible `(m,n)`. -/
def DQ0 (p0 : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {f | ∃ m n : ℕ, m ≤ n ∧ f = binomialPosteriorDensity p0 m n}

/-- `μ ≤_{lr} μ'` for two measures on `ℝ` with densities w.r.t. a common dominating measure `ρ`
(Bäuerle–Rieder, Definition B.3.5, p. 360, PDF 366): *some* versions of the densities satisfy
`f(t) g(s) ≤ f(s) g(t)` for all `s ≤ t`. -/
def LRMeasure (ρ μ μ' : Measure ℝ) : Prop :=
  ∃ f g : ℝ → ℝ, Measurable f ∧ Measurable g ∧ (∀ θ, 0 ≤ f θ) ∧ (∀ θ, 0 ≤ g θ) ∧
    μ = ρ.withDensity (fun θ => ENNReal.ofReal (f θ)) ∧
    μ' = ρ.withDensity (fun θ => ENNReal.ofReal (g θ)) ∧ LikelihoodRatioOrder f g

/-- The normalization `μ / μ(ℝ)` of a finite nonzero measure. -/
noncomputable def normalize (μ : Measure ℝ) : Measure ℝ := (μ Set.univ)⁻¹ • μ

/-- The probability measure on `Θ = (0,1)` proportional to the density `p` w.r.t. Lebesgue
measure, used to turn a (unnormalized) posterior *density* (`binomialPosteriorDensity`, `DQ0`)
into the probability measure `\hat μ(\cdot\mid m,n)` on `Θ` that `dBin`/`FilterOp.mu` expect (the
unobservable factor `EY` specializes to `Θ ⊆ ℝ` for the binomial sub-model). -/
noncomputable def measureOfDensity (p : ℝ → ℝ) : Measure ℝ :=
  normalize ((MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity fun θ =>
    ENNReal.ofReal (p θ))

/-- `p_0` is a prior density on `Θ = (0,1)`. -/
def IsPriorDensity (p0 : ℝ → ℝ) : Prop :=
  Measurable p0 ∧ (∀ θ, 0 ≤ p0 θ) ∧ ∫⁻ θ in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (p0 θ) = 1

/-- `\bar ρ := \int θ \, ρ(dθ)`, the posterior mean up-probability. -/
noncomputable def rhobar (ρ : Measure ℝ) : ℝ := ∫ θ, θ ∂ρ

/-- `\bar u := u/(1+i) - 1` as a one-dimensional relative-risk vector (p. 179). -/
noncomputable def ubar (u i : ℝ) : Fin 1 → ℝ := fun _ => u / (1 + i) - 1

/-- `\bar d := d/(1+i) - 1` as a one-dimensional relative-risk vector (p. 179). -/
noncomputable def dbar (dn i : ℝ) : Fin 1 → ℝ := fun _ => dn / (1 + i) - 1

/-- The **binomial market with unknown up-probability** (Bäuerle–Rieder, p. 178-179, PDF
191-192) as an instance of `FilterMarket ℝ 1`: `E_Y = ℝ` carrying `Θ = (0,1)`; the hidden
parameter is constant (`Q^Y(·|θ) = δ_θ`, the Bayesian model of Example 5.2.4); given `θ` the
relative risk is `\bar u` with probability `θ` and `\bar d` with probability `1-θ` (density w.r.t.
the counting measure on `{\bar u, \bar d}`). -/
def IsBinomialMarket (M : FilterMarket ℝ 1) (u dn i : ℝ) : Prop :=
  M.lam = Measure.dirac (ubar u i) + Measure.dirac (dbar dn i) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) 1, M.qR θ (ubar u i) = θ ∧ M.qR θ (dbar dn i) = 1 - θ) ∧
    M.QY = Kernel.id

/-- The one-step objective of (6.4)/(6.5) whose maximiser is `α_n^*(ρ)` (Bäuerle–Rieder, proof of
Theorem 6.1.5, p. 179-180, PDF 192-193), for the binomial market with up-factor `u`, down-factor
`d`, rate `i`, power `γ`, posterior density `p`, and value-so-far `dk : ℝ → ℝ` (`d_{n-1}`, itself a
function of the posterior density, e.g. via `dPow` composed with `Fd.Phi`'s density): the
`\bar ρ`-weighted combination `\bar ρ \, d_k(\hat p(\cdot\mid \Phi(ρ,\bar u))) (1+i+α(u-1-i))^γ +
(1-\bar ρ) \, d_k(\hat p(\cdot\mid\Phi(ρ,\bar d))) (1+i+α(d-1-i))^γ`, where `\bar ρ := \int θ \,
ρ(dθ)` is represented directly via the hypotheses of the theorems using it, rather than
re-derived from `dPow`, since the objective's *shape* (not `dPow`'s specific recursion) is what
`Theorem 6.1.5` compares across two posteriors. -/
noncomputable def binomialObjective (u dn i γ dku dkd rhobar : ℝ) (α : ℝ) : ℝ :=
  rhobar * dku * (1 + i + α * (u - 1 - i)) ^ γ +
    (1 - rhobar) * dkd * (1 + i + α * (dn - 1 - i)) ^ γ

/-- `α` **is an optimal fraction** at posterior `ρ` (represented by its `\bar ρ := \int θ\,ρ(dθ)`
and the two continuation values `d_k(\Phi(ρ,\bar u))`, `d_k(\Phi(ρ,\bar d))`) if it maximises
`binomialObjective` over `[0,1]` (Bäuerle–Rieder, p. 179-180: "`\tilde A := [0,1]`" after excluding
short-selling, and `α_n^*(ρ)` "is a maximum point of (6.4)"): stated as *a* maximiser rather than
the closed-form `α^*(λ)` the book's own proof derives (Lemma 4.2.9's formula, from a different,
unavailable chunk), since Theorem 6.1.5's comparison inequality is a fact about *any* maximiser of
this concave one-variable problem, not about the specific closed form used to exhibit it. -/
def IsOptimalFraction (u dn i γ dku dkd rhobar α : ℝ) : Prop :=
  α ∈ Set.Icc (0 : ℝ) 1 ∧
    IsMaxOn (binomialObjective u dn i γ dku dkd rhobar) (Set.Icc 0 1) α

/-- The binomial market's auxiliary recursion (6.4) (Bäuerle–Rieder, p. 179, PDF 192): the power
recursion (6.3) with short-selling excluded, `\tilde A := [0,1]`, which "reduces to one which is
linear in `θ`": `d_0 \equiv 1/γ`, `d_{k+1}(ρ) := \sup_{0 ≤ α ≤ 1} [d_k(Φ(ρ,\bar u)) \bar ρ
(1+i+α(u-1-i))^γ + d_k(Φ(ρ,\bar d)) (1-\bar ρ)(1+i+α(d-1-i))^γ] (1+i)^{-γ}`, indexed by stages
remaining. This is the recursion whose maximizers are the optimal fractions `α_n^*(ρ)` of Lemma
6.1.4 and Theorem 6.1.5 (the general `dPow` uses the full admissible set `\tilde A` of (6.3)). -/
noncomputable def dBin (M : FilterMarket ℝ 1) (Fd : FilterOp M) (u dn i γ : ℝ) :
    ℕ → Measure ℝ → ℝ
  | 0, _ => 1 / γ
  | (k + 1), ρ =>
      (⨆ α ∈ Set.Icc (0 : ℝ) 1, binomialObjective u dn i γ
        (dBin M Fd u dn i γ k (Fd.Phi ρ (ubar u i))) (dBin M Fd u dn i γ k (Fd.Phi ρ (dbar dn i)))
        (rhobar ρ) α) * (1 + i) ^ (-γ)

end MDPFinance.POMDPFinance


