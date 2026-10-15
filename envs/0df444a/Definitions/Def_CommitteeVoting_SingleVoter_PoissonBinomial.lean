-- Prove2me | Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial
-- name    : CommitteeVoting_SingleVoter_PoissonBinomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T08:58:42.668332+00:00
-- url     : https://prove2.me/theorems/88240ec3-55ed-4741-afcf-e51c715984df
-- title:
--   Definition 7 and (84), p. 49 — the Poisson binomial law: pmf, cdf and upper tail
-- statement:
--   Let $(q_i)_{i \in S}$ be real numbers indexed by a finite set $S$, read as the success probabilities of independent Bernoulli trials. For a set $A \subseteq S$ of successful trials, its **weight** is
--
--   $$
--   w_q^S(A) = \prod_{i \in A} q_i \prod_{i \in S \setminus A} (1 - q_i),
--   $$
--
--   the probability under the product of the Bernoulli laws that exactly the trials in $A$ succeed. The number of successes $X_S = \sum_{i\in S} X_i$ has the **Poisson binomial distribution** with parameters $(q_i)_{i\in S}$ (Definition 7), whose probability mass function is the counting formula (84),
--
--   $$
--   \Pr[X_S = \ell] = \sum_{A \subseteq S,\ |A| = \ell} \ \prod_{i \in A} q_i \prod_{j \in S\setminus A} (1 - q_j), \qquad \ell \in \mathbb N .
--   $$
--
--   Its cumulative distribution function at a natural threshold $x$ is $F_{X_S}(x) = \Pr[X_S \le x] = \sum_{\ell = 0}^{x} \Pr[X_S = \ell]$, and its upper tail is $\Pr[X_S > x] = \sum_{A \subseteq S,\ |A| > x} w_q^S(A)$.
--
--   These are the objects compared in Lemmas 4, 5 and 1 of the paper: the number of honest members of a committee $S$ of candidates whose types are independent with honesty probabilities $q_i$ is Poisson binomial with parameters $(q_i)_{i\in S}$.
--
--   **Formalization Note** The law is defined by its counting form (84) rather than through a probability space: the weight of a success set is exactly the product-measure probability of that outcome for independent Bernoulli($q_i$) trials, so this is Definition 7 itself. The definitions are algebraic and make sense for any real $q_i$; the theorems that need $0 \le q_i \le 1$ assume it. Thresholds are natural numbers; since $X_S$ takes values in $\{0,\dots,|S|\}$, $F_{X_S}(x) = F_{X_S}(\lfloor x\rfloor)$ for real $x \ge 0$ and $F_{X_S}(x) = 0$ for $x < 0$, so nothing is lost.
-- source:
--   Benhaim, Falk, Tsoukalas, Scaling Blockchains: Can Committee-based Consensus Help?, arXiv:2110.08673v2, p. 49, Definition 7 and (84); upper tail as used in Lemma 1, p. 19

import Mathlib

namespace CommitteeVoting.SingleVoter

/-- Weight of the outcome "exactly the trials in `A` succeed" among the independent Bernoulli
trials indexed by `S`, trial `i` having success probability `q i`:
`(∏_{i ∈ A} q i) * ∏_{i ∈ S \ A} (1 - q i)`. Meaningful for `A ⊆ S`. -/
def pbWeight {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (S A : Finset ι) : ℝ :=
  (∏ i ∈ A, q i) * ∏ i ∈ S \ A, (1 - q i)

/-- Probability mass function of the Poisson binomial law with parameters `(q i)_{i ∈ S}`,
in the counting form (84) of Benhaim–Falk–Tsoukalas (Definition 7, p. 49):
`Pr[X = ℓ] = ∑_{A ⊆ S, |A| = ℓ} ∏_{i ∈ A} q i ∏_{j ∈ S \ A} (1 - q j)`. -/
def pbPMF {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (S : Finset ι) (ℓ : ℕ) : ℝ :=
  ∑ A ∈ S.powersetCard ℓ, pbWeight q S A

/-- Cumulative distribution function `Pr[X ≤ x] = ∑_{ℓ = 0}^{x} Pr[X = ℓ]` of the Poisson binomial
law with parameters `(q i)_{i ∈ S}`, at a natural threshold `x`. -/
def pbCDF {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (S : Finset ι) (x : ℕ) : ℝ :=
  ∑ ℓ ∈ Finset.range (x + 1), pbPMF q S ℓ

/-- Upper tail `Pr[X > x]` of the Poisson binomial law with parameters `(q i)_{i ∈ S}`: the total
weight of the success sets `A ⊆ S` with more than `x` elements. -/
def pbTail {ι : Type*} [DecidableEq ι] (q : ι → ℝ) (S : Finset ι) (x : ℕ) : ℝ :=
  ∑ A ∈ S.powerset.filter (fun A => x < A.card), pbWeight q S A

end CommitteeVoting.SingleVoter


