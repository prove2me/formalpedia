-- Prove2me | Definitions.Def_RiskUncSets_Symmetric_Setting
-- name    : RiskUncSets_Symmetric_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:07:41.647501+00:00
-- url     : https://prove2.me/theorems/66fbb183-4857-4e0f-8b48-6e2b2575a873
-- title:
--   Definitions 4.6–4.9 and equations (4), (9), (10): ordered weights, permutohulls, central symmetry, and generators
-- statement:
--   Let $N\ge 1$ observations be indexed by $1,\ldots,N$. The **restricted simplex** $\widehat\Delta^N$ consists of probability vectors $q$ whose entries are nonincreasing. For data $\mathcal A=\{a_1,\ldots,a_N\}\subseteq\mathbb R^n$, the **$q$-permutohull** $\Pi_q(\mathcal A)$ is the convex hull of all weighted sums $\sum_i q_{\sigma(i)}a_i$ over permutations $\sigma$. The sample mean is $\widehat a=N^{-1}\sum_i a_i$. A set $P$ is **centrally symmetric through** $x_0\in P$ when $x_0+x\in P$ implies $x_0-x\in P$.
--
--   The **symmetric restricted simplex** consists of $q\in\widehat\Delta^N$ for which some permutation $\sigma$ satisfies
--
--   $$
--   q_i=\frac{2}{N}-q_{\sigma(i)}\qquad(1\le i\le N).
--   $$
--
--   For an observation vector $X$ with increasing order statistics $x_{(1)}\le\cdots\le x_{(N)}$, the associated reward-sign risk measure is $\mu_q(X)=-\sum_iq_ix_{(i)}$. The $\widehat N=\lfloor N/2\rfloor+1$ generator vectors $\bar q^{j}$ have entries $2/N$ for $i<j$, $1/N$ for $j\le i\le N-j+1$, and $0$ otherwise.
--
--   These definitions supply the objects used to characterize the centrally symmetric subclass in Theorem 4.4.
--
--   **Formalization Note** The sample space is `Fin N`; the displayed indices begin at one, while Lean's begin at zero. The middle range of the generator is translated accordingly. The uniform reference distribution of Assumption 4.1 is encoded by the constant $1/N$; $N>0$ is required by all theorem statements using it. The same paper-specific definitions are local to this mission because the other series missions remain drafts.
-- source:
--   Bertsimas & Brown, Constructing uncertainty sets for robust linear optimization, Oper. Res. 57(6) (2009), pp. 1489–1491, Definitions 4.6–4.9, equations (4), (9), (10); DOI 10.1287/opre.1080.0646

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fin.Tuple.Sort
noncomputable section

namespace RiskUncSets.Symmetric

/-- Definition 4.6: probability weights in decreasing order. -/
def restrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin N) ∧ Antitone q}

/-- Definition 4.7: the convex hull of all weighted permutations of the data. -/
def permutohull {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  convexHull ℝ (Set.range fun σ : Equiv.Perm (Fin N) => ∑ i, q (σ i) • a i)

/-- The sample mean `A e_N` of the data. -/
def sampleMean {N n : ℕ} (a : Fin N → Fin n → ℝ) : Fin n → ℝ :=
  ∑ i, (1 / (N : ℝ)) • a i

/-- Definition 4.8: symmetry about a point belonging to the set. -/
def CentrallySymmetric {n : ℕ} (P : Set (Fin n → ℝ)) (x₀ : Fin n → ℝ) : Prop :=
  x₀ ∈ P ∧ ∀ x, x₀ + x ∈ P → x₀ - x ∈ P

/-- Definition 4.9 and equation (9). -/
def symRestrictedSimplex (N : ℕ) : Set (Fin N → ℝ) :=
  {q | q ∈ restrictedSimplex N ∧
    ∃ σ : Equiv.Perm (Fin N), q = fun i => 2 / (N : ℝ) - q (σ i)}

/-- Equation (4): the reward-sign distortion risk measure for ordered observations. -/
def muQ {N : ℕ} (q X : Fin N → ℝ) : ℝ :=
  -∑ i, q i * X (Tuple.sort X i)

/-- The number of symmetric generators in Theorem 4.4. -/
def Nhat (N : ℕ) : ℕ := N / 2 + 1

/-- Equation (10), with both the observation and generator indices starting at zero. -/
def qbar {N : ℕ} (j : Fin (Nhat N)) : Fin N → ℝ :=
  fun i =>
    if (i : ℕ) < (j : ℕ) then 2 / (N : ℝ)
    else if (j : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) + (j : ℕ) + 1 ≤ N then 1 / (N : ℝ)
    else 0

end RiskUncSets.Symmetric


