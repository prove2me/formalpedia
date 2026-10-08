-- Prove2me | Definitions.Def_KingmanSubadditive_Ulam_Permutations
-- name    : KingmanSubadditive_Ulam_Permutations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:27:07.094501+00:00
-- url     : https://prove2.me/theorems/33e87048-b304-47d0-a6ee-b9a213d46cbd
-- title:
--   §2.4 — ascending sequences of a permutation, l(π), the count ν, the uniform law on 𝒮_n, convergence in probability of n^{−½}l(π_n), and the exponent of (2.4.8)
-- statement:
--   This file fixes the objects of §2.4 of Kingman's *Subadditive ergodic theory* (random permutations and Ulam's problem).
--
--   Let $\mathcal S_n$ be the group of permutations of $\{1,2,\dots,n\}$, and let $\sigma\in\mathcal S_n$.
--
--   1. A set of positions $\{i_1<i_2<\dots<i_k\}\subseteq\{1,\dots,n\}$ is **ascending** for $\sigma$ if $\sigma(i_1)<\sigma(i_2)<\dots<\sigma(i_k)$.
--   2. The **length of the longest ascending sequence** $l(\sigma)$ is the largest integer $k$ for which there exist integers $i_1,\dots,i_k$ with
--   $$1\le i_1<i_2<\dots<i_k\le n,\qquad \sigma(i_1)<\sigma(i_2)<\dots<\sigma(i_k).$$
--   3. For an integer $k\ge0$, $\nu_k(\sigma)$ is the **number of ascending sequences of length $k$**, that is, the number of $k$-element ascending sets of positions.
--   4. The **uniform distribution** on $\mathcal S_n$ gives an event $A\subseteq\mathcal S_n$ the probability $P\{A\}=|A|/n!$.
--   5. $n^{-1/2}\,l(\pi_n)$ **converges in probability to** $c\in\mathbb R$, for $\pi_n$ uniformly distributed over $\mathcal S_n$, if for every $\varepsilon>0$
--   $$P\big\{\,|n^{-1/2}\,l(\pi_n)-c|>\varepsilon\,\big\}\to 0\qquad(n\to\infty).$$
--   6. The **exponent of (2.4.8)**: for $0<\alpha<b$,
--   $$E(\alpha,b)=2\alpha+(b-\alpha)\log(b-\alpha)-\alpha\log\alpha-b\log b .$$
--
--   These are the vocabulary of Hammersley's theorem (Theorem 7) and of Kingman's bounds on the Ulam constant (Theorem 8).
--
--   **Formalization Note** The paper writes $\pi$ for the permutation; Lean writes $\sigma$, because $\pi$ is the circle constant in Theorem 8. $\mathcal S_n$ is `Equiv.Perm (Fin n)`. Convergence in probability is a property of the law of each $\pi_n$ alone (the paper says so on p. 895), so it is stated through the counting probability $|A|/n!$ rather than through random variables on a common probability space. At $n=0$ Lean reads $l(\sigma)/\sqrt 0$ as $0$, which does not affect a limit. The paper writes $\beta$ for the second argument of (2.4.8); it is $b$ here because $\beta$ also names the constant of Theorem 8.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, pp. 893–896, §2.4 (𝒮_n and l(π), pp. 893–894; Theorem 7, p. 895; ν and (2.4.8), p. 896)

import Mathlib

namespace KingmanSubadditive.Ulam

open Filter Topology

/-- A set `s` of positions is **ascending** for the permutation `σ` of `{1, …, n}` (here `Fin n`)
if `σ` is strictly increasing on it: whenever `i < j` lie in `s`, `σ i < σ j`. A `k`-element
ascending set `{i₁ < ⋯ < i_k}` is exactly a sequence with `π(i₁) < ⋯ < π(i_k)` in the sense of
Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4, pp. 893–894. -/
def IsAscendingOn {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i < j → σ i < σ j

instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Finset (Fin n)) :
    Decidable (IsAscendingOn σ s) := by
  unfold IsAscendingOn; infer_instance

/-- `l(π)`, the length of the longest ascending sequence in `σ ∈ 𝒮_n` (Kingman 1973, §2.4,
pp. 893–894): the largest `k` for which there exist `1 ≤ i₁ < ⋯ < i_k ≤ n` with
`σ(i₁) < ⋯ < σ(i_k)`, i.e. the largest cardinality of an ascending set of positions.

**Formalization Note** The paper's permutation is called `π`; it is `σ` here because `π` is
`Real.pi` in Theorem 8. `𝒮_n` is `Equiv.Perm (Fin n)`. The empty set is ascending, so `lis σ`
is well defined (it is `0` only for `n = 0`). -/
def lis {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun s => IsAscendingOn σ s)).sup Finset.card

/-- `ν`, the number of ascending sequences `i₁ < i₂ < ⋯ < i_k ≤ n` of length `k` in `σ`
(Kingman 1973, §2.4, proof of Theorem 8, p. 896): the number of `k`-element sets of positions
on which `σ` is strictly increasing. -/
def numAscending {n : ℕ} (k : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (((Finset.univ : Finset (Fin n)).powersetCard k).filter (fun s => IsAscendingOn σ s)).card

/-- The uniform distribution on `𝒮_n` (Kingman 1973, §2.4, p. 894): the probability of an
event `A ⊆ 𝒮_n` is `#A / n!`, the proportion of the `n!` permutations of `{1, …, n}` lying
in `A`. -/
noncomputable def unifProb (n : ℕ) (A : Equiv.Perm (Fin n) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter A).card : ℝ) / (Nat.factorial n : ℝ)

/-- `n^{−½} l(π_n)` **converges in probability to `c`** when `π_n` is uniformly distributed
over `𝒮_n` (Kingman 1973, §2.4, Theorem 7, p. 895): for every `ε > 0`,
`P{|n^{−½} l(π_n) − c| > ε} → 0` as `n → ∞`, the probability being the uniform one on `𝒮_n`.

**Formalization Note** Convergence in probability depends only on the law of each `π_n`
(the paper says so on p. 895), so it is stated through the counting probability `unifProb`.
At `n = 0` Lean reads `l(π)/√0` as `0`; a single index does not affect a limit. -/
def ConvergesInProbUniform (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => unifProb n (fun σ => ε < |(lis σ : ℝ) / Real.sqrt n - c|))
      atTop (𝓝 0)

/-- The exponent of the Stirling estimate (2.4.8) (Kingman 1973, §2.4, proof of Theorem 8,
p. 896): `2α + (b − α) log (b − α) − α log α − b log b`, the paper's left side of (2.4.8)
with its `β` renamed `b` (the paper also uses `β` for the constant of Theorem 8). It is used
only for `0 < α < b`, where every logarithm has a positive argument. -/
noncomputable def stirlingExponent (α b : ℝ) : ℝ :=
  2 * α + (b - α) * Real.log (b - α) - α * Real.log α - b * Real.log b

end KingmanSubadditive.Ulam


