-- Prove2me | Definitions.Def_JointMixND_QuadOT_Problems
-- name    : JointMixND_QuadOT_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:06.130213+00:00
-- url     : https://prove2.me/theorems/de37c3de-497a-457f-8e43-51cad145d6f1
-- title:
--   (7), (8), (11)–(13), pp. 10–12 — costs C^f_μ and C²_μ, symmetric uncertainty sets, minimizers of (11), (12), (13)
-- statement:
--   Let $F$ be a distribution on $\mathbb R$ and let $\mathbf X=(X_1,\dots,X_n)$ have law $P$ on $\mathbb R^n$.
--
--   1. **Probabilities on $2^{[n]}$.** A probability on the power set of $[n]$ is a weight $\mu(K)\ge 0$ for each $K\subseteq[n]$ with $\sum_{K\subseteq[n]}\mu(K)=1$. An **uncertainty set** $\mathcal M$ is a set of such probabilities.
--   2. **Permutation of $\mu$.** For a permutation $\pi$ of $[n]$, $\mu_\pi(K)=\mu(\{\pi(i):i\in K\})$. The set $\mathcal M$ is **symmetric** if $\mu\in\mathcal M$ implies $\mu_\pi\in\mathcal M$ for every $\pi\in\mathfrak S_n$.
--   3. **Cost (7).** For $f:\mathbb R\to\mathbb R$,
--   $$C^f_\mu(X_1,\dots,X_n)=\sum_{K\subseteq[n]}\mathbb E\Big[f\Big(\sum_{i\in K}X_i\Big)\Big]\mu(K),$$
--   with $\sum_{i\in\emptyset}X_i=0$. The worst-case cost of (8) is $\sup_{\mu\in\mathcal M}C^f_\mu(\mathbf X)$; the quadratic cost $C^2_\mu$ is the case $f(x)=x^2$.
--   4. **Problem (11).** $\mathbf X$ is a minimizer to (11) if all its marginals are $F$ and $\sup_{\mu\in\mathcal M}C^2_\mu(\mathbf X)\le\sup_{\mu\in\mathcal M}C^2_\mu(\mathbf Y)$ for every random vector $\mathbf Y$ with all marginals $F$.
--   5. **Problem (12).** The objective is $\max_{K\subseteq[n]}\mathbb E\big[(\sum_{i\in K}X_i)^2\big]$; a minimizer has all marginals $F$ and objective at most that of every $\mathbf Y$ with all marginals $F$.
--   6. **Problem (13).** For a fixed $k$, the objective is $\max_{K\subseteq[n],\,|K|=k}\mathbb E\big[(\sum_{i\in K}X_i)^2\big]$, with minimizers defined in the same way.
--
--   These are the multi-marginal optimal transport problems of §4: the subset $K$ of components whose aggregate cost is incurred is uncertain, and the decision maker minimizes the worst case over $\mathcal M$.
--
--   **Formalization Note** A probability on $2^{[n]}$ is a function `Finset (Fin n) → ℝ` (0-based components); theorems that use $\mathcal M$ carry `M ⊆ ProbOnSubsets n` explicitly. $\mu_\pi(K)$ is `μ (K.map π)`. The supremum over $\mathcal M$ is `sSup` of the image in $\mathbb R$; for $\mathcal M\subseteq$ probabilities on $2^{[n]}$ and square-integrable vectors this set is bounded, and for $\mathcal M=\emptyset$ every law has the same value. The maxima in (12) and (13) are taken over finite index sets (`Finset.sup'` over all subsets; `⨆` over the subsets of cardinality $k$, nonempty when $k\le n$, which every theorem using (13) assumes). The competitor class in every minimizer notion is **all** probability laws on $\mathbb R^n$ with every marginal equal to $F$. Expectations are Bochner integrals; the theorems carry the finite second moment of $F$ (§4's standing assumption, p. 9), which makes every integrand $(\sum_{i\in K}X_i)^2$ integrable.
-- source:
--   Koike, Lin & Wang, Joint mixability and notions of negative dependence, arXiv:2204.11438v4, p. 10, (7)–(8); p. 11, symmetric 𝓜 and (11); p. 12, (12)–(13)

import Mathlib
import Definitions.Def_JointMixND_QuadOT_Basic

namespace JointMixND.QuadOT

open MeasureTheory ProbabilityTheory

/-- Probabilities on `2^[n]`: weights `μ K ≥ 0` on the subsets `K ⊆ [n]` summing to `1` (p. 10). -/
def ProbOnSubsets (n : ℕ) : Set (Finset (Fin n) → ℝ) :=
  {μ | (∀ K, 0 ≤ μ K) ∧ ∑ K, μ K = 1}

/-- The permutation `μ_π` of `μ`: `μ_π(K) = μ({π(i) : i ∈ K})` (p. 11). -/
def permProb {n : ℕ} (π : Equiv.Perm (Fin n)) (μ : Finset (Fin n) → ℝ) : Finset (Fin n) → ℝ :=
  fun K => μ (K.map π.toEmbedding)

/-- An uncertainty set `𝓜` is symmetric if `μ ∈ 𝓜` implies `μ_π ∈ 𝓜` for every permutation `π` (p. 11). -/
def IsSymmetric {n : ℕ} (M : Set (Finset (Fin n) → ℝ)) : Prop :=
  ∀ μ ∈ M, ∀ π : Equiv.Perm (Fin n), permProb π μ ∈ M

/-- The cost (7), p. 10: `C^f_μ(X) = ∑_{K ⊆ [n]} E[f(∑_{i∈K} X_i)] μ(K)` for `X ∼ P`
(the empty sum is `0`). -/
noncomputable def costF {n : ℕ} (f : ℝ → ℝ) (P : Measure (Fin n → ℝ))
    (μ : Finset (Fin n) → ℝ) : ℝ :=
  ∑ K : Finset (Fin n), (∫ x, f (∑ i ∈ K, x i) ∂P) * μ K

/-- The objective of (8), p. 10: `sup_{μ∈𝓜} C^f_μ(X)`; the quadratic cost (11) is `f = (·)^2`. -/
noncomputable def worstCost {n : ℕ} (f : ℝ → ℝ) (M : Set (Finset (Fin n) → ℝ))
    (P : Measure (Fin n → ℝ)) : ℝ :=
  sSup ((fun μ => costF f P μ) '' M)

/-- `P` is a minimizer to (11), p. 11: it has all marginals `F`, and its worst-case quadratic cost
over `𝓜` is at most that of every law with all marginals `F`. -/
def IsMinimizer11 {n : ℕ} (F : Measure ℝ) (M : Set (Finset (Fin n) → ℝ))
    (P : Measure (Fin n → ℝ)) : Prop :=
  IsCoupling F P ∧ ∀ Q : Measure (Fin n → ℝ), IsCoupling F Q →
    worstCost (fun t => t ^ 2) M P ≤ worstCost (fun t => t ^ 2) M Q

/-- The objective of (12), p. 12: `max_{K ⊆ [n]} E[(∑_{i∈K} X_i)^2]`. -/
noncomputable def maxCost {n : ℕ} (P : Measure (Fin n → ℝ)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun K : Finset (Fin n) => ∫ x, (∑ i ∈ K, x i) ^ 2 ∂P)

/-- The objective of (13), p. 12: `max_{K ⊆ [n], |K| = k} E[(∑_{i∈K} X_i)^2]`
(a maximum over a finite set, nonempty when `k ≤ n`). -/
noncomputable def maxCostCard {n : ℕ} (k : ℕ) (P : Measure (Fin n → ℝ)) : ℝ :=
  ⨆ K : {K : Finset (Fin n) // K.card = k}, ∫ x, (∑ i ∈ K.1, x i) ^ 2 ∂P

/-- `P` is a minimizer to (12), p. 12, among all laws with all marginals `F`. -/
def IsMinimizer12 {n : ℕ} (F : Measure ℝ) (P : Measure (Fin n → ℝ)) : Prop :=
  IsCoupling F P ∧ ∀ Q : Measure (Fin n → ℝ), IsCoupling F Q → maxCost P ≤ maxCost Q

/-- `P` is a minimizer to (13), p. 12, for the cardinality `k`, among all laws with all marginals `F`. -/
def IsMinimizer13 {n : ℕ} (F : Measure ℝ) (k : ℕ) (P : Measure (Fin n → ℝ)) : Prop :=
  IsCoupling F P ∧ ∀ Q : Measure (Fin n → ℝ), IsCoupling F Q → maxCostCard k P ≤ maxCostCard k Q

end JointMixND.QuadOT


