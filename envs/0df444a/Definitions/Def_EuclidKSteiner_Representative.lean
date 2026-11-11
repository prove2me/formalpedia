-- Prove2me | Definitions.Def_EuclidKSteiner_Representative
-- name    : EuclidKSteiner_Representative
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:03.996302+00:00
-- url     : https://prove2.me/theorems/0575b040-5d0a-48fc-afb2-93813a13a527
-- title:
--   Definition 2.1: representative subfamilies of weighted $p$-element set families
-- statement:
--   Fix a ground set $U_0$ and a function $\Psi$ on subsets of $U_0$. A **weighted family of $p$-element sets** is a finite family $\mathcal A$ of pairs $(A,w)$ with $A\subseteq U_0$, $|A|=p$ and $w\in\mathbb R$; the same set may appear with several costs. Let $0\le p\le r$.
--
--   **Definition 2.1.** A subfamily $\widehat{\mathcal A}\subseteq\mathcal A$ is **representative for $\Psi$** if for every $B\subseteq U_0$ with $|B|=r-p$,
--   $$\max_{\substack{(A,w)\in\widehat{\mathcal A}\\ A\cap B=\emptyset}}\bigl(\Psi(A\cup B)-w\bigr)=\max_{\substack{(A,w)\in\mathcal A\\ A\cap B=\emptyset}}\bigl(\Psi(A\cup B)-w\bigr),$$
--   where an empty maximum is $-\infty$.
--
--   The operations of Lemma 4.6 are also defined: the **union** $\bigcup_j\mathcal A_j$, the **common cost shift** $\mathrm{shift}_\delta(\mathcal A)=\{(A,w+\delta)\}$ and the **disjoint product** $\mathcal A\star\mathcal A'=\{(A\cup A',w+w'):A\cap A'=\emptyset\}$.
--
--   Representative families let the dynamic program keep, for every possible outside extension $B$, a partial solution with the best completed score $\Phi(A\cup B)-w$.
--
--   **Formalization Note** Representativeness is stated as: $\widehat{\mathcal A}\subseteq\mathcal A$, and for every such $B$ and every $(A,w)\in\mathcal A$ with $A\cap B=\emptyset$ there is $(A',w')\in\widehat{\mathcal A}$ with $A'\cap B=\emptyset$ and $\Psi(A\cup B)-w\le\Psi(A'\cup B)-w'$. Given $\widehat{\mathcal A}\subseteq\mathcal A$ this is the equality of the two maxima with the $-\infty$ convention. Families are sets of pairs.
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), §2.1, Definition 2.1, (2.2), p.5 (PDF p.7); Lemma 4.6, p.18 (PDF p.20)

import Mathlib

namespace EuclidKSteiner

/-!
# Weighted families of p-element sets and representative subfamilies (Definition 2.1)

Bhore, Kisfaludi-Bak, Marx, Odak, *Parameterized Tractability of Euclidean k-Steiner Tree*,
STOC 2027 submission (manuscript sha256 75361687…), §2.1, p.5 (PDF p.7): "A weighted family of
p-element sets is a finite family of pairs (A, w), where A ⊆ U, |A| = p, and w ∈ ℝ. Different costs
for the same set are allowed. Here 0 ≤ p ≤ r, and r is the size of a completed set."
"Definition 2.1. A subfamily Â ⊆ 𝒜 is representative for Ψ if, for every B ⊆ U with |B| = r − p,
max_{(A,w)∈Â, A∩B=∅} (Ψ(A ∪ B) − w) = max_{(A,w)∈𝒜, A∩B=∅} (Ψ(A ∪ B) − w). (2.2) An empty maximum
is −∞, and −∞ − w = −∞."
Lemma 4.6, p.18 (PDF p.20): union, common cost shift, disjoint product.

**Formalization Note**
* A family is a `Set (Finset U × ℝ)` of pairs `(A, w)`; "finite family of p-element sets" is the
  predicate `IsWeightedFamily U₀ p 𝒜` (finite, every `A ⊆ U₀` with `|A| = p`). The ground set is a
  finite set `U₀` inside a type `U`.
* `Representative Ψ U₀ r p 𝒜 Â` says `Â ⊆ 𝒜` and, for every `B ⊆ U₀` with `|B| = r − p` and every
  `(A, w) ∈ 𝒜` with `A ∩ B = ∅`, some `(A', w') ∈ Â` has `A' ∩ B = ∅` and
  `Ψ(A ∪ B) − w ≤ Ψ(A' ∪ B) − w'`. Given `Â ⊆ 𝒜` this is (2.2) with the `−∞` convention: both maxima
  are empty together, and otherwise the left one is at least the right one. `r − p` is used with
  `p ≤ r` only.
-/

/-- A **weighted family of `p`-element sets** over the ground set `U₀`: a finite set of pairs
`(A, w)` with `A ⊆ U₀`, `|A| = p`. Source: §2.1, p.5 (PDF p.7). -/
def IsWeightedFamily {U : Type*} (U₀ : Finset U) (p : ℕ) (𝒜 : Set (Finset U × ℝ)) : Prop :=
  𝒜.Finite ∧ ∀ x ∈ 𝒜, x.1 ⊆ U₀ ∧ x.1.card = p

/-- **Definition 2.1 (representative subfamily).** `Â` is a representative subfamily of `𝒜` for
`Ψ`, completed size `r` and set size `p`, over the ground set `U₀`.
Source: Bhore, Kisfaludi-Bak, Marx, Odak, STOC 2027 submission (manuscript sha256 75361687…),
Definition 2.1, (2.2), p.5 (PDF p.7). -/
def Representative {U : Type*} [DecidableEq U] (Ψ : Finset U → ℝ) (U₀ : Finset U) (r p : ℕ)
    (𝒜 Â : Set (Finset U × ℝ)) : Prop :=
  Â ⊆ 𝒜 ∧ ∀ B : Finset U, B ⊆ U₀ → B.card = r - p → ∀ x ∈ 𝒜, Disjoint x.1 B →
    ∃ y ∈ Â, Disjoint y.1 B ∧ Ψ (x.1 ∪ B) - x.2 ≤ Ψ (y.1 ∪ B) - y.2

/-- **Union** `⋃_{j=1}^m 𝒜_j` of the families `𝒜_0, …, 𝒜_{m−1}`. Source: Lemma 4.6 (1), p.18. -/
def famUnion {U : Type*} {m : ℕ} (𝒜 : Fin m → Set (Finset U × ℝ)) : Set (Finset U × ℝ) :=
  {x | ∃ j, x ∈ 𝒜 j}

/-- **Common cost shift** `shift_δ(𝒜) = {(A, w + δ) : (A, w) ∈ 𝒜}`. Source: Lemma 4.6 (2), p.18. -/
def famShift {U : Type*} (δ : ℝ) (𝒜 : Set (Finset U × ℝ)) : Set (Finset U × ℝ) :=
  {x | ∃ y ∈ 𝒜, x = (y.1, y.2 + δ)}

/-- **Disjoint product** `𝒜 ⋆ 𝒜' = {(A ∪ A', w + w') : (A, w) ∈ 𝒜, (A', w') ∈ 𝒜', A ∩ A' = ∅}`.
Source: Lemma 4.6 (3), p.18 (PDF p.20). -/
def famProd {U : Type*} [DecidableEq U] (𝒜 𝒜' : Set (Finset U × ℝ)) : Set (Finset U × ℝ) :=
  {x | ∃ a ∈ 𝒜, ∃ b ∈ 𝒜', Disjoint a.1 b.1 ∧ x = (a.1 ∪ b.1, a.2 + b.2)}

end EuclidKSteiner


