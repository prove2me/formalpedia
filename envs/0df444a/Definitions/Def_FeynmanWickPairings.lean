-- Prove2me | Definitions.Def_FeynmanWickPairings
-- name    : FeynmanWickPairings
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-21T02:52:33.609364+00:00
-- url     : https://prove2.me/theorems/4f35cfe4-04ef-415e-a568-53602afdfc20
-- title:
--   Pairings of $2n$ labels and the Wick sum
-- statement:
--   This file fixes the combinatorial model used throughout the mission.
--
--   Let $n \in \mathbb{N}$ and consider the $2n$ labels $0, 1, \dots, 2n-1$. A **pairing** of these
--   labels is a permutation $\sigma$ of them that is an involution without fixed points:
--
--   $$ \sigma(\sigma(i)) = i \quad\text{and}\quad \sigma(i) \neq i \qquad \text{for every label } i. $$
--
--   Such a $\sigma$ is the same datum as a partition of the labels into $n$ unordered pairs
--   $\{i, \sigma(i)\}$, i.e. a perfect matching of the $2n$ labels. The collection of all pairings is
--   the finite set $P_n$; for $n = 0$ the condition is vacuous and $P_0$ consists of the empty
--   permutation alone.
--
--   Given a weight $W_{ab}$ attached to ordered pairs of labels, the **product over the pairs** of a
--   pairing $\sigma$ is
--
--   $$ \Pi_\sigma(W) \;=\; \prod_{i \,:\, i < \sigma(i)} W_{i\,\sigma(i)}, $$
--
--   where the index runs over those labels that are smaller than their partner, so that each of the
--   $n$ pairs contributes exactly one factor. The **Wick sum** of $W$ is the sum of these products
--   over all pairings,
--
--   $$ \mathrm{Wick}(W) \;=\; \sum_{\sigma \in P_n} \Pi_\sigma(W). $$
--
--   For $n = 1$ the Wick sum is $W_{01}$; for $n = 2$ it is
--   $W_{01}W_{23} + W_{02}W_{13} + W_{03}W_{12}$.
--
--   These notions are the diagrammatic side of Wick's theorem: a pairing is a way of joining $2n$
--   dangling half-lines into $n$ lines, and the Wick sum collects one propagator factor per line over
--   all such diagrams. They are stated for real-valued weights and are reusable for any moment
--   computation of Gaussian type.
-- source:
--   Feynman diagram, Wikipedia (revision captured 2026-09-20), https://en.wikipedia.org/wiki/Feynman_diagram, sections 'Wick theorem' and 'Higher Gaussian moments — completing Wick's theorem'

import Mathlib

namespace FeynmanWick

/-- `IsPairing σ` says that the permutation `σ` of the `2 * n` labels
`0, 1, …, 2 * n - 1` is a fixed-point-free involution: it squares to the identity
and moves every label. Such a permutation is the same thing as a partition of the
labels into `n` unordered pairs `{i, σ i}` (a perfect matching). -/
def IsPairing {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i, σ (σ i) = i) ∧ ∀ i, σ i ≠ i

instance instDecidableIsPairing {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) :
    Decidable (IsPairing σ) :=
  inferInstanceAs (Decidable ((∀ i, σ (σ i) = i) ∧ ∀ i, σ i ≠ i))

/-- The finite set of all pairings (perfect matchings) of the `2 * n` labels. -/
def pairings (n : ℕ) : Finset (Equiv.Perm (Fin (2 * n))) :=
  Finset.univ.filter IsPairing

/-- The product of the weights `G i (σ i)` over the pairs of a pairing `σ`.
Each pair `{i, σ i}` is counted exactly once, by summing over its smaller element. -/
def pairProd {n : ℕ} (G : Fin (2 * n) → Fin (2 * n) → ℝ)
    (σ : Equiv.Perm (Fin (2 * n))) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i => i < σ i), G i (σ i)

/-- The Wick sum of a symmetric weight `G`: the sum, over all pairings of the
`2 * n` labels, of the product of the weights of the pairs. -/
def wickSum {n : ℕ} (G : Fin (2 * n) → Fin (2 * n) → ℝ) : ℝ :=
  ∑ σ ∈ pairings n, pairProd G σ

end FeynmanWick


