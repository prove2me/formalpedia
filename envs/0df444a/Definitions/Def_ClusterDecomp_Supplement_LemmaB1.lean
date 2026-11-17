-- Prove2me | Definitions.Def_ClusterDecomp_Supplement_LemmaB1
-- name    : ClusterDecomp_Supplement_LemmaB1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:58:31.222099+00:00
-- url     : https://prove2.me/theorems/0c93c747-fc7b-45de-bb57-2efd8df02c20
-- title:
--   The induced-subgraph spectral claim refuted in Appendix B
-- statement:
--   **Lemma B.1**, attributed by the paper to [OGT14, Lemma 1.1], asserts that there is a universal $c_0>0$ such that for every $k\ge2$ and every partition of a graph's vertices into $1\le\ell\le k-1$ parts, some part satisfies
--
--   $$
--   \lambda_2(L_{G[P_i]})\le 2c_0k^6\lambda_k(L_G).
--   $$
--
--   Here $G[P_i]$ is the ordinary induced subgraph. The proposition `LemmaB1` packages this universal claim so that Theorem B.6 can assert its negation.
--
--   **Formalization Note** The quantified class is finite simple unweighted positive-degree graphs, and every induced part has at least two vertices and positive degree; $k$ is required to lie in the spectrum's range. These restrictions retain the counterexamples while ensuring every displayed eigenvalue has its intended meaning.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Lemma B.1 p.36 (PDF p.38)

import Mathlib
import Definitions.Def_ClusterDecomp_Supplement_lam

open Finset

namespace ClusterDecomp.Supplement

/-!
# Lemma B.1 (Lemma 1.1 of [OGT14]), the statement the paper refutes

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), Lemma B.1, p.36 (PDF p.38).

"There is a universal constant `c0 > 0` such that for any `k ≥ 2` and any partitioning of `V` into
`ℓ ≤ k − 1` sets `P_1, …, P_ℓ`, `min_{1≤i≤ℓ} λ_2(L_{G[P_i]}) ≤ 2c0 k⁶ λ_k`."

**Formalization Note.**
* `LemmaB1` is a `Prop`, asserted false by Theorem B.6. Since it is refuted, every restriction of the class of
  graphs and partitions it quantifies over makes it weaker and its negation stronger. It is stated only for
  finite simple unweighted graphs (`IsUnweighted`, weights `0/1`, no loops) in which every vertex has positive
  degree, for `k ≤ |V|`, and for partitions whose parts induce subgraphs `G[P_i]` with positive degrees
  everywhere — exactly the cases in which `L_G`, `λ_k(L_G)` and every `λ_2(L_{G[P_i]})` are defined (a
  positive-degree part of a loopless graph has at least two vertices). The junk values of `normLap` and `lam`
  never enter.
* The partition is `P : Fin ℓ → Finset V`, pairwise disjoint and covering `V`, with `1 ≤ ℓ ≤ k − 1`.
  Every part has at least two vertices and positive internal degrees, so `λ_2` is in range. The clause
  "`min_i λ_2(…) ≤ X`" is written as "some `i` has `λ_2(…) ≤ X`".
* `λ_k` is `λ_k(L_G)` and `G[P_i]` is the plain induced subgraph `induced G (P i)`, not `G{P_i}`.
* The vertex type ranges over `Type` (universe 0), which contains every finite graph up to isomorphism.
-/

open ClusterDecomp

/-- Lemma B.1 ([OGT14, Lemma 1.1]) for finite simple unweighted graphs, as a proposition. -/
def LemmaB1 : Prop :=
  ∃ c0 : ℝ, 0 < c0 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), IsUnweighted G → G.PosDeg →
      ∀ k : ℕ, 2 ≤ k → k ≤ Fintype.card V →
        ∀ (ℓ : ℕ) (P : Fin ℓ → Finset V), 1 ≤ ℓ → ℓ ≤ k - 1 →
          (Pairwise fun i j => Disjoint (P i) (P j)) → (∀ v, ∃ i, v ∈ P i) →
          (∀ i, 2 ≤ (P i).card) →
          (∀ i, (induced G (P i)).PosDeg) →
          ∃ i, lam (induced G (P i)) 2 ≤ 2 * c0 * (k : ℝ) ^ 6 * lam G k

end ClusterDecomp.Supplement


