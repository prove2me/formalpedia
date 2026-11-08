-- Prove2me | Definitions.Def_FairFacilityLoc_IsWeightSet
-- name    : FairFacilityLoc_IsWeightSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:15.675923+00:00
-- url     : https://prove2.me/theorems/dc2ad692-112c-4fa3-adfb-922669f67f78
-- title:
--   Weight set of a group effect
-- statement:
--   A **weight set** of a group effect $E$ of $G$ is a compact set $K\subseteq\mathbb R^G_{\ge0}$ that is invariant under bijections of $G$, meaning $(a_{\pi(i)})_{i\in G}\in K$ for all $a\in K$ and all bijections $\pi$, and that satisfies
--   $$E(u)=\max_{a\in K}\sum_{i\in G}a_iu_i\qquad\text{for every }u\in\mathbb R^G_{\ge0}.$$
--
--   An element of $K$ is a weight vector. Proposition 2.3 shows these sets characterize sublinear effects, and the scores of the mechanism for $d\le3$ are computed over them.
--
--   **Formalization Note** The maximum is expressed by `IsGreatest`, so it is attained and $K$ is nonempty.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), §2.1, p.14 (PDF p.16)

import Mathlib

open scoped NNReal

namespace FairFacilityLoc

/-- **Weight set** of a group effect (Yan, Zhou, manuscript, sha256 642a1268…, §2.1, p.14, PDF p.16): a
compact set `K ⊆ ℝ^ι_{≥0}`, invariant under bijections of the group, with
`E u = max_{a ∈ K} ∑ i, a i * u i` for every `u`.

**Formalization Note.** "max" is `IsGreatest`, so the maximum is attained and `K` is nonempty; no default
value of a supremum is involved. The topology on `ι → ℝ≥0` is the product topology. -/
structure IsWeightSet {ι : Type*} [Fintype ι] (E : (ι → ℝ≥0) → ℝ≥0) (K : Set (ι → ℝ≥0)) : Prop where
  /-- `K` is compact. -/
  isCompact : IsCompact K
  /-- `K` is invariant under bijections of the group. -/
  invariant : ∀ a ∈ K, ∀ π : Equiv.Perm ι, (fun i => a (π i)) ∈ K
  /-- `E u` is the largest weighted total distance over `K`. -/
  isGreatest : ∀ u : ι → ℝ≥0, IsGreatest ((fun a : ι → ℝ≥0 => ∑ i, a i * u i) '' K) (E u)

end FairFacilityLoc


