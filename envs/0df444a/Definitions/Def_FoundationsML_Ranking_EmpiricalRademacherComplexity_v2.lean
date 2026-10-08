-- Prove2me | Definitions.Def_FoundationsML_Ranking_EmpiricalRademacherComplexity_v2
-- name    : FoundationsML_Ranking_EmpiricalRademacherComplexity_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:27.701387+00:00
-- url     : https://prove2.me/theorems/4bb2c4d1-1c73-414e-92dc-701ecc3ddefe
-- title:
--   Empirical Rademacher complexity (Definition 3.1) — corrected, Ranking chapter copy
-- statement:
--   **Definition 3.1 (Empirical Rademacher complexity), p. 30, PDF p. 47.** Let $G$ be a family of functions mapping from $Z$ to $[a,b]$ and $S=(z_1,\dots,z_m)$ a fixed sample of size $m$. The empirical Rademacher complexity of $G$ with respect to $S$ is
--   $$\hat R_S(G) = \mathbb E_\sigma\Big[\sup_{g\in G} \frac1m\sum_{i=1}^m \sigma_i g(z_i)\Big],$$
--   where $\sigma_1,\dots,\sigma_m$ are independent uniform $\{-1,+1\}$-valued (Rademacher) random variables.
--
--   **Formalization Note.** Corrected re-issue of the retired module of the same name (same namespace and declaration name). The retired module wrote the supremum as `⨆ g ∈ G, …`, which on $\mathbb R$ is `⨆ g, ⨆ (_ : g ∈ G), …` and equals $\max(\sup_{g\in G}\cdots,0)$ whenever $G\neq$ `univ` (the inner supremum over the empty index $g\notin G$ is `sSup ∅ = 0`), so negative suprema were clipped and the $\sigma\leftrightarrow-\sigma$ symmetry on which Talagrand's lemma and Lemma 9.1 rely was broken. The supremum is now `sSup` of the image of exactly $G$. `σ` ranges over `Fin m → Bool` (`true` = $+1$), so the expectation over $\sigma$ is the exact uniform average over $2^m$ outcomes. Definition 3.1's standing assumption that $G$ maps into a bounded interval $[a,b]$ is carried as an explicit hypothesis by every theorem using the definition; for $m=0$ or $G=\emptyset$ the value is `0`, outside the book's domain.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 30, Definition 3.1 (PDF p. 47)

import Mathlib

namespace FoundationsML.Ranking

/-- The empirical Rademacher complexity of a family `G` of functions `Z → ℝ` with respect to
a fixed sample `S : Fin m → Z` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, Definition 3.1, p. 30, PDF p. 47):
`R̂_S(G) = E_σ[sup_{g∈G} (1/m) ∑_{i=1}^m σ_i g(z_i)]`, where `σ_1,…,σ_m` are independent
uniform `{−1,+1}`-valued (Rademacher) random variables.

**Formalization Note.** `σ` ranges over the finite type `Fin m → Bool` (`true` standing for
`+1`, `false` for `−1`), so the expectation over `σ` is the exact finite uniform average over
its `2^m` outcomes. The supremum over `g ∈ G` is the real supremum `sSup` of the image of `G`
under `g ↦ (1/m) ∑ σ_i g(z_i)`, i.e. the supremum over exactly the set `G`. (The retired
module wrote it as `⨆ g ∈ G, …`, which on `ℝ` unfolds to `⨆ g, ⨆ (_ : g ∈ G), …` and silently
replaces the book's `sup_{g∈G}` by `max(sup_{g∈G} …, 0)` whenever `G ≠ univ`, because the inner
supremum over the empty index `g ∉ G` is `sSup ∅ = 0`; this clipped negative suprema and broke
the `σ ↔ −σ` symmetry on which Talagrand's lemma and the other Rademacher identities rely.)
Definition 3.1 assumes that `G` maps into a bounded interval `[a, b]`; under that standing
assumption every image set is bounded above and, for nonempty `G`, `sSup` is the genuine
supremum. Theorems that use this definition carry that boundedness as an explicit hypothesis.
For `m = 0` or `G = ∅` the value is `0` (Lean's `sSup ∅ = 0`), which lies outside the book's
domain (`m ≥ 1`, `G ≠ ∅`). -/
noncomputable def EmpiricalRademacherComplexity {Z : Type*} {m : ℕ}
    (G : Set (Z → ℝ)) (S : Fin m → Z) : ℝ :=
  (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
    sSup ((fun g : Z → ℝ =>
      (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)) '' G)

end FoundationsML.Ranking


