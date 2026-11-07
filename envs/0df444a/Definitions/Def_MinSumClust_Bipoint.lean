-- Prove2me | Definitions.Def_MinSumClust_Bipoint
-- name    : MinSumClust_Bipoint
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:30.646279+00:00
-- url     : https://prove2.me/theorems/a627dedd-0376-4910-9f0a-4698a7ca9ab9
-- title:
--   Good and bad clients, the bipoint weight $\alpha$, and the random labelings $\ell_M,\ell_L$
-- statement:
--   Let $\mathcal S_1,\mathcal S_2$ be partitions of the clients $D$ into $k_1$ and $k_2$ clusters, $C_i(j)$ the cluster of $\mathcal S_i$ containing $j$ and $s_i(j)=|C_i(j)|$. A client $j$ is **good** if $s_1(j)\ge s_2(j)$ and **bad** otherwise; $\mathrm{Good}(S)$ and $\mathrm{Bad}(S)$ are the good and bad clients of a set $S$ (§5.1). The bipoint weight is
--
--   $$\alpha=\frac{k_2-k}{k_2-k_1}.$$
--
--   **Labelings** (§5.3). Independently: for each $S_1\in\mathcal S_1$ with $\mathrm{Good}(S_1)\ne\emptyset$, a uniformly random $j\in\mathrm{Good}(S_1)$ gives the matching label $\ell_M(S_1)=C_2(j)$ (and $\ell_M(S_1)=\bot$ if $\mathrm{Good}(S_1)=\emptyset$); for each $S_2\in\mathcal S_2$ with a bad client, a uniformly random $j\in\mathrm{Bad}(S_2)$ gives the link $\ell_L(S_2)=C_1(j)$. A pair of labelings is **valid** if this sampling can produce it.
--
--   **Formalization Note** The independent uniform choices are one uniform choice from the product of the per-cluster choice sets, which is the same distribution. This $\alpha$ is unrelated to the dual vector of §4.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), §5, "Notation", p.42 (PDF p.44); §5.1, p.42; §5.3, pp.43–44 (PDF pp.45–46)

import Mathlib
import Definitions.Def_MinSumClust_pexp

namespace MinSumClust

variable {D : Type} [Fintype D] [DecidableEq D]

/-- The good clients of a set `S` (§5.1, p.42): `j` is good iff `s₁(j) ≥ s₂(j)`, where
`s_i(j) = |C_i(j)|` is the size of the cluster of `𝒮_i` containing `j`.

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), §5.1, p.42 (PDF p.44). -/
def good (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (S : Finset D) : Finset D :=
  S.filter fun j => (S₂.part j).card ≤ (S₁.part j).card

/-- The bad clients of a set `S` (§5.1, p.42): `s₁(j) < s₂(j)`. -/
def bad (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (S : Finset D) : Finset D :=
  S.filter fun j => (S₁.part j).card < (S₂.part j).card

/-- **The bipoint weight** `α = (k₂ − k)/(k₂ − k₁)` of §5 ("Notation", p.42), with
`k_i = |𝒮_i|`. (Not the dual vector of §4.) -/
noncomputable def alphaBip (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ) : ℝ :=
  ((S₂.parts.card : ℝ) - k) / ((S₂.parts.card : ℝ) - S₁.parts.card)

/-- A pair of labelings (§5.3, p.43): the matching labeling `ℓ_M : 𝒮₁ → 𝒮₂ ∪ {⊥}` and the linking
labeling `ℓ_L : 𝒮_{2,B} → 𝒮₁`; `none` is `⊥` (and the value off the domain). -/
structure Labels (D : Type) where
  /-- the matching labeling `ℓ_M` -/
  lM : Finset D → Option (Finset D)
  /-- the linking labeling `ℓ_L` -/
  lL : Finset D → Option (Finset D)

/-- **The random labelings of §5.3** (pp.43–44). Independently: for each `S₁ ∈ 𝒮₁` with
`Good(S₁) ≠ ∅` a uniform good `j ∈ Good(S₁)` and `ℓ_M(S₁) = C₂(j)` (`ℓ_M(S₁) = ⊥` if
`Good(S₁) = ∅`); for each `S₂ ∈ 𝒮_{2,B}` (a cluster with a bad client) a uniform bad `j ∈ Bad(S₂)`
and `ℓ_L(S₂) = C₁(j)`.

**Formalization Note.** The independent uniform choices are one uniform choice from the product of
the per-cluster choice sets (`Fintype.piFinset`); a coordinate with nothing to sample is `none`. -/
noncomputable def labelPMF (S₁ S₂ : Finpartition (Finset.univ : Finset D)) : PMF (Labels D) :=
  (unifOr
      (Fintype.piFinset (fun S : Finset D =>
          if S ∈ S₁.parts ∧ (good S₁ S₂ S).Nonempty then (good S₁ S₂ S).image some else {none}) ×ˢ
        Fintype.piFinset (fun S : Finset D =>
          if S ∈ S₂.parts ∧ (bad S₁ S₂ S).Nonempty then (bad S₁ S₂ S).image some else {none}))
      (fun _ => none, fun _ => none)).map
    fun c => ⟨fun S => (c.1 S).map S₂.part, fun S => (c.2 S).map S₁.part⟩

/-- Labelings that §5.3 can produce (the support of `labelPMF`); "conditioning on `ℓ_M, ℓ_L`" fixes
such a pair. -/
def ValidLabels (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (ℓ : Labels D) : Prop :=
  ℓ ∈ (labelPMF S₁ S₂).support

end MinSumClust


