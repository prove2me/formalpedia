-- Prove2me | Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate
-- name    : BCFGJPSSV26_Stable_Submod_Candidate
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:10:03.433026+00:00
-- url     : https://prove2.me/theorems/78563b9a-c23e-41c7-9a66-38a291e804b9
-- title:
--   BCFGJPSSV26.Stable.Submod.Candidate — The submodular candidate
-- statement:
--   This is module `BCFGJPSSV26.Stable.Submod.Candidate` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   [BCFGJPSSV26b, Section 5]: given the outcome `(LS', Λ)` of the samplings, a coloring of `LS'` in
--   red and blue, and a number `z` of centers to close, the candidate is `(LS' \ Ẑ) ∪ Ŷ`, where `Ŷ`
--   meets every ball of `Λ` and minimizes (approximately) `g = g₁ + g₂`
--   (`BCFGJPSSV26.Stable.gfun`):
--
--   * `g₁(Y) = ∑_j min(d(j, M'), d(j, Y))`, `M' = (LS', Λ)` (`BCFGJPSSV26.Stable.g₁`);
--   * `g₂(Y)`, the sum of the `z` smallest `h_c(Y) = cost_{M'}(M_c) + |M_c| d(c, blue ∪ Λ ∪ Y)` over
--     red `c` (`BCFGJPSSV26.Stable.hcl`, `BCFGJPSSV26.Stable.g₂`), and `Ẑ` attains it.
--
--   Facts:
--
--   * `f = g(∅) - g` is monotone and submodular (`BCFGJPSSV26.Stable.gfun_isMonoF`,
--     `BCFGJPSSV26.Stable.gfun_isSubmod`), from `BCFGJPSSV26.Stable.minOver_supermod` and
--     `BCFGJPSSV26.Stable.sumSmallest_exchange`.
--   * ([BCFGJPSSV26b, Lemma 5.2]) `cost((LS' \ Ẑ) ∪ Ŷ) ≤ g(Ŷ)`
--     (`BCFGJPSSV26.Stable.costF_le_gfun`).
--   * ([BCFGJPSSV26b, Lemma 5.3]) under the color event, `g(∅) ≤ cost(M*_Λ) + 3ε³ opt` and
--     `g(O_Λ ∪ O_P) ≤ cost(M*) + 3ε³ opt`, for `M* = (LS' \ Z*) ∪ O_Λ ∪ O_P` and
--     `M*_Λ = (LS' \ Z*, Λ)` (`BCFGJPSSV26.Stable.Partition.g_bounds`).
--   * ([BCFGJPSSV26b, Lemma 5.4]) `(1 - 1/e) cost(M*) + (1/e) cost(M*_Λ) ≤ Ψ_T + 40 ε opt`
--     and `cost(M*_Λ) ≤ 6 opt` (`BCFGJPSSV26.Stable.Partition.mixed_bd`), with `Ψ_T` the sum of the
--     submodular rows (`BCFGJPSSV26.Stable.Partition.PsiT`).
--   * ([BCFGJPSSV26b, Theorem 3.4]) with the greedy guarantee
--     (`BCFGJPSSV26.Stable.GreedyGuarantee`) for the guess `|O_P|`, the candidate costs at most
--     `Ψ_T + 60 ε opt` (`BCFGJPSSV26.Stable.Partition.costF_candidate_le`).
--
--   **Contents.** The module is published as a whole: 45 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Stable.Partition.costF_candidate_le`, `BCFGJPSSV26.Stable.gfun_isSubmod` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Stable_Submod_Candidate`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Stable/Submod/Candidate.lean

module

public import Definitions.Def_BCFGJPSSV26_Stable_Structure_Partition
public import Definitions.Def_BCFGJPSSV26_Stable_Submod_SeqGreedy
public import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Stable.Submod.Candidate` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The submodular candidate

[BCFGJPSSV26b, Section 5]: given the outcome `(LS', Λ)` of the samplings, a coloring of `LS'` in
red and blue, and a number `z` of centers to close, the candidate is `(LS' \ Ẑ) ∪ Ŷ`, where `Ŷ`
meets every ball of `Λ` and minimizes (approximately) `g = g₁ + g₂`
(`BCFGJPSSV26.Stable.gfun`):

* `g₁(Y) = ∑_j min(d(j, M'), d(j, Y))`, `M' = (LS', Λ)` (`BCFGJPSSV26.Stable.g₁`);
* `g₂(Y)`, the sum of the `z` smallest `h_c(Y) = cost_{M'}(M_c) + |M_c| d(c, blue ∪ Λ ∪ Y)` over
  red `c` (`BCFGJPSSV26.Stable.hcl`, `BCFGJPSSV26.Stable.g₂`), and `Ẑ` attains it.

Facts:

* `f = g(∅) - g` is monotone and submodular (`BCFGJPSSV26.Stable.gfun_isMonoF`,
  `BCFGJPSSV26.Stable.gfun_isSubmod`), from `BCFGJPSSV26.Stable.minOver_supermod` and
  `BCFGJPSSV26.Stable.sumSmallest_exchange`.
* ([BCFGJPSSV26b, Lemma 5.2]) `cost((LS' \ Ẑ) ∪ Ŷ) ≤ g(Ŷ)`
  (`BCFGJPSSV26.Stable.costF_le_gfun`).
* ([BCFGJPSSV26b, Lemma 5.3]) under the color event, `g(∅) ≤ cost(M*_Λ) + 3ε³ opt` and
  `g(O_Λ ∪ O_P) ≤ cost(M*) + 3ε³ opt`, for `M* = (LS' \ Z*) ∪ O_Λ ∪ O_P` and
  `M*_Λ = (LS' \ Z*, Λ)` (`BCFGJPSSV26.Stable.Partition.g_bounds`).
* ([BCFGJPSSV26b, Lemma 5.4]) `(1 - 1/e) cost(M*) + (1/e) cost(M*_Λ) ≤ Ψ_T + 40 ε opt`
  and `cost(M*_Λ) ≤ 6 opt` (`BCFGJPSSV26.Stable.Partition.mixed_bd`), with `Ψ_T` the sum of the
  submodular rows (`BCFGJPSSV26.Stable.Partition.PsiT`).
* ([BCFGJPSSV26b, Theorem 3.4]) with the greedy guarantee
  (`BCFGJPSSV26.Stable.GreedyGuarantee`) for the guess `|O_P|`, the candidate costs at most
  `Ψ_T + 60 ε opt` (`BCFGJPSSV26.Stable.Partition.costF_candidate_le`).
-/

@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

variable {I : Instance}

variable (I) in
/-- `g₁(Y) = ∑_j min(d(j, (LS', Λ)), d(j, Y))`. -/
noncomputable def g₁ (LS' : Finset (Fin I.m)) (Λ : List (Dummy I)) (Y : Finset (Fin I.m)) : ℝ :=
  ∑ j, min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y)

variable (I) in
/-- `h_c(Y) = cost_{M'}(M_c) + |M_c| d(c, blue ∪ Λ ∪ Y)`. -/
noncomputable def hcl (LS' : Finset (Fin I.m)) (Λ : List (Dummy I)) (blue : Finset (Fin I.m))
    (c : Fin I.m) (Y : Finset (Fin I.m)) : ℝ :=
  costMixOn I LS' Λ (clusterMix I LS' Λ c) +
    (clusterMix I LS' Λ c).card * dMix I (.inr c) (blue ∪ Y) Λ

variable (I) in
/-- `g₂(Y)`: the sum of the `z` smallest `h_c(Y)`, `c` red. -/
noncomputable def g₂ (LS' : Finset (Fin I.m)) (Λ : List (Dummy I)) (red blue : Finset (Fin I.m))
    (z : ℕ) (Y : Finset (Fin I.m)) : ℝ :=
  sumSmallest z red fun c ↦ hcl I LS' Λ blue c Y

variable (I) in
/-- `g = g₁ + g₂`. -/
noncomputable def gfun (LS' : Finset (Fin I.m)) (Λ : List (Dummy I)) (red blue : Finset (Fin I.m))
    (z : ℕ) (Y : Finset (Fin I.m)) : ℝ :=
  g₁ I LS' Λ Y + g₂ I LS' Λ red blue z Y

private theorem dMix_union_insert (hv : I.Valid) (a : I.Pt) (F Y : Finset (Fin I.m))
    (Λ : List (Dummy I)) (e : Fin I.m) :
    dMix I a (F ∪ insert e Y) Λ = min (dMix I a (F ∪ Y) Λ) (I.dd a (.inr e)) := by
  unfold dMix
  rw [union_insert, Instance.dSet_insert hv]
  exact min_right_comm _ _ _

private theorem dMix_anti (hv : I.Valid) (a : I.Pt) {F F' : Finset (Fin I.m)} (h : F ⊆ F')
    (Λ : List (Dummy I)) : dMix I a F' Λ ≤ dMix I a F Λ :=
  min_le_min_right _ (Instance.dSet_anti hv h a)

private theorem hcl_insert (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (blue : Finset (Fin I.m)) (c : Fin I.m) (Y : Finset (Fin I.m)) (e : Fin I.m) :
    hcl I LS' Λ blue c (insert e Y) = min (hcl I LS' Λ blue c Y)
      (costMixOn I LS' Λ (clusterMix I LS' Λ c) +
        (clusterMix I LS' Λ c).card * I.dd (.inr c) (.inr e)) := by
  unfold hcl
  rw [dMix_union_insert hv, mul_min_of_nonneg _ _ (Nat.cast_nonneg _), min_add_add_left]

private theorem hcl_anti (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (blue : Finset (Fin I.m)) (c : Fin I.m) {Y Y' : Finset (Fin I.m)} (h : Y ⊆ Y') :
    hcl I LS' Λ blue c Y' ≤ hcl I LS' Λ blue c Y := by
  unfold hcl
  have := dMix_anti hv (.inr c) (union_subset_union_right h (s := blue)) Λ
  have h0 : (0 : ℝ) ≤ (clusterMix I LS' Λ c).card := Nat.cast_nonneg _
  nlinarith

private theorem g₁_term_insert (hv : I.Valid) (a : I.Pt) (M : ℝ) (Y : Finset (Fin I.m))
    (e : Fin I.m) :
    min M (I.dSet a (insert e Y)) = min (min M (I.dSet a Y)) (I.dd a (.inr e)) := by
  rw [Instance.dSet_insert hv, min_assoc]

private theorem gfun_anti (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (red blue : Finset (Fin I.m)) (z : ℕ) {A B : Finset (Fin I.m)} (h : A ⊆ B) :
    gfun I LS' Λ red blue z B ≤ gfun I LS' Λ red blue z A := by
  unfold gfun g₁ g₂
  refine add_le_add (sum_le_sum fun j _ ↦ min_le_min_left _ (Instance.dSet_anti hv h _)) ?_
  exact sumSmallest_mono fun c _ ↦ hcl_anti hv LS' Λ blue c h

private theorem gfun_supermod (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (red blue : Finset (Fin I.m)) (z : ℕ) {A B : Finset (Fin I.m)} (h : A ⊆ B) (e : Fin I.m) :
    gfun I LS' Λ red blue z B - gfun I LS' Λ red blue z (insert e B) ≤
      gfun I LS' Λ red blue z A - gfun I LS' Λ red blue z (insert e A) := by
  unfold gfun
  have h1 : g₁ I LS' Λ B - g₁ I LS' Λ (insert e B) ≤ g₁ I LS' Λ A - g₁ I LS' Λ (insert e A) := by
    unfold g₁
    rw [← sum_sub_distrib, ← sum_sub_distrib]
    refine sum_le_sum fun j _ ↦ ?_
    rw [g₁_term_insert hv, g₁_term_insert hv]
    have hAB : min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) B) ≤
        min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) A) :=
      min_le_min_left _ (Instance.dSet_anti hv h _)
    set a := min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) A)
    set b := min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) B)
    rw [min_def, min_def]
    split_ifs <;> linarith
  have h2 : g₂ I LS' Λ red blue z B + g₂ I LS' Λ red blue z (insert e A) ≤
      g₂ I LS' Λ red blue z A + g₂ I LS' Λ red blue z (insert e B) := by
    unfold g₂
    simp only [hcl_insert hv]
    exact sumSmallest_exchange z red _ fun c _ ↦ hcl_anti hv LS' Λ blue c h
  linarith

private theorem mem_clusterMix_iff {F : Finset (Fin I.m)} {Λ : List (Dummy I)} {c : Fin I.m}
    {j : Fin I.n} :
    j ∈ clusterMix I F Λ c ↔ j ∈ I.cluster F c ∧ I.dSet (.inl j) F ≤ dDums I (.inl j) Λ := by
  classical
  unfold clusterMix
  rw [mem_filter]

private theorem dMix_of_mem_clusterMix {F : Finset (Fin I.m)} {Λ : List (Dummy I)} {c : Fin I.m}
    {j : Fin I.n} (hj : j ∈ clusterMix I F Λ c) :
    dMix I (.inl j) F Λ = I.dd (.inl j) (.inr c) := by
  obtain ⟨h1, h2⟩ := mem_clusterMix_iff.1 hj
  unfold dMix
  rw [min_eq_left h2, Instance.dSet_of_mem_cluster h1]

private theorem pairwise_clusterMix (F : Finset (Fin I.m)) (Λ : List (Dummy I))
    (Z : Finset (Fin I.m)) : (Z : Set (Fin I.m)).PairwiseDisjoint (clusterMix I F Λ) := by
  classical
  intro c _ c' _ hne
  exact (I.disjoint_cluster F hne).mono (filter_subset _ _) (filter_subset _ _)

private theorem sum_split_mix (F : Finset (Fin I.m)) (Λ : List (Dummy I)) (Z : Finset (Fin I.m))
    (G : Fin I.n → ℝ) :
    ∑ j, G j = ∑ j ∈ univ \ Z.biUnion (clusterMix I F Λ), G j +
      ∑ c ∈ Z, ∑ j ∈ clusterMix I F Λ c, G j := by
  rw [← sum_biUnion (pairwise_clusterMix F Λ Z), sum_sdiff (subset_univ _)]

private theorem dMix_sdiff_le {F Z : Finset (Fin I.m)} {Λ : List (Dummy I)}
    {j : Fin I.n} (hj : j ∉ Z.biUnion (clusterMix I F Λ)) :
    dMix I (.inl j) (F \ Z) Λ ≤ dMix I (.inl j) F Λ := by
  rcases F.eq_empty_or_nonempty with rfl | hF
  · rw [empty_sdiff]
  have hjc : j ∈ I.cluster F (I.near F hF (.inl j)) := Instance.mem_cluster_near hF j
  by_cases hc : I.near F hF (.inl j) ∈ Z
  · have hnot : ¬ I.dSet (.inl j) F ≤ dDums I (.inl j) Λ := fun h ↦
      hj (mem_biUnion.2 ⟨_, hc, mem_clusterMix_iff.2 ⟨hjc, h⟩⟩)
    unfold dMix
    rw [min_eq_right (not_le.1 hnot).le]
    exact min_le_right _ _
  · have hmem : I.near F hF (.inl j) ∈ F \ Z := mem_sdiff.2 ⟨Instance.near_mem hF _, hc⟩
    unfold dMix
    refine min_le_min_right _ ?_
    rw [← Instance.dd_near hF]
    exact Instance.dSet_le hmem _

private theorem hcl_eq_sum (LS' : Finset (Fin I.m)) (Λ : List (Dummy I)) (blue : Finset (Fin I.m))
    (c : Fin I.m) (Y : Finset (Fin I.m)) :
    hcl I LS' Λ blue c Y = ∑ j ∈ clusterMix I LS' Λ c,
      (dMix I (.inl j) LS' Λ + dMix I (.inr c) (blue ∪ Y) Λ) := by
  unfold hcl costMixOn
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]

private theorem dSet_le_of_near {F Zs blue : Finset (Fin I.m)} {c : Fin I.m}
    (hcol : ∀ h : (F \ Zs).Nonempty, I.near (F \ Zs) h (.inr c) ∈ blue) (hv : I.Valid) :
    I.dSet (.inr c) blue ≤ I.dSet (.inr c) (F \ Zs) := by
  rcases (F \ Zs).eq_empty_or_nonempty with h | h
  · rw [h, Instance.dSet_empty]
    exact Instance.dSet_le_dMax hv _ _
  · rw [← Instance.dd_near h]
    exact Instance.dSet_le (hcol h) _

/-- **The bound of [BCFGJPSSV26b, Lemma 5.3], abstractly**: with `Z` of the right size in `red`,
whose nearest centers outside `Z` are blue,
`g(Y) ≤ cost((LS' \ Z) ∪ Y, Λ) + 3 ∑_{c ∈ Z} cost_{M'}(M_c)`. -/
private theorem gfun_le_of_color (hv : I.Valid) {LS' red blue Zs : Finset (Fin I.m)}
    {Λ : List (Dummy I)} {z : ℕ} (hZr : Zs ⊆ red) (hZc : Zs.card = z)
    (hcol : ∀ c ∈ Zs, ∀ h : (LS' \ Zs).Nonempty, I.near (LS' \ Zs) h (.inr c) ∈ blue)
    (Y : Finset (Fin I.m)) :
    gfun I LS' Λ red blue z Y ≤ costMix I ((LS' \ Zs) ∪ Y) Λ +
      3 * ∑ c ∈ Zs, costMixOn I LS' Λ (clusterMix I LS' Λ c) := by
  have h2 := sumSmallest_le hZr hZc fun c ↦ hcl I LS' Λ blue c Y
  have hT : ∀ j : Fin I.n, dMix I (.inl j) ((LS' \ Zs) ∪ Y) Λ =
      min (dMix I (.inl j) (LS' \ Zs) Λ) (I.dSet (.inl j) Y) := by
    intro j
    unfold dMix
    rw [Instance.dSet_union hv]
    exact min_right_comm _ _ _
  have hout : ∀ j : Fin I.n, min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y) ≤
      dMix I (.inl j) ((LS' \ Zs) ∪ Y) Λ := by
    intro j
    rw [hT]
    exact min_le_min_right _ (dMix_anti hv _ sdiff_subset Λ)
  have hin : ∀ c ∈ Zs, ∀ j ∈ clusterMix I LS' Λ c, dMix I (.inr c) (blue ∪ Y) Λ ≤
      dMix I (.inl j) LS' Λ + dMix I (.inl j) ((LS' \ Zs) ∪ Y) Λ := by
    intro c hc j hj
    have h1 : dMix I (.inr c) (blue ∪ Y) Λ ≤ dMix I (.inr c) ((LS' \ Zs) ∪ Y) Λ := by
      unfold dMix
      refine min_le_min_right _ ?_
      rw [Instance.dSet_union hv, Instance.dSet_union hv]
      exact min_le_min_right _ (dSet_le_of_near (hcol c hc) hv)
    have h3 := dMix_triangle hv (.inr c) (.inl j) ((LS' \ Zs) ∪ Y) Λ
    rw [dMix_of_mem_clusterMix hj, Instance.dd_comm hv]
    linarith
  unfold gfun g₂
  refine (add_le_add le_rfl h2).trans ?_
  unfold g₁ costMix costMixOn
  rw [sum_split_mix LS' Λ Zs, sum_split_mix LS' Λ Zs (fun j ↦
    dMix I (.inl j) ((LS' \ Zs) ∪ Y) Λ)]
  simp only [hcl_eq_sum, mul_sum]
  have e1 := sum_le_sum (s := univ \ Zs.biUnion (clusterMix I LS' Λ)) fun j _ ↦ hout j
  have e2 : ∀ c ∈ Zs, ∑ j ∈ clusterMix I LS' Λ c,
      min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y) +
      ∑ j ∈ clusterMix I LS' Λ c, (dMix I (.inl j) LS' Λ + dMix I (.inr c) (blue ∪ Y) Λ) ≤
      ∑ j ∈ clusterMix I LS' Λ c, dMix I (.inl j) ((LS' \ Zs) ∪ Y) Λ +
        ∑ j ∈ clusterMix I LS' Λ c, 3 * dMix I (.inl j) LS' Λ := by
    intro c hc
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum fun j hj ↦ ?_
    have := hin c hc j hj
    have := min_le_left (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y)
    linarith
  have e3 := sum_le_sum e2
  rw [sum_add_distrib, sum_add_distrib] at e3
  linarith

/-- `g(∅) - g` is monotone. -/
theorem gfun_isMonoF (hv : I.Valid) (LS' : Finset (Fin I.m)) (Λ : List (Dummy I))
    (red blue : Finset (Fin I.m)) (z : ℕ) :
    IsMonoF fun Y ↦ gfun I LS' Λ red blue z ∅ - gfun I LS' Λ red blue z Y := by
  intro A B h
  have := gfun_anti hv LS' Λ red blue z h
  simp only
  linarith

/-- **The candidate costs at most `g(Ŷ)`** ([BCFGJPSSV26b, Lemma 5.2]), when `Ŷ` meets every ball
and `Ẑ` attains `g₂(Ŷ)`. -/
theorem costF_le_gfun (hv : I.Valid) {LS' red blue : Finset (Fin I.m)} {Λ : List (Dummy I)}
    {z : ℕ} (hred : red ⊆ LS') (hblue : blue = LS' \ red) {Y Zh : Finset (Fin I.m)}
    (hY : ∀ l ∈ Λ, ∃ i ∈ Y, i ∈ l.ball) (hZ : Zh ⊆ red) (hZc : Zh.card = z)
    (hZs : ∑ c ∈ Zh, hcl I LS' Λ blue c Y = g₂ I LS' Λ red blue z Y) :
    I.costF ((LS' \ Zh) ∪ Y) ≤ gfun I LS' Λ red blue z Y := by
  have _ := hred
  have _ := hZc
  have hrad : ∀ l ∈ Λ, 0 ≤ l.radius := fun l hl ↦ by
    obtain ⟨i, -, hi⟩ := hY l hl
    exact (Instance.dd_nonneg hv _ _).trans (Dummy.mem_ball.1 hi)
  have hblueT : blue ∪ Y ⊆ (LS' \ Zh) ∪ Y := by
    refine union_subset_union_left ?_
    rw [hblue]
    exact sdiff_subset_sdiff le_rfl hZ
  have hout : ∀ j ∉ Zh.biUnion (clusterMix I LS' Λ), I.dSet (.inl j) ((LS' \ Zh) ∪ Y) ≤
      min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y) := by
    intro j hj
    refine le_min ?_ (Instance.dSet_anti hv subset_union_right _)
    exact (dSet_union_le_dMix hv hY _ _).trans (dMix_sdiff_le hj)
  have hin : ∀ c ∈ Zh, ∀ j ∈ clusterMix I LS' Λ c, I.dSet (.inl j) ((LS' \ Zh) ∪ Y) ≤
      dMix I (.inl j) LS' Λ + dMix I (.inr c) (blue ∪ Y) Λ := by
    intro c _ j hj
    rw [dMix_of_mem_clusterMix hj]
    refine (Instance.dSet_triangle hv _ (.inr c) _).trans (add_le_add le_rfl ?_)
    calc I.dSet (.inr c) ((LS' \ Zh) ∪ Y) ≤ I.dSet (.inr c) ((blue ∪ Y) ∪ Y) :=
          Instance.dSet_anti hv (by rw [union_assoc, union_self]; exact hblueT) _
      _ ≤ dMix I (.inr c) (blue ∪ Y) Λ := dSet_union_le_dMix hv hY _ _
  unfold gfun
  rw [← hZs]
  unfold Instance.costF g₁
  rw [sum_split_mix LS' Λ Zh, sum_split_mix LS' Λ Zh (fun j ↦
    min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y))]
  simp only [hcl_eq_sum]
  have h1 := sum_le_sum (s := univ \ Zh.biUnion (clusterMix I LS' Λ))
    fun j hj ↦ hout j (mem_sdiff.1 hj).2
  have h2 := sum_le_sum fun c hc ↦ sum_le_sum fun j hj ↦ hin c hc j hj
  have h3 : 0 ≤ ∑ c ∈ Zh, ∑ j ∈ clusterMix I LS' Λ c,
      min (dMix I (.inl j) LS' Λ) (I.dSet (.inl j) Y) :=
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦
      le_min (dMix_nonneg hv hrad _ _) (Instance.dSet_nonneg hv _ _)
  linarith

variable (I) in
/-- **The greedy guarantee** for the guess `p'`, with `T` rounds: `Ŷ` gains at least a fraction
`1 - (T/(T + 1))^T` of what any choice of one facility in each ball and `p'` more facilities
gains. -/
def GreedyGuarantee (T : ℕ) (g : Finset (Fin I.m) → ℝ) (Λ : List (Dummy I)) (p' : ℕ)
    (Y : Finset (Fin I.m)) : Prop :=
  ∀ o : Fin Λ.length → Fin I.m, (∀ i, o i ∈ (Λ.get i).ball) → ∀ E : Finset (Fin I.m),
    E.card = p' → (1 - ((T : ℝ) / (T + 1)) ^ T) * (g ∅ - g (univ.image o ∪ E)) ≤ g ∅ - g Y

private theorem mixed_arith_L {ie ε A P S SM SA Cr kl : ℝ} (hie0 : 0 ≤ ie)
    (hie1 : ie ≤ 36875 / 100000) (hε : 0 ≤ ε) (hε' : ε < 1 / 200) (hP0 : 0 ≤ P) (hS0 : 0 ≤ S)
    (hkl1 : kl ≤ 23 / 65) (hSM : SM ≤ A) (hSA : SA ≤ A + 2 * Cr)
    (hCr : Cr ≤ (1 + kl + 8 * ε) * P + ε * S) :
    (1 - ie) * SM + ie * SA ≤ A + 2 * ie * ((1 + kl) * P) + ε * (59 / 10 * P + 3 / 4 * S) ∧
      SA ≤ A + 3 * P + 2 * ε * S := by
  have e1 := mul_le_mul_of_nonneg_left hSM (by linarith : (0 : ℝ) ≤ 1 - ie)
  have e2 := mul_le_mul_of_nonneg_left hSA hie0
  have e3 := mul_le_mul_of_nonneg_left hCr hie0
  have hεP := mul_nonneg hε hP0
  have hεS := mul_nonneg hε hS0
  have e4 := mul_le_mul_of_nonneg_right hie1 hεP
  have e5 := mul_le_mul_of_nonneg_right hie1 hεS
  have e6 := mul_le_mul_of_nonneg_right hkl1 hP0
  have e7 := mul_le_mul_of_nonneg_right hε'.le hP0
  constructor
  · nlinarith
  · nlinarith

private theorem mixed_arith_P {ie ε A P S SM SA κ : ℝ} (hie0 : 0 ≤ ie) (hie1 : ie ≤ 36875 / 100000)
    (hε : 0 ≤ ε) (hε' : ε < 1 / 200) (hP0 : 0 ≤ P) (hS0 : 0 ≤ S) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 23 / 65) (hSM : SM ≤ A) (hSA : SA ≤ A + (1 + κ + 4 * ε) * P) :
    (1 - ie) * SM + ie * SA ≤ A + 2 * ie * ((1 + κ) * P) + ε * (59 / 10 * P + 3 / 4 * S) ∧
      SA ≤ A + 3 * P + 2 * ε * S := by
  have e1 := mul_le_mul_of_nonneg_left hSM (by linarith : (0 : ℝ) ≤ 1 - ie)
  have e2 := mul_le_mul_of_nonneg_left hSA hie0
  have hεP := mul_nonneg hε hP0
  have hεS := mul_nonneg hε hS0
  have e4 := mul_le_mul_of_nonneg_right hie1 hεP
  have e6 := mul_le_mul_of_nonneg_right hκ1 hP0
  have e7 := mul_le_mul_of_nonneg_right hε'.le hP0
  have e8 : 0 ≤ ie * ((1 + κ) * P) := mul_nonneg hie0 (mul_nonneg (by linarith) hP0)
  constructor
  · nlinarith
  · nlinarith

private theorem mixed_arith_R {ie ε A P S SM SA : ℝ} (hie0 : 0 ≤ ie) (hie1 : ie ≤ 36875 / 100000)
    (hε : 0 ≤ ε) (hε' : ε < 1 / 200) (hP0 : 0 ≤ P) (hS0 : 0 ≤ S)
    (hSM : SM ≤ A + (P + ε * P)) (hSA : SA ≤ A + (P + ε * P)) :
    (1 - ie) * SM + ie * SA ≤ A + P + ε * (59 / 10 * P + 3 / 4 * S) ∧
      SA ≤ A + 3 * P + 2 * ε * S := by
  have e1 := mul_le_mul_of_nonneg_left hSM (by linarith : (0 : ℝ) ≤ 1 - ie)
  have e2 := mul_le_mul_of_nonneg_left hSA hie0
  have hεP := mul_nonneg hε hP0
  have hεS := mul_nonneg hε hS0
  have e7 := mul_le_mul_of_nonneg_right hε'.le hP0
  constructor
  · nlinarith
  · nlinarith

/-- The dummies of a list of length `|A|` containing the distinct `φ c`, `c ∈ A`, are those. -/
private theorem exists_eq_of_length_eq_card' {X : Ctx} {Λ : List (Dummy X.I)}
    {A : Finset (Fin X.I.m)} {φ : Fin X.I.m → Dummy X.I} (hlen : Λ.length = A.card)
    (hmem : ∀ c ∈ A, φ c ∈ Λ) (hinj : Set.InjOn φ A) {l : Dummy X.I} (hl : l ∈ Λ) :
    ∃ c ∈ A, φ c = l := by
  classical
  have hsub : A.image φ ⊆ Λ.toFinset := fun x hx ↦ by
    obtain ⟨c, hc, rfl⟩ := mem_image.1 hx
    exact List.mem_toFinset.2 (hmem c hc)
  have hcard : Λ.toFinset.card ≤ (A.image φ).card := by
    rw [card_image_of_injOn hinj, ← hlen]
    exact List.toFinset_card_le Λ
  have heq := eq_of_subset_of_card_le hsub hcard
  exact mem_image.1 (heq ▸ List.mem_toFinset.2 hl)

namespace Partition

variable {X : Ctx} {Λ₁ : List (Dummy X.I)} {w₁ : ClientWitness X Λ₁}
  {LS' : Finset (Fin X.I.m)} {Λ₂ : List (Dummy X.I)} {w₂ : ClusterWitness w₁ LS' Λ₂}
  (Q : Partition w₂)

open Classical in
/-- The **submodular row** of an optimal cluster. -/
noncomputable def rowT (c : Fin X.I.m) : ℝ :=
  if c ∈ X.OSall w₁.OL then (1 + eta) * X.costO c
  else if c ∈ w₁.OLe then X.costO c + 2 / Real.exp 1 * ((X.C c).card * X.per c)
  else if c ∈ Q.OLam ∪ Q.OP then
    X.costO c + 2 / Real.exp 1 * ((1 + X.kap c) * ((X.C c).card * X.per c))
  else X.costO c + (X.C c).card * X.per c

/-- `Ψ_T`: the sum of the submodular rows. -/
noncomputable def PsiT : ℝ := ∑ c ∈ X.O, Q.rowT c

/-- The substitutes of `O_S` and `O_R` are kept centers outside `Z*`. -/
private theorem mem_sdiff_Zstar {i : Fin X.I.m}
    (hi : i ∈ (X.OSall w₁.OL).image X.σ₀ ∪ Q.OR.image Q.σR) : i ∈ LS' \ Q.Zstar := by
  classical
  refine mem_sdiff.2 ⟨?_, fun hZ ↦ (mem_sdiff.1 (Q.Zstar_sub hZ)).2 hi⟩
  rcases mem_union.1 hi with h | h
  · exact Q.σ₀_sub h
  · obtain ⟨c, hc, rfl⟩ := mem_image.1 h
    exact Q.Gam_sub (mem_biUnion.2 ⟨c, hc, (Q.σR_gam c hc).1⟩)

/-- A kept center serves both mixed sets. -/
private theorem le_of_mem_sdiff_Zstar (hv : X.I.Valid) {i : Fin X.I.m} (hi : i ∈ LS' \ Q.Zstar)
    (j : Fin X.I.n) :
    X.I.dSet (.inl j) ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP) ≤ X.I.dd (.inl j) (.inr i) ∧
      dMix X.I (.inl j) (LS' \ Q.Zstar) (Λ₁ ++ Λ₂) ≤ X.I.dd (.inl j) (.inr i) := by
  have h := Instance.dSet_le hi (.inl j)
  refine ⟨(Instance.dSet_anti hv ?_ _).trans h, (dMix_le_dSet _ _ _).trans h⟩
  exact subset_union_left.trans subset_union_left

/-- `|C*| avg_S(C*) ≤ cost_S(C*)`. -/
private theorem card_mul_avgS_le (H : Hyp X) (c : Fin X.I.m) :
    ((X.C c).card : ℝ) * X.avgS c ≤ X.costS (X.C c) := by
  have h0 : 0 ≤ X.costS (X.C c) := Instance.costOn_nonneg H.valid _ _
  unfold Ctx.avgS
  rcases eq_or_ne ((X.C c).card : ℝ) 0 with h | h
  · rw [h, zero_mul]
    exact h0
  · rw [mul_div_cancel₀ _ h]

/-- `1/e ≤ 0.36875`. -/
private theorem inv_exp_le : 1 / Real.exp 1 ≤ 36875 / 100000 := by
  have hE : (2718 : ℝ) / 1000 < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  rw [div_le_iff₀ (Real.exp_pos 1)]
  nlinarith

/-- The sums of a cluster in the two mixed sets. -/
private noncomputable def SM (c : Fin X.I.m) : ℝ :=
  ∑ j ∈ X.C c, X.I.dSet (.inl j) ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP)

/-- The sums of a cluster in the two mixed sets. -/
private noncomputable def SA (c : Fin X.I.m) : ℝ :=
  ∑ j ∈ X.C c, dMix X.I (.inl j) (LS' \ Q.Zstar) (Λ₁ ++ Λ₂)

private theorem sum_dd_add (c : Fin X.I.m) (t : ℝ) :
    ∑ j ∈ X.C c, (X.I.dd (.inl j) (.inr c) + t) = X.costO c + (X.C c).card * t := by
  rw [sum_add_distrib, sum_const, nsmul_eq_mul]
  rfl

/-- A center of `M*` serves its own cluster. -/
private theorem SM_le_own (H : Hyp X) {c : Fin X.I.m} (h : c ∈ (LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP) :
    Q.SM c ≤ X.costO c := by
  have _ := H
  exact sum_le_sum fun j _ ↦ Instance.dSet_le h _

/-- A kept center at distance `t` of `c`. -/
private theorem le_of_kept (H : Hyp X) {c i : Fin X.I.m} (hi : i ∈ LS' \ Q.Zstar) {t : ℝ}
    (ht : X.dF c i ≤ t) :
    Q.SM c ≤ X.costO c + (X.C c).card * t ∧ Q.SA c ≤ X.costO c + (X.C c).card * t := by
  have hle : ∀ j, X.I.dd (.inl j) (.inr i) ≤ X.I.dd (.inl j) (.inr c) + t := fun j ↦
    (Instance.dd_triangle H.valid _ (.inr c) _).trans (by unfold Ctx.dF at ht; linarith)
  rw [← sum_dd_add]
  exact ⟨sum_le_sum fun j _ ↦ (Q.le_of_mem_sdiff_Zstar H.valid hi j).1.trans (hle j),
    sum_le_sum fun j _ ↦ (Q.le_of_mem_sdiff_Zstar H.valid hi j).2.trans (hle j)⟩

private theorem P_nonneg (H : Hyp X) (c : Fin X.I.m) : 0 ≤ ((X.C c).card : ℝ) * X.per c :=
  mul_nonneg (Nat.cast_nonneg _) (per_nonneg H.valid _ _ _)

/-- The mixed bound of a cluster of `O_Λ`. -/
private theorem row_mixed_L (H : Hyp X) {c : Fin X.I.m} (hcS : c ∉ X.OSall w₁.OL)
    (hL : c ∈ Q.OLam) :
    (1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c ≤
      Q.rowT c + X.ε * (59 / 10 * ((X.C c).card * X.per c) + 3 / 4 * X.costS (X.C c)) ∧
    Q.SA c ≤ X.costO c + 3 * ((X.C c).card * X.per c) + 2 * X.ε * X.costS (X.C c) := by
  classical
  obtain ⟨hmem, -, -, hrad⟩ := Q.φ_spec H
  obtain ⟨hr1, hr2⟩ := hrad c hL
  have hSA : Q.SA c ≤ X.costO c + 2 * ((X.C c).card * (Q.φ c).radius) := by
    rw [show 2 * ((X.C c).card * (Q.φ c).radius) = (X.C c).card * (2 * (Q.φ c).radius) by ring,
      ← sum_dd_add]
    refine sum_le_sum fun j _ ↦ (dMix_le_dist (hmem c hL) _ _).trans ?_
    have := Dummy.dist_le H.valid (Q.φ c) (.inl j) (.inr c)
    linarith
  have hCr : ((X.C c).card : ℝ) * (Q.φ c).radius ≤
      (1 + (if c ∈ w₁.OLe then 0 else X.kap c) + 8 * X.ε) * ((X.C c).card * X.per c) +
        X.ε * X.costS (X.C c) := by
    have h1 := mul_le_mul_of_nonneg_left hr2 (Nat.cast_nonneg (α := ℝ) (X.C c).card)
    have h3 := mul_le_mul_of_nonneg_left (card_mul_avgS_le H c) H.eps_pos.le
    linarith
  have hκ := kappa_mem (X.xr c)
  have hkl : (if c ∈ w₁.OLe then 0 else X.kap c) ≤ 23 / 65 := by
    split_ifs
    · norm_num
    · exact hκ.2
  have hie0 : 0 ≤ 1 / Real.exp 1 := by positivity
  have h := mixed_arith_L (S := X.costS (X.C c)) hie0 inv_exp_le H.eps_pos.le H.eps_lt
    (P_nonneg H c)
    (Instance.costOn_nonneg H.valid _ _ : 0 ≤ X.costS (X.C c)) hkl
    (Q.SM_le_own H (mem_union_left _ (mem_union_right _ hL))) hSA hCr
  refine ⟨le_of_le_of_eq h.1 ?_, h.2⟩
  unfold rowT
  rw [if_neg hcS]
  split_ifs with h1 h2
  · ring
  · ring
  · exact absurd (mem_union_left _ hL) h2

/-- The mixed bound of a cluster of `O_P`. -/
private theorem row_mixed_P (H : Hyp X) {c : Fin X.I.m} (hcS : c ∉ X.OSall w₁.OL) (hP : c ∈ Q.OP) :
    (1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c ≤
      Q.rowT c + X.ε * (59 / 10 * ((X.C c).card * X.per c) + 3 / 4 * X.costS (X.C c)) ∧
    Q.SA c ≤ X.costO c + 3 * ((X.C c).card * X.per c) + 2 * X.ε * X.costS (X.C c) := by
  classical
  obtain ⟨-, -, hd2, -⟩ := Q.cover H
  have hnL : c ∉ Q.OLam := fun h ↦ disjoint_left.1 hd2 (mem_union_right _ h) hP
  have hnE : c ∉ w₁.OLe := fun h ↦ hnL (mem_union_left _ (w₁.OLe_sub h))
  have hSA := (Q.le_of_kept H (Q.mem_sdiff_Zstar (Q.ψ_mem c hP)) (Q.ψ_dist c hP)).2
  rw [show ((X.C c).card : ℝ) * ((1 + X.kap c + 4 * X.ε) * X.per c) =
    (1 + X.kap c + 4 * X.ε) * ((X.C c).card * X.per c) by ring] at hSA
  have hκ : 12 / 65 ≤ X.kap c ∧ X.kap c ≤ 23 / 65 := kappa_mem (X.xr c)
  have hie0 : 0 ≤ 1 / Real.exp 1 := by positivity
  have h := mixed_arith_P (S := X.costS (X.C c)) (κ := X.kap c) hie0 inv_exp_le H.eps_pos.le
    H.eps_lt (P_nonneg H c)
    (Instance.costOn_nonneg H.valid _ _ : 0 ≤ X.costS (X.C c)) (by linarith [hκ.1]) hκ.2
    (Q.SM_le_own H (mem_union_right _ hP)) hSA
  refine ⟨le_of_le_of_eq h.1 ?_, h.2⟩
  unfold rowT
  rw [if_neg hcS, if_neg hnE, if_pos (mem_union_right _ hP)]
  ring

/-- The mixed bound of a cluster of `O_R`. -/
private theorem row_mixed_R (H : Hyp X) {c : Fin X.I.m} (hcS : c ∉ X.OSall w₁.OL) (hR : c ∈ Q.OR) :
    (1 - 1 / Real.exp 1) * Q.SM c + 1 / Real.exp 1 * Q.SA c ≤
      Q.rowT c + X.ε * (59 / 10 * ((X.C c).card * X.per c) + 3 / 4 * X.costS (X.C c)) ∧
    Q.SA c ≤ X.costO c + 3 * ((X.C c).card * X.per c) + 2 * X.ε * X.costS (X.C c) := by
  classical
  obtain ⟨-, -, -, hd3⟩ := Q.cover H
  have hnLP : c ∉ Q.OLam ∪ Q.OP := fun h ↦ by
    rcases mem_union.1 h with h | h
    · exact disjoint_left.1 hd3 (mem_union_left _ (mem_union_right _ h)) hR
    · exact disjoint_left.1 hd3 (mem_union_right _ h) hR
  have hnE : c ∉ w₁.OLe := fun h ↦
    hnLP (mem_union_left _ (show c ∈ Q.OLam from mem_union_left _ (w₁.OLe_sub h)))
  obtain ⟨hSM, hSA⟩ := Q.le_of_kept H
    (Q.mem_sdiff_Zstar (mem_union_right _ (mem_image_of_mem _ hR))) (Q.σR_gam c hR).2
  have e : ((X.C c).card : ℝ) * ((1 + X.ε) * X.per c) =
      (X.C c).card * X.per c + X.ε * ((X.C c).card * X.per c) := by ring
  rw [e] at hSM hSA
  have hie0 : 0 ≤ 1 / Real.exp 1 := by positivity
  have h := mixed_arith_R (S := X.costS (X.C c)) hie0 inv_exp_le H.eps_pos.le H.eps_lt
    (P_nonneg H c)
    (Instance.costOn_nonneg H.valid _ _ : 0 ≤ X.costS (X.C c)) hSM hSA
  refine ⟨le_of_le_of_eq h.1 ?_, h.2⟩
  unfold rowT
  rw [if_neg hcS, if_neg hnE, if_neg hnLP]

/-- The mixed bound of a cluster of `O_S`. -/
private theorem row_mixed_S (H : Hyp X) {c : Fin X.I.m} (hS : c ∈ X.OSall w₁.OL) :
    Q.SM c ≤ ∑ j ∈ X.C c, X.dist j (X.σ₀ c) ∧ Q.SA c ≤ ∑ j ∈ X.C c, X.dist j (X.σ₀ c) := by
  have hi := Q.mem_sdiff_Zstar (mem_union_left _ (mem_image_of_mem X.σ₀ hS))
  exact ⟨sum_le_sum fun j _ ↦ (Q.le_of_mem_sdiff_Zstar H.valid hi j).1,
    sum_le_sum fun j _ ↦ (Q.le_of_mem_sdiff_Zstar H.valid hi j).2⟩

/-- `|C*| per ≤ (1 + 2ε) cost_OPT(C*)`. -/
private theorem card_mul_per_le (H : Hyp X) (c : Fin X.I.m) :
    ((X.C c).card : ℝ) * X.per c ≤ (1 + 2 * X.ε) * X.costO c := by
  rcases (X.C c).eq_empty_or_nonempty with hC | hC
  · rw [hC, card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (by linarith [H.eps_pos]) (sum_nonneg fun _ _ ↦ Instance.dd_nonneg H.valid _ _)
  · have h := per_le_avg H.valid H.eps_pos (by linarith [H.eps_lt]) hC c
    have hn : (0 : ℝ) < (X.C c).card := by exact_mod_cast hC.card_pos
    have e : (1 + 2 * X.ε) * X.costO c =
        (X.C c).card * ((1 + 2 * X.ε) * (X.costO c / (X.C c).card)) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h hn.le

/-- The facilities of the balls: each dummy's cluster center is in its ball. -/
theorem exists_ball_choice (H : Hyp X) :
    ∃ o : Fin (Λ₁ ++ Λ₂).length → Fin X.I.m, (∀ i, o i ∈ ((Λ₁ ++ Λ₂).get i).ball) ∧
      univ.image o = Q.OLam := by
  classical
  obtain ⟨hmem, hinj, hlen, hrad⟩ := Q.φ_spec H
  have hex : ∀ l ∈ Λ₁ ++ Λ₂, ∃ c ∈ Q.OLam, Q.φ c = l := fun l hl ↦
    exists_eq_of_length_eq_card' hlen hmem hinj hl
  refine ⟨fun i ↦ (hex _ (List.get_mem _ i)).choose, fun i ↦ ?_, ?_⟩
  · obtain ⟨hc, heq⟩ := (hex _ (List.get_mem _ i)).choose_spec
    rw [Dummy.mem_ball]
    have := (hrad _ hc).1
    rw [heq, Instance.dd_comm H.valid] at this
    exact this
  · ext c
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact (hex _ (List.get_mem _ i)).choose_spec.1
    · intro hc
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 (hmem c hc)
      refine ⟨i, ?_⟩
      obtain ⟨h1, h2⟩ := (hex _ (List.get_mem _ i)).choose_spec
      exact hinj h1 hc (h2.trans hi)

/-- **The values of `g` at `∅` and at `O_Λ ∪ O_P`**, under the color event ([BCFGJPSSV26b,
Lemma 5.3]). -/
theorem g_bounds (H : Hyp X) {red blue : Finset (Fin X.I.m)} (hred : red ⊆ LS')
    (hblue : blue = LS' \ red) (hcol : Q.ColorEvent red blue) :
    gfun X.I LS' (Λ₁ ++ Λ₂) red blue Q.z ∅ ≤
        costMix X.I (LS' \ Q.Zstar) (Λ₁ ++ Λ₂) + 3 * X.ε ^ 3 * X.opt ∧
      gfun X.I LS' (Λ₁ ++ Λ₂) red blue Q.z (Q.OLam ∪ Q.OP) ≤
        X.I.costF ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP) + 3 * X.ε ^ 3 * X.opt := by
  have _ := hred
  have _ := hblue
  have hrad := Q.radius_nonneg H
  have hZ : ∑ c ∈ Q.Zstar, costMixOn X.I LS' (Λ₁ ++ Λ₂) (clusterMix X.I LS' (Λ₁ ++ Λ₂) c) <
      X.ε ^ 3 * X.opt := by
    refine lt_of_le_of_lt ?_ Q.cost_mix
    refine sum_le_sum_of_subset_of_nonneg (Q.Zstar_sub.trans subset_union_right) fun c _ _ ↦ ?_
    exact sum_nonneg fun j _ ↦ dMix_nonneg H.valid hrad _ _
  have hg := fun Y ↦
    gfun_le_of_color (Λ := Λ₁ ++ Λ₂) (z := Q.z) H.valid hcol.1 Q.Zstar_card hcol.2 Y
  refine ⟨?_, ?_⟩
  · have := hg ∅
    rw [union_empty] at this
    linarith
  · have := hg (Q.OLam ∪ Q.OP)
    have hle : costMix X.I ((LS' \ Q.Zstar) ∪ (Q.OLam ∪ Q.OP)) (Λ₁ ++ Λ₂) ≤
        X.I.costF ((LS' \ Q.Zstar) ∪ Q.OLam ∪ Q.OP) := by
      rw [← union_assoc]
      unfold costMix costMixOn Instance.costF
      exact sum_le_sum fun j _ ↦ dMix_le_dSet (.inl j) _ _
    linarith

end Partition

end BCFGJPSSV26.Stable


