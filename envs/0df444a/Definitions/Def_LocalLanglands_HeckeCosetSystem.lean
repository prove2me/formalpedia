-- Prove2me | Definitions.Def_LocalLanglands_HeckeCosetSystem
-- name    : LocalLanglands_HeckeCosetSystem
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/8737b6ce-5af4-587d-bf24-37094bc8a7be
-- title:
--   Coset systems for double cosets, and their volumes
-- statement:
--   Fix a group $G$, a subgroup $U \le G$ and an element $g \in G$, and write $UgU$ for the project's set [`HeckePair.doubleCoset U g`](../def/LocalLanglands_HeckePair.html#L405), defined as the pointwise product $(U) \cdot \{g\} \cdot (U)$ of subsets of $G$. The structure `IsHeckeCosetSystem U g reps`, for a family $\mathrm{reps} : \iota \to G$ indexed by an arbitrary type $\iota$, is a proposition-valued structure with three fields: each $\mathrm{reps}\,i$ lies in $UgU$; every $x \in UgU$ has the same image as some $\mathrm{reps}\,i$ under the projection $G \to G \mathbin{/} U$ to left cosets (so the family covers all left cosets meeting $UgU$); and $i \mapsto \mathrm{reps}\,i\,U$ is injective. Thus a coset system is a family of elements of $UgU$ hitting each left coset contained in $UgU$ exactly once; no finiteness of $\iota$ is required in the definition.
--
--   The basic consequences are recorded: $\mathrm{reps}\,i \cdot U \subseteq UgU$, the decomposition $UgU = \bigcup_i \mathrm{reps}\,i \cdot U$, pairwise disjointness of the sets $\mathrm{reps}\,i \cdot U$ for distinct indices, and injectivity of $\mathrm{reps}$ itself. Auxiliary lemmas identify membership in a left coset $y\cdot U$ with equality of classes in $G \mathbin{/} U$, show $(U)\cdot\{g\} \subseteq UgU$, and show that the chosen representative `Quotient.out` of the class of a point of $UgU$ again lies in $UgU$. From this, `canonical_isHeckeCosetSystem` produces a coset system whenever the image of $(U)\cdot\{g\}$ in $G \mathbin{/} U$ is finite — the same finiteness hypothesis that the project's Hecke indicator and Hecke operator require — indexing it by that finite set of cosets and taking `Quotient.out` of each.
--
--   In the measurable setting ($G$ with a measurable space structure and measurable multiplication) it is shown that $y\cdot U$ is the preimage of $U$ under $x \mapsto y^{-1}x$, hence measurable when $U$ is, and of the same measure as $U$ for a left-invariant measure $\mu$. Consequently, for a coset system with $\iota$ a `Fintype` and $U$ measurable, $UgU$ is measurable and $\mu(UgU) = |\iota| \cdot \mu(U)$ in $[0,\infty]$; no Haar normalisation, finiteness or non-vanishing of $\mu(U)$ is assumed.
--
--   **Relation to Mathlib.** `IsHeckeCosetSystem` is the project's own predicate, stated for the project's [`HeckePair.doubleCoset`](../def/LocalLanglands_HeckePair.html#L405) (a pointwise product of subsets) rather than for Mathlib's `Doset`; the measure-theoretic lemmas are applications of Mathlib's invariance of left Haar-type measures under left translation and of additivity over finite disjoint unions.
--
--   **Where it is used.** These decompositions are the abstract mechanism by which local Hecke operators, defined in the project as sums over the left cosets in a double coset, are matched with integrals of the indicator function of that double coset against a left-invariant measure; the volume formula $\mu(UgU) = |\iota|\,\mu(U)$ specialises, for $U$ a maximal compact subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$ and $g = \mathrm{diag}(p,1)$, to the factor $p+1$ attached to $T_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LocalLanglands_HeckeCosetSystem.lean

import Mathlib
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise ENNReal
open MulAction MeasureTheory

namespace HeckeIntegralSeam

section CosetSystem

variable {G : Type*} [Group G]

structure IsHeckeCosetSystem (U : Subgroup G) (g : G) {ι : Type*} (reps : ι → G) : Prop where

  mem_doubleCoset : ∀ i, reps i ∈ HeckePair.doubleCoset U g

  covers : ∀ x ∈ HeckePair.doubleCoset U g,
    ∃ i, (QuotientGroup.mk x : G ⧸ U) = QuotientGroup.mk (reps i)

  mk_injective : Function.Injective fun i => (QuotientGroup.mk (reps i) : G ⧸ U)

variable {U : Subgroup G} {g : G}

theorem mem_smul_coe_iff {y x : G} :
    x ∈ y • (U : Set G) ↔ (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk x := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, SetLike.mem_coe, QuotientGroup.eq]

theorem mulSet_subset_doubleCoset : (U : Set G) * {g} ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hx
  obtain rfl : w = g := hw
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u, hu, 1, one_mem U, by group⟩

theorem out_mk_mem_doubleCoset {x : G} (hx : x ∈ HeckePair.doubleCoset U g) :
    Quotient.out (QuotientGroup.mk x : G ⧸ U) ∈ HeckePair.doubleCoset U g := by
  have hmem : Quotient.out (QuotientGroup.mk x : G ⧸ U) ∈ x • (U : Set G) :=
    mem_smul_coe_iff.mpr (QuotientGroup.out_eq' _).symm
  obtain ⟨u, hu, hux⟩ := Set.mem_smul_set.mp hmem
  rw [← hux, smul_eq_mul]
  exact HeckePair.doubleCoset_mul_mem hx hu

namespace IsHeckeCosetSystem

variable {ι : Type*} {reps : ι → G}

theorem smul_subset (hsys : IsHeckeCosetSystem U g reps) (i : ι) :
    reps i • (U : Set G) ⊆ HeckePair.doubleCoset U g := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Set.mem_smul_set.mp hx
  rw [smul_eq_mul]
  exact HeckePair.doubleCoset_mul_mem (hsys.mem_doubleCoset i) hu

theorem doubleCoset_eq_iUnion (hsys : IsHeckeCosetSystem U g reps) :
    HeckePair.doubleCoset U g = ⋃ i, reps i • (U : Set G) := by
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun i => hsys.smul_subset i)
  obtain ⟨i, hi⟩ := hsys.covers x hx
  exact Set.mem_iUnion.mpr ⟨i, mem_smul_coe_iff.mpr hi.symm⟩

theorem disjoint (hsys : IsHeckeCosetSystem U g reps) {i j : ι} (hij : i ≠ j) :
    Disjoint (reps i • (U : Set G)) (reps j • (U : Set G)) := by
  refine Set.disjoint_left.mpr fun x hxi hxj => hij ?_
  exact hsys.mk_injective ((mem_smul_coe_iff.mp hxi).trans (mem_smul_coe_iff.mp hxj).symm)

theorem reps_injective (hsys : IsHeckeCosetSystem U g reps) : Function.Injective reps :=
  fun i j hij => hsys.mk_injective (by simp only [hij])

end IsHeckeCosetSystem

theorem canonical_isHeckeCosetSystem
    (hfin : (QuotientGroup.mk '' ((U : Set G) * {g}) : Set (G ⧸ U)).Finite) :
    IsHeckeCosetSystem U g (fun q : ↥hfin.toFinset => Quotient.out (q : G ⧸ U)) := by
  constructor
  · rintro ⟨q, hq⟩
    rw [Set.Finite.mem_toFinset] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    exact out_mk_mem_doubleCoset (mulSet_subset_doubleCoset hz)
  · intro x hx
    have hmk : (QuotientGroup.mk x : G ⧸ U) ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, ← HeckePair.image_mk_doubleCoset g]
      exact Set.mem_image_of_mem _ hx
    exact ⟨⟨QuotientGroup.mk x, hmk⟩, (QuotientGroup.out_eq' _).symm⟩
  · intro q q' h
    refine Subtype.ext ?_
    have h' : QuotientGroup.mk (Quotient.out (q : G ⧸ U))
        = QuotientGroup.mk (Quotient.out (q' : G ⧸ U)) := h
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h'

end CosetSystem

section Volume

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {U : Subgroup G} {g : G}

theorem smul_coe_eq_preimage (y : G) :
    y • (U : Set G) = (fun x => y⁻¹ * x) ⁻¹' (U : Set G) := by
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rfl

theorem measurableSet_smul_coe (hU : MeasurableSet (U : Set G)) (y : G) :
    MeasurableSet (y • (U : Set G)) := by
  rw [smul_coe_eq_preimage]
  exact (measurable_const_mul y⁻¹) hU

theorem measure_smul_coe (μ : Measure G) [μ.IsMulLeftInvariant] (y : G) :
    μ (y • (U : Set G)) = μ (U : Set G) := by
  rw [smul_coe_eq_preimage]
  exact measure_preimage_mul μ y⁻¹ _

theorem IsHeckeCosetSystem.measure_doubleCoset {ι : Type*} [Fintype ι] {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (μ : Measure G) [μ.IsMulLeftInvariant]
    (hU : MeasurableSet (U : Set G)) :
    μ (HeckePair.doubleCoset U g) = (Fintype.card ι : ℝ≥0∞) * μ (U : Set G) := by
  classical
  rw [hsys.doubleCoset_eq_iUnion]
  have hbU : (⋃ i, reps i • (U : Set G))
      = ⋃ i ∈ (Finset.univ : Finset ι), reps i • (U : Set G) := by
    simp
  rw [hbU, measure_biUnion_finset (fun i _ j _ hij => hsys.disjoint hij)
    (fun i _ => measurableSet_smul_coe hU (reps i))]
  rw [Finset.sum_congr rfl fun i _ => measure_smul_coe μ (reps i), Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

theorem IsHeckeCosetSystem.measurableSet_doubleCoset {ι : Type*} [Fintype ι] {reps : ι → G}
    (hsys : IsHeckeCosetSystem U g reps) (hU : MeasurableSet (U : Set G)) :
    MeasurableSet (HeckePair.doubleCoset U g) := by
  rw [hsys.doubleCoset_eq_iUnion]
  exact MeasurableSet.iUnion fun i => measurableSet_smul_coe hU (reps i)

end Volume

end HeckeIntegralSeam


