-- Prove2me | Definitions.Def_Mathlib_MeasureTheory_Group_Action
-- name    : Mathlib_MeasureTheory_Group_Action
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/13824c7d-b8b6-5b9b-92eb-b0c69f6f9e21
-- title:
--   Invariant measures pulled back along measurable monoid embeddings
-- statement:
--   Four lemmas on the pullback (`comap`) of an invariant measure, together with the measurable-group instances on subgroups needed to state them. First, for a group $G$ and a monoid $H$, both with measurable spaces whose multiplications are measurable, and a monoid homomorphism $\varphi : G \to^* H$ which is a measurable embedding, the measure $\varphi^{*}\mu$ on $G$ obtained by pullback from a left-invariant measure $\mu$ on $H$ is again left invariant, i.e. satisfies `IsMulLeftInvariant`; [`MeasurableEmbedding.isMulRightInvariant_comap`](../def/Mathlib_MeasureTheory_Group_Action.html#L33) is the same statement for right invariance. (By `to_additive`, additive counterparts are produced as well.) The proof compares $\varphi(g \cdot {-})^{-1}(s)$ with $(\varphi(g) \cdot {-})^{-1}(\varphi(s))$, using that $\varphi$ has measurable image.
--
--   For a subgroup $H \le G$ of a measurable group, instances record that $H$, with the subspace measurable structure, again has measurable multiplication (as a two-variable map, and separately by left and right translations) and measurable inversion whenever $G$ does. Specialising the pullback lemmas to the coercion $H \hookrightarrow G$, which is a measurable embedding as soon as $H$ is a measurable subset of $G$, gives `isMulLeftInvariant_subtypeVal` and `isMulRightInvariant_subtypeVal`: the comap of a left- (resp. right-) invariant measure $\mu$ on $G$ along `Subtype.val` is a left- (resp. right-) invariant measure on $H$.
--
--   Finally, `index_mul_haar_subgroup_eq_haar_subgroup` states: if $H \le K$ are subgroups of $G$ with $H$ of finite relative index in $K$, both measurable as subsets of $G$, and $\mu$ is a left-invariant measure on $G$, then $[K : H] \cdot \mu(H) = \mu(K)$, where $[K:H]$ is `Subgroup.relIndex` and $\mu(H)$, $\mu(K)$ are the measures of the underlying sets. It is deduced from Mathlib's `Subgroup.index_mul_measure` applied to $H$ viewed inside $K$, for the measure pulled back to $K$.
--
--   **Relation to Mathlib.** All declarations are placed in Mathlib's own namespaces (`MeasurableEmbedding`, `MeasureTheory`) and are stated for Mathlib's `comap`, `IsMulLeftInvariant`/`IsMulRightInvariant`, `MeasurableMul`/`MeasurableMul₂`/`MeasurableInv` and `Subgroup.relIndex`; they supplement Mathlib's `Subgroup.index_mul_measure` with its relative-index form and with the subgroup instances and pullback lemmas used to obtain it.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/MeasureTheory/Group/Action.lean` — © 2024 Yaël Dillies; authors: Yaël Dillies, Kevin Buzzard, Ruben Van de Velde, David Ledvinka). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_MeasureTheory_Group_Action.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

section MeasurableEmbeddingComap

open MeasureTheory Measure

@[to_additive]
lemma _root_.MeasurableEmbedding.isMulLeftInvariant_comap {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Monoid H] [MeasurableSpace H] [MeasurableMul H]
    {φ : G →* H} (hφ : MeasurableEmbedding φ) (μ : Measure H) [IsMulLeftInvariant μ] :
    IsMulLeftInvariant (comap φ μ) where
  map_mul_left_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [MeasurableEmbedding.comap_apply hφ]
    have : φ '' ((fun x ↦ g * x) ⁻¹' s) = (fun x ↦ φ g * x) ⁻¹' (φ '' s) := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        refine ⟨g⁻¹ * y, by simp [yins], ?_⟩
        apply congrArg (φ g⁻¹ * ·) at hy
        simp_rw [← mul_assoc, ← φ.map_mul, inv_mul_cancel, map_one, one_mul] at hy
        exact hy
    rw [this, ← map_apply (by fun_prop), IsMulLeftInvariant.map_mul_left_eq_self]
    exact hφ.measurableSet_image.mpr hs

@[to_additive]
lemma _root_.MeasurableEmbedding.isMulRightInvariant_comap {G H : Type*}
    [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Monoid H] [MeasurableSpace H] [MeasurableMul H]
    {φ : G →* H} (hφ : MeasurableEmbedding φ) (μ : Measure H) [IsMulRightInvariant μ] :
    IsMulRightInvariant (comap φ μ) where
  map_mul_right_eq_self g := by
    ext s hs
    rw [map_apply (by fun_prop) hs]
    repeat rw [MeasurableEmbedding.comap_apply hφ]
    have : φ '' ((fun x ↦ x * g) ⁻¹' s) = (fun x ↦ x * φ g) ⁻¹' (φ '' s) := by
      ext
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y * g, hy, by simp⟩
      · intro ⟨y, yins, hy⟩
        refine ⟨y * g⁻¹, by simp [yins], ?_⟩
        apply congrArg (· * φ g⁻¹) at hy
        simp_rw [mul_assoc, ← φ.map_mul, mul_inv_cancel, map_one, mul_one] at hy
        exact hy
    rw [this, ← map_apply (by fun_prop), IsMulRightInvariant.map_mul_right_eq_self]
    exact hφ.measurableSet_image.mpr hs

end MeasurableEmbeddingComap

open Subgroup Set
open scoped Pointwise

namespace MeasureTheory
variable {G α : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace α]
  {H K : Subgroup G}

@[to_additive]
instance [MeasurableMul₂ G] : MeasurableMul₂ H where
  measurable_mul := Measurable.subtype_mk (by measurability)

@[to_additive]
instance [MeasurableInv G] : MeasurableInv H where
  measurable_inv := Measurable.subtype_mk (by measurability)

variable [MeasurableMul G]

@[to_additive]
instance : MeasurableMul H where
  measurable_mul_const c := Measurable.subtype_mk (by measurability)
  measurable_const_mul c := Measurable.subtype_mk (by measurability)

@[to_additive]
lemma isMulLeftInvariant_subtypeVal (μ : Measure G) [μ.IsMulLeftInvariant]
  (hH : MeasurableSet (H : Set G)) : (μ.comap Subtype.val : Measure H).IsMulLeftInvariant :=
  have hφ : MeasurableEmbedding H.subtype := MeasurableEmbedding.subtype_coe hH
  hφ.isMulLeftInvariant_comap μ

@[to_additive]
lemma isMulRightInvariant_subtypeVal (μ : Measure G) [μ.IsMulRightInvariant]
    (hH : MeasurableSet (H : Set G)) : (μ.comap Subtype.val : Measure H).IsMulRightInvariant :=
  have hφ : MeasurableEmbedding H.subtype := MeasurableEmbedding.subtype_coe hH
  hφ.isMulRightInvariant_comap μ

@[to_additive index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup]
lemma index_mul_haar_subgroup_eq_haar_subgroup [H.IsFiniteRelIndex K] (hHK : H ≤ K)
    (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (μ : Measure G)
    [μ.IsMulLeftInvariant] : H.relIndex K * μ H = μ K := by
  have := isMulLeftInvariant_subtypeVal μ hK
  have := Subgroup.index_mul_measure (H.subgroupOf K) (measurable_subtype_coe hH)
    (μ.comap Subtype.val)
  rw [MeasurableEmbedding.comap_apply, MeasurableEmbedding.comap_apply] at this
  · simp only [image_univ, Subtype.range_coe_subtype, SetLike.setOf_mem_eq] at this
    unfold subgroupOf at this
    rwa [coe_comap, coe_subtype, Set.image_preimage_eq_of_subset (by simpa)] at this
  · exact .subtype_coe hK
  · exact .subtype_coe hK

end MeasureTheory


