-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient
-- name    : GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:53:44.714257+00:00
-- url     : https://prove2.me/theorems/53767cbc-c361-5b27-811a-0587c7fbb467
-- title:
--   Idele Measure Quotient
-- statement:
--   Definitions and structural lemmas for Idele Measure Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_standardOpenSubgroupEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_diagonal_injective
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_isClosed_normOneSubgroup
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_standardOpenSubgroupEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_discreteTopology_principalSubgroup
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_standardOpenSubgroupEquiv_symm_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.standardOpenSubgroupEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
namespace GroundTheory.Global
noncomputable section
section Discrete
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
instance discreteTopology_range_diagonal : DiscreteTopology (diagonal K).range := by
  let f : (diagonal K).range → AdeleRing.principalSubgroup (𝓞 K) K := fun x ↦
    ⟨((x : IdeleGroup K) : 𝔸[K]), by
      obtain ⟨k, hk⟩ := x.2
      exact ⟨(k : K), by rw [← hk]; rfl⟩⟩
  have : DiscreteTopology (AdeleRing.principalSubgroup (𝓞 K) K) :=
    discreteTopology_principalSubgroup K
  exact DiscreteTopology.of_continuous_injective (f := f)
    ((Units.continuous_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h ↦ Subtype.ext (Units.ext (show ((x : IdeleGroup K) : 𝔸[K]) = (y : IdeleGroup K)
      from congrArg Subtype.val h))
abbrev diagonalNormOne : Subgroup (normOneSubgroup K) :=
  (diagonal K).range.subgroupOf (normOneSubgroup K)
instance discreteTopology_diagonalNormOne : DiscreteTopology (diagonalNormOne K) := by
  let f : diagonalNormOne K → (diagonal K).range := fun x ↦
    ⟨((x : normOneSubgroup K) : IdeleGroup K), x.2⟩
  exact DiscreteTopology.of_continuous_injective (f := f)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun x y h ↦ Subtype.ext (Subtype.ext (show ((x : normOneSubgroup K) : IdeleGroup K) =
      ((y : normOneSubgroup K) : IdeleGroup K) from
        congrArg (fun z : (diagonal K).range ↦ (z : IdeleGroup K)) h))
def diagonalToNormOne : Kˣ →* normOneSubgroup K :=
  (diagonal K).codRestrict (normOneSubgroup K) fun k ↦
    range_diagonal_le_normOneSubgroup K ⟨k, rfl⟩
@[simp]
theorem coe_diagonalToNormOne (k : Kˣ) :
    ((diagonalToNormOne K k : normOneSubgroup K) : IdeleGroup K) = diagonal K k :=
  rfl
def diagonalNormOneEquiv : Kˣ ≃ diagonalNormOne K where
  toFun k := ⟨diagonalToNormOne K k, ⟨k, rfl⟩⟩
  invFun x := x.2.choose
  left_inv k := diagonal_injective K ((⟨diagonalToNormOne K k, ⟨k, rfl⟩⟩ :
    diagonalNormOne K).2.choose_spec)
  right_inv x := Subtype.ext (Subtype.ext x.2.choose_spec)
@[simp]
theorem coe_diagonalNormOneEquiv (k : Kˣ) :
    (((diagonalNormOneEquiv K k : diagonalNormOne K) : normOneSubgroup K) : IdeleGroup K) =
      diagonal K k :=
  rfl
instance countable_units : Countable Kˣ := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  exact Units.val_injective.countable
instance countable_diagonalNormOne : Countable (diagonalNormOne K) :=
  (diagonalNormOneEquiv K).symm.injective.countable
end Discrete
section FundamentalDomain
variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
theorem exists_fundamentalDomain_of_discrete (Γ : Subgroup G) [DiscreteTopology Γ] {D : Set G}
    (hD : IsCompact D) (hcov : ∀ x : G, ∃ γ ∈ Γ, x * γ ∈ D) :
    ∃ E : Set G, MeasurableSet E ∧ IsCompact (closure E) ∧
      ∀ x : G, ∃! γ : Γ.op, γ • x ∈ E := by
  classical

  obtain ⟨U, hUo, hU⟩ : ∃ U : Set G, IsOpen U ∧ Subtype.val ⁻¹' U = ({1} : Set Γ) :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have h1U : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ Subtype.val ⁻¹' U := by rw [hU]; rfl
    exact this
  have hUΓ : ∀ γ ∈ Γ, γ ∈ U → γ = 1 := fun γ hγ hγU ↦ by
    have : (⟨γ, hγ⟩ : Γ) ∈ Subtype.val ⁻¹' U := hγU
    rw [hU] at this
    exact congrArg Subtype.val (Set.mem_singleton_iff.1 this)

  have hW : IsOpen {q : G × G | q.1 / q.2 ∈ U} := hUo.preimage continuous_div'
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ :=
    isOpen_prod_iff.1 hW 1 1 (by simpa using h1U)
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds (1 : G)
  set V : Set G := u ∩ v ∩ interior C with hVdef
  have hVo : IsOpen V := (hu.inter hv).inter isOpen_interior
  have hV1 : (1 : G) ∈ V := ⟨⟨hu1, hv1⟩, mem_interior_iff_mem_nhds.2 hCn⟩
  have hVdiv : ∀ a ∈ V, ∀ b ∈ V, a / b ∈ U := fun a ha b hb ↦
    huv (Set.mk_mem_prod ha.1.1 hb.1.2)
  have hVC : V ⊆ C := fun a ha ↦ interior_subset ha.2

  obtain ⟨t, ht⟩ := hD.elim_finite_subcover (fun x : G ↦ (x * ·) '' V)
    (fun x ↦ (Homeomorph.mulLeft x).isOpenMap _ hVo)
    (fun x _ ↦ Set.mem_iUnion.2 ⟨x, 1, hV1, mul_one x⟩)
  let p : Fin t.card → G := fun i ↦ (t.equivFin.symm i : G)
  let B : Fin t.card → Set G := fun i ↦ (p i * ·) '' V
  let O : Fin t.card → Set G := fun j ↦ ⋃ γ : Γ, (· * (γ : G)) '' B j
  let E : Set G := ⋃ i, (B i \ ⋃ j, ⋃ (_h : j < i), O j)
  have hBo : ∀ i, IsOpen (B i) := fun i ↦ (Homeomorph.mulLeft (p i)).isOpenMap _ hVo
  have hOo : ∀ j, IsOpen (O j) := fun j ↦
    isOpen_iUnion fun γ ↦ (Homeomorph.mulRight (γ : G)).isOpenMap _ (hBo j)
  have hmemO : ∀ j y, y ∈ O j ↔ ∃ γ ∈ Γ, y * γ ∈ B j := by
    intro j y
    simp only [O, Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨γ, b, hb, rfl⟩
      exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, by rwa [mul_inv_cancel_right]⟩
    · rintro ⟨γ, hγ, hy⟩
      exact ⟨⟨γ⁻¹, Γ.inv_mem hγ⟩, y * γ, hy, by simp⟩
  have hDB : D ⊆ ⋃ i, B i := by
    intro y hy
    obtain ⟨z, hz⟩ := Set.mem_iUnion₂.1 (ht hy)
    obtain ⟨hzt, hyz⟩ := hz
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨z, hzt⟩, ?_⟩
    simp only [B, p, Equiv.symm_apply_apply]
    exact hyz
  refine ⟨E, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun i ↦ (hBo i).measurableSet.diff
      (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ (hOo j).measurableSet)
  · have hK : IsCompact (⋃ i, (p i * ·) '' C) :=
      isCompact_iUnion fun i ↦ hC.image (continuous_const.mul continuous_id)
    refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
    obtain ⟨a, ha, rfl⟩ := hi.1
    exact Set.mem_iUnion.2 ⟨i, a, hVC ha, rfl⟩
  · intro x
    have hsmul : ∀ γ : Γ.op, γ • x = x * ((γ : Gᵐᵒᵖ).unop) := fun _ ↦ rfl
    have hmemE : ∀ y, y ∈ E ↔ ∃ i, y ∈ B i ∧ ∀ j < i, y ∉ O j := by
      intro y
      simp only [E, Set.mem_iUnion, Set.mem_sdiff, not_exists]

    let S : Finset (Fin t.card) := Finset.univ.filter fun i ↦ ∃ γ ∈ Γ, x * γ ∈ B i
    have hS : S.Nonempty := by
      obtain ⟨γ, hγ, hxγ⟩ := hcov x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hDB hxγ)
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, γ, hγ, hi⟩⟩
    set i := S.min' hS
    obtain ⟨γ, hγ, hγi⟩ := (Finset.mem_filter.1 (S.min'_mem hS)).2
    have hEi : ∀ j < i, x * γ ∉ O j := fun j hj hO ↦ by
      obtain ⟨γ', hγ', hB⟩ := (hmemO j _).1 hO
      have hjS : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, γ * γ', Γ.mul_mem hγ hγ',
        by rwa [← mul_assoc]⟩
      exact absurd (S.min'_le j hjS) (not_le.2 hj)
    refine ⟨⟨MulOpposite.op γ, Subgroup.mem_op.2 hγ⟩, ?_, ?_⟩
    · show x * γ ∈ E
      exact (hmemE _).2 ⟨i, hγi, hEi⟩
    · rintro ⟨g, hg⟩ hgE
      have hg' : g.unop ∈ Γ := Subgroup.mem_op.1 hg
      change x * g.unop ∈ E at hgE
      obtain ⟨k, hk, hkO⟩ := (hmemE _).1 hgE
      have hba : g.unop = γ := by
        rcases lt_trichotomy i k with hik | rfl | hki
        · refine absurd ((hmemO i _).2 ⟨g.unop⁻¹ * γ, Γ.mul_mem (Γ.inv_mem hg') hγ, ?_⟩)
            (hkO i hik)
          rwa [mul_assoc, mul_inv_cancel_left]
        · obtain ⟨v₁, hv₁, h₁⟩ := hγi
          obtain ⟨v₂, hv₂, h₂⟩ := hk
          have hdiv : g.unop / γ = v₂ / v₁ := by
            rw [← mul_div_mul_left_eq_div _ _ x, ← h₁, ← h₂, mul_div_mul_left_eq_div]
          have h1 := hUΓ _ (Γ.div_mem hg' hγ) (hdiv ▸ hVdiv v₂ hv₂ v₁ hv₁)
          exact div_eq_one.1 h1
        · refine absurd ((hmemO k _).2 ⟨γ⁻¹ * g.unop, Γ.mul_mem (Γ.inv_mem hγ) hg', ?_⟩)
            (hEi k hki)
          rwa [mul_assoc, mul_inv_cancel_left]
      exact Subtype.ext (MulOpposite.unop_injective hba)
end FundamentalDomain
section NormOneClasses
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]
theorem exists_fundamentalDomain_normOne :
    ∃ E : Set (normOneSubgroup K), MeasurableSet E ∧ IsCompact (closure E) ∧
      ∀ x : normOneSubgroup K, ∃! γ : (diagonalNormOne K).op, γ • x ∈ E := by
  obtain ⟨D, hD, hDJ, hxD⟩ := exists_isCompact_normOneSubgroup K
  refine exists_fundamentalDomain_of_discrete (diagonalNormOne K)
    (D := Subtype.val ⁻¹' D)
    ((isClosed_normOneSubgroup K).isClosedEmbedding_subtypeVal.isCompact_preimage hD) ?_
  intro x
  obtain ⟨k, hk⟩ := hxD x x.2
  refine ⟨diagonalToNormOne K k, ⟨k, rfl⟩, ?_⟩
  change (x : IdeleGroup K) * diagonal K k ∈ D
  rwa [mul_comm]
def normOneFundamentalDomain : Set (normOneSubgroup K) :=
  (exists_fundamentalDomain_normOne K).choose
theorem measurableSet_normOneFundamentalDomain :
    MeasurableSet (normOneFundamentalDomain K) :=
  (exists_fundamentalDomain_normOne K).choose_spec.1
theorem isCompact_closure_normOneFundamentalDomain :
    IsCompact (closure (normOneFundamentalDomain K)) :=
  (exists_fundamentalDomain_normOne K).choose_spec.2.1
theorem isFundamentalDomain_normOneFundamentalDomain (μ : Measure (normOneSubgroup K)) :
    IsFundamentalDomain (diagonalNormOne K).op (normOneFundamentalDomain K) μ :=
  IsFundamentalDomain.mk' (measurableSet_normOneFundamentalDomain K).nullMeasurableSet
    (exists_fundamentalDomain_normOne K).choose_spec.2.2
theorem normOneMeasure_normOneFundamentalDomain_lt_top :
    normOneMeasure K (normOneFundamentalDomain K) < ∞ :=
  (measure_mono subset_closure).trans_lt
    (isCompact_closure_normOneFundamentalDomain K).measure_lt_top
def normOneClassMeasure : Measure (normOneSubgroup K ⧸ diagonalNormOne K) :=
  Measure.map QuotientGroup.mk ((normOneMeasure K).restrict (normOneFundamentalDomain K))
instance quotientMeasureEqMeasurePreimage_normOneClassMeasure :
    QuotientMeasureEqMeasurePreimage (normOneMeasure K) (normOneClassMeasure K) :=
  (isFundamentalDomain_normOneFundamentalDomain K _).quotientMeasureEqMeasurePreimage_quotientMeasure
instance isFiniteMeasure_normOneClassMeasure : IsFiniteMeasure (normOneClassMeasure K) := by
  have : Fact (normOneMeasure K (normOneFundamentalDomain K) < ∞) :=
    ⟨normOneMeasure_normOneFundamentalDomain_lt_top K⟩
  unfold normOneClassMeasure
  infer_instance
end NormOneClasses
section Unfolding
open IdeleGroup
variable {K : Type*} [Field K] [NumberField K]
end Unfolding
section Volume
variable {K : Type*} [Field K] [NumberField K]
end Volume
end
end GroundTheory.Global


