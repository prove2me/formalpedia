-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:13.784933+00:00
-- url     : https://prove2.me/theorems/6402abeb-f9eb-4e7e-8f29-953e3edfd458
-- title:
--   Exists Is Fundamental Domain And Quot Measure Eq
-- statement:
--   Definitions and structural lemmas for Exists Is Fundamental Domain And Quot Measure Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsFundamentalDomainAndQuotMeasureEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
namespace GlobalTheory
structure IsAEAddOrbitSection (G : Type*) {X : Type*} [VAdd G X] [MeasurableSpace X]
    (D : Set X) (μ : Measure X) : Prop where
  protected nullMeasurableSet : NullMeasurableSet D μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g +ᵥ x ∈ D
  protected ae_unique : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g +ᵥ x ∈ D → g +ᵥ x = x
@[to_additive IsAEAddOrbitSection]
structure IsAEOrbitSection (G : Type*) {X : Type*} [SMul G X] [MeasurableSpace X]
    (D : Set X) (μ : Measure X) : Prop where
  protected nullMeasurableSet : NullMeasurableSet D μ
  protected ae_covers : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ D
  protected ae_unique : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x
section Existence
variable {G X : Type*} [Group G] [MulAction G X]
@[to_additive exists_measurableSet_addOrbitSection_of_discreteOrbits
]
theorem exists_measurableSet_orbitSection_of_discreteOrbits [Countable G] [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [MeasurableConstSMul G X] (hfix : ∀ g : G, MeasurableSet {x : X | g • x = x})
    (hdisc : ∀ x : X, ∃ U ∈ 𝓝 x, ∀ g : G, g • x ∈ U → g • x = x) :
    ∃ D : Set X, MeasurableSet D ∧ (∀ x, ∃ g : G, g • x ∈ D) ∧
      ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x := by
  classical
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis X
  obtain ⟨B, hB⟩ := (hbc.insert ∅).exists_eq_range (insert_nonempty _ _)
  have hBo : ∀ n, IsOpen (B n) := fun n => by
    have : B n ∈ insert ∅ b := hB ▸ mem_range_self n
    rcases this with h | h
    · rw [h]; exact isOpen_empty
    · exact hb.isOpen h
  let S : ℕ → Set X := fun n => B n ∩ ⋂ g : G, (((g • ·) ⁻¹' B n)ᶜ ∪ {x | g • x = x})
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    (hBo n).measurableSet.inter <| MeasurableSet.iInter fun g =>
      ((measurable_const_smul g) (hBo n).measurableSet).compl.union (hfix g)
  have hSmem : ∀ n x, x ∈ S n ↔ x ∈ B n ∧ ∀ g : G, g • x ∈ B n → g • x = x := fun n x => by
    simp only [S, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff, mem_preimage,
      mem_setOf_eq, imp_iff_not_or]
  have hS : ∀ x, ∃ n, x ∈ S n := fun x => by
    obtain ⟨U, hU, h⟩ := hdisc x
    obtain ⟨t, ht, hxt, htU⟩ := hb.mem_nhds_iff.1 hU
    have : t ∈ range B := hB ▸ mem_insert_of_mem _ ht
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, (hSmem n x).2 ⟨hxt, fun g hg => h g (htU hg)⟩⟩
  let T : ℕ → Set X := fun n => ⋃ g : G, (g • ·) ⁻¹' S n
  have hTm : ∀ n, MeasurableSet (T n) := fun n =>
    MeasurableSet.iUnion fun g => (measurable_const_smul g) (hSm n)
  have hTmem : ∀ n x, x ∈ T n ↔ ∃ g : G, g • x ∈ S n := fun n x => by simp [T]
  refine ⟨⋃ n, S n \ ⋃ m, ⋃ (_ : m < n), T m, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hSm n).diff <|
      MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ => hTm m
  · intro x
    have hx : ∃ n, x ∈ T n := by
      obtain ⟨n, hn⟩ := hS x
      exact ⟨n, (hTmem n x).2 ⟨1, by simpa using hn⟩⟩
    obtain ⟨g, hg⟩ := (hTmem _ x).1 (Nat.find_spec hx)
    refine ⟨g, mem_iUnion.2 ⟨Nat.find hx, hg, fun h => ?_⟩⟩
    obtain ⟨m, hm, h⟩ := mem_iUnion₂.1 h
    obtain ⟨k, hk⟩ := (hTmem _ _).1 h
    exact Nat.find_min hx hm ((hTmem _ _).2 ⟨k * g, by rwa [mul_smul]⟩)
  · intro x hx g hg
    obtain ⟨n, hn, hn'⟩ := mem_iUnion.1 hx
    obtain ⟨m, hm, hm'⟩ := mem_iUnion.1 hg
    rcases lt_trichotomy m n with h | rfl | h
    · exact (hn' (mem_iUnion₂.2 ⟨m, h, (hTmem _ _).2 ⟨g, hm⟩⟩)).elim
    · exact ((hSmem _ _).1 hn).2 g ((hSmem _ _).1 hm).1
    · exact (hm' (mem_iUnion₂.2 ⟨n, h, (hTmem _ _).2 ⟨g⁻¹, by rwa [inv_smul_smul]⟩⟩)).elim
end Existence
section Comparison
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
@[to_additive measure_le_of_ae_unique_of_ae_covers_add
]
theorem measure_le_of_ae_unique_of_ae_covers [Countable G] [MeasurableConstSMul G X]
    [SMulInvariantMeasure G X μ] {S B : Set X} (hS : NullMeasurableSet S μ)
    (hB : NullMeasurableSet B μ) (hu : ∀ᵐ x ∂μ, x ∈ S → ∀ g : G, g • x ∈ S → g • x = x)
    (hc : ∀ᵐ x ∂μ, x ∈ S → ∃ g : G, g • x ∈ B) : μ S ≤ μ B := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat G
  have hq : ∀ g : G, Measure.QuasiMeasurePreserving (g • · : X → X) μ μ := fun g =>
    (measurePreserving_smul g μ).quasiMeasurePreserving
  let P : G → Set X := fun g => (S ∩ (g • ·) ⁻¹' B) \ ⋃ h, ⋃ (_ : e h < e g), (h • ·) ⁻¹' B
  have hPm : ∀ g, NullMeasurableSet (P g) μ := fun g =>
    (hS.inter (hB.preimage (hq g))).diff <|
      NullMeasurableSet.iUnion fun h => NullMeasurableSet.iUnion fun _ => hB.preimage (hq h)
  let Q : G → Set X := fun g => (g⁻¹ • ·) ⁻¹' P g
  have hQm : ∀ g, NullMeasurableSet (Q g) μ := fun g => (hPm g).preimage (hq _)
  have h1 : S ≤ᵐ[μ] ⋃ g, P g := by
    filter_upwards [hc] with x hx hxS
    have hex : ∃ n, ∃ g : G, e g = n ∧ g • x ∈ B := by
      obtain ⟨g, hg⟩ := hx hxS
      exact ⟨_, g, rfl, hg⟩
    obtain ⟨g, hg, hgB⟩ := Nat.find_spec hex
    refine mem_iUnion.2 ⟨g, ⟨hxS, hgB⟩, fun h => ?_⟩
    obtain ⟨k, hk, h⟩ := mem_iUnion₂.1 h
    exact Nat.find_min hex (hg ▸ hk) ⟨k, rfl, h⟩
  have h2 : Pairwise (Function.onFun (AEDisjoint μ) Q) := by
    intro g h hgh
    have := (hq g⁻¹).ae hu
    refine measure_mono_null (fun y hy => ?_) this
    intro hy'
    obtain ⟨⟨⟨hg1, hg2⟩, hg3⟩, ⟨hh1, hh2⟩, hh3⟩ := hy
    have key : h⁻¹ • y = g⁻¹ • y := by
      have := hy' hg1 (h⁻¹ * g) (by simpa [mul_smul] using hh1)
      simpa [mul_smul] using this
    rcases lt_trichotomy (e g) (e h) with hl | hl | hl
    · exact hh3 (mem_iUnion₂.2 ⟨g, hl, by rw [mem_preimage]; beta_reduce; rw [key]; exact hg2⟩)
    · exact hgh (he hl)
    · exact hg3 (mem_iUnion₂.2 ⟨h, hl, by rw [mem_preimage]; beta_reduce; rw [← key]; exact hh2⟩)
  calc μ S ≤ μ (⋃ g, P g) := measure_mono_ae h1
    _ ≤ ∑' g, μ (P g) := measure_iUnion_le _
    _ = ∑' g, μ (Q g) := tsum_congr fun g => (measure_preimage_smul μ g⁻¹ (P g)).symm
    _ = μ (⋃ g, Q g) := (measure_iUnion₀ h2 hQm).symm
    _ ≤ μ B := measure_mono <| iUnion_subset fun g y hy => by simpa using hy.1.2
end Comparison
section Quot
variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X] {μ : Measure X}
@[to_additive addQuotMeasure  ]
noncomputable def quotMeasure (G : Type*) {X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    (μ : Measure X) : Measure (Quotient (MulAction.orbitRel G X)) :=
  ⨆ (D : Set X) (_ : NullMeasurableSet D μ)
    (_ : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x),
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X))
@[to_additive map_restrict_le_addQuotMeasure]
theorem map_restrict_le_quotMeasure {D : Set X} (hD : NullMeasurableSet D μ)
    (hu : ∀ᵐ x ∂μ, x ∈ D → ∀ g : G, g • x ∈ D → g • x = x) :
    (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) ≤ quotMeasure G μ :=
  le_iSup_of_le D (le_iSup_of_le hD (le_iSup_of_le hu le_rfl))
@[to_additive isAEAddOrbitSection_of_forall  ]
theorem isAEOrbitSection_of_forall {D : Set X} (hD : MeasurableSet D) (hc : ∀ x, ∃ g : G, g • x ∈ D)
    (hu : ∀ x ∈ D, ∀ g : G, g • x ∈ D → g • x = x) (μ : Measure X) : IsAEOrbitSection G D μ :=
  ⟨hD.nullMeasurableSet, Eventually.of_forall hc, Eventually.of_forall hu⟩
@[to_additive IsAEAddOrbitSection.of_sameOrbits  ]
theorem IsAEOrbitSection.of_sameOrbits {H : Type*} [SMul H X] {D : Set X}
    (hD : IsAEOrbitSection H D μ) (h₁ : ∀ (h : H) (x : X), ∃ g : G, g • x = h • x)
    (h₂ : ∀ (g : G) (x : X), ∃ h : H, h • x = g • x) : IsAEOrbitSection G D μ where
  nullMeasurableSet := hD.nullMeasurableSet
  ae_covers := by
    filter_upwards [hD.ae_covers] with x ⟨h, hh⟩
    obtain ⟨g, hg⟩ := h₁ h x
    exact ⟨g, hg ▸ hh⟩
  ae_unique := by
    filter_upwards [hD.ae_unique] with x hx hxD g hg
    obtain ⟨h, hh⟩ := h₂ g x
    rw [← hh] at hg ⊢
    exact hx hxD h hg
@[to_additive isAEAddOrbitSection_of_isAddFundamentalDomain
]
theorem isAEOrbitSection_of_isFundamentalDomain [Countable G] {D : Set X}
    (hD : IsFundamentalDomain G D μ) : IsAEOrbitSection G D μ where
  nullMeasurableSet := hD.nullMeasurableSet
  ae_covers := hD.ae_covers
  ae_unique := by
    have : ∀ᵐ x ∂μ, ∀ g : G, x ∈ D → g • x ∈ D → g • x = x := by
      refine ae_all_iff.2 fun g => ?_
      by_cases hg : g = 1
      · exact Eventually.of_forall fun x _ _ => by rw [hg, one_smul]
      · have := hD.aedisjoint (inv_ne_one.2 hg)
        refine measure_mono_null (fun x hx => ?_) this
        simp only [mem_compl_iff, mem_setOf_eq, Classical.not_imp] at hx
        refine ⟨?_, ?_⟩
        · rw [mem_smul_set_iff_inv_smul_mem, inv_inv]; exact hx.2.1
        · simpa using hx.1
    filter_upwards [this] with x hx hxD g hg using hx g hxD hg
variable [Countable G] [MeasurableConstSMul G X] [SMulInvariantMeasure G X μ]
@[to_additive map_restrict_le_map_restrict_of_ae_unique_of_ae_covers_add]
theorem map_restrict_le_map_restrict_of_ae_unique_of_ae_covers {S B : Set X}
    (hS : NullMeasurableSet S μ) (hB : NullMeasurableSet B μ)
    (hu : ∀ᵐ x ∂μ, x ∈ S → ∀ g : G, g • x ∈ S → g • x = x) (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) :
    (μ.restrict S).map (Quotient.mk (MulAction.orbitRel G X)) ≤
      (μ.restrict B).map (Quotient.mk (MulAction.orbitRel G X)) := by
  refine Measure.le_iff.2 fun U hU => ?_
  rw [measure_map_restrict_apply μ S hU, measure_map_restrict_apply μ B hU]
  have hU' : NullMeasurableSet (Quotient.mk (MulAction.orbitRel G X) ⁻¹' U) μ :=
    (measurableSet_quotient.1 hU).nullMeasurableSet
  refine measure_le_of_ae_unique_of_ae_covers (G := G) (hU'.inter hS) (hU'.inter hB) ?_ ?_
  · filter_upwards [hu] with x hx hxS g hg using hx hxS.2 g hg.2
  · filter_upwards [hc] with x ⟨g, hg⟩ hxS
    refine ⟨g, ?_, hg⟩
    have : Quotient.mk (MulAction.orbitRel G X) (g • x) = Quotient.mk (MulAction.orbitRel G X) x :=
      Quotient.sound ⟨g, rfl⟩
    rw [mem_preimage, this]
    exact hxS.1
@[to_additive addQuotMeasure_le_map_restrict
]
theorem quotMeasure_le_map_restrict {B : Set X} (hB : NullMeasurableSet B μ)
    (hc : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ B) :
    quotMeasure G μ ≤ (μ.restrict B).map (Quotient.mk (MulAction.orbitRel G X)) :=
  iSup_le fun _ => iSup_le fun hS => iSup_le fun hu =>
    map_restrict_le_map_restrict_of_ae_unique_of_ae_covers hS hB hu hc
namespace IsAEOrbitSection
variable {D D' : Set X}
@[to_additive IsAEAddOrbitSection.addQuotMeasure_eq
]
theorem quotMeasure_eq (hD : IsAEOrbitSection G D μ) :
    quotMeasure G μ = (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) :=
  le_antisymm (quotMeasure_le_map_restrict hD.nullMeasurableSet hD.ae_covers)
    (map_restrict_le_quotMeasure hD.nullMeasurableSet hD.ae_unique)
end IsAEOrbitSection
@[to_additive addQuotMeasure_eq_of_isAddFundamentalDomain
]
theorem quotMeasure_eq_of_isFundamentalDomain {D : Set X} (hD : IsFundamentalDomain G D μ) :
    quotMeasure G μ = (μ.restrict D).map (Quotient.mk (MulAction.orbitRel G X)) :=
  (isAEOrbitSection_of_isFundamentalDomain hD).quotMeasure_eq
@[to_additive addQuotMeasure_addQuotientMeasureEqMeasurePreimage]
instance quotMeasure_quotientMeasureEqMeasurePreimage :
    QuotientMeasureEqMeasurePreimage μ (quotMeasure G μ) :=
  ⟨fun _ h => quotMeasure_eq_of_isFundamentalDomain h⟩
end Quot
section ProperlyDiscontinuous
variable (G X : Type*) [Group G] [Countable G] [MulAction G X] [TopologicalSpace X] [T2Space X]
  [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ContinuousConstSMul G X]
variable {X}
end ProperlyDiscontinuous
section DiscreteSubgroup
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
variable [MeasurableSpace G] [BorelSpace G]
end DiscreteSubgroup
end GlobalTheory


