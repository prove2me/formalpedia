-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_ExistsFinsetOfEventually
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:14:41.34821+00:00
-- url     : https://prove2.me/theorems/a2b6d6f0-5338-4ee6-967f-5afe94c3326e
-- title:
--   Exists Finset Of Eventually
-- statement:
--   Definitions and structural lemmas for Exists Finset Of Eventually, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExistsFinsetOfEventually.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RestrMeas
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal NNReal
section Cyl
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type}
def cyl (pa : ∀ w, X → Ya w) (pf : ∀ v, X → Yf v) (K : ∀ v, Set (Yf v)) (S : Finset V)
    (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)) : Set X :=
  {x | (∀ w, pa w x ∈ A w) ∧ (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v}
variable {pa : ∀ w, X → Ya w} {pf : ∀ v, X → Yf v} {K K' : ∀ v, Set (Yf v)}
theorem mem_cyl {S : Finset V} {A : ∀ w, Set (Ya w)} {B : ∀ v, Set (Yf v)} {x : X} :
    x ∈ cyl pa pf K S A B ↔ (∀ w, pa w x ∈ A w) ∧ (∀ v ∈ S, pf v x ∈ B v) ∧ ∀ v ∉ S, pf v x ∈ K v := Iff.rfl
open Classical in

theorem cyl_eq_of_subset {S T : Finset V} (h : S ⊆ T) (hK : ∀ v ∉ T, K v = K' v) (A : ∀ w, Set (Ya w))
    (B : ∀ v, Set (Yf v)) : cyl pa pf K' S A B = cyl pa pf K T A fun v => if v ∈ S then B v else K' v := by
  refine Set.ext fun x => and_congr_right fun _ => ⟨fun ⟨h1, h2⟩ => ⟨fun v _ => ?_, fun v hv => ?_⟩,
    fun ⟨h1, h2⟩ => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · by_cases hv : v ∈ S
    · simpa [hv] using h1 v hv
    · simpa [hv] using h2 v hv
  · rw [hK v hv]; exact h2 v fun h' => hv (h h')
  · simpa [hv] using h1 v (h hv)
  · by_cases hT : v ∈ T
    · simpa [hv] using h1 v hT
    · rw [← hK v hT]; exact h2 v hT
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
def IsCylProd (pa : ∀ w, X → Ya w) (pf : ∀ v, X → Yf v) (K : ∀ v, Set (Yf v)) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) (μ : Measure X) : Prop :=
  (∀ᶠ v in cofinite, μf v (K v) = 1) ∧
  ∀ S : Finset V, (∀ v ∉ S, μf v (K v) = 1) → ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)),
    (∀ w, MeasurableSet (A w)) → (∀ v ∈ S, MeasurableSet (B v)) →
    μ (cyl pa pf K S A B) = (∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ : Measure X}
theorem exists_finset_of_eventually {p : V → Prop} (h : ∀ᶠ v in cofinite, p v) : ∃ S : Finset V, ∀ v ∉ S, p v :=
  ⟨(eventually_cofinite.1 h).toFinset, fun v hv => by simpa using hv⟩
theorem eventually_of_finset {p : V → Prop} (S : Finset V) (h : ∀ v ∉ S, p v) : ∀ᶠ v in cofinite, p v :=
  S.eventually_cofinite_notMem.mono h
theorem isCylProd_of_large (hK' : ∀ v, MeasurableSet (K' v)) (S₀ : Finset V) (h1 : ∀ v ∉ S₀, μf v (K' v) = 1)
    (hK : ∀ v ∉ S₀, K v = K' v)
    (h : ∀ S : Finset V, S₀ ⊆ S → ∀ (A : ∀ w, Set (Ya w)) (B : ∀ v, Set (Yf v)),
      (∀ w, MeasurableSet (A w)) → (∀ v ∈ S, MeasurableSet (B v)) →
      μ (cyl pa pf K S A B) = (∏ w, μa w (A w)) * ∏ v ∈ S, μf v (B v)) : IsCylProd pa pf K' μa μf μ := by
  classical
  refine ⟨eventually_of_finset S₀ h1, fun S hS A B hA hB => ?_⟩
  rw [cyl_eq_of_subset (K := K) (T := S ∪ S₀) Finset.subset_union_left
    (fun v hv => hK v fun h' => hv (Finset.mem_union_right _ h')), h _ Finset.subset_union_right _ _ hA fun v _ => ?_]
  · congr 1
    rw [← Finset.prod_subset Finset.subset_union_left fun v _ hv => by simp only [if_neg hv, hS v hv]]
    exact Finset.prod_congr rfl fun v hv => by simp only [if_pos hv]
  · split_ifs with hv
    exacts [hB v hv, hK' v]
theorem IsCylProd.congr (h : IsCylProd pa pf K μa μf μ) (hK' : ∀ v, MeasurableSet (K' v))
    (hK : ∀ᶠ v in cofinite, K v = K' v) : IsCylProd pa pf K' μa μf μ := by
  obtain ⟨S₀, hS⟩ := exists_finset_of_eventually (h.1.and hK)
  exact isCylProd_of_large hK' S₀ (fun v hv => (hS v hv).2 ▸ (hS v hv).1) (fun v hv => (hS v hv).2)
    fun S hs => h.2 S fun v hv => (hS v fun h' => hv (hs h')).1
theorem IsCylProd.map {X' : Type} [MeasurableSpace X'] (h : IsCylProd pa pf K μa μf μ) (e : X ≃ᵐ X')
    {pa' : ∀ w, X' → Ya w} {pf' : ∀ v, X' → Yf v} (ha : ∀ w x, pa' w (e x) = pa w x)
    (hf : ∀ v x, pf' v (e x) = pf v x) : IsCylProd pa' pf' K μa μf (μ.map e) :=
  ⟨h.1, fun S hS A B hA hB => by
    rw [e.map_apply, ← h.2 S hS A B hA hB]
    congr 1
    ext x
    simp only [mem_preimage, mem_cyl, ha, hf]⟩
end Cyl
section Group
variable {X W V : Type} {Ya : W → Type} {Yf : V → Type} [Group X] [∀ w, Group (Ya w)] [∀ v, Group (Yf v)]
  [TopologicalSpace X] [∀ w, TopologicalSpace (Ya w)] [∀ v, TopologicalSpace (Yf v)]
structure IsRestrGroup (pa : ∀ w, X →* Ya w) (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) : Prop where
  continuous_pa : ∀ w, Continuous (pa w)
  continuous_pf : ∀ v, Continuous (pf v)
  isOpen_K : ∀ v, IsOpen (K v : Set (Yf v))
  isCompact_K : ∀ v, IsCompact (K v : Set (Yf v))
  ext : ∀ x y, (∀ w, pa w x = pa w y) → (∀ v, pf v x = pf v y) → x = y
  eventually_mem : ∀ x, ∀ᶠ v in cofinite, pf v x ∈ K v
  exists_eq : ∀ (a : ∀ w, Ya w) (y : ∀ v, Yf v), (∀ᶠ v in cofinite, y v ∈ K v) →
    ∃ x, (∀ w, pa w x = a w) ∧ ∀ v, pf v x = y v
  isOpen_level : IsOpen {x | ∀ v, pf v x ∈ K v}
  isCompact_level : ∀ C : ∀ w, Set (Ya w), (∀ w, IsCompact (C w)) →
    IsCompact {x | (∀ w, pa w x ∈ C w) ∧ ∀ v, pf v x ∈ K v}
def noArch (X : Type) [Group X] : ∀ _ : Empty, X →* PUnit := fun _ => 1
variable {pa : ∀ w, X →* Ya w} {pf : ∀ v, X →* Yf v} {K K' : ∀ v, Subgroup (Yf v)}
theorem IsRestrGroup.noArch [IsEmpty W] (h : IsRestrGroup pa pf K) : IsRestrGroup (noArch X) pf K :=
  ⟨fun w => w.elim, h.continuous_pf, h.isOpen_K, h.isCompact_K, fun x y _ hf => h.ext x y isEmptyElim hf,
    h.eventually_mem, fun _ y hy => (h.exists_eq isEmptyElim y hy).imp fun _ hx => ⟨fun w => w.elim, hx.2⟩,
    h.isOpen_level, fun _ _ => by simpa using h.isCompact_level isEmptyElim isEmptyElim⟩
def levelAway (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) (S : Finset V) : Subgroup X :=
  ⨅ v, ⨅ (_ : v ∉ S), (K v).comap (pf v)
variable [Fintype W] [MeasurableSpace X] [∀ w, MeasurableSpace (Ya w)] [∀ v, MeasurableSpace (Yf v)]
def IsHaarProd (pa : ∀ w, X →* Ya w) (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) (μa : ∀ w, Measure (Ya w))
    (μf : ∀ v, Measure (Yf v)) (μ : Measure X) : Prop :=
  (∀ w, (μa w).IsHaarMeasure) ∧ (∀ v, (μf v).IsHaarMeasure) ∧ μ.IsHaarMeasure ∧
    IsCylProd (fun w => pa w) (fun v => pf v) (fun v => (K v : Set (Yf v))) μa μf μ
def IsHaarProdFin (pf : ∀ v, X →* Yf v) (K : ∀ v, Subgroup (Yf v)) (μf : ∀ v, Measure (Yf v)) (μ : Measure X) :
    Prop := IsHaarProd (noArch X) pf K (fun w => w.elim) μf μ
variable {μa : ∀ w, Measure (Ya w)} {μf : ∀ v, Measure (Yf v)} {μ μ' : Measure X}
variable [BorelSpace X] [∀ w, BorelSpace (Ya w)] [∀ v, BorelSpace (Yf v)] [IsTopologicalGroup X]
variable [LocallyCompactSpace X] [SecondCountableTopology X] [∀ w, IsTopologicalGroup (Ya w)]
  [∀ w, LocallyCompactSpace (Ya w)] [∀ w, T2Space (Ya w)]
variable [∀ w, SecondCountableTopology (Ya w)] [∀ v, IsTopologicalGroup (Yf v)] [∀ v, LocallyCompactSpace (Yf v)]
  [∀ v, SecondCountableTopology (Yf v)]
section Split
variable {X' : Type} [Group X'] [TopologicalSpace X'] [MeasurableSpace X'] [BorelSpace X'] [IsTopologicalGroup X']
  [LocallyCompactSpace X'] [SecondCountableTopology X']
end Split
end Group
def normHaar {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : Measure G :=
  haarMeasure ⟨⟨K, hc⟩, by
    rw [TopologicalSpace.Compacts.carrier_eq_coe, TopologicalSpace.Compacts.coe_mk, ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩
instance {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : (normHaar K ho hc).IsHaarMeasure :=
  isHaarMeasure_haarMeasure _
example {Y : Type} [MeasurableSpace Y] (ν μ : Measure Y) :
    IsCylProd (W := Unit) (V := Empty) (Ya := fun _ => Y) (Yf := fun _ => Y) (fun _ => id) (fun _ => id)
      (fun _ => univ) (fun _ => ν) (fun _ => ν) μ ↔ μ = ν := by
  refine ⟨fun h => Measure.ext fun s hs => ?_, ?_⟩
  · simpa [cyl] using h.2 ∅ (fun v => v.elim) (fun _ => s) (fun _ => s) (fun _ => hs) fun v => v.elim
  · rintro rfl
    refine ⟨Eventually.of_forall fun v => v.elim, fun S _ A B _ _ => ?_⟩
    simp [cyl, Finset.eq_empty_of_isEmpty S, Unique.forall_iff]
end GlobalTheory.RestrMeas
end


