-- Prove2me | Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
-- name    : LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:13:00.695867+00:00
-- url     : https://prove2.me/theorems/e6b393d2-3168-47d3-9d7b-3557b481d1f8
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Antonio Avilés; Mitchell A. Taylor; Pedro Tradacete; David Muñoz-Lahoz; LeanPool contributors's pinned Order closure, order adherence and Fatou norms development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/BanLat/OrderContinuous/Basic.lean

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Convergences_Order
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderComplete
public import Theorems.Thm_isVLArchimedean_iff_le_zero_of_forall_nsmul_le

set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
class IsSigmaOrderContinuousNorm (X : Type*) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {u : ℕ → X}, Antitone u → (∀ n, 0 ≤ u n) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)
class IsOrderContinuousNorm (X : Type u) [NormedAddCommGroup X] [Lattice X]
    [IsOrderedAddMonoid X] [NormedVectorLattice X] : Prop where
  tendsto_of_antitone_isGLB_zero :
    ∀ {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
      {u : ι → X}, Antitone u → (∀ i, 0 ≤ u i) →
      IsGLB (Set.range u) 0 →
      Filter.Tendsto u Filter.atTop (nhds 0)
instance (priority := 100)
    IsOrderContinuousNorm.toIsSigmaOrderContinuousNorm {X : Type u}
    [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
    [NormedVectorLattice X] [h : IsOrderContinuousNorm X] :
    IsSigmaOrderContinuousNorm X := by
  refine ⟨fun {u} hanti hnn hglb => ?_⟩
  -- Transfer the ℕ-indexed sequence to the universe of `X` via `ULift`.
  let u' : ULift.{u, 0} ℕ → X := fun n => u n.down
  have hu'_anti : Antitone u' := fun a b h => hanti (by exact h)
  have hu'_nn : ∀ i, 0 ≤ u' i := fun i => hnn i.down
  have hu'_glb : IsGLB (Set.range u') 0 := by
    have hrange : Set.range u' = Set.range u := by
      ext z; constructor
      · rintro ⟨⟨n⟩, rfl⟩; exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩; exact ⟨⟨n⟩, rfl⟩
    rw [hrange]; exact hglb
  have htend := h.tendsto_of_antitone_isGLB_zero hu'_anti hu'_nn hu'_glb
  -- Pull back to ℕ: the map `n ↦ ⟨n⟩ : ℕ → ULift ℕ` is order isomorphic.
  have : Filter.Tendsto (fun n : ℕ => u' ⟨n⟩) Filter.atTop (nhds 0) := by
    refine htend.comp ?_
    refine Filter.tendsto_atTop.mpr fun ⟨b⟩ => ?_
    exact Filter.eventually_atTop.mpr ⟨b, fun n hn => hn⟩
  exact this
namespace IsSigmaOrderContinuousNorm
variable [NormedVectorLattice X] [IsSigmaOrderContinuousNorm X]
end IsSigmaOrderContinuousNorm
namespace BanachLattice
variable [BanachLattice X]
omit [BanachLattice X] in
/-- Archimedean "gap" lemma. In an Archimedean
vector lattice, any common lower bound of all differences `w - a` with `w` an
upper bound of a nonempty bounded-above set `A` and `a ∈ A` must be `≤ 0`. -/
lemma le_zero_of_lb_upperBounds_sub [IsVLArchimedean X]
    {A : Set X} (hne : A.Nonempty) (hbd : BddAbove A) {ε : X}
    (hε : ∀ w ∈ upperBounds A, ∀ a ∈ A, ε ≤ w - a) : ε ≤ 0 := by
  have key : ∀ n : ℕ, ∀ w ∈ upperBounds A, ∀ a ∈ A, n • ε ≤ w - a := by
    intro n
    induction n with
    | zero =>
        intro w hw a ha
        simpa using sub_nonneg.mpr (hw ha)
    | succ k ih =>
        intro w hw a ha
        have hub : w - k • ε ∈ upperBounds A := fun s hs =>
          le_sub_comm.mp (ih w hw s hs)
        have hstep : ε ≤ (w - k • ε) - a := hε _ hub a ha
        have h : k • ε + ε ≤ k • ε + ((w - k • ε) - a) :=
          add_le_add (le_refl (k • ε)) hstep
        have h3 : k • ε + ((w - k • ε) - a) = w - a := by abel
        rw [h3] at h
        simpa [succ_nsmul] using h
  obtain ⟨w₀, hw₀⟩ := hbd
  obtain ⟨a₀, ha₀⟩ := hne
  exact isVLArchimedean_iff_le_zero_of_forall_nsmul_le.mp inferInstance
    (fun n => key n w₀ hw₀ a₀ ha₀)
@[reducible]
noncomputable def conditionallyCompleteLatticeOfIsOrderContinuousNorm
    [IsOrderContinuousNorm X] :
    ConditionallyCompleteLattice X := by
  haveI : Nonempty X := ⟨0⟩
  refine conditionallyCompleteLatticeOfPosSet X
    (fun {S} _ hSne hSbdd => ?_)
  obtain ⟨w₀, hw₀⟩ := hSbdd
  obtain ⟨s₀, hs₀⟩ := hSne
  classical
  -- Index: (upper bound of S) ×ᵒᵈ (nonempty finite subset of S), ordered so
  -- that upper bounds decrease and finite subsets increase.
  let Ub : Type _ := {w : X // w ∈ upperBounds S}
  let Fn : Type _ := {F : Finset X // (↑F : Set X) ⊆ S ∧ F.Nonempty}
  let I : Type _ := Ubᵒᵈ × Fn
  have : Nonempty Ub := ⟨⟨w₀, hw₀⟩⟩
  have : Nonempty Fn := ⟨⟨{s₀}, by
    refine ⟨?_, Finset.singleton_nonempty s₀⟩
    intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact hs₀⟩⟩
  have : Nonempty I := instNonemptyProd
  have : IsDirected Fn (· ≤ ·) := by
    refine ⟨fun F G => ?_⟩
    refine ⟨⟨F.val ∪ G.val, ?_, F.prop.2.mono Finset.subset_union_left⟩,
            Finset.subset_union_left, Finset.subset_union_right⟩
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · exact F.prop.1 h
    · exact G.prop.1 h
  have : IsDirected Ubᵒᵈ (· ≤ ·) := by
    refine ⟨fun a b => ?_⟩
    refine ⟨OrderDual.toDual ⟨(OrderDual.ofDual a).val ⊓ (OrderDual.ofDual b).val,
      fun s hs => le_inf ((OrderDual.ofDual a).prop hs) ((OrderDual.ofDual b).prop hs)⟩,
      ?_, ?_⟩
    · change (_ : Ub) ≤ OrderDual.ofDual a
      exact inf_le_left
    · change (_ : Ub) ≤ OrderDual.ofDual b
      exact inf_le_right
  have : IsDirected I (· ≤ ·) := by
    refine ⟨fun p q => ?_⟩
    obtain ⟨c, hac, hbc⟩ := (‹IsDirected Ubᵒᵈ (· ≤ ·)›).directed p.1 q.1
    obtain ⟨d, had, hbd⟩ := (‹IsDirected Fn (· ≤ ·)›).directed p.2 q.2
    exact ⟨(c, d), ⟨hac, had⟩, ⟨hbc, hbd⟩⟩
  -- The antitone net `z` on `I`: `z (w, F) = w - sup' F`.
  let z : I → X := fun p =>
    (OrderDual.ofDual p.1).val - p.2.val.sup' p.2.prop.2 id
  have hFle : ∀ p : I, p.2.val.sup' p.2.prop.2 id ≤ (OrderDual.ofDual p.1).val :=
    fun p => Finset.sup'_le _ _ fun x hx =>
      (OrderDual.ofDual p.1).prop (p.2.prop.1 hx)
  have hz_nn : ∀ p : I, 0 ≤ z p := fun p => sub_nonneg.mpr (hFle p)
  have hz_anti : Antitone z := by
    intro p q hpq
    have h1 : (OrderDual.ofDual q.1).val ≤ (OrderDual.ofDual p.1).val := hpq.1
    have h2 : p.2.val ⊆ q.2.val := hpq.2
    have hsup : p.2.val.sup' p.2.prop.2 id ≤ q.2.val.sup' q.2.prop.2 id :=
      Finset.sup'_mono _ h2 p.2.prop.2
    exact sub_le_sub h1 hsup
  have hz_glb : IsGLB (Set.range z) 0 := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨p, rfl⟩; exact hz_nn p
    · intro ε hε
      -- `ε` is a lower bound of range `z`; apply the Archimedean gap lemma.
      refine le_zero_of_lb_upperBounds_sub ⟨s₀, hs₀⟩ ⟨w₀, hw₀⟩ ?_
      intro w hw a ha
      -- Form the element `(w, {a})` of `I` and evaluate `z`.
      let p : I := (OrderDual.toDual ⟨w, hw⟩,
        ⟨{a}, by
          refine ⟨?_, Finset.singleton_nonempty a⟩
          intro x hx; rcases Finset.mem_singleton.mp hx with rfl; exact ha⟩)
      have hzp : z p = w - a := by
        simp [z, p, Finset.sup'_singleton]
      have := hε ⟨p, rfl⟩
      rw [hzp] at this
      exact this
  -- Apply OCN to get `z → 0` in norm.
  have htend : Filter.Tendsto z Filter.atTop (nhds 0) :=
    IsOrderContinuousNorm.tendsto_of_antitone_isGLB_zero hz_anti hz_nn hz_glb
  -- Extract from `htend` that the monotone net `u_F = sup' F` is norm-Cauchy.
  let u : Fn → X := fun F => F.val.sup' F.prop.2 id
  have hu_mono : Monotone u := fun F G h => Finset.sup'_mono _ h F.prop.2
  have hu_cauchy : Cauchy (Filter.map u Filter.atTop) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
    rw [Metric.tendsto_nhds] at htend
    have hev := htend (ε/2) (by linarith)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨p₀, hp₀⟩ := hev
    refine ⟨u '' {F | p₀.2 ≤ F}, ?_, ?_⟩
    · exact Filter.image_mem_map (Filter.mem_atTop p₀.2)
    · rintro _ ⟨F, hF, rfl⟩ _ ⟨G, hG, rfl⟩
      have hpF : p₀ ≤ (p₀.1, F) := ⟨le_refl _, hF⟩
      have hpG : p₀ ≤ (p₀.1, G) := ⟨le_refl _, hG⟩
      have h1 : dist (z (p₀.1, F)) 0 < ε/2 := hp₀ _ hpF
      have h2 : dist (z (p₀.1, G)) 0 < ε/2 := hp₀ _ hpG
      rw [dist_zero_right] at h1 h2
      have hzF : z (p₀.1, F) = (OrderDual.ofDual p₀.1).val - u F := rfl
      have hzG : z (p₀.1, G) = (OrderDual.ofDual p₀.1).val - u G := rfl
      rw [dist_eq_norm]
      have heq : u F - u G = z (p₀.1, G) - z (p₀.1, F) := by
        rw [hzF, hzG]; abel
      rw [heq]
      have : ‖z (p₀.1, G) - z (p₀.1, F)‖ ≤ ‖z (p₀.1, G)‖ + ‖z (p₀.1, F)‖ := by
        rw [sub_eq_add_neg]
        exact (norm_add_le _ _).trans_eq (by rw [norm_neg])
      linarith
  -- By Banach completeness, `u` has a limit `x`.
  obtain ⟨x, hx_tend⟩ := CompleteSpace.complete hu_cauchy
  -- `x` is the LUB of range of `u`, which equals LUB of `S`.
  have hx_lub : IsLUB (Set.range u) x :=
    isLUB_of_tendsto_atTop hu_mono hx_tend
  refine ⟨x, ?_, ?_⟩
  · -- `x` is an upper bound of `S`
    intro s hs
    have hprop : (↑({s} : Finset X) : Set X) ⊆ S ∧ ({s} : Finset X).Nonempty := by
      refine ⟨?_, Finset.singleton_nonempty s⟩
      intro y hy; rcases Finset.mem_singleton.mp hy with rfl; exact hs
    have huFs : u ⟨{s}, hprop⟩ = s := by
      change ({s} : Finset X).sup' (Finset.singleton_nonempty s) id = s
      rw [Finset.sup'_singleton]; rfl
    rw [← huFs]
    exact hx_lub.1 ⟨⟨{s}, hprop⟩, rfl⟩
  · -- `x` is the least upper bound
    intro y hy
    refine hx_lub.2 ?_
    rintro _ ⟨F, rfl⟩
    exact Finset.sup'_le _ _ (fun s hs => hy (F.prop.1 hs))
end BanachLattice


