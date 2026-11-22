-- Prove2me | Definitions.Def_EventStructures_General_Basic
-- name    : EventStructures_General_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:36:25.967703+00:00
-- url     : https://prove2.me/theorems/69c9716b-58c2-4b61-af87-58c9ce4ac1e1
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/General/Basic.lean

import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Preorder.Finite
import Mathlib.Order.Minimal
set_option autoImplicit true
structure GES (Label : Type*) where
  Event : Type*
  Con : Finset Event → Prop
  enable : Finset Event → Event → Prop
  label : Event → Label
  con_empty : Con ∅
  con_subset : ∀ {X Y : Finset Event}, Con Y → X ⊆ Y → Con X
  enable_mono : ∀ {X Y : Finset Event} {e}, enable X e → X ⊆ Y → Con Y → enable Y e
namespace GES
variable {L : Type*} (G : GES L)
local infix:50 " ⊢ " => G.enable
def secApprox (x : Set G.Event) : ℕ → Set G.Event
  | 0 => ∅
  | n + 1 => {e ∈ x | ∃ X : Finset G.Event, ↑X ⊆ secApprox x n ∧ X ⊢ e}
variable {G}
lemma secApprox_subset {x : Set G.Event} : ∀ n, G.secApprox x n ⊆ x
  | 0 => fun _ h => h.elim
  | _ + 1 => fun _ h => h.1
lemma secApprox_succ {x : Set G.Event} : ∀ n, G.secApprox x n ⊆ G.secApprox x (n + 1)
  | 0 => fun _ h => h.elim
  | n + 1 => fun _ h => ⟨h.1, h.2.imp fun _ hX => ⟨hX.1.trans (secApprox_succ n), hX.2⟩⟩
lemma secApprox_mono {x : Set G.Event} {m n : ℕ} (h : m ≤ n) :
    G.secApprox x m ⊆ G.secApprox x n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (secApprox_succ _)
lemma secApprox_mono_set {x y : Set G.Event} (hxy : x ⊆ y) :
    ∀ n, G.secApprox x n ⊆ G.secApprox y n
  | 0 => fun _ h => h.elim
  | n + 1 => fun _ h => ⟨hxy h.1, h.2.imp fun _ hX => ⟨hX.1.trans (secApprox_mono_set hxy n), hX.2⟩⟩
variable (G)
def Consistent (s : Set G.Event) : Prop := ∀ X : Finset G.Event, ↑X ⊆ s → G.Con X
def isConf (x : Set G.Event) : Prop :=
  G.Consistent x ∧ ∀ e ∈ x, ∃ n, e ∈ G.secApprox x n
noncomputable def rank (x : Set G.Event) (e : G.Event) : ℕ :=
  sInf {n | e ∈ G.secApprox x n}
variable {G}
lemma rank_mem {x : Set G.Event} {e : G.Event} (h : ∃ n, e ∈ G.secApprox x n) :
    e ∈ G.secApprox x (G.rank x e) :=
  Nat.sInf_mem h
lemma rank_le {x : Set G.Event} {e : G.Event} {n : ℕ} (h : e ∈ G.secApprox x n) :
    G.rank x e ≤ n :=
  Nat.sInf_le h
lemma exists_bound {x : Set G.Event} {X : Finset G.Event}
    (h : ∀ g ∈ X, ∃ n, g ∈ G.secApprox x n) : ∃ N, ↑X ⊆ G.secApprox x N := by
  classical
  induction X using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert g X _ ih =>
    obtain ⟨n, hn⟩ := h g (Finset.mem_insert_self g X)
    obtain ⟨N, hN⟩ := ih fun f hf => h f (Finset.mem_insert_of_mem hf)
    refine ⟨max n N, ?_⟩
    rw [Finset.coe_insert]
    exact Set.insert_subset (secApprox_mono (le_max_left n N) hn)
      (hN.trans (secApprox_mono (le_max_right n N)))
variable (G)
lemma isConf_empty : G.isConf ∅ :=
  ⟨fun _ hX => Finset.coe_eq_empty.mp (Set.subset_empty_iff.mp hX) ▸ G.con_empty,
   fun _ h => h.elim⟩
lemma isConf_secured {x y : Set G.Event} (hx : G.isConf x) (hy : G.isConf y)
    (hsub : y ⊆ x) (hfin : (x \ y).Finite) (hne : x ≠ y) :
    ∃ e ∈ x \ y, G.isConf (x \ {e}) := by
  classical
  have hDne : (x \ y).Nonempty := by
    by_contra h
    exact hne (Set.Subset.antisymm (fun z hz => by
      by_contra hzy; exact h ⟨z, hz, hzy⟩) hsub)
  obtain ⟨e, hmax⟩ := hfin.exists_maximalFor (G.rank x) _ hDne
  have heD : e ∈ x \ y := hmax.1
  have hemax : ∀ f ∈ x \ y, G.rank x f ≤ G.rank x e := fun _ hf => not_lt.mp (hmax.not_gt hf)
  -- induction: every `f ∈ x` other than `e` is secured without `e`
  have key : ∀ n f, f ∈ x → f ≠ e → G.rank x f = n → ∃ m, f ∈ G.secApprox (x \ {e}) m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rintro f hf hfe rfl
      by_cases hfy : f ∈ y
      · obtain ⟨m, hm⟩ := hy.2 f hfy
        have hyx : y ⊆ x \ {e} := fun z hz =>
          ⟨hsub hz, fun hze => heD.2 (Set.mem_singleton_iff.mp hze ▸ hz)⟩
        exact ⟨m, secApprox_mono_set hyx m hm⟩
      · obtain ⟨k, hk⟩ : ∃ k, G.rank x f = k + 1 := by
          have hpos : G.rank x f ≠ 0 := by
            intro h0
            have hmem := rank_mem (hx.2 f hf)
            rw [h0] at hmem
            exact hmem
          exact ⟨G.rank x f - 1, by omega⟩
        obtain ⟨-, X, hXsub, hXen⟩ := hk ▸ rank_mem (hx.2 f hf)
        have hXlt : ∀ g ∈ X, G.rank x g < G.rank x f :=
          fun g hg => hk ▸ Nat.lt_succ_of_le (rank_le (hXsub hg))
        obtain ⟨N, hN⟩ := exists_bound (x := x \ {e}) fun g hg => by
          have hgx : g ∈ x := secApprox_subset _ (hXsub hg)
          have hge : g ≠ e := by
            rintro rfl
            have h₁ := hXlt g hg
            have h₂ := hemax f ⟨hf, hfy⟩
            omega
          exact ih _ (hXlt g hg) g hgx hge rfl
        exact ⟨N + 1, ⟨hf, fun hfe' => hfe (Set.mem_singleton_iff.mp hfe')⟩, X, hN, hXen⟩
  exact ⟨e, heD, fun X hX => hx.1 X (hX.trans Set.sdiff_subset),
    fun f hf => key _ f hf.1 (fun h => hf.2 (Set.mem_singleton_iff.mpr h)) rfl⟩
def pmapSet {L' : Type*} {G : GES L} {H : GES L'} (φ : G.Event → Option H.Event)
    (c : Set G.Event) : Set H.Event :=
  {x | ∃ u ∈ c, φ u = some x}
def toFamily : ConfFamily L where
  Event := G.Event
  Config := G.isConf
  label := G.label
  empty_mem := G.isConf_empty
  secured := G.isConf_secured
end GES


