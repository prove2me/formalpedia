-- Prove2me | Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Ray
-- name    : LeanPool_NashWilliams_Combinatorics_Front_Ray
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:43:24.324185+00:00
-- url     : https://prove2.me/theorems/6b039bbb-f6ef-4827-968e-bfc5dc62bdb5
-- title:
--   Ray
-- statement:
--   Definitions and structural lemmas for Ray, from Yann Pequignot; LeanPool contributors's pinned Nash-Williams fronts and better-quasi-orders development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NashWilliams/Combinatorics/Front/Ray.lean

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank
public import Mathlib.Order.Lattice.Nat
public import Theorems.Thm_Front_IsInit_head_eq
public import Theorems.Thm_Front_isInit_nil
public import Theorems.Thm_Front_isInit_take
public import Theorems.Thm_List_IsPrefix_head_eq
attribute [local simp] Front.isInit_nil


set_option autoImplicit true
@[expose] public section
@[expose] public section
open Set List
noncomputable section
variable {M : ℕ → ℕ}
def afterShift (M : ℕ → ℕ) (a : ℕ) : ℕ := sInf {j | a < M j}
def rayEnum (M : ℕ → ℕ) (a : ℕ) : ℕ → ℕ := fun i => M (i + afterShift M a)
theorem afterShift_spec (hM : StrictMono M) (a : ℕ) : a < M (afterShift M a) := by
  have hne : {j | a < M j}.Nonempty :=
    ⟨a + 1, lt_of_lt_of_le (Nat.lt_succ_self a) (hM.le_apply : a + 1 ≤ M (a + 1))⟩
  exact Nat.sInf_mem hne
theorem rayEnum_strictMono (hM : StrictMono M) (a : ℕ) : StrictMono (rayEnum M a) :=
  fun _ _ hxy => hM (by omega)
theorem rayEnum_gt (hM : StrictMono M) (a i : ℕ) : a < rayEnum M a i :=
  lt_of_lt_of_le (afterShift_spec hM a) (hM.monotone (by omega))
theorem rayEnum_mem_range (a i : ℕ) : rayEnum M a i ∈ Set.range M :=
  ⟨i + afterShift M a, rfl⟩
theorem mem_range_rayEnum_iff (hM : StrictMono M) (a n : ℕ) :
    n ∈ Set.range (rayEnum M a) ↔ n ∈ Set.range M ∧ a < n := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rayEnum_mem_range a i, rayEnum_gt hM a i⟩
  · rintro ⟨⟨k, rfl⟩, hlt⟩
    have hk : afterShift M a ≤ k := Nat.sInf_le hlt
    exact ⟨k - afterShift M a, by rw [rayEnum]; congr 1; omega⟩
namespace Front
variable {F : Set (List ℕ)}
def ray (F : Set (List ℕ)) (a : ℕ) : Set (List ℕ) := {t | a :: t ∈ F}
theorem exists_frontElem_isInit (hF : IsFront F M) {N : ℕ → ℕ} (hN : StrictMono N)
    (hsub : Set.range N ⊆ Set.range M) : ∃ u ∈ F, IsInit u N := by
  obtain ⟨h, hh, hcomp⟩ := exists_strictMono_comp hF.mono hN fun i => hsub ⟨i, rfl⟩
  obtain ⟨u, hu, hInit⟩ := hF.dense h hh
  rw [hcomp] at hInit
  exact ⟨u, hu, hInit⟩
theorem nil_not_mem (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F) : [] ∉ F := by
  intro hnil
  obtain ⟨w, hw, hpre⟩ := ha
  have := hF.incomp [] hnil w hw List.nil_prefix
  rw [← this] at hpre
  simpa using hpre.length_le
theorem IsFront.singleton_mem_tree (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : [n] ∈ tree F := by
  obtain ⟨k, rfl⟩ := hn
  set N : ℕ → ℕ := fun i => M (i + k) with hN
  have hNmono : StrictMono N := fun x y h => hF.mono (by omega)
  have hNsub : Set.range N ⊆ Set.range M := by rintro _ ⟨i, rfl⟩; exact ⟨i + k, rfl⟩
  obtain ⟨u, hu, hInit⟩ := exists_frontElem_isInit hF hNmono hNsub
  have hune : u ≠ [] := fun h => h0 (h ▸ hu)
  have hhead : u.head? = some (M k) := by rw [hInit.head_eq hune]; simp [hN]
  obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
  exact ⟨u, hu, hys ▸ ⟨ys, rfl⟩⟩
theorem exists_cons_mem (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F)
    {Q : ℕ → ℕ} (hQ : StrictMono Q) (haQ : a < Q 0) (hQM : ∀ i, Q i ∈ Set.range M) :
    ∃ t, a :: t ∈ F ∧ IsInit t Q := by
  have haM : a ∈ Set.range M := by
    obtain ⟨w, hw, hpre⟩ := ha
    exact hF.subM w hw a (hpre.subset (List.mem_singleton_self a))
  set N : ℕ → ℕ := fun i => if i = 0 then a else Q (i - 1) with hN
  have hN0 : N 0 = a := by simp [hN]
  have hNsucc : ∀ k, N (k + 1) = Q k := by intro k; simp [hN]
  have hNmono : StrictMono N := by
    apply strictMono_nat_of_lt_succ
    intro i
    cases i with
    | zero => rw [hN0, hNsucc]; exact haQ
    | succ k => rw [hNsucc, hNsucc]; exact hQ (Nat.lt_succ_self k)
  have hNsub : Set.range N ⊆ Set.range M := by
    rintro _ ⟨i, rfl⟩
    cases i with
    | zero => rw [hN0]; exact haM
    | succ k => rw [hNsucc]; exact hQM k
  obtain ⟨u, hu, hInit⟩ := exists_frontElem_isInit hF hNmono hNsub
  have hune : u ≠ [] := fun h => nil_not_mem hF ha (h ▸ hu)
  obtain ⟨m, hm⟩ : ∃ m, u.length = m + 1 := ⟨u.length - 1, by
    have : 0 < u.length := List.length_pos_iff.mpr hune; omega⟩
  have hu_eq : u = a :: (List.range m).map Q := by
    rw [hInit, hm, List.range_succ_eq_map, List.map_cons, hN0]
    congr 1
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    exact hNsucc k
  refine ⟨(List.range m).map Q, ?_, isInit_take Q m⟩
  rw [← hu_eq]; exact hu
theorem ray_isFront (hF : IsFront F M) {a : ℕ} (ha : [a] ∈ tree F) :
    IsFront (ray F a) (rayEnum M a) where
  mono := rayEnum_strictMono hF.mono a
  sorted t ht := (hF.sorted (a :: t) ht).of_cons
  subM t ht x hx := by
    have hxM : x ∈ Set.range M := hF.subM (a :: t) ht x (List.mem_cons_of_mem a hx)
    have hax : a < x := (List.pairwise_cons.mp (hF.sorted (a :: t) ht)).1 x hx
    exact (mem_range_rayEnum_iff hF.mono a x).mpr ⟨hxM, hax⟩
  incomp s hs t ht hst := by
    have heq : a :: s = a :: t :=
      hF.incomp (a :: s) hs (a :: t) ht ((List.prefix_cons_inj a).mpr hst)
    injection heq with _ h
  dense g hg := by
    have hQmono : StrictMono (rayEnum M a ∘ g) := (rayEnum_strictMono hF.mono a).comp hg
    obtain ⟨t, htF, htInit⟩ := exists_cons_mem hF ha hQmono
      (by exact rayEnum_gt hF.mono a (g 0)) (fun i => rayEnum_mem_range a (g i))
    exact ⟨t, htF, htInit⟩
  base := by
    by_cases haF : [a] ∈ F
    · left
      ext t
      simp only [ray, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro ht
        have heq := hF.incomp [a] haF (a :: t) ht ((List.prefix_cons_inj a).mpr List.nil_prefix)
        injection heq with _ h; exact h.symm
      · rintro rfl; exact haF
    · right
      ext n
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨t, ht, hnt⟩
        have hxM : n ∈ Set.range M := hF.subM (a :: t) ht n (List.mem_cons_of_mem a hnt)
        have hax : a < n := (List.pairwise_cons.mp (hF.sorted (a :: t) ht)).1 n hnt
        exact (mem_range_rayEnum_iff hF.mono a n).mpr ⟨hxM, hax⟩
      · intro hn
        obtain ⟨hnM, hax⟩ := (mem_range_rayEnum_iff hF.mono a n).mp hn
        obtain ⟨k, rfl⟩ := hnM
        have hQmono : StrictMono (fun i => M (i + k)) := fun x y hxy => hF.mono (by omega)
        obtain ⟨t, htF, htInit⟩ := exists_cons_mem hF ha hQmono (by simpa using hax)
          (fun i => ⟨i + k, rfl⟩)
        have htne : t ≠ [] := by rintro rfl; exact haF htF
        have hhead : t.head? = some (M k) := by rw [htInit.head_eq htne]; simp
        refine ⟨t, htF, ?_⟩
        obtain ⟨ys, hys⟩ := List.head?_eq_some_iff.mp hhead
        rw [hys]; simp
theorem IsFront.ray_isFront_mem (hF : IsFront F M) (h0 : [] ∉ F) {n : ℕ}
    (hn : n ∈ Set.range M) : IsFront (ray F n) (rayEnum M n) :=
  ray_isFront hF (hF.singleton_mem_tree h0 hn)
end Front


