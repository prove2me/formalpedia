-- Prove2me | solution 1 for AppliedComb.Flows.max_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:49:24.744188+00:00
-- url     : https://prove2.me/submissions/d597e854-7c08-40d4-9355-8167dba6c37e

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network



namespace AppliedComb.Flows

namespace FFX

variable {V : Type*} [Fintype V] [DecidableEq V]

def R0 (N : Network V) (ϕ : V → V → ℝ) (x y : V) : Prop :=
  (N.adj x y ∧ ϕ x y < N.cap x y) ∨ (N.adj y x ∧ 0 < ϕ y x)

def Rd (N : Network V) (ϕ : V → V → ℝ) (δ : ℝ) (x y : V) : Prop :=
  (N.adj x y ∧ ϕ x y + δ ≤ N.cap x y) ∨ (N.adj y x ∧ δ ≤ ϕ y x)

def exc (g : V → V → ℝ) (w : V) : ℝ := ∑ x, g x w - ∑ x, g w x

def single (u v : V) : V → V → ℝ := fun x y => if x = u ∧ y = v then 1 else 0

inductive NPath {α : Type*} (r : α → α → Prop) : α → α → List α → Prop
  | nil (a : α) : NPath r a a [a]
  | cons {a b c : α} {l : List α} : r a b → NPath r b c l → NPath r a c (a :: l)

theorem NPath.head_mem {α : Type*} {r : α → α → Prop} {a c : α} {l : List α}
    (h : NPath r a c l) : a ∈ l := by
  cases h <;> simp

theorem NPath.shortcut {α : Type*} {r : α → α → Prop} {b c : α} {l : List α}
    (h : NPath r b c l) : ∀ a, a ∈ l → ∃ l', l'.Sublist l ∧ NPath r a c l' := by
  induction h with
  | nil b =>
    intro a ha
    simp at ha
    subst ha
    exact ⟨[a], List.Sublist.refl _, NPath.nil a⟩
  | cons hab hp ih =>
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.Sublist.refl _, NPath.cons hab hp⟩
    · obtain ⟨l'', hs, hp'⟩ := ih a ha
      exact ⟨l'', hs.cons _, hp'⟩

theorem exists_nodup {α : Type*} {r : α → α → Prop} {a b : α}
    (h : Relation.ReflTransGen r a b) : ∃ l, l.Nodup ∧ NPath r a b l := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], List.nodup_singleton _, NPath.nil b⟩
  | @head a c hac hcb ih =>
    obtain ⟨l, hl, hp⟩ := ih
    by_cases ha : a ∈ l
    · obtain ⟨l', hs, hp'⟩ := hp.shortcut a ha
      exact ⟨l', hl.sublist hs, hp'⟩
    · exact ⟨a :: l, List.nodup_cons.2 ⟨ha, hl⟩, NPath.cons hac hp⟩

theorem exc_add (f g : V → V → ℝ) (w : V) :
    exc (fun x y => f x y + g x y) w = exc f w + exc g w := by
  simp only [exc, Finset.sum_add_distrib]; ring

theorem exc_mul (c : ℝ) (f : V → V → ℝ) (w : V) :
    exc (fun x y => c * f x y) w = c * exc f w := by
  simp only [exc, ← Finset.mul_sum]; ring

theorem exc_single (u v : V) (huv : u ≠ v) (w : V) :
    exc (single u v) w = (if w = v then 1 else 0) - (if w = u then 1 else 0) := by
  by_cases hw : w = v
  · subst hw
    have : w ≠ u := fun h => huv h.symm
    simp [exc, single, this]
  · by_cases hw' : w = u
    · subst hw'
      simp [exc, single, hw]
    · simp [exc, single, hw, hw']

theorem aug {N : Network V} {ϕ : V → V → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hϕ : ∀ x y, N.adj x y → 0 ≤ ϕ x y ∧ ϕ x y ≤ N.cap x y)
    {a c : V} {l : List V} (hp : NPath (Rd N ϕ δ) a c l) (hl : l.Nodup) :
    ∃ g : V → V → ℝ, (∀ x y, g x y ≠ 0 → x ∈ l ∧ y ∈ l) ∧
      (∀ x y, N.adj x y → 0 ≤ ϕ x y + g x y ∧ ϕ x y + g x y ≤ N.cap x y) ∧
      (∀ x y, ¬ N.adj x y → g x y = 0) ∧
      (∀ w, exc g w = δ * ((if w = c then 1 else 0) - (if w = a then 1 else 0))) ∧
      (∀ x y, ∃ n : ℤ, g x y = n * δ) := by
  classical
  induction hp with
  | nil a =>
    refine ⟨fun _ _ => 0, by simp, fun x y h => by simpa using hϕ x y h, fun _ _ _ => rfl,
      fun w => by simp [exc], fun _ _ => ⟨0, by simp⟩⟩
  | @cons a b c l hab hp ih =>
    have ha : a ∉ l := (List.nodup_cons.1 hl).1
    obtain ⟨g, hsupp, hbd, hz, hexc, hint⟩ := ih (List.nodup_cons.1 hl).2
    have hbl : b ∈ l := hp.head_mem
    have hab' : a ≠ b := fun h => ha (h ▸ hbl)
    have g0 : ∀ y, g a y = 0 ∧ g y a = 0 := by
      intro y
      constructor
      · by_contra h; exact ha (hsupp _ _ h).1
      · by_contra h; exact ha (hsupp _ _ h).2
    by_cases hadj : N.adj a b
    · have hcap : ϕ a b + δ ≤ N.cap a b := by
        rcases hab with h | h
        · exact h.2
        · exact absurd h.1 (N.oriented _ _ hadj)
      refine ⟨fun x y => δ * single a b x y + g x y, ?_, ?_, ?_, ?_, ?_⟩
      · intro x y hxy
        by_cases h : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h; simp [hbl]
        · have : g x y ≠ 0 := by simpa [single, h] using hxy
          obtain ⟨h1, h2⟩ := hsupp x y this
          exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      · intro x y hxy
        by_cases h : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h
          have := hϕ x y hxy
          simp only [single, and_self, if_true, mul_one, (g0 y).1]
          constructor <;> linarith
        · simpa [single, h] using hbd x y hxy
      · intro x y hxy
        by_cases h : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h; exact absurd hadj hxy
        · simp [single, h, hz x y hxy]
      · intro w
        rw [exc_add, exc_mul, exc_single a b hab', hexc]
        ring
      · intro x y
        obtain ⟨n, hn⟩ := hint x y
        by_cases h : x = a ∧ y = b
        · obtain ⟨rfl, rfl⟩ := h; exact ⟨1 + n, by simp [single, hn]; ring⟩
        · exact ⟨n, by simp [single, h, hn]⟩
    · have hcap : N.adj b a ∧ δ ≤ ϕ b a := by
        rcases hab with h | h
        · exact absurd h.1 hadj
        · exact h
      refine ⟨fun x y => (-δ) * single b a x y + g x y, ?_, ?_, ?_, ?_, ?_⟩
      · intro x y hxy
        by_cases h : x = b ∧ y = a
        · obtain ⟨rfl, rfl⟩ := h; simp [hbl]
        · have : g x y ≠ 0 := by simpa [single, h] using hxy
          obtain ⟨h1, h2⟩ := hsupp x y this
          exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩
      · intro x y hxy
        by_cases h : x = b ∧ y = a
        · obtain ⟨rfl, rfl⟩ := h
          have := hϕ x y hxy
          simp only [single, and_self, if_true, mul_one, (g0 x).2]
          constructor <;> linarith
        · simpa [single, h] using hbd x y hxy
      · intro x y hxy
        by_cases h : x = b ∧ y = a
        · obtain ⟨rfl, rfl⟩ := h; exact absurd hcap.1 hxy
        · simp [single, h, hz x y hxy]
      · intro w
        rw [exc_add, exc_mul, exc_single b a hab'.symm, hexc]
        ring
      · intro x y
        obtain ⟨n, hn⟩ := hint x y
        by_cases h : x = b ∧ y = a
        · obtain ⟨rfl, rfl⟩ := h; exact ⟨-1 + n, by simp [single, hn]; ring⟩
        · exact ⟨n, by simp [single, h, hn]⟩

theorem flow_aug {N : Network V} {ϕ : V → V → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hϕ : N.IsFlow ϕ)
    (hr : Relation.ReflTransGen (Rd N ϕ δ) N.S N.T) :
    ∃ g : V → V → ℝ, N.IsFlow (fun x y => ϕ x y + g x y) ∧
      N.value (fun x y => ϕ x y + g x y) = N.value ϕ + δ ∧
      (∀ x y, ∃ n : ℤ, g x y = n * δ) := by
  classical
  obtain ⟨l, hl, hp⟩ := exists_nodup hr
  obtain ⟨g, -, hbd, hz, hexc, hint⟩ := aug hδ hϕ.1 hp hl
  have hST := N.source_ne_sink
  have hinS : ∑ x, g x N.S = 0 :=
    Finset.sum_eq_zero fun x _ => hz x _ (N.no_edge_into_source x)
  have houtT : ∑ x, g N.T x = 0 :=
    Finset.sum_eq_zero fun x _ => hz _ x (N.no_edge_out_of_sink x)
  have hS : ∑ x, g N.S x = δ := by
    have := hexc N.S
    simp only [exc, hST, if_false, if_true, hinS] at this
    linarith
  have hT : ∑ x, g x N.T = δ := by
    have := hexc N.T
    simp only [exc, hST.symm, if_false, if_true, houtT] at this
    linarith
  obtain ⟨h1, h2, h3, h4⟩ := hϕ
  refine ⟨g, ⟨hbd, fun x y h => by simp [h2 x y h, hz x y h], ?_, ?_⟩, ?_, hint⟩
  · simp only [Finset.sum_add_distrib, hS, hT, h3]
  · intro y hy1 hy2
    have := hexc y
    simp only [exc, hy1, hy2, if_false, sub_zero, mul_zero] at this
    simp only [Finset.sum_add_distrib, h4 y hy1 hy2]
    linarith
  · simp only [Network.value, Finset.sum_add_distrib, hS]

theorem value_eq_cut {N : Network V} {ϕ : V → V → ℝ} (hϕ : N.IsFlow ϕ) (L : Finset V)
    (hL : N.IsCut L) :
    N.value ϕ = ∑ x ∈ L, ∑ y ∈ Lᶜ, ϕ x y - ∑ x ∈ L, ∑ y ∈ Lᶜ, ϕ y x := by
  obtain ⟨h1, h2, h3, h4⟩ := hϕ
  have hin : ∀ x, ϕ x N.S = 0 := fun x => h2 x _ (N.no_edge_into_source x)
  have key : ∀ x ∈ L, (∑ y, ϕ x y - ∑ y, ϕ y x) = if x = N.S then N.value ϕ else 0 := by
    intro x hx
    by_cases hxS : x = N.S
    · subst hxS; simp [hin, Network.value]
    · have hxT : x ≠ N.T := fun h => hL.2 (h ▸ hx)
      simp [hxS, h4 x hxS hxT]
  have hsum : ∑ x ∈ L, (∑ y, ϕ x y - ∑ y, ϕ y x) = N.value ϕ := by
    rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' L N.S, if_pos hL.1]
  rw [← hsum, Finset.sum_sub_distrib]
  simp only [← Finset.sum_add_sum_compl L, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := L) (t := L) (f := fun x y => ϕ y x)]
  ring

theorem weak_dual {N : Network V} {ϕ : V → V → ℝ} (hϕ : N.IsFlow ϕ) (L : Finset V)
    (hL : N.IsCut L) : N.value ϕ ≤ N.cutCapacity L := by
  classical
  rw [value_eq_cut hϕ L hL, Network.cutCapacity]
  have hA : ∑ x ∈ L, ∑ y ∈ Lᶜ, ϕ x y ≤ ∑ x ∈ L, ∑ y ∈ Lᶜ, if N.adj x y then N.cap x y else 0 := by
    apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
    split_ifs with h
    · exact (hϕ.1 x y h).2
    · exact le_of_eq (hϕ.2.1 x y h)
  have hB : 0 ≤ ∑ x ∈ L, ∑ y ∈ Lᶜ, ϕ y x := by
    apply Finset.sum_nonneg; intro x _; apply Finset.sum_nonneg; intro y _
    by_cases h : N.adj y x
    · exact (hϕ.1 y x h).1
    · exact le_of_eq (hϕ.2.1 y x h).symm
  linarith

theorem reach_cut {N : Network V} {ϕ : V → V → ℝ} (hϕ : N.IsFlow ϕ)
    (hT : ¬ Relation.ReflTransGen (R0 N ϕ) N.S N.T) :
    ∃ L : Finset V, N.IsCut L ∧ N.cutCapacity L = N.value ϕ := by
  classical
  let L : Finset V := Finset.univ.filter (fun x => Relation.ReflTransGen (R0 N ϕ) N.S x)
  have hL : N.IsCut L := by
    constructor
    · simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Relation.ReflTransGen.refl
    · simpa [L] using hT
  refine ⟨L, hL, ?_⟩
  rw [value_eq_cut hϕ L hL, Network.cutCapacity]
  have hnr : ∀ x ∈ L, ∀ y ∈ Lᶜ, ¬ R0 N ϕ x y := by
    intro x hx y hy hr
    simp only [L, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    exact hy (hx.tail hr)
  have hA : ∑ x ∈ L, ∑ y ∈ Lᶜ, ϕ x y = ∑ x ∈ L, ∑ y ∈ Lᶜ, if N.adj x y then N.cap x y else 0 := by
    apply Finset.sum_congr rfl; intro x hx; apply Finset.sum_congr rfl; intro y hy
    have := hnr x hx y hy
    split_ifs with h
    · have := (hϕ.1 x y h).2
      by_contra hne
      exact (hnr x hx y hy) (Or.inl ⟨h, lt_of_le_of_ne this hne⟩)
    · exact hϕ.2.1 x y h
  have hB : ∑ x ∈ L, ∑ y ∈ Lᶜ, ϕ y x = 0 := by
    apply Finset.sum_eq_zero; intro x hx; apply Finset.sum_eq_zero; intro y hy
    by_cases h : N.adj y x
    · have := (hϕ.1 y x h).1
      by_contra hne
      exact (hnr x hx y hy) (Or.inr ⟨h, lt_of_le_of_ne this (Ne.symm hne)⟩)
    · exact hϕ.2.1 y x h
  rw [hA, hB, sub_zero]

theorem Rd_mono {N : Network V} {ϕ : V → V → ℝ} {δ δ' : ℝ} (h : δ' ≤ δ) {x y : V}
    (hr : Rd N ϕ δ x y) : Rd N ϕ δ' x y := by
  rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by linarith⟩
  · exact Or.inr ⟨h1, by linarith⟩

theorem R0_Rd {N : Network V} {ϕ : V → V → ℝ} {a b : V}
    (h : Relation.ReflTransGen (R0 N ϕ) a b) :
    ∃ δ > 0, Relation.ReflTransGen (Rd N ϕ δ) a b := by
  induction h with
  | refl => exact ⟨1, one_pos, Relation.ReflTransGen.refl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨δ1, hδ1, h1⟩ := ih
    obtain ⟨δ2, hδ2, h2⟩ : ∃ δ2 > 0, Rd N ϕ δ2 b c := by
      rcases hbc with ⟨h, h'⟩ | ⟨h, h'⟩
      · exact ⟨N.cap b c - ϕ b c, by linarith, Or.inl ⟨h, by linarith⟩⟩
      · exact ⟨ϕ c b, h', Or.inr ⟨h, le_rfl⟩⟩
    refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
    exact (Relation.ReflTransGen.mono (fun x y hr => Rd_mono (min_le_left _ _) hr) _ _ h1).tail
      (Rd_mono (min_le_right _ _) h2)

theorem zero_flow (N : Network V) : N.IsFlow (fun _ _ => 0) := by
  refine ⟨fun x y h => ⟨le_rfl, N.cap_nonneg x y h⟩, fun _ _ _ => rfl, by simp, fun _ _ _ => by simp⟩

theorem exists_max (N : Network V) :
    ∃ ϕ, N.IsFlow ϕ ∧ ∀ ψ, N.IsFlow ψ → N.value ψ ≤ N.value ϕ := by
  classical
  let F : Set (V → V → ℝ) := {ϕ | N.IsFlow ϕ}
  let box : Set (V → V → ℝ) :=
    Set.pi Set.univ (fun x => Set.pi Set.univ (fun y => Set.Icc (-|N.cap x y|) |N.cap x y|))
  have hbox : IsCompact box := isCompact_univ_pi (fun x => isCompact_univ_pi (fun y => isCompact_Icc))
  have hsub : F ⊆ box := by
    intro ϕ hϕ
    simp only [box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    intro x y
    by_cases h : N.adj x y
    · have := hϕ.1 x y h
      constructor
      · linarith [abs_nonneg (N.cap x y)]
      · linarith [le_abs_self (N.cap x y)]
    · rw [hϕ.2.1 x y h]
      constructor
      · linarith [abs_nonneg (N.cap x y)]
      · exact abs_nonneg _
  have hclosed : IsClosed F := by
    simp only [F, Network.IsFlow, Set.ofPred_and, Set.ofPred_forall]
    refine IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => ?_) (IsClosed.inter (isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_iInter fun _ => ?_) (IsClosed.inter ?_ (isClosed_iInter fun y =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_)))
    · exact IsClosed.inter (isClosed_le continuous_const (by fun_prop))
        (isClosed_le (by fun_prop) continuous_const)
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact isClosed_eq (by fun_prop) (by fun_prop)
  have hK : IsCompact F := hbox.of_isClosed_subset hclosed hsub
  have hne : F.Nonempty := ⟨_, zero_flow N⟩
  have hcont : ContinuousOn (fun ϕ : V → V → ℝ => N.value ϕ) F := by
    apply Continuous.continuousOn
    unfold Network.value
    fun_prop
  obtain ⟨ϕ, hϕ, hmax⟩ := hK.exists_isMaxOn hne hcont
  exact ⟨ϕ, hϕ, fun ψ hψ => hmax hψ⟩

theorem mfmc_core (N : Network V) :
    ∃ v₀ : ℝ,
      IsGreatest {v : ℝ | ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧ N.value ϕ = v} v₀ ∧
      IsLeast {c : ℝ | ∃ L : Finset V, N.IsCut L ∧ N.cutCapacity L = c} v₀ := by
  obtain ⟨ϕ, hϕ, hmax⟩ := exists_max N
  refine ⟨N.value ϕ, ⟨⟨ϕ, hϕ, rfl⟩, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro v ⟨ψ, hψ, rfl⟩
    exact hmax ψ hψ
  · by_cases hT : Relation.ReflTransGen (R0 N ϕ) N.S N.T
    · exfalso
      obtain ⟨δ, hδ, hr⟩ := R0_Rd hT
      obtain ⟨g, hg, hv, -⟩ := flow_aug hδ.le hϕ hr
      have := hmax _ hg
      linarith
    · obtain ⟨L, hL, hc⟩ := reach_cut hϕ hT
      exact ⟨L, hL, hc⟩
  · rintro c ⟨L, hL, rfl⟩
    exact weak_dual hϕ L hL

theorem integral_core (N : Network V)
    (hcap : ∀ x y, N.adj x y → ∃ n : ℤ, N.cap x y = n) :
    ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧
      (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value ϕ) ∧
      ∀ x y, N.adj x y → ∃ n : ℤ, ϕ x y = n := by
  classical
  let L0 : Finset V := {N.S}
  have hL0 : N.IsCut L0 := ⟨by simp [L0], by simpa [L0] using N.source_ne_sink.symm⟩
  set C := N.cutCapacity L0
  have step : ∀ ϕ, N.IsFlow ϕ → (∀ x y, ∃ k : ℤ, ϕ x y = k) →
      (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value ϕ) ∨
      ∃ ψ, N.IsFlow ψ ∧ (∀ x y, ∃ k : ℤ, ψ x y = k) ∧ N.value ψ = N.value ϕ + 1 := by
    intro ϕ hϕ hint
    by_cases hT : Relation.ReflTransGen (R0 N ϕ) N.S N.T
    · right
      have hr : Relation.ReflTransGen (Rd N ϕ 1) N.S N.T := by
        refine Relation.ReflTransGen.mono (fun x y hxy => ?_) _ _ hT
        rcases hxy with ⟨h, h'⟩ | ⟨h, h'⟩
        · left
          refine ⟨h, ?_⟩
          obtain ⟨k, hk⟩ := hint x y
          obtain ⟨m, hm⟩ := hcap x y h
          rw [hk, hm] at h' ⊢
          have : k < m := by exact_mod_cast h'
          have : k + 1 ≤ m := this
          exact_mod_cast this
        · right
          refine ⟨h, ?_⟩
          obtain ⟨k, hk⟩ := hint y x
          rw [hk] at h' ⊢
          have : (0:ℤ) < k := by exact_mod_cast h'
          have : (1:ℤ) ≤ k := this
          exact_mod_cast this
      obtain ⟨g, hg, hv, hgi⟩ := flow_aug zero_le_one hϕ hr
      refine ⟨_, hg, fun x y => ?_, hv⟩
      obtain ⟨k, hk⟩ := hint x y
      obtain ⟨m, hm⟩ := hgi x y
      exact ⟨k + m, by simp [hk, hm]⟩
    · left
      obtain ⟨L, hL, hc⟩ := reach_cut hϕ hT
      intro ψ hψ
      rw [← hc]
      exact weak_dual hψ L hL
  have main : ∀ n : ℕ, ∀ ϕ, N.IsFlow ϕ → (∀ x y, ∃ k : ℤ, ϕ x y = k) →
      C - N.value ϕ ≤ n →
      ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧
        (∀ ψ : V → V → ℝ, N.IsFlow ψ → N.value ψ ≤ N.value ϕ) ∧
        ∀ x y, ∃ k : ℤ, ϕ x y = k := by
    intro n
    induction n with
    | zero =>
      intro ϕ hϕ hint hn
      rcases step ϕ hϕ hint with h | ⟨ψ, hψ, -, hv⟩
      · exact ⟨ϕ, hϕ, h, hint⟩
      · have := weak_dual hψ L0 hL0
        push_cast at hn
        linarith
    | succ m ih =>
      intro ϕ hϕ hint hn
      rcases step ϕ hϕ hint with h | ⟨ψ, hψ, hψi, hv⟩
      · exact ⟨ϕ, hϕ, h, hint⟩
      · apply ih ψ hψ hψi
        push_cast at hn
        linarith
  have h0 : N.value (fun _ _ => (0:ℝ)) = 0 := by simp [Network.value]
  obtain ⟨ϕ, hϕ, hmax, hint⟩ := main ⌈C⌉₊ _ (zero_flow N) (fun _ _ => ⟨0, by simp⟩)
    (by rw [h0, sub_zero]; exact Nat.le_ceil C)
  exact ⟨ϕ, hϕ, hmax, fun x y _ => hint x y⟩

end FFX

end AppliedComb.Flows

open AppliedComb.Flows


theorem solution {V : Type*} [Fintype V] [DecidableEq V] (N : Network V) :
    ∃ v₀ : ℝ,
      IsGreatest {v : ℝ | ∃ ϕ : V → V → ℝ, N.IsFlow ϕ ∧ N.value ϕ = v} v₀ ∧
      IsLeast {c : ℝ | ∃ L : Finset V, N.IsCut L ∧ N.cutCapacity L = c} v₀ := by
  exact FFX.mfmc_core N
