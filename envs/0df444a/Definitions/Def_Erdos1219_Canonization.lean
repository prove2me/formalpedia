-- Prove2me | Definitions.Def_Erdos1219_Canonization
-- name    : Erdos1219_Canonization
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:48:20.476855+00:00
-- url     : https://prove2.me/theorems/867e609a-47e3-4794-a4e3-05b71c2c4c14
-- title:
--   Canonization
-- statement:
--   Definitions and structural lemmas for Canonization, from Ji Ho Bae (jbaelaw/erdos1219-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos Problem 1219 on cardinal partition relations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Theorems.Thm_Erdos1219_Homog_mono
import Theorems.Thm_Erdos1219_aleph0_le_two_pow
import Theorems.Thm_Erdos1219_erdosRado_unbalanced
import Theorems.Thm_Erdos1219_exists_fiber_eq_of_isRegular
import Theorems.Thm_Erdos1219_mk_bounded_subsets_le
import Theorems.Thm_Erdos1219_mk_iUnion_lt_of_isRegular
import Theorems.Thm_Erdos1219_nonempty_of_mk_eq

set_option autoImplicit false
open Cardinal Ordinal Function
namespace Erdos1219
universe u
structure Ctx (V : Type u) where
  f : V → V → Bool
  hf : ∀ x y, f x y = f y x
  n : ℕ → ℕ
  hn : StrictMono n
  hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)
  h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0)
  A : ℕ → Set V
  hA : ∀ k, #(A k) = Order.succ ((2 : Cardinal.{u}) ^ ℵ_ (n k))
  hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  hno : ∀ (c : Bool) (H : Set V), Homog f c H → #H ≠ ℵ_ ω
namespace Ctx
variable {V : Type u} (S : Ctx V)
noncomputable def μ (k : ℕ) : Cardinal.{u} := ℵ_ (S.n k : Ordinal.{u})
noncomputable def lam (k : ℕ) : Cardinal.{u} := Order.succ (2 ^ S.μ k)
theorem mk_A (k : ℕ) : #(S.A k) = S.lam k := S.hA k
theorem aleph0_le_μ (k : ℕ) : ℵ₀ ≤ S.μ k := aleph0_le_aleph _
theorem μ_mono {i k : ℕ} (h : i ≤ k) : S.μ i ≤ S.μ k :=
  aleph_le_aleph.2 (by exact_mod_cast S.hn.monotone h)
theorem two_pow_μ_lt {i k : ℕ} (h : i < k) : (2 : Cardinal.{u}) ^ S.μ i < 2 ^ S.μ k := S.hpow h
theorem two_pow_μ_le {i k : ℕ} (h : i ≤ k) : (2 : Cardinal.{u}) ^ S.μ i ≤ 2 ^ S.μ k :=
  S.hpow.monotone h
theorem aleph0_le_two_pow_μ (k : ℕ) : ℵ₀ ≤ (2 : Cardinal.{u}) ^ S.μ k :=
  aleph0_le_two_pow (S.aleph0_le_μ k)
theorem lam_isRegular (k : ℕ) : (S.lam k).IsRegular := isRegular_succ (S.aleph0_le_two_pow_μ k)
theorem two_pow_lt_lam (k : ℕ) : (2 : Cardinal.{u}) ^ S.μ k < S.lam k := Order.lt_succ _
theorem lam_le_two_pow_succ (k : ℕ) : S.lam k ≤ 2 ^ S.μ (k + 1) :=
  Order.succ_le_of_lt (S.two_pow_μ_lt (Nat.lt_succ_self k))
theorem aleph_omega_lt_two_pow (k : ℕ) : ℵ_ ω < (2 : Cardinal.{u}) ^ S.μ k :=
  S.h0.trans_le (S.two_pow_μ_le (Nat.zero_le k))
theorem aleph_omega_lt_lam (k : ℕ) : ℵ_ ω < S.lam k :=
  (S.aleph_omega_lt_two_pow k).trans (S.two_pow_lt_lam k)
theorem two_pow_aleph0_lt_lam (k : ℕ) : (2 : Cardinal.{u}) ^ ℵ₀ < S.lam k :=
  (power_le_power_left two_ne_zero (S.aleph0_le_μ k)).trans_lt (S.two_pow_lt_lam k)
theorem noBig (k : ℕ) (c : Bool) (H : Set V) (hH : Homog S.f c H) : #H ≠ S.lam k := by
  intro hHk
  obtain ⟨H', hH'sub, hH'⟩ :=
    le_mk_iff_exists_subset.1 ((S.aleph_omega_lt_lam k).le.trans_eq hHk.symm)
  exact S.hno c H' (hH.mono hH'sub) hH'
theorem exists_homog_two (k : ℕ) (C : Set V) (hC : #C = S.lam k) :
    ∃ B0 B1 : Set V, B0 ⊆ C ∧ B1 ⊆ C ∧ #B0 = S.μ k ∧ #B1 = S.μ k ∧
      Homog S.f false B0 ∧ Homog S.f true B1 := by
  have h0 := erdosRado_unbalanced S.f S.hf (S.μ k) (S.aleph0_le_μ k) C hC true
  have h1 := erdosRado_unbalanced S.f S.hf (S.μ k) (S.aleph0_le_μ k) C hC false
  rcases h0 with ⟨H, -, hH, hom⟩ | ⟨H0, hH0C, hH0, hom0⟩
  · exact absurd hH (S.noBig k true H hom)
  rcases h1 with ⟨H, -, hH, hom⟩ | ⟨H1, hH1C, hH1, hom1⟩
  · exact absurd hH (S.noBig k false H hom)
  obtain ⟨B0, hB0, hB0c⟩ :=
    le_mk_iff_exists_subset.1 ((Order.le_succ (S.μ k)).trans_eq hH0.symm)
  obtain ⟨B1, hB1, hB1c⟩ :=
    le_mk_iff_exists_subset.1 ((Order.le_succ (S.μ k)).trans_eq hH1.symm)
  exact ⟨B0, B1, hB0.trans hH0C, hB1.trans hH1C, hB0c, hB1c, hom0.mono hB0, hom1.mono hB1⟩
noncomputable def U (S : Ctx V) : ℕ → Set V
  | 0 => ∅
  | k + 1 => U S k ∪ S.A k
theorem mem_U {v : V} {k : ℕ} : v ∈ S.U k ↔ ∃ i, i < k ∧ v ∈ S.A i := by
  induction k with
  | zero => simp [U]
  | succ k ih =>
    simp only [U, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨k, Nat.lt_succ_self k, hv⟩
    · rintro ⟨i, hi, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact Or.inl ⟨i, hi, hv⟩
      · exact Or.inr hv
theorem A_subset_U {i k : ℕ} (h : i < k) : S.A i ⊆ S.U k := fun _ hv => S.mem_U.2 ⟨i, h, hv⟩
theorem mk_U_le (k : ℕ) : #(S.U k) ≤ 2 ^ S.μ k := by
  induction k with
  | zero => simp [U]
  | succ k ih =>
    calc #(S.U (k + 1)) = #(S.U k ∪ S.A k : Set V) := by rw [U]
      _ ≤ #(S.U k) + #(S.A k) := mk_union_le _ _
      _ ≤ 2 ^ S.μ (k + 1) + 2 ^ S.μ (k + 1) :=
          add_le_add (ih.trans (S.two_pow_μ_le (Nat.le_succ k)))
            (by rw [S.mk_A]; exact S.lam_le_two_pow_succ k)
      _ = 2 ^ S.μ (k + 1) := add_eq_self (S.aleph0_le_two_pow_μ _)
def cls (k : ℕ) (a : V) (B : Set V) : Set V := {a' ∈ S.A k | ∀ b ∈ B, S.f a' b = S.f a b}
theorem cls_subset_A (k : ℕ) (a : V) (B : Set V) : S.cls k a B ⊆ S.A k := fun _ h => h.1
def bad (k : ℕ) : Set V :=
  {a ∈ S.A k | ∃ B : Set V, B ⊆ S.U k ∧ #B ≤ S.μ k ∧ #(S.cls k a B) < S.lam k}
def tp (a : V) (B : Set V) : Set (↥B) := {b | S.f a b = true}
theorem cls_eq_fib (k : ℕ) (a : V) (B : Set V) :
    S.cls k a B = {a' ∈ S.A k | S.tp a' B = S.tp a B} := by
  ext a'
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    ext b
    show S.f a' b = true ↔ S.f a b = true
    rw [h2 b b.2]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun b hb => ?_⟩
    have := Set.ext_iff.1 h2 ⟨b, hb⟩
    exact Bool.eq_iff_iff.2 this
theorem mk_small_lt (k : ℕ) (B : Set V) (hB : #B ≤ S.μ k) :
    #({a ∈ S.A k | #(S.cls k a B) < S.lam k} : Set V) < S.lam k := by
  have hsub : {a ∈ S.A k | #(S.cls k a B) < S.lam k} ⊆
      ⋃ (t : {t : Set (↥B) // #({a ∈ S.A k | S.tp a B = t} : Set V) < S.lam k}),
        {a ∈ S.A k | S.tp a B = t.1} := by
    rintro a ⟨ha, hlt⟩
    rw [S.cls_eq_fib] at hlt
    exact Set.mem_iUnion.2 ⟨⟨S.tp a B, hlt⟩, ha, rfl⟩
  refine (mk_le_mk_of_subset hsub).trans_lt
    (mk_iUnion_lt_of_isRegular (S.lam_isRegular k) ?_ _ fun t => t.2)
  calc #{t : Set (↥B) // #({a ∈ S.A k | S.tp a B = t} : Set V) < S.lam k}
      ≤ #(Set (↥B)) := mk_subtype_le _
    _ = 2 ^ #B := mk_set
    _ ≤ 2 ^ S.μ k := power_le_power_left two_ne_zero hB
    _ < S.lam k := S.two_pow_lt_lam k
theorem mk_bad_lt (k : ℕ) : #(S.bad k) < S.lam k := by
  have hsub : S.bad k ⊆ ⋃ (B : {B : Set V // B ⊆ S.U k ∧ #B ≤ S.μ k}),
      {a ∈ S.A k | #(S.cls k a B.1) < S.lam k} := by
    rintro a ⟨ha, B, hBU, hBμ, hlt⟩
    exact Set.mem_iUnion.2 ⟨⟨B, hBU, hBμ⟩, ha, hlt⟩
  refine (mk_le_mk_of_subset hsub).trans_lt
    (mk_iUnion_lt_of_isRegular (S.lam_isRegular k) ?_ _ fun B => S.mk_small_lt k B.1 B.2.2)
  exact (mk_bounded_subsets_le (S.U k) (S.aleph0_le_μ k) (S.mk_U_le k)).trans_lt
    (S.two_pow_lt_lam k)
theorem exists_guide (k : ℕ) : ∃ a, a ∈ S.A k ∧ a ∉ S.bad k := by
  by_contra h
  have hsub : S.A k ⊆ S.bad k := fun a ha => by
    by_contra hb
    exact h ⟨a, ha, hb⟩
  have := (mk_le_mk_of_subset hsub).trans_lt (S.mk_bad_lt k)
  rw [S.mk_A] at this
  exact lt_irrefl _ this
noncomputable def guide (k : ℕ) : V := (S.exists_guide k).choose
theorem guide_mem (k : ℕ) : S.guide k ∈ S.A k := (S.exists_guide k).choose_spec.1
theorem guide_not_bad (k : ℕ) : S.guide k ∉ S.bad k := (S.exists_guide k).choose_spec.2
theorem mk_cls_guide (k : ℕ) (B : Set V) (hBU : B ⊆ S.U k) (hBμ : #B ≤ S.μ k) :
    #(S.cls k (S.guide k) B) = S.lam k := by
  apply le_antisymm
  · exact (mk_le_mk_of_subset (S.cls_subset_A k _ B)).trans_eq (S.mk_A k)
  · by_contra h
    exact S.guide_not_bad k ⟨S.guide_mem k, B, hBU, hBμ, lt_of_not_ge h⟩
structure Basic (k : ℕ) (p : Set V × Set V) : Prop where
  sub : p.1 ∪ p.2 ⊆ S.A k
  mk_le : #(p.1 ∪ p.2 : Set V) ≤ S.μ k
noncomputable def prevU (S : Ctx V) : (k : ℕ) → (∀ i, i < k → Set V × Set V) → Set V
  | 0, _ => ∅
  | k + 1, prev =>
      prevU S k (fun i h => prev i (Nat.lt_succ_of_lt h)) ∪
        ((prev k (Nat.lt_succ_self k)).1 ∪ (prev k (Nat.lt_succ_self k)).2)
theorem mem_prevU {k : ℕ} {prev : ∀ i, i < k → Set V × Set V} {v : V} :
    v ∈ S.prevU k prev ↔ ∃ i, ∃ h : i < k, v ∈ (prev i h).1 ∪ (prev i h).2 := by
  induction k with
  | zero => simp [prevU]
  | succ k ih =>
    simp only [prevU, Set.mem_union, ih]
    constructor
    · rintro (⟨i, hi, hv⟩ | hv)
      · exact ⟨i, Nat.lt_succ_of_lt hi, hv⟩
      · exact ⟨k, Nat.lt_succ_self k, hv⟩
    · rintro ⟨i, hi, hv⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | rfl
      · exact Or.inl ⟨i, hi', hv⟩
      · exact Or.inr hv
theorem mk_prevU_le {k : ℕ} {prev : ∀ i, i < k → Set V × Set V}
    (hprev : ∀ i h, S.Basic i (prev i h)) : #(S.prevU k prev) ≤ S.μ k := by
  induction k with
  | zero => simp [prevU]
  | succ k ih =>
    calc #(S.prevU (k + 1) prev)
        ≤ #(S.prevU k (fun i h => prev i (Nat.lt_succ_of_lt h))) +
            #((prev k (Nat.lt_succ_self k)).1 ∪ (prev k (Nat.lt_succ_self k)).2 : Set V) :=
          mk_union_le _ _
      _ ≤ S.μ (k + 1) + S.μ (k + 1) :=
          add_le_add ((ih (fun i h => hprev i _)).trans (S.μ_mono (Nat.le_succ k)))
            ((hprev k _).mk_le.trans (S.μ_mono (Nat.le_succ k)))
      _ = S.μ (k + 1) := add_eq_self (S.aleph0_le_μ _)
theorem prevU_subset_U {k : ℕ} {prev : ∀ i, i < k → Set V × Set V}
    (hprev : ∀ i h, S.Basic i (prev i h)) : S.prevU k prev ⊆ S.U k := by
  intro v hv
  obtain ⟨i, hi, hvi⟩ := S.mem_prevU.1 hv
  exact S.A_subset_U hi ((hprev i hi).sub hvi)
structure Good (k : ℕ) (prev : ∀ i, i < k → Set V × Set V) (p : Set V × Set V) : Prop where
  sub1 : p.1 ⊆ S.A k
  sub2 : p.2 ⊆ S.A k
  mk1 : #p.1 = S.μ k
  mk2 : #p.2 = S.μ k
  hom1 : Homog S.f false p.1
  hom2 : Homog S.f true p.2
  cls : ∀ a ∈ p.1 ∪ p.2, ∀ b ∈ S.prevU k prev, S.f a b = S.f (S.guide k) b
  same : ∀ a ∈ p.1 ∪ p.2, ∀ a' ∈ p.1 ∪ p.2, ∀ j, S.f a (S.guide j) = S.f a' (S.guide j)
def gtp (a : V) : Set (ULift.{u} ℕ) := {j | S.f a (S.guide j.down) = true}
theorem mk_set_uLift_nat_lt_lam (k : ℕ) : #(Set (ULift.{u} ℕ)) < S.lam k := by
  rw [mk_set, mk_uLift, mk_nat, Cardinal.lift_aleph0]
  exact S.two_pow_aleph0_lt_lam k
theorem exists_blocks (k : ℕ) (prev : ∀ i, i < k → Set V × Set V)
    (hprev : ∀ i h, S.Basic i (prev i h)) : ∃ p, S.Good k prev p ∧ S.Basic k p := by
  have hB1c : #(S.cls k (S.guide k) (S.prevU k prev)) = S.lam k :=
    S.mk_cls_guide k _ (S.prevU_subset_U hprev) (S.mk_prevU_le hprev)
  obtain ⟨t, ht⟩ := exists_fiber_eq_of_isRegular (S.lam_isRegular k) _ hB1c S.gtp
    (S.mk_set_uLift_nat_lt_lam k)
  obtain ⟨B0, B1, hB0, hB1, hB0c, hB1c, hom0, hom1⟩ := S.exists_homog_two k _ ht
  have hB0A : B0 ⊆ S.A k := fun a ha => (hB0 ha).1.1
  have hB1A : B1 ⊆ S.A k := fun a ha => (hB1 ha).1.1
  have hcls : ∀ a ∈ B0 ∪ B1, a ∈ S.cls k (S.guide k) (S.prevU k prev) := by
    rintro a (ha | ha)
    · exact (hB0 ha).1
    · exact (hB1 ha).1
  have htp : ∀ a ∈ B0 ∪ B1, S.gtp a = t := by
    rintro a (ha | ha)
    · exact (hB0 ha).2
    · exact (hB1 ha).2
  refine ⟨(B0, B1), ⟨hB0A, hB1A, hB0c, hB1c, hom0, hom1, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a ha b hb
    exact (hcls a ha).2 b hb
  · intro a ha a' ha' j
    have h := (htp a ha).trans (htp a' ha').symm
    have h' : S.f a (S.guide j) = true ↔ S.f a' (S.guide j) = true := Set.ext_iff.1 h ⟨j⟩
    exact Bool.eq_iff_iff.2 h'
  · exact Set.union_subset hB0A hB1A
  · calc #(B0 ∪ B1 : Set V) ≤ #B0 + #B1 := mk_union_le _ _
      _ = S.μ k + S.μ k := by rw [hB0c, hB1c]
      _ = S.μ k := add_eq_self (S.aleph0_le_μ k)
noncomputable def blocks (S : Ctx V) : (k : ℕ) → {p : Set V × Set V // S.Basic k p}
  | k =>
    ⟨(S.exists_blocks k (fun i _ => (blocks S i).1) (fun i _ => (blocks S i).2)).choose,
      (S.exists_blocks k (fun i _ => (blocks S i).1) (fun i _ => (blocks S i).2)).choose_spec.2⟩
termination_by k => k
noncomputable def B (k : ℕ) : Set V × Set V := (S.blocks k).1
theorem blocks_good (k : ℕ) : S.Good k (fun i _ => S.B i) (S.B k) := by
  unfold B
  rw [blocks]
  exact (S.exists_blocks k (fun i _ => (S.blocks i).1)
    (fun i _ => (S.blocks i).2)).choose_spec.1
noncomputable def Bu (k : ℕ) : Set V := (S.B k).1 ∪ (S.B k).2
noncomputable def pick (i : ℕ) : V :=
  (nonempty_of_mk_eq (S.blocks_good i).mk1 (S.aleph0_le_μ i)).choose
noncomputable def g (i j : ℕ) : Bool := S.f (S.pick i) (S.guide j)
noncomputable def part (δ : Bool) (k : ℕ) : Set V := bif δ then (S.B k).2 else (S.B k).1
end Ctx
end Erdos1219


