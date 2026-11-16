-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptCard
-- name    : IntMul_Kappa_R8_Data_BitOppbankNDptCard
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:06:05.576028+00:00
-- url     : https://prove2.me/theorems/33ea77b3-0feb-4bec-a4ac-a216b3b2aedf
-- title:
--   ND–PT Le helper pack: triangle point-sets and bfF-of-orthTL on published Pnd
-- statement:
--   # ND–PT Le helpers, triangle-card pack
--
--   Identifies the NetFB point-set of triangle $T$ with its three vertices, and proves that a bit of $\mathrm{orthTL}(T)$ corresponds to a triangle sharing exactly one vertex with $T$, hence $\mathrm{bf}(t_v^Q(i),x_v(T))=0$. Published Pnd only (no PndFix). Depends on the `NDptBits` pack.
-- source:
--   R8 BitOppbank FormalOK published Pnd nest_Le_ND_NDpt helper pack (triangle cards).

-- NDpt helper pack (published Pnd only; no PndFix).
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptBits
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open Matrix
open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.MoveFacts2
open IntMul.Kappa.R8.Bit.Oppbank.SupG
open IntMul.Kappa.R8.Bit.Oppbank.NDptBits
namespace IntMul.Kappa.R8.Bit.Oppbank.NDptCard

theorem and_le_right' (a b : ℕ) : a &&& b ≤ b := Nat.and_le_right

theorem or_le_left (a b : ℕ) : a ≤ a ||| b := by
  have hbits : ∀ i, a.testBit i = true → (a ||| b).testBit i = true := by
    intro i hi; simp [Nat.testBit_or, hi]
  have heq : a &&& (a ||| b) = a := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp [Nat.testBit_and, Nat.testBit_or]
    cases h : a.testBit i <;> simp
  simpa [heq] using (and_le_right' a (a ||| b))

theorem pts_lt_23 {T : ℕ} (hT : T < 1771) :
    ptsL T 0 < 23 ∧ ptsL T 1 < 23 ∧ ptsL T 2 < 23 := by
  have htri : ProjB.tri T < 2 ^ 23 := (NetFB.tri_spec hT).1
  have hle (k : ℕ) (hk : (1 : ℕ) <<< ptsL T k ≤ ProjB.tri T) : ptsL T k < 23 := by
    have : 2 ^ ptsL T k < 2 ^ 23 := by
      have := lt_of_le_of_lt hk htri
      simpa [Nat.shiftLeft_eq, Nat.one_mul] using this
    exact (Nat.pow_lt_pow_iff_right (by decide : (1 : ℕ) < 2)).1 this
  refine ⟨hle 0 ?_, hle 1 ?_, hle 2 ?_⟩
  · simp only [ProjB.tri, ptsL_eq]
    exact le_trans (or_le_left _ _) (or_le_left _ _)
  · simp only [ProjB.tri, ptsL_eq]
    have : (1 : ℕ) <<< ptsL T 1 ≤ (1 <<< ptsL T 0) ||| (1 <<< ptsL T 1) := by
      rw [Nat.or_comm]; exact or_le_left _ _
    exact le_trans this (or_le_left _ _)
  · simp only [ProjB.tri, ptsL_eq]
    have : (1 : ℕ) <<< ptsL T 2 ≤
        ((1 <<< ptsL T 0) ||| (1 <<< ptsL T 1)) ||| (1 <<< ptsL T 2) := by
      rw [Nat.or_comm]; exact or_le_left _ _
    exact this

theorem mem_F_tri (T : ℕ) (p : Fin 23) :
    p ∈ NetFB.F (ProjB.tri T) ↔
      p.val = ptsL T 0 ∨ p.val = ptsL T 1 ∨ p.val = ptsL T 2 := by
  have hbit (k : ℕ) : ((1 : ℕ) <<< k).testBit p.val = true ↔ p.val = k :=
    testBit_one_shl k p.val
  have htri : ProjB.tri T =
      ((1 <<< ptsL T 0) ||| (1 <<< ptsL T 1)) ||| (1 <<< ptsL T 2) := by
    simp only [ProjB.tri, ptsL_eq]
    rfl
  simp only [NetFB.F, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [htri, Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true,
    hbit, hbit, hbit]
  rw [or_assoc]

theorem F_eq_pts {T : ℕ} (hT : T < 1771) :
    NetFB.F (ProjB.tri T) =
      ({⟨ptsL T 0, (pts_lt_23 hT).1⟩, ⟨ptsL T 1, (pts_lt_23 hT).2.1⟩,
        ⟨ptsL T 2, (pts_lt_23 hT).2.2⟩} : Finset (Fin 23)) := by
  ext p
  constructor
  · intro hp
    have h := (mem_F_tri T p).mp hp
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases h with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  · intro hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    apply (mem_F_tri T p).mpr
    rcases hp with h | h | h
    · exact Or.inl (by cases h; rfl)
    · exact Or.inr (Or.inl (by cases h; rfl))
    · exact Or.inr (Or.inr (by cases h; rfl))

theorem card_insert_le_two (a b : Fin 23) :
    ({a, b} : Finset (Fin 23)).card ≤ 2 :=
  le_trans (Finset.card_insert_le _ _) (by simp [Finset.card_singleton])

theorem pts_distinct {T : ℕ} (hT : T < 1771) :
    ptsL T 0 ≠ ptsL T 1 ∧ ptsL T 0 ≠ ptsL T 2 ∧ ptsL T 1 ≠ ptsL T 2 := by
  have hcard : (NetFB.F (ProjB.tri T)).card = 3 := (NetFB.tri_spec hT).2
  rw [F_eq_pts hT] at hcard
  set p0 : Fin 23 := ⟨ptsL T 0, (pts_lt_23 hT).1⟩
  set p1 : Fin 23 := ⟨ptsL T 1, (pts_lt_23 hT).2.1⟩
  set p2 : Fin 23 := ⟨ptsL T 2, (pts_lt_23 hT).2.2⟩
  change ({p0, p1, p2} : Finset (Fin 23)).card = 3 at hcard
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hp : p0 = p1 := Fin.ext h
    have : ({p0, p1, p2} : Finset (Fin 23)).card ≤ 2 := by
      simpa [hp] using card_insert_le_two p0 p2
    omega
  · intro h
    have hp : p0 = p2 := Fin.ext h
    have : ({p0, p1, p2} : Finset (Fin 23)).card ≤ 2 := by
      have heq : ({p0, p1, p2} : Finset (Fin 23)) = {p0, p1} := by
        rw [show p2 = p0 from hp.symm]
        ext x
        simp [Finset.mem_insert, Finset.mem_singleton, eq_comm]
        try tauto
      simpa [heq] using card_insert_le_two p0 p1
    omega
  · intro h
    have hp : p1 = p2 := Fin.ext h
    have : ({p0, p1, p2} : Finset (Fin 23)).card ≤ 2 := by
      have heq : ({p0, p1, p2} : Finset (Fin 23)) = {p0, p1} := by
        rw [show p2 = p1 from hp.symm]
        ext x
        simp [Finset.mem_insert, Finset.mem_singleton, eq_comm]
        try tauto
      simpa [heq] using card_insert_le_two p0 p1
    omega

theorem filter_three_one {p0 p1 p2 : Fin 23}
    (hne : p0 ≠ p1 ∧ p0 ≠ p2 ∧ p1 ≠ p2)
    {s : Finset (Fin 23)} (h0 : p0 ∈ s) (n1 : p1 ∉ s) (n2 : p2 ∉ s) :
    ({p0, p1, p2} : Finset (Fin 23)).filter (fun p => p ∈ s) = {p0} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hs⟩
    rcases hp with rfl | rfl | rfl
    · rfl
    · exact (n1 hs).elim
    · exact (n2 hs).elim
  · rintro rfl
    exact ⟨Or.inl rfl, h0⟩

theorem card_inter_eq_one {T i : ℕ} (hT : T < 1771) (hi : i < 1771)
    (horth : (Pnd.orthTL T).testBit i = true) :
    (NetFB.F (ProjB.tri i) ∩ NetFB.F (ProjB.tri T)).card = 1 := by
  have hS (c : ℕ) : (Pnd.starL c).testBit i = true ↔ starP c i :=
    (mem_starL c i).trans ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩
  have hmem := (mem_orthTL T i).mp horth
  have hfalse (c : ℕ) : (Pnd.starL c).testBit i = false ↔ ¬ starP c i := by
    rw [← Bool.not_eq_true, (hS c).not]
  have h1 :
      starP (ptsL T 0) i ∧ ¬ starP (ptsL T 1) i ∧ ¬ starP (ptsL T 2) i ∨
      starP (ptsL T 1) i ∧ ¬ starP (ptsL T 0) i ∧ ¬ starP (ptsL T 2) i ∨
      starP (ptsL T 2) i ∧ ¬ starP (ptsL T 0) i ∧ ¬ starP (ptsL T 1) i := by
    simpa [hS, hfalse] using hmem
  have hinter :
      NetFB.F (ProjB.tri i) ∩ NetFB.F (ProjB.tri T) =
        (NetFB.F (ProjB.tri T)).filter (fun p => p ∈ NetFB.F (ProjB.tri i)) := by
    ext p; simp [Finset.mem_inter, Finset.mem_filter, and_comm]
  have hFI (p : Fin 23) : p ∈ NetFB.F (ProjB.tri i) ↔ starP p.val i := by
    rw [mem_F_tri]
    simp only [starP, eq_comm]
  have ⟨hne01, hne02, hne12⟩ := pts_distinct hT
  rw [hinter, F_eq_pts hT]
  set p0 : Fin 23 := ⟨ptsL T 0, (pts_lt_23 hT).1⟩
  set p1 : Fin 23 := ⟨ptsL T 1, (pts_lt_23 hT).2.1⟩
  set p2 : Fin 23 := ⟨ptsL T 2, (pts_lt_23 hT).2.2⟩
  have hneP : p0 ≠ p1 ∧ p0 ≠ p2 ∧ p1 ≠ p2 :=
    ⟨fun h => hne01 (congrArg Fin.val h), fun h => hne02 (congrArg Fin.val h),
      fun h => hne12 (congrArg Fin.val h)⟩
  have hp0 : starP p0.val i ↔ starP (ptsL T 0) i := Iff.rfl
  have hp1 : starP p1.val i ↔ starP (ptsL T 1) i := Iff.rfl
  have hp2 : starP p2.val i ↔ starP (ptsL T 2) i := Iff.rfl
  rcases h1 with ⟨hs0, n1, n2⟩ | ⟨hs1, n0, n2⟩ | ⟨hs2, n0, n1⟩
  · have : ({p0, p1, p2} : Finset (Fin 23)).filter
        (fun p => p ∈ NetFB.F (ProjB.tri i)) = {p0} :=
      filter_three_one hneP (by exact (hFI p0).mpr hs0)
        (fun h => n1 ((hFI p1).mp h)) (fun h => n2 ((hFI p2).mp h))
    simp [this]
  · have hneP' : p1 ≠ p0 ∧ p1 ≠ p2 ∧ p0 ≠ p2 :=
      ⟨hneP.1.symm, hneP.2.2, hneP.2.1⟩
    have hswap : ({p0, p1, p2} : Finset (Fin 23)) = {p1, p0, p2} := by
      ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
    have : ({p0, p1, p2} : Finset (Fin 23)).filter
        (fun p => p ∈ NetFB.F (ProjB.tri i)) = {p1} := by
      rw [hswap]
      exact filter_three_one hneP' (by exact (hFI p1).mpr hs1)
        (fun h => n0 ((hFI p0).mp h)) (fun h => n2 ((hFI p2).mp h))
    simp [this]
  · have hneP' : p2 ≠ p0 ∧ p2 ≠ p1 ∧ p0 ≠ p1 :=
      ⟨hneP.2.1.symm, hneP.2.2.symm, hneP.1⟩
    have hswap : ({p0, p1, p2} : Finset (Fin 23)) = {p2, p0, p1} := by
      ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
    have : ({p0, p1, p2} : Finset (Fin 23)).filter
        (fun p => p ∈ NetFB.F (ProjB.tri i)) = {p2} := by
      rw [hswap]
      exact filter_three_one hneP' (by exact (hFI p2).mpr hs2)
        (fun h => n0 ((hFI p0).mp h)) (fun h => n1 ((hFI p1).mp h))
    simp [this]

theorem bfF_of_orthTL {T i : ℕ} (hT : T < 1771) (hi : i < 1771)
    (horth : (Pnd.orthTL T).testBit i = true) : bfF (tvQ i) (xv T) = 0 := by
  have : xv T = tvQ T := rfl
  rw [this, bf_tvQ' hi hT, card_inter_eq_one hT hi horth]; norm_num

end IntMul.Kappa.R8.Bit.Oppbank.NDptCard


