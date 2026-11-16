-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNDptBits
-- name    : IntMul_Kappa_R8_Data_BitOppbankNDptBits
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T11:04:11.033455+00:00
-- url     : https://prove2.me/theorems/39383d29-404e-4aaf-b7ef-f0cf5e704dee
-- title:
--   ND–PT Le helper pack: star / exclTL / orthTL membership on published Pnd
-- statement:
--   # ND–PT Le helpers, bit-membership pack
--
--   Transfer lemmas identifying the published `Pnd` copies of $p,t_v^Q,x_v,y_v,\mathrm{bf}$ with their `ProjB`/`NetFB` counterparts, together with bit-membership characterisations of `starL`, `exclTL`, and `orthTL`. These are used to read $\mathrm{orthOK}(n,T)$ as Bilinear-form orthogonality of the generators of $\mathrm{span}S(\mathrm{densSup}_G(n))$ to $x_v(T)$. Published Pnd only (no PndFix).
-- source:
--   R8 BitOppbank FormalOK published Pnd nest_Le_ND_NDpt helper pack (bit membership).

-- NDpt helper pack (published Pnd only; no PndFix).
import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankNetFB
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankMoveFacts2
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankProjB
import Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_AllDensCentred
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
namespace IntMul.Kappa.R8.Bit.Oppbank.NDptBits


theorem ptsL_eq (T k : ℕ) : ptsL T k = ProjB.pts T k := rfl

theorem triL_eq (T : ℕ) : triL T = ProjB.tri T := by
  simp only [triL, ProjB.tri, ptsL_eq]

theorem tvQ_eq (T : ℕ) : tvQ T = ProjB.tvQ T := by
  funext p
  simp only [tvQ, ProjB.tvQ, triL_eq]

theorem xv_eq (T : ℕ) : xv T = ProjB.xv T := by
  simp only [xv, ProjB.xv, tvQ_eq]

theorem yv_eq (T : ℕ) : yv T = ProjB.yv T := by
  funext p
  simp only [yv, ProjB.yv, tvQ_eq]

theorem bfF_eq (u v : V23) : bfF u v = NetFB.bfF u v := rfl

theorem yv_dot' (T : ℕ) (v : V23) : yv T ⬝ᵥ v = bfF (xv T) v / 2 := by
  rw [yv_eq, xv_eq, bfF_eq, NetFB.yv_dot]

theorem xv_ne' {T : ℕ} (hT : T < 1771) : bfF (xv T) (xv T) = 2 := by
  rw [xv_eq, bfF_eq, NetFB.xv_ne hT]

theorem yx' {T : ℕ} (hT : T < 1771) : yv T ⬝ᵥ xv T = 1 := by
  rw [yv_dot', xv_ne' hT]; norm_num

theorem bf_tvQ' {i j : ℕ} (hi : i < 1771) (hj : j < 1771) :
    bfF (tvQ i) (tvQ j) =
      ((NetFB.F (ProjB.tri i) ∩ NetFB.F (ProjB.tri j)).card : ℚ) - 1 := by
  rw [tvQ_eq i, tvQ_eq j, bfF_eq, NetFB.bf_tvQ hi hj]

/-! ## Pnd.starL / Pnd.exclTL / Pnd.orthTL bit membership -/

def starP (c T : ℕ) : Prop :=
  ptsL T 0 = c ∨ ptsL T 1 = c ∨ ptsL T 2 = c

def starFold (c : ℕ) (acc T : ℕ) : ℕ :=
  if ptsL T 0 = c ∨ ptsL T 1 = c ∨ ptsL T 2 = c then acc ||| (1 <<< T) else acc

theorem testBit_one_shl (T i : ℕ) : ((1 : ℕ) <<< T).testBit i = true ↔ i = T := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow, decide_eq_true_iff]
  exact eq_comm

theorem testBit_starFold (c : ℕ) :
    ∀ (l : List ℕ) (acc i : ℕ),
      (List.foldl (starFold c) acc l).testBit i = true ↔
        acc.testBit i = true ∨ ∃ T ∈ l, T = i ∧ starP c T := by
  intro l
  induction l with
  | nil =>
    intro acc i
    simp [List.foldl, starP]
  | cons T l ih =>
    intro acc i
    simp only [List.foldl]
    by_cases hP : ptsL T 0 = c ∨ ptsL T 1 = c ∨ ptsL T 2 = c
    · have hsf : starFold c acc T = acc ||| (1 <<< T) := by simp [starFold, hP]
      rw [hsf]
      have ih' := ih (acc ||| (1 <<< T)) i
      constructor
      · intro h
        rcases ih'.mp h with hacc | ⟨U, hUl, hUi, hUP⟩
        · rw [Nat.testBit_or, Bool.or_eq_true] at hacc
          rcases hacc with hacc | hsh
          · exact Or.inl hacc
          · have : i = T := (testBit_one_shl T i).mp hsh
            exact Or.inr ⟨T, List.mem_cons_self, this.symm ▸ rfl, hP⟩
        · exact Or.inr ⟨U, List.mem_cons_of_mem _ hUl, hUi, hUP⟩
      · intro h
        apply ih'.mpr
        rcases h with hacc | ⟨U, hUl, hUi, hUP⟩
        · exact Or.inl (by rw [Nat.testBit_or, Bool.or_eq_true]; exact Or.inl hacc)
        · rcases List.mem_cons.1 hUl with hUT | hUl'
          · -- hUT : U = T, hUi : U = i, so i = T
            have hbit : ((1 : ℕ) <<< T).testBit i = true :=
              (testBit_one_shl T i).mpr (hUT ▸ hUi).symm
            exact Or.inl (by
              rw [Nat.testBit_or, Bool.or_eq_true]
              exact Or.inr hbit)
          · exact Or.inr ⟨U, hUl', hUi, hUP⟩
    · have hsf : starFold c acc T = acc := by simp [starFold, hP]
      rw [hsf]
      have ih' := ih acc i
      constructor
      · intro h
        rcases ih'.mp h with hacc | ⟨U, hUl, hUi, hUP⟩
        · exact Or.inl hacc
        · exact Or.inr ⟨U, List.mem_cons_of_mem _ hUl, hUi, hUP⟩
      · intro h
        apply ih'.mpr
        rcases h with hacc | ⟨U, hUl, hUi, hUP⟩
        · exact Or.inl hacc
        · rcases List.mem_cons.1 hUl with rfl | hUl'
          · exact (hP (by simpa [starP, hUi] using hUP)).elim
          · exact Or.inr ⟨U, hUl', hUi, hUP⟩

theorem mem_starL (c i : ℕ) :
    (Pnd.starL c).testBit i = true ↔ i < 1771 ∧ starP c i := by
  have hfold :
      List.foldl
        (fun acc T =>
          if ptsL T 0 = c ∨ ptsL T 1 = c ∨ ptsL T 2 = c then acc ||| (1 <<< T) else acc)
        0 (List.range 1771) =
      List.foldl (starFold c) 0 (List.range 1771) := rfl
  constructor
  · intro ht
    have h' :
        (0 : ℕ).testBit i = true ∨ ∃ T ∈ List.range 1771, T = i ∧ starP c T := by
      simpa [Pnd.starL, hfold] using (testBit_starFold c (List.range 1771) 0 i).mp ht
    rcases h' with hacc | ⟨T, hT, hTi, hP⟩
    · simp [Nat.testBit_zero] at hacc
    · exact ⟨by simpa [hTi] using List.mem_range.1 hT, by simpa [hTi] using hP⟩
  · intro ⟨hlt, hP⟩
    have : (List.foldl (starFold c) 0 (List.range 1771)).testBit i = true :=
      (testBit_starFold c (List.range 1771) 0 i).mpr
        (Or.inr ⟨i, List.mem_range.2 hlt, rfl, hP⟩)
    simpa [Pnd.starL, hfold] using this

theorem mem_exclTL (c t1 t2 i : ℕ) :
    (Pnd.exclTL c t1 t2).testBit i = true ↔
      (Pnd.starL c).testBit i = true ∧
        (Pnd.starL t1).testBit i = false ∧ (Pnd.starL t2).testBit i = false := by
  unfold Pnd.exclTL
  change ((Pnd.starL c ^^^ (Pnd.starL c &&& (Pnd.starL t1 ||| Pnd.starL t2)))).testBit i = true ↔
    (Pnd.starL c).testBit i = true ∧
      (Pnd.starL t1).testBit i = false ∧ (Pnd.starL t2).testBit i = false
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_or]
  cases (Pnd.starL c).testBit i <;> cases (Pnd.starL t1).testBit i <;>
    cases (Pnd.starL t2).testBit i <;> simp

theorem mem_orthTL (T i : ℕ) :
    (Pnd.orthTL T).testBit i = true ↔
      ((Pnd.starL (ptsL T 0)).testBit i = true ∧
        (Pnd.starL (ptsL T 1)).testBit i = false ∧
        (Pnd.starL (ptsL T 2)).testBit i = false) ∨
      ((Pnd.starL (ptsL T 1)).testBit i = true ∧
        (Pnd.starL (ptsL T 0)).testBit i = false ∧
        (Pnd.starL (ptsL T 2)).testBit i = false) ∨
      ((Pnd.starL (ptsL T 2)).testBit i = true ∧
        (Pnd.starL (ptsL T 0)).testBit i = false ∧
        (Pnd.starL (ptsL T 1)).testBit i = false) := by
  unfold Pnd.orthTL
  change
    (((exclTL (ptsL T 0) (ptsL T 1) (ptsL T 2)) |||
      (exclTL (ptsL T 1) (ptsL T 0) (ptsL T 2))) |||
      (exclTL (ptsL T 2) (ptsL T 0) (ptsL T 1))).testBit i = true ↔
    ((Pnd.starL (ptsL T 0)).testBit i = true ∧
      (Pnd.starL (ptsL T 1)).testBit i = false ∧
      (Pnd.starL (ptsL T 2)).testBit i = false) ∨
    ((Pnd.starL (ptsL T 1)).testBit i = true ∧
      (Pnd.starL (ptsL T 0)).testBit i = false ∧
      (Pnd.starL (ptsL T 2)).testBit i = false) ∨
    ((Pnd.starL (ptsL T 2)).testBit i = true ∧
      (Pnd.starL (ptsL T 0)).testBit i = false ∧
      (Pnd.starL (ptsL T 1)).testBit i = false)
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true]
  simp only [mem_exclTL]
  rw [or_assoc]

end IntMul.Kappa.R8.Bit.Oppbank.NDptBits


