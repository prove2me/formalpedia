-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
-- name    : IntMul_Kappa_R8_Data_BitOppbankBlock0CoreACopy
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-11-15T17:09:14.462666+00:00
-- url     : https://prove2.me/theorems/f7bf5483-684f-47d9-824c-9004b42bc710
-- title:
--   Block-0 initial state, copy-out instructions, and MovesV append
-- statement:
--   # Block-0 copy-out generators
--
--   Abstract append and fold lemmas for the generator `genF`, together with the initial labeling `initR` and the copy-out instruction sequence `copyoND` that writes each source code `cND t` onto the corresponding auxiliary wire. The pack also records that every instruction code in the concrete prefix `preF` is zero, and that `MovesV` is preserved when `copyoND` is appended to `preF`.
--
--   Depends on the published `Block0CoreAData` and `Block0CoreABits` packs. Prefix / block-0 helper only; not a full-word W1F certificate.
--
--   ## Formalization Note
--
--   Lean identifiers: `initR`, `copyoND`, `genF_append`, `MovesV_copyoND_from`, `MovesV_preF_copyoND_holds`, `genF_append_fst`.
-- source:
--   IntMul Kappa R8 Bit Oppbank FormalOK: CoreA copy split. Prefix / block-0 pack only; not a full-word W1F certificate.

import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankGenF
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankLab1
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankQHNetRecR
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreAData
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankBlock0CoreABits
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
Block-0 `initR`, `copyoND`, and abstract `MovesV` append lemmas through `MovesV_preF_copyoND_holds`.
Prefix / block-0 helper only; not a full-word W1F certificate.
-/

open IntMul.Kappa.R8.Bit.Oppbank
open IntMul.Kappa.R8.Bit.Oppbank.Gen (genF genStepF mvF)
open IntMul.Kappa.R8.Bit.Oppbank.Lab (ValidOn MovesV)
open IntMul.Kappa.R8.Bit.Oppbank.Pnd (nestOK argRel isND)
open IntMul.Kappa.R8.Bit.Oppbank.QHNetRecR

def initR (w : ℕ) : ℕ :=
  if w < v then cND w
  else if wAuxEnd ≤ w ∧ w < NL then cND (retN (w - wAuxEnd))
  else 0

theorem nestOK_of_le1 {o c : ℕ} (h : o ≤ 1 ∨ c ≤ 1) : nestOK o c = true := by
  unfold nestOK
  cases h with
  | inl ho =>
    have : Nat.ble o 1 = true := Nat.ble_eq.mpr ho
    simp [this]
  | inr hc =>
    have : Nat.ble c 1 = true := Nat.ble_eq.mpr hc
    simp [this]

theorem foldl_genStepF_acc :
    ∀ (W : List (ℕ × List ℕ × List (ℕ × ℕ))) (f : ℕ → ℕ)
      (acc : List (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))),
    W.foldl genStepF (f, acc) =
      ((W.foldl genStepF (f, [])).1, (W.foldl genStepF (f, [])).2 ++ acc)
  | [], f, acc => by simp [List.foldl]
  | i :: W, f, acc => by
    simp only [List.foldl_cons, genStepF]
    rw [foldl_genStepF_acc W _ ((i.1, _, i.2.2) :: acc),
        foldl_genStepF_acc W _ [(i.1, _, i.2.2)]]
    simp

theorem genF_append (f : ℕ → ℕ)
    (W W' : List (ℕ × List ℕ × List (ℕ × ℕ))) :
    genF f (W ++ W') =
      ((genF (genF f W).1 W').1, (genF f W).2 ++ (genF (genF f W).1 W').2) := by
  simp only [genF, List.foldl_append]
  rw [foldl_genStepF_acc W' _ (W.foldl genStepF (f, [])).2]
  simp

theorem MovesV_append {cs cs' : List (ℕ × List (ℕ × ℕ) × List (ℕ × ℕ))} :
    MovesV (cs ++ cs') ↔ MovesV cs ∧ MovesV cs' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro ch hc mv hmv; exact h ch (List.mem_append.2 (Or.inl hc)) mv hmv
    · intro ch hc mv hmv; exact h ch (List.mem_append.2 (Or.inr hc)) mv hmv
  · intro ⟨h1, h2⟩ ch hc mv hmv
    rcases List.mem_append.1 hc with h | h
    · exact h1 ch h mv hmv
    · exact h2 ch h mv hmv

theorem foldl_mvF_inv (c : ℕ) (ws : List ℕ) (f₀ f : ℕ → ℕ)
    (acc : List (ℕ × ℕ))
    (hf : ∀ x, f x = f₀ x ∨ f x = c)
    (hacc : ∀ mv ∈ acc, mv.2 = f₀ mv.1) :
    (∀ x, (ws.foldl (mvF c) (f, acc)).1 x = f₀ x ∨
      (ws.foldl (mvF c) (f, acc)).1 x = c) ∧
    (∀ mv ∈ (ws.foldl (mvF c) (f, acc)).2, mv.2 = f₀ mv.1) := by
  induction ws generalizing f acc with
  | nil =>
    exact ⟨hf, hacc⟩
  | cons w ws ih =>
    simp only [List.foldl_cons]
    by_cases hfw : f w = c
    · have hmv : mvF c (f, acc) w = (f, acc) := by simp [mvF, hfw]
      rw [hmv]
      exact ih f acc hf hacc
    · have hmv : mvF c (f, acc) w = (fun x => if x = w then c else f x, (w, f w) :: acc) := by
        simp [mvF, hfw]
      rw [hmv]
      refine ih (fun x => if x = w then c else f x) ((w, f w) :: acc) ?_ ?_
      · intro x
        by_cases hx : x = w
        · subst hx; simp
        · simp [hx]; exact hf x
      · intro mv hmv
        rcases List.mem_cons.1 hmv with h | h
        · subst h
          have hx := hf w
          exact hx.resolve_right hfw
        · exact hacc mv h

theorem foldl_mvF_old (c : ℕ) (ws : List ℕ) (f : ℕ → ℕ) :
    (∀ mv ∈ (ws.foldl (mvF c) (f, [])).2, mv.2 = f mv.1) ∧
      (∀ x, (ws.foldl (mvF c) (f, [])).1 x = f x ∨
        (ws.foldl (mvF c) (f, [])).1 x = c) := by
  have := foldl_mvF_inv c ws f f [] (fun _ => Or.inl rfl) (fun _ h => by cases h)
  exact ⟨this.2, this.1⟩

theorem foldl_mvF_bound (c : ℕ) (hc : c < SupG.codeBound)
    (ws : List ℕ) (f : ℕ → ℕ) (hf : ∀ x, f x < SupG.codeBound) :
    ∀ x, (ws.foldl (mvF c) (f, [])).1 x < SupG.codeBound := by
  intro x
  have := (foldl_mvF_old c ws f).2 x
  cases this with
  | inl h => rw [h]; exact hf x
  | inr h => rw [h]; exact hc

theorem genF_codes_le1 (W : List (ℕ × List ℕ × List (ℕ × ℕ))) (f : ℕ → ℕ)
    (hW : ∀ i ∈ W, i.1 ≤ 1) (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f W).2 ∧ ∀ x, (genF f W).1 x < SupG.codeBound := by
  induction W generalizing f with
  | nil =>
    constructor
    · intro ch hc; cases hc
    · intro x; simpa [genF] using hf x
  | cons i W ih =>
    have hi : i.1 ≤ 1 := hW i (List.mem_cons.2 (Or.inl rfl))
    have hiB : i.1 < SupG.codeBound := by
      have : SupG.codeBound = 64251 := SupG.codeBound_eq
      omega
    have hW' : ∀ j ∈ W, j.1 ≤ 1 := fun j hj => hW j (List.mem_cons_of_mem _ hj)
    -- genF f (i::W) = genF (step i f) W, with one new chunk
    have hstep :
        genF f (i :: W) =
          ((genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).1,
            (i.1, (i.2.1.foldl (mvF i.1) (f, [])).2.reverse, i.2.2) ::
              (genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).2) := by
      have h := genF_append f [i] W
      simp only [List.singleton_append] at h
      rw [h]
      simp [genF, genStepF]
    rw [hstep]
    have hf' : ∀ x, (i.2.1.foldl (mvF i.1) (f, [])).1 x < SupG.codeBound :=
      foldl_mvF_bound i.1 hiB i.2.1 f hf
    have ⟨hMV, hB⟩ := ih (i.2.1.foldl (mvF i.1) (f, [])).1 hW' hf'
    constructor
    · intro ch hch mv hmv
      rcases List.mem_cons.1 hch with rfl | hch
      · have hold := (foldl_mvF_old i.1 i.2.1 f).1
        have : mv ∈ (i.2.1.foldl (mvF i.1) (f, [])).2 := by
          simpa using (List.mem_reverse.1 (by
            -- ch.2.1 is the reversed move list
            change mv ∈ (i.2.1.foldl (mvF i.1) (f, [])).2.reverse at hmv
            exact hmv))
        have hold' : mv.2 = f mv.1 := hold mv this
        refine ⟨nestOK_of_le1 (Or.inr hi), ?_, ?_⟩
        · rw [hold']; exact hf mv.1
        · exact hiB
      · exact hMV ch hch mv hmv
    · exact hB

theorem preF_codes_le1 : ∀ i ∈ preF, i.1 ≤ 1 := by
  intro i hi
  simp only [preF] at hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · -- mixF fun _ => cLOW
        obtain ⟨r, _, rfl⟩ := List.mem_map.1 hi
        simp [mk, cLOW]
      · -- scat rdS fun _ => cLOW
        obtain ⟨T, _, rfl⟩ := List.mem_map.1 hi
        simp [mk, cLOW]
    · -- injo fun _ => cLOW
      obtain ⟨T, _, rfl⟩ := List.mem_map.1 hi
      simp [mk, cLOW]
  · -- mixI fun _ => cLOW
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hi
    simp [mk, cLOW]

theorem retN_lt_nNodes {c : ℕ} (hc : c < h) : retN c < 62478 := by
  have : h = 23 := rfl
  rw [this] at hc
  interval_cases c <;> decide

theorem initR_lt (w : ℕ) : initR w < SupG.codeBound := by
  unfold initR
  split_ifs with h1 h2
  · -- cND w, w < v
    have hv : v = 1771 := rfl
    have : cND w = 1773 + w := rfl
    have : SupG.codeBound = 64251 := SupG.codeBound_eq
    omega
  · have ⟨hw1, hw2⟩ := h2
    have hNL : NL = wAuxEnd + h := NL_eq
    have hc : w - wAuxEnd < h := by omega
    have hr := retN_lt_nNodes hc
    have : cND (retN (w - wAuxEnd)) = 1773 + retN (w - wAuxEnd) := rfl
    have : SupG.codeBound = 64251 := SupG.codeBound_eq
    omega
  · have : SupG.codeBound = 64251 := SupG.codeBound_eq
    omega

theorem initR_ValidOn : ValidOn initR := fun _ _ => initR_lt _


theorem srcS_get {t : ℕ} (ht : t < v) :
    srcS t = srcS_vals[t]'(by rw [srcS_vals_len]; have : v = 1771 := rfl; omega) := by
  have htL : t < srcS_vals.length := by
    rw [srcS_vals_len]; have : v = 1771 := rfl; omega
  have hidx : t < ((List.range v).map srcS).length := by
    simpa [srcS_map_eq] using htL
  have heql : srcS_vals[t]'htL = ((List.range v).map srcS)[t]'hidx := by
    simp [srcS_map_eq]
  rw [heql, List.getElem_map, List.getElem_range]

theorem srcS_lt {t : ℕ} (ht : t < v) : srcS t < 11091 := by
  have htL : t < srcS_vals.length := by
    rw [srcS_vals_len]; have : v = 1771 := rfl; omega
  have hmem : srcS_vals[t]'htL ∈ srcS_vals := List.getElem_mem _
  have : srcS t = srcS_vals[t]'htL := srcS_get ht
  rw [this]
  exact srcS_vals_lt_11091 _ hmem

theorem cND_eq (t : ℕ) : cND t = 1773 + t := rfl
theorem cND_ne_zero (t : ℕ) : cND t ≠ 0 := by
  rw [cND_eq]; omega
theorem cND_lt_bound {t : ℕ} (ht : t < v) : cND t < SupG.codeBound := by
  have : v = 1771 := rfl
  have : cND t = 1773 + t := rfl
  have : SupG.codeBound = 64251 := SupG.codeBound_eq
  omega

theorem wEnt_v : v < wEnt := by decide
theorem wS_ge (q : ℕ) : wEnt ≤ wS q := Nat.le_add_right _ _
theorem wX_eq (t : ℕ) : wX t = t := rfl
theorem wS_eq (q : ℕ) : wS q = wEnt + q := rfl

theorem wX_lt_wEnt {t : ℕ} (ht : t < v) : wX t < wEnt := by
  rw [wX_eq]
  exact Nat.lt_trans ht wEnt_v

theorem wS_ne_wX (q t : ℕ) (ht : t < v) : wS q ≠ wX t := by
  intro h
  exact (Nat.not_le_of_gt (wX_lt_wEnt ht)) (h ▸ wS_ge q)

theorem wS_srcS_lt_wAuxEnd {t : ℕ} (ht : t < v) : wS (srcS t) < wAuxEnd := by
  have : wS (srcS t) = wEnt + srcS t := rfl
  have hs : srcS t < 11091 := srcS_lt ht
  have : wEnt = 3542 := rfl
  have : wAuxEnd = 31336 := rfl
  omega

theorem initR_wS (q : ℕ) (hq : wS q < wAuxEnd) : initR (wS q) = 0 := by
  unfold initR
  have h1 : ¬ wS q < v := Nat.not_lt.mpr (le_trans (le_of_lt wEnt_v) (wS_ge q))
  have h2 : ¬ (wAuxEnd ≤ wS q ∧ wS q < NL) := by
    intro h
    exact Nat.not_le_of_gt hq h.1
  rw [if_neg h1, if_neg h2]

theorem initR_wX {t : ℕ} (ht : t < v) : initR (wX t) = cND t := by
  have hx : wX t = t := wX_eq t
  have ht' : wX t < v := by rwa [hx]
  unfold initR
  rw [if_pos ht', hx]

def copyoAt (t : ℕ) : LInstr := mk (cND t) [(wS (srcS t), wX t)]

theorem copyoND_eq : copyoND = (List.range v).map copyoAt := by
  unfold copyoND copyo copyoAt
  rfl
theorem copyoAt_code (t : ℕ) : (copyoAt t).1 = cND t := rfl
theorem copyoAt_touch (t : ℕ) : (copyoAt t).2.1 = [wS (srcS t), wX t] := rfl

theorem preF_codes_eq_zero : ∀ i ∈ preF, i.1 = 0 := by
  intro i hi
  simp only [preF] at hi
  rcases List.mem_append.1 hi with hi | hi
  · rcases List.mem_append.1 hi with hi | hi
    · rcases List.mem_append.1 hi with hi | hi
      · obtain ⟨r, _, rfl⟩ := List.mem_map.1 hi
        simp [mk, cLOW]
      · obtain ⟨T, _, rfl⟩ := List.mem_map.1 hi
        simp [mk, cLOW]
    · obtain ⟨T, _, rfl⟩ := List.mem_map.1 hi
      simp [mk, cLOW]
  · obtain ⟨r, _, rfl⟩ := List.mem_map.1 hi
    simp [mk, cLOW]

theorem genF_singleton (f : ℕ → ℕ) (i : LInstr) :
    genF f [i] =
      ((i.2.1.foldl (mvF i.1) (f, [])).1,
        [(i.1, (i.2.1.foldl (mvF i.1) (f, [])).2.reverse, i.2.2)]) := by
  simp [genF, genStepF]

theorem genF_state_of_zero (W : List LInstr) (f : ℕ → ℕ)
    (hW : ∀ i ∈ W, i.1 = 0) :
    ∀ x, (genF f W).1 x = f x ∨ (genF f W).1 x = 0 := by
  induction W generalizing f with
  | nil =>
    intro x
    simp [genF]
  | cons i W ih =>
    have hi : i.1 = 0 := hW i (List.mem_cons.2 (Or.inl rfl))
    have hW' : ∀ j ∈ W, j.1 = 0 := fun j hj => hW j (List.mem_cons_of_mem _ hj)
    have hstep : (genF f (i :: W)).1 =
        (genF (i.2.1.foldl (mvF i.1) (f, [])).1 W).1 := by
      have h := genF_append f [i] W
      simp only [List.singleton_append] at h
      rw [h]
      simp [genF_singleton]
    intro x
    rw [hstep, hi]
    have hf' := (foldl_mvF_old 0 i.2.1 f).2
    rcases ih (i.2.1.foldl (mvF 0) (f, [])).1 hW' x with hx | hx
    · rw [hx]; exact hf' x
    · exact Or.inr hx

theorem preF_state (x : ℕ) :
    (genF initR preF).1 x = initR x ∨ (genF initR preF).1 x = 0 :=
  genF_state_of_zero preF initR preF_codes_eq_zero x

theorem preF_wS (t : ℕ) (ht : t < v) :
    (genF initR preF).1 (wS (srcS t)) = 0 := by
  have h := preF_state (wS (srcS t))
  have h0 : initR (wS (srcS t)) = 0 :=
    initR_wS (srcS t) (wS_srcS_lt_wAuxEnd ht)
  rcases h with h | h
  · rwa [h0] at h
  · exact h

theorem preF_wX (t : ℕ) (ht : t < v) :
    (genF initR preF).1 (wX t) = 0 ∨ (genF initR preF).1 (wX t) = cND t := by
  have h := preF_state (wX t)
  have hx : initR (wX t) = cND t := initR_wX ht
  rcases h with h | h
  · rw [h, hx]; exact Or.inr rfl
  · exact Or.inl h

theorem foldl_mvF_copyoAt (f : ℕ → ℕ) (t : ℕ) (ht : t < v)
    (hS : f (wS (srcS t)) = 0)
    (hX : f (wX t) = 0 ∨ f (wX t) = cND t) :
    (∀ mv ∈ ([wS (srcS t), wX t].foldl (mvF (cND t)) (f, [])).2, mv.2 = 0) ∧
    (∀ x, ([wS (srcS t), wX t].foldl (mvF (cND t)) (f, [])).1 x = f x ∨
      ((x = wS (srcS t) ∨ x = wX t) ∧
        ([wS (srcS t), wX t].foldl (mvF (cND t)) (f, [])).1 x = cND t)) := by
  set w1 := wS (srcS t) with hw1
  set w2 := wX t with hw2
  set c := cND t with hc
  have hne : w1 ≠ w2 := wS_ne_wX (srcS t) t ht
  have hc0 : c ≠ 0 := by rw [hc]; exact cND_ne_zero t
  have hf1 : f w1 ≠ c := by
    rw [hS]
    exact hc0.symm
  have hstep1 :
      mvF c (f, []) w1 = (fun x => if x = w1 then c else f x, [(w1, f w1)]) := by
    unfold mvF
    rw [if_neg hf1]
  have hacc1 : ∀ mv ∈ ([(w1, f w1)] : List (ℕ × ℕ)), mv.2 = 0 := by
    intro mv hmv
    simp only [List.mem_singleton] at hmv
    subst mv
    exact hS
  simp only [List.foldl_cons, List.foldl_nil]
  rw [hstep1]
  set f1 := fun x => if x = w1 then c else f x
  have hf1w2 : f1 w2 = f w2 := if_neg (Ne.symm hne)
  by_cases h2c : f w2 = c
  · have hskip : mvF c (f1, [(w1, f w1)]) w2 = (f1, [(w1, f w1)]) := by
      have : f1 w2 = c := by rwa [hf1w2]
      unfold mvF
      rw [if_pos this]
    rw [hskip]
    constructor
    · intro mv hmv
      exact hacc1 mv hmv
    · intro x
      by_cases hx : x = w1
      · subst hx
        refine Or.inr ⟨Or.inl rfl, if_pos rfl⟩
      · refine Or.inl (if_neg hx)
  · have hw2old : f w2 = 0 := hX.resolve_right h2c
    have hwrite :
        mvF c (f1, [(w1, f w1)]) w2 =
          (fun x => if x = w2 then c else f1 x, (w2, f1 w2) :: [(w1, f w1)]) := by
      have : f1 w2 ≠ c := by
        rw [hf1w2]
        exact h2c
      unfold mvF
      rw [if_neg this]
    rw [hwrite]
    constructor
    · intro mv hmv
      rcases List.mem_cons.1 hmv with hmv | hmv
      · subst mv
        rw [hf1w2]
        exact hw2old
      · exact hacc1 mv hmv
    · intro x
      by_cases hx2 : x = w2
      · subst hx2
        refine Or.inr ⟨Or.inr rfl, if_pos rfl⟩
      · by_cases hx1 : x = w1
        · subst hx1
          refine Or.inr ⟨Or.inl rfl, ?_⟩
          change (if w1 = w2 then c else f1 w1) = c
          rw [if_neg hne]
          exact if_pos rfl
        · refine Or.inl ?_
          change (if x = w2 then c else f1 x) = f x
          rw [if_neg hx2]
          change f1 x = f x
          exact if_neg hx1

theorem MovesV_copyoAt (f : ℕ → ℕ) (t : ℕ) (ht : t < v)
    (hS : f (wS (srcS t)) = 0)
    (hX : f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f [copyoAt t]).2 ∧
      (∀ x, (genF f [copyoAt t]).1 x < SupG.codeBound) ∧
      (∀ x, (genF f [copyoAt t]).1 x = f x ∨
        ((x = wS (srcS t) ∨ x = wX t) ∧ (genF f [copyoAt t]).1 x = cND t)) := by
  have hfold := foldl_mvF_copyoAt f t ht hS hX
  have htouch : (copyoAt t).2.1 = [wS (srcS t), wX t] := copyoAt_touch t
  have hcode : (copyoAt t).1 = cND t := copyoAt_code t
  have hgen := genF_singleton f (copyoAt t)
  rw [hgen, htouch, hcode]
  have hcB : cND t < SupG.codeBound := cND_lt_bound ht
  refine ⟨?_, ?_, ?_⟩
  · intro ch hch mv hmv
    simp only [List.mem_singleton] at hch
    subst ch
    have hmv' : mv ∈ ([wS (srcS t), wX t].foldl (mvF (cND t)) (f, [])).2 := by
      simpa using (List.mem_reverse.1 hmv)
    have hold : mv.2 = 0 := hfold.1 mv hmv'
    refine ⟨nestOK_of_le1 (Or.inl (by rw [hold]; exact Nat.zero_le 1)), ?_, ?_⟩
    · rw [hold]
      have : SupG.codeBound = 64251 := SupG.codeBound_eq
      omega
    · exact hcB
  · intro x
    rcases hfold.2 x with hx | hx
    · rw [hx]; exact hf x
    · rw [hx.2]; exact hcB
  · exact hfold.2

theorem MovesV_copyo_map (f : ℕ → ℕ) (ts : List ℕ)
    (hnd : ts.Nodup)
    (htv : ∀ t ∈ ts, t < v)
    (hS : ∀ t ∈ ts, f (wS (srcS t)) = 0)
    (hX : ∀ t ∈ ts, f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f (ts.map copyoAt)).2 ∧
      ∀ x, (genF f (ts.map copyoAt)).1 x < SupG.codeBound := by
  induction ts generalizing f with
  | nil =>
    constructor
    · intro ch hc; cases hc
    · intro x; simpa [genF] using hf x
  | cons t ts ih =>
    have hcons := List.nodup_cons.1 hnd
    have htnin : t ∉ ts := hcons.1
    have hnd' : ts.Nodup := hcons.2
    have ht : t < v := htv t (List.mem_cons.2 (Or.inl rfl))
    have htv' : ∀ t' ∈ ts, t' < v := fun t' ht' => htv t' (List.mem_cons_of_mem _ ht')
    have hone := MovesV_copyoAt f t ht (hS t (List.mem_cons.2 (Or.inl rfl)))
      (hX t (List.mem_cons.2 (Or.inl rfl))) hf
    have happ := genF_append f [copyoAt t] (ts.map copyoAt)
    simp only [List.singleton_append] at happ
    -- (t :: ts).map copyoAt = copyoAt t :: ts.map copyoAt
    have hmap : (t :: ts).map copyoAt = copyoAt t :: ts.map copyoAt := rfl
    rw [hmap, happ]
    -- new state
    set f' := (genF f [copyoAt t]).1
    have hf' : ∀ x, f' x < SupG.codeBound := hone.2.1
    have hinv := hone.2.2
    have hS' : ∀ t' ∈ ts, f' (wS (srcS t')) = 0 := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne_t : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hneS : wS (srcS t') ≠ wS (srcS t) := by
        intro heq
        have heq' : wEnt + srcS t' = wEnt + srcS t := by
          rw [← wS_eq, ← wS_eq, heq]
        exact hne_t (srcS_inj ht'v ht (Nat.add_left_cancel heq'))
      have hneX : wS (srcS t') ≠ wX t := wS_ne_wX (srcS t') t ht
      have hx := hinv (wS (srcS t'))
      rcases hx with hx | hx
      · rw [hx]; exact hS t' (List.mem_cons_of_mem _ ht')
      · rcases hx.1 with hx1 | hx1
        · exact (hneS hx1).elim
        · exact (hneX hx1).elim
    have hX' : ∀ t' ∈ ts, f' (wX t') = 0 ∨ f' (wX t') = cND t' := by
      intro t' ht'
      have ht'v : t' < v := htv' t' ht'
      have hne_t : t' ≠ t := by
        intro heq; subst heq; exact htnin ht'
      have hneX : wX t' ≠ wX t := by
        intro heq
        exact hne_t (by simpa [wX_eq] using heq)
      have hneS : wX t' ≠ wS (srcS t) := (wS_ne_wX (srcS t) t' ht'v).symm
      have hx := hinv (wX t')
      rcases hx with hx | hx
      · rw [hx]; exact hX t' (List.mem_cons_of_mem _ ht')
      · rcases hx.1 with hx1 | hx1
        · exact (hneS hx1).elim
        · exact (hneX hx1).elim
    have ⟨hMVrest, hBrest⟩ := ih f' hnd' htv' hS' hX' hf'
    constructor
    · exact (MovesV_append.2 ⟨hone.1, hMVrest⟩)
    · exact hBrest

theorem MovesV_copyoND_from (f : ℕ → ℕ)
    (hS : ∀ t, t < v → f (wS (srcS t)) = 0)
    (hX : ∀ t, t < v → f (wX t) = 0 ∨ f (wX t) = cND t)
    (hf : ∀ x, f x < SupG.codeBound) :
    MovesV (genF f copyoND).2 ∧
      ∀ x, (genF f copyoND).1 x < SupG.codeBound := by
  have H : ∀ n, n = v →
      MovesV (genF f ((List.range n).map copyoAt)).2 ∧
        ∀ x, (genF f ((List.range n).map copyoAt)).1 x < SupG.codeBound := by
    intro n hn
    refine MovesV_copyo_map f (List.range n) List.nodup_range ?htv ?hS ?hX hf
    · intro t ht
      exact Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn
    · intro t ht
      exact hS t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
    · intro t ht
      exact hX t (Nat.lt_of_lt_of_eq (List.mem_range.mp ht) hn)
  have h := H v rfl
  exact copyoND_eq ▸ h

theorem MovesV_genF_append_of (f : ℕ → ℕ)
    (W W' : List (ℕ × List ℕ × List (ℕ × ℕ)))
    (hW : MovesV (genF f W).2 ∧ ∀ x, (genF f W).1 x < SupG.codeBound)
    (hW' : MovesV (genF (genF f W).1 W').2 ∧
           ∀ x, (genF (genF f W).1 W').1 x < SupG.codeBound) :
    MovesV (genF f (W ++ W')).2 ∧ ValidOn (genF f (W ++ W')).1 := by
  have hsnd := congrArg Prod.snd (genF_append f W W')
  have hfst := congrArg Prod.fst (genF_append f W W')
  refine ⟨?mv, ?vo⟩
  · rw [hsnd]
    exact MovesV_append.2 ⟨hW.1, hW'.1⟩
  · rw [hfst]
    exact fun w _ => hW'.2 w

theorem MovesV_preF_copyoND_holds :
    ValidOn initR ∧
      MovesV (genF initR (preF ++ copyoND)).2 ∧
        ValidOn (genF initR (preF ++ copyoND)).1 := by
  refine ⟨initR_ValidOn, ?_⟩
  have hpre := genF_codes_le1 preF initR preF_codes_le1 (fun _ => initR_lt _)
  have hf1 : ∀ x, (genF initR preF).1 x < SupG.codeBound := hpre.2
  have hcopy :=
    MovesV_copyoND_from (genF initR preF).1
      (fun t ht => preF_wS t ht)
      (fun t ht => preF_wX t ht)
      hf1
  exact MovesV_genF_append_of initR preF copyoND hpre hcopy


/-! Leaf mixFB prefix of `segsH` / `segsR` (1771 leaf recs, no preloads).
Do not unfold `segsR` / `preloadHits`. -/

theorem genF_append_fst (f : ℕ → ℕ)
    (W W' : List (ℕ × List ℕ × List (ℕ × ℕ))) :
    (genF f (W ++ W')).1 = (genF (genF f W).1 W').1 := by
  rw [genF_append]


