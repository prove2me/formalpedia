-- Prove2me | solution 1 for AbelianCayleyHDX.explicit_HD_matrices
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T02:07:32.003556+00:00
-- url     : https://prove2.me/submissions/ca2685a6-699a-46dd-91bb-311ab55ded54

import Mathlib
import Definitions.Def_AbelianCayleyHDX_HD
import Definitions.Def_AbelianCayleyHDX_RowIdx
import Definitions.Def_OAIQ053K038
import Definitions.Def_OAIQ053K039
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_AbelianCayleyHDX_encRat
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ReplParity_Vec
import Definitions.Def_AbelianCayleyHDX_kerF2
import Definitions.Def_AbelianCayleyHDX_rowspan
import Theorems.Thm_ShiTM_comp_outputsInTime
import Definitions.Def_AbelianCayleyHDX_encFVec

namespace AbelianCayleyHDX.XH

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F))

/-! ### Codes of field elements -/

def code (x : F) : ℕ := (enc x).val

lemma code_lt (x : F) : code enc x < Fintype.card F := (enc x).2

lemma code_inj {x y : F} (h : code enc x = code enc y) : x = y :=
  enc.injective (Fin.ext h)

/-- Unit index `u < Q - 1` ↦ field code, skipping the code of `0`. -/
def uc (u : ℕ) : ℕ := if u < code enc 0 then u else u + 1

lemma uc_ne (u : ℕ) : uc enc u ≠ code enc 0 := by
  unfold uc; split_ifs <;> omega

lemma uc_lt {u : ℕ} (hu : u < Fintype.card F - 1) : uc enc u < Fintype.card F := by
  have := code_lt enc 0
  unfold uc; split_ifs <;> omega

lemma uc_inj {u v : ℕ} (h : uc enc u = uc enc v) : u = v := by
  unfold uc at h; split_ifs at h <;> omega

lemma card_pos : 0 < Fintype.card F := Fintype.card_pos

noncomputable def toUnit (u : Fin (Fintype.card F - 1)) : Fˣ :=
  Units.mk0 (enc.symm ⟨uc enc u, uc_lt enc u.2⟩) (by
    intro h
    apply uc_ne enc u
    have := congrArg enc h
    rw [Equiv.apply_symm_apply] at this
    rw [code, ← this])

lemma code_toUnit (u : Fin (Fintype.card F - 1)) : code enc (toUnit enc u : F) = uc enc u := by
  simp [toUnit, code]

lemma toUnit_bij : Function.Bijective (toUnit enc) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun u v h => ?_, ?_⟩
  · have := congrArg (fun w : Fˣ => code enc (w : F)) h
    simp only [code_toUnit] at this
    exact Fin.ext (uc_inj enc this)
  · rw [Fintype.card_fin, Fintype.card_units]

noncomputable def unitE : Fin (Fintype.card F - 1) ≃ Fˣ := Equiv.ofBijective _ (toUnit_bij enc)

/-! ### Vectors -/

noncomputable def vecE (t : ℕ) : Fin (Fintype.card F ^ t) ≃ (Fin t → F) :=
  finFunctionFinEquiv.symm.trans (Equiv.arrowCongr (Equiv.refl _) enc.symm)

lemma code_vecE (t : ℕ) (v : Fin (Fintype.card F ^ t)) (k : Fin t) :
    code enc (vecE enc t v k) = v.val / Fintype.card F ^ k.val % Fintype.card F := by
  simp [vecE, code, Equiv.arrowCongr, finFunctionFinEquiv_symm_apply_val]

/-! ### Columns -/

noncomputable def eΩ0 (t : ℕ) : AbelianCayleyHDX.Omega F t ≃ Fin ((Fintype.card F - 1) * Fintype.card F ^ t) :=
  (Equiv.prodCongr (unitE enc).symm (vecE enc t).symm).trans finProdFinEquiv

lemma eΩ0_symm (t : ℕ) (ω : Fin ((Fintype.card F - 1) * Fintype.card F ^ t)) :
    (eΩ0 enc t).symm ω = (unitE enc ω.divNat, vecE enc t ω.modNat) := by
  simp [eΩ0, finProdFinEquiv_symm_apply]

/-! ### Triples -/

noncomputable def eL : {ℓ // ℓ ∈ AbelianCayleyHDX.LF F} ≃ Fin (AbelianCayleyHDX.LF F).card :=
  (AbelianCayleyHDX.LF F).equivFin

/-- The codes of the elements of the triples, in the order of `eL`. -/
noncomputable def LFcodes : List (List ℕ) :=
  (List.finRange (AbelianCayleyHDX.LF F).card).map
    (fun li => ((eL (F := F)).symm li).1.toList.map (code enc))

end AbelianCayleyHDX.XH


namespace AbelianCayleyHDX.XH

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F))
variable {t : ℕ} (D : Finset (AbelianCayleyHDX.PG t F)) (reps : List (Fin t → F))

lemma mem_Dhat' {b : Fin t → F} :
    b ∈ AbelianCayleyHDX.Dhat D ↔ ∃ hb : b ≠ 0, Projectivization.mk F b hb ∈ D := by
  classical
  unfold AbelianCayleyHDX.Dhat
  simp

structure RepsSpec : Prop where
  len : reps.length = D.card
  mem : ∀ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha ∈ D
  cov : ∀ d ∈ D, ∃ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha = d

variable {D reps}

lemma rep_ne (hR : RepsSpec D reps) (i : Fin reps.length) : reps[i] ≠ 0 :=
  (hR.mem _ (List.getElem_mem _)).1

noncomputable def pointOf (hR : RepsSpec D reps) (i : Fin reps.length) : {d // d ∈ D} :=
  ⟨Projectivization.mk F reps[i] (rep_ne hR i), (hR.mem _ (List.getElem_mem _)).2⟩

lemma pointOf_bij (hR : RepsSpec D reps) : Function.Bijective (pointOf hR) := by
  rw [Fintype.bijective_iff_surjective_and_card]
  refine ⟨fun d => ?_, by rw [Fintype.card_fin, Fintype.card_coe, hR.len]⟩
  obtain ⟨a, ha, hne, hd⟩ := hR.cov d.1 d.2
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  exact ⟨⟨i, hi⟩, Subtype.ext hd⟩

noncomputable def phiB (hR : RepsSpec D reps) (x : Fin reps.length × Fin (Fintype.card F - 1)) :
    {b // b ∈ AbelianCayleyHDX.Dhat D} :=
  ⟨((unitE enc x.2 : Fˣ) : F) • reps[x.1], by
    rw [mem_Dhat']
    have hne := rep_ne hR x.1
    have h0 : ((unitE enc x.2 : Fˣ) : F) • reps[x.1] ≠ 0 := smul_ne_zero (Units.ne_zero _) hne
    refine ⟨h0, ?_⟩
    have : Projectivization.mk F (((unitE enc x.2 : Fˣ) : F) • reps[x.1]) h0 =
        Projectivization.mk F reps[x.1] hne :=
      (Projectivization.mk_eq_mk_iff' F _ _ h0 hne).2 ⟨_, rfl⟩
    rw [this]; exact (hR.mem _ (List.getElem_mem _)).2⟩

lemma phiB_bij (hR : RepsSpec D reps) : Function.Bijective (phiB enc hR) := by
  constructor
  · rintro ⟨i, u⟩ ⟨i', u'⟩ h
    have hv := congrArg Subtype.val h
    simp only [phiB] at hv
    have hi := rep_ne hR i
    have hi' := rep_ne hR i'
    have h0 : ((unitE enc u : Fˣ) : F) • reps[i] ≠ 0 := smul_ne_zero (Units.ne_zero _) hi
    have hpt : pointOf hR i = pointOf hR i' := by
      apply Subtype.ext
      simp only [pointOf]
      have e1 : Projectivization.mk F reps[i] hi = Projectivization.mk F
          (((unitE enc u : Fˣ) : F) • reps[i]) h0 :=
        ((Projectivization.mk_eq_mk_iff' F _ _ h0 hi).2 ⟨_, rfl⟩).symm
      have h0' : ((unitE enc u' : Fˣ) : F) • reps[i'] ≠ 0 := hv ▸ h0
      have e2 : Projectivization.mk F reps[i'] hi' = Projectivization.mk F
          (((unitE enc u' : Fˣ) : F) • reps[i']) h0' :=
        ((Projectivization.mk_eq_mk_iff' F _ _ h0' hi').2 ⟨_, rfl⟩).symm
      rw [e1, e2]; congr 1
    have hii := (pointOf_bij hR).1 hpt
    subst hii
    have hu : ((unitE enc u : Fˣ) : F) = ((unitE enc u' : Fˣ) : F) :=
      smul_left_injective F hi hv
    have : u = u' := (unitE enc).injective (Units.ext hu)
    rw [this]
  · rintro ⟨b, hb⟩
    obtain ⟨hb0, hbD⟩ := (mem_Dhat' D).1 hb
    obtain ⟨i, hi⟩ := (pointOf_bij hR).2 ⟨_, hbD⟩
    have hi' := congrArg Subtype.val hi
    simp only [pointOf] at hi'
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff F _ _ hb0 (rep_ne hR i)).1 hi'.symm
    refine ⟨(i, (unitE enc).symm c), Subtype.ext ?_⟩
    simp only [phiB, Equiv.apply_symm_apply]
    rw [← hc, Units.smul_def]

noncomputable def eB (hR : RepsSpec D reps) :
    {b // b ∈ AbelianCayleyHDX.Dhat D} ≃ Fin (reps.length * (Fintype.card F - 1)) :=
  (Equiv.ofBijective _ (phiB_bij enc hR)).symm.trans finProdFinEquiv

noncomputable def eR0 (hR : RepsSpec D reps) :
    AbelianCayleyHDX.RowIdx D ≃
      Fin (reps.length * (Fintype.card F - 1) * (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card)) :=
  (Equiv.prodCongr (eB enc hR) (Equiv.prodCongr (vecE enc t).symm (eL (F := F)))).trans
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)

lemma eR0_symm (hR : RepsSpec D reps) (ρ : Fin (reps.length * (Fintype.card F - 1) *
    (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card))) :
    (eR0 enc hR).symm ρ =
      (phiB enc hR (ρ.divNat.divNat, ρ.divNat.modNat), vecE enc t ρ.modNat.divNat,
        (eL (F := F)).symm ρ.modNat.modNat) := by
  simp [eR0, eB, finProdFinEquiv_symm_apply]

end AbelianCayleyHDX.XH


namespace AbelianCayleyHDX.XH

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F))

/-- Decode a number to a field element. -/
noncomputable def dec (i : ℕ) : F := enc.symm ⟨i % Fintype.card F, Nat.mod_lt _ (card_pos)⟩

lemma dec_code (x : F) : dec enc (code enc x) = x := by
  unfold dec code
  have : (⟨(enc x).val % Fintype.card F, Nat.mod_lt _ card_pos⟩ : Fin (Fintype.card F)) = enc x :=
    Fin.ext (Nat.mod_eq_of_lt (enc x).2)
  rw [this, Equiv.symm_apply_apply]

noncomputable def addT : List (List ℕ) :=
  (List.range (Fintype.card F)).map (fun i => (List.range (Fintype.card F)).map
    (fun j => code enc (dec enc i + dec enc j)))

noncomputable def mulT : List (List ℕ) :=
  (List.range (Fintype.card F)).map (fun i => (List.range (Fintype.card F)).map
    (fun j => code enc (dec enc i * dec enc j)))

def tab (T : List (List ℕ)) (i j : ℕ) : ℕ := (T.getD i []).getD j 0

lemma tab_eq (f : ℕ → ℕ → ℕ) (Q : ℕ) {i j : ℕ} (hi : i < Q) (hj : j < Q) :
    tab ((List.range Q).map (fun i => (List.range Q).map (f i))) i j = f i j := by
  unfold tab
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp [hi, hj]

lemma tab_add (x y : F) : tab (addT enc) (code enc x) (code enc y) = code enc (x + y) := by
  unfold addT
  rw [tab_eq (fun i j => code enc (dec enc i + dec enc j)) _ (code_lt enc x) (code_lt enc y),
    dec_code, dec_code]

lemma tab_mul (x y : F) : tab (mulT enc) (code enc x) (code enc y) = code enc (x * y) := by
  unfold mulT
  rw [tab_eq (fun i j => code enc (dec enc i * dec enc j)) _ (code_lt enc x) (code_lt enc y),
    dec_code, dec_code]

/-- The numeric bit. -/
noncomputable def bitN (ks : List ℕ) (rc : List (List ℕ)) (pows : List ℕ) (Qt ρ ω : ℕ) : Bool :=
  let Q := Fintype.card F
  let L := (AbelianCayleyHDX.LF F).card
  let bi := ρ / (Qt * L)
  let xi := ρ % (Qt * L) / L
  let li := ρ % (Qt * L) % L
  let i := bi / (Q - 1)
  let u := bi % (Q - 1)
  let p := uc enc (ω / Qt)
  let yi := ω % Qt
  (!(((LFcodes enc).getD li []).filter (fun c => decide (c = p))).isEmpty) &&
    (ks.filter (fun k => !(decide (yi / pows.getD k 0 % Q =
      tab (addT enc) (xi / pows.getD k 0 % Q)
        (tab (mulT enc) p (tab (mulT enc) (uc enc u) ((rc.getD i []).getD k 0))))))).isEmpty

variable {t : ℕ} {D : Finset (AbelianCayleyHDX.PG t F)} {reps : List (Fin t → F)}

def repCodes (reps : List (Fin t → F)) : List (List ℕ) := reps.map (fun a => (List.ofFn a).map (code enc))

lemma isEmpty_filter_range (t : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((List.range t).filter (fun k => !(decide (P k)))).isEmpty = decide (∀ k < t, P k) := by
  by_cases h : ∀ k < t, P k
  · rw [decide_eq_true h, List.isEmpty_iff, List.filter_eq_nil_iff]
    intro k hk; simp [h k (List.mem_range.1 hk)]
  · rw [decide_eq_false h]
    push Not at h
    obtain ⟨k, hk, hP⟩ := h
    simp only [Bool.eq_false_iff, ne_eq, List.isEmpty_iff]
    intro h0
    have : k ∈ (List.range t).filter (fun k => !(decide (P k))) :=
      List.mem_filter.2 ⟨List.mem_range.2 hk, by simp [hP]⟩
    rw [h0] at this; simp at this

lemma mem_LFcodes (li : Fin (AbelianCayleyHDX.LF F).card) (p : F) :
    (!(((LFcodes enc).getD li []).filter (fun c => decide (c = code enc p))).isEmpty) =
      decide (p ∈ ((eL (F := F)).symm li).1) := by
  have hg : (LFcodes enc).getD li [] = ((eL (F := F)).symm li).1.toList.map (code enc) := by
    unfold LFcodes
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  rw [hg]
  by_cases hp : p ∈ ((eL (F := F)).symm li).1
  · rw [decide_eq_true hp]
    have : code enc p ∈ (((eL (F := F)).symm li).1.toList.map (code enc)).filter
        (fun c => decide (c = code enc p)) :=
      List.mem_filter.2 ⟨List.mem_map.2 ⟨p, Finset.mem_toList.2 hp, rfl⟩, by simp⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff_exists_mem]
    exact ⟨_, this⟩
  · rw [decide_eq_false hp]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, List.isEmpty_iff, List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
    simp only [decide_eq_true_eq]
    intro hxp
    exact hp (code_inj enc hxp ▸ Finset.mem_toList.1 hx)

theorem bitN_eq (hR : RepsSpec D reps)
    (ρ : Fin (reps.length * (Fintype.card F - 1) * (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card)))
    (ω : Fin ((Fintype.card F - 1) * Fintype.card F ^ t)) (pows : List ℕ)
    (hpows : ∀ k < t, pows.getD k 0 = Fintype.card F ^ k) :
    bitN enc (List.range t) (repCodes enc reps) pows (Fintype.card F ^ t) ρ ω =
      decide (AbelianCayleyHDX.HD D ((eR0 enc hR).symm ρ) ((eΩ0 enc t).symm ω) = 1) := by
  rw [eR0_symm, eΩ0_symm]
  unfold AbelianCayleyHDX.HD bitN
  simp only
  have hval : ∀ c : Prop, [Decidable c] → decide ((if c then (1 : ZMod 2) else 0) = 1) = decide c := by
    intro c _; by_cases hc : c <;> simp [hc]
  rw [hval]
  set p := unitE enc ω.divNat
  have hp : code enc (p : F) = uc enc (ω / Fintype.card F ^ t) := by
    show code enc (toUnit enc ω.divNat : F) = _
    rw [code_toUnit]; simp [Fin.coe_divNat]
  rw [← hp]
  have hL := mem_LFcodes enc (ρ.modNat.modNat) (p : F)
  simp only [Fin.coe_modNat] at hL
  rw [hL, Bool.decide_and]
  congr 1
  rw [isEmpty_filter_range]
  apply decide_eq_decide.2
  set i := ρ.divNat.divNat
  set u := ρ.divNat.modNat
  have hy : ∀ k : Fin t, code enc (vecE enc t ω.modNat k) =
      ω % Fintype.card F ^ t / pows.getD k 0 % Fintype.card F := by
    intro k; rw [code_vecE, hpows k k.2]; simp [Fin.coe_modNat]
  have hx : ∀ k : Fin t, code enc (vecE enc t ρ.modNat.divNat k) =
      ρ % (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card) / (AbelianCayleyHDX.LF F).card /
        pows.getD k 0 % Fintype.card F := by
    intro k; rw [code_vecE, hpows k k.2]; simp [Fin.coe_modNat, Fin.coe_divNat]
  have hb : ∀ k : Fin t, code enc ((phiB enc hR (i, u)).1 k) =
      tab (mulT enc) (uc enc (ρ / (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card) %
        (Fintype.card F - 1))) (((repCodes enc reps).getD (ρ / (Fintype.card F ^ t *
          (AbelianCayleyHDX.LF F).card) / (Fintype.card F - 1)) []).getD k 0) := by
    intro k
    have hi : i.1 = ρ / (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card) / (Fintype.card F - 1) := by
      simp [i, Fin.coe_divNat]
    have hu : u.1 = ρ / (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card) % (Fintype.card F - 1) := by
      simp [u, Fin.coe_modNat, Fin.coe_divNat]
    have e1 : ((repCodes enc reps).getD i.1 []).getD k 0 = code enc (reps[i] k) := by
      have h1 : (repCodes enc reps).getD i.1 [] = (List.ofFn reps[i]).map (code enc) := by
        unfold repCodes
        simp [List.getD_eq_getElem?_getD]
      rw [h1, List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [← hi, ← hu, e1, ← code_toUnit enc u, tab_mul]
    simp [phiB, unitE]
  constructor
  · intro hall
    funext k
    have := hall k k.2
    rw [← hy k, ← hx k, ← hb k, tab_mul, tab_add] at this
    have := code_inj enc this
    rw [this]; simp
  · intro heq k hk
    have := congrFun heq ⟨k, hk⟩
    have e : code enc (vecE enc t ω.modNat ⟨k, hk⟩) = code enc (vecE enc t ρ.modNat.divNat ⟨k, hk⟩ +
        (p : F) * (phiB enc hR (i, u)).1 ⟨k, hk⟩) := by rw [this]; simp
    rw [hy, ← tab_add, ← tab_mul, hx, hb] at e
    exact e

end AbelianCayleyHDX.XH


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XP

/-! ### General `Poly` combinators -/

theorem foldl_append_eq {α : Type} (xs : List (List α)) (acc : List α) :
    List.foldl (fun b a => b ++ a) acc xs = acc ++ xs.flatten := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, List.append_assoc]

theorem poly_flatten {α : Type} [Coding α] [Inhabited α] : Poly (List.flatten : List (List α) → List α) := by
  let P : PolyProgram (encodePair (encodeList (encodeList (enc : α → List Bool)))
      (encodeList (enc : α → List Bool))) (encodeList (enc : α → List Bool))
      (fun x : List (List α) × List α => List.foldl (fun b a => (b, a).1 ++ (b, a).2) x.2 x.1) :=
    PolyProgram.listFoldLinear (PolyProgram.listAppend (enc : α → List Bool) default) [] 1 (by
      intro b a
      simp only [EncodedList.append, List.length_append]
      omega)
  have h1 : Poly (fun xs : List (List α) => (xs, ([] : List α))) :=
    Poly.pair Poly.identity (OAI.MetricKMedian.Binary.Automatic.Poly.const ([] : List α))
  have h2 : Poly (fun x : List (List α) × List α =>
      List.foldl (fun b a => (b, a).1 ++ (b, a).2) x.2 x.1) := ⟨P⟩
  have := Poly.comp h2 h1
  convert this using 1
  funext xs
  simp only
  rw [foldl_append_eq, List.nil_append]

attribute [fun_prop] poly_flatten

variable {γ α β δ : Type} [Coding γ] [Coding α] [Coding β] [Coding δ]

@[fun_prop] theorem flatMap_ctx [Inhabited β] [Inhabited δ] {f : γ → β → List δ} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) := by
  have h := Poly.comp poly_flatten (Poly.list_map hf ha)
  convert h using 2 with x
  rw [List.flatMap_def]

@[fun_prop] theorem map_ctx [Inhabited β] [Inhabited δ] {f : γ → β → δ} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) := Poly.list_map hf ha

@[fun_prop] theorem append_comp [Inhabited α] {f g : γ → List α} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x ++ g x) := Poly.comp Poly.list_append (Poly.pair hf hg)

@[fun_prop] theorem cons_comp {f : γ → α} {g : γ → List α} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x :: g x) := Poly.comp Poly.list_cons (Poly.pair hf hg)

@[fun_prop] theorem length_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => (f x).length) := Poly.comp Poly.list_length hf

@[fun_prop] theorem range_length_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => List.range (f x).length) :=
  Poly.comp (f := fun xs : List α => List.range xs.length) Poly.list_indices hf

@[fun_prop] theorem nat_eq_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x = g x)) := Poly.comp Poly.nat_eq (Poly.pair hf hg)

@[fun_prop] theorem nat_add_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x + g x) := Poly.comp Poly.nat_add (Poly.pair hf hg)

@[fun_prop] theorem nat_sub_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x - g x) := Poly.comp Poly.nat_sub (Poly.pair hf hg)

@[fun_prop] theorem rat_mul_comp {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.rat_mul (Poly.pair hf hg)

@[fun_prop] theorem rat_div_comp {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) := Poly.comp Poly.rat_div (Poly.pair hf hg)

@[fun_prop] theorem rat_lt_comp' {f g : γ → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := Poly.comp Poly.rat_lt (Poly.pair hf hg)

@[fun_prop] theorem rat_ofNat_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => ((f x : ℕ) : ℚ)) :=
  Poly.comp Poly.rat_ofNat hf

@[fun_prop] theorem bits_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => Nat.bits (f x)) :=
  Poly.comp (⟨PolyProgram.natAsList⟩ : Poly (Nat.bits : ℕ → List Bool)) hf

@[fun_prop] theorem value_comp {f : γ → List Bool} (hf : Poly f) : Poly (fun x => Word.value (f x)) :=
  Poly.comp (⟨BooleanLists.valueProgram⟩ : Poly (Word.value : List Bool → ℕ)) hf

@[fun_prop] theorem num_abs_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => (f x).num.natAbs) :=
  Poly.comp (⟨PolyProgram.intAbs⟩ : Poly (Int.natAbs : ℤ → ℕ))
    (Poly.comp (⟨PolyProgram.ratNum⟩ : Poly (Rat.num : ℚ → ℤ)) hf)

@[fun_prop] theorem den_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => (f x).den) :=
  Poly.comp (⟨PolyProgram.ratDen⟩ : Poly (Rat.den : ℚ → ℕ)) hf

@[fun_prop] theorem const' (b : β) : Poly (fun _ : γ => b) :=
  OAI.MetricKMedian.Binary.Automatic.Poly.const b

@[fun_prop] theorem id' : Poly (fun x : γ => x) := Poly.identity

@[fun_prop] theorem fst' : Poly (fun x : γ × β => x.1) := Poly.fst

@[fun_prop] theorem snd' : Poly (fun x : γ × β => x.2) := Poly.snd

@[fun_prop] theorem fst_comp {f : γ → α × β} (hf : Poly f) : Poly (fun x => (f x).1) :=
  Poly.comp Poly.fst hf

@[fun_prop] theorem snd_comp {f : γ → α × β} (hf : Poly f) : Poly (fun x => (f x).2) :=
  Poly.comp Poly.snd hf

@[fun_prop] theorem pair' {f : γ → α} {g : γ → β} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => (f x, g x)) := Poly.pair hf hg

@[fun_prop] theorem ite' {p : γ → Bool} {f g : γ → α} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x = true then f x else g x) := Poly.ite hp hf hg

end AbelianCayleyHDX.XP

namespace AbelianCayleyHDX.XP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

variable {γ α : Type} [Coding γ] [Coding α]

@[fun_prop] theorem tail_comp [Inhabited α] {f : γ → List α} (hf : Poly f) :
    Poly (fun x => (f x).tail) := Poly.comp Poly.list_tail hf

/-! ### The output function -/

/-- `encNat`, written with `Nat.bits`. -/
def encNatB (m : ℕ) : List Bool := (Nat.bits m).flatMap (fun b => [false, b]) ++ [true, false]

/-- `encNat 0` / `encNat 1`. -/
def cbit (b : Bool) : List Bool := if b then [false, true, true, false] else [true, false]

def encRatB (q : ℚ) : List Bool := decide (q < 0) :: (encNatB q.num.natAbs ++ encNatB q.den)

def vecB (n : ℕ) (cs : List Bool) : List Bool := encNatB n ++ cs.flatMap cbit

def posZero (k : ℕ) : List Bool := (List.range k).map (fun _ => false)

def posE (k i : ℕ) : List Bool := (List.range k).map (fun r => decide (r = i))

def pow2B (k : ℕ) : ℕ := Word.value (((List.range k).tail.map (fun _ => false)) ++ [true])

/-- The normalization `Z(k) = k · 2^{k-1} · K`. -/
def ZB (Kc : ℚ) (k : ℕ) : ℚ := (k : ℚ) * (pow2B k : ℚ) * Kc

def gensC (labNZ : List (List Bool)) (k : ℕ) : List (List Bool) :=
  (posZero k :: (List.range k).map (posE k)).flatMap (fun p => labNZ.map (fun b => p ++ b))

def repsC (T1 : List (List (List Bool))) (T2 : List (List (List Bool) × List (List Bool) × ℚ))
    (ws : ℚ) (k : ℕ) : List (List (List Bool) × ℚ) :=
  T1.map (fun L => (L.map (fun b => posZero k ++ b), ws * (k : ℚ))) ++
    (List.range k).flatMap (fun i => T2.map (fun e =>
      (e.1.map (fun b => posZero k ++ b) ++ e.2.1.map (fun b => posE k i ++ b), e.2.2)))

def outB (a : ℕ) (labNZ : List (List Bool)) (T1 : List (List (List Bool)))
    (T2 : List (List (List Bool) × List (List Bool) × ℚ)) (ws Kc : ℚ) (k : ℕ) : List Bool :=
  encNatB (k + a) ++
    (encNatB (gensC labNZ k).length ++ (gensC labNZ k).flatMap (vecB (k + a))) ++
    (encNatB (repsC T1 T2 ws k).length ++ (repsC T1 T2 ws k).flatMap (fun e =>
      encNatB e.1.length ++ e.1.flatMap (vecB (k + a)) ++ encRatB (e.2 / ZB Kc k)))

@[fun_prop] theorem encNatB_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => encNatB (f x)) := by
  unfold encNatB; fun_prop

@[fun_prop] theorem cbit_comp {f : γ → Bool} (hf : Poly f) : Poly (fun x => cbit (f x)) := by
  unfold cbit; fun_prop

@[fun_prop] theorem encRatB_comp {f : γ → ℚ} (hf : Poly f) : Poly (fun x => encRatB (f x)) := by
  unfold encRatB; fun_prop

@[fun_prop] theorem vecB_comp {f : γ → ℕ} {g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => vecB (f x) (g x)) := by
  unfold vecB; fun_prop

theorem poly_outB (a : ℕ) (labNZ : List (List Bool)) (T1 : List (List (List Bool)))
    (T2 : List (List (List Bool) × List (List Bool) × ℚ)) (ws Kc : ℚ) :
    Poly (fun w : List Bool => outB a labNZ T1 T2 ws Kc w.length) := by
  unfold outB gensC repsC ZB pow2B posE posZero
  fun_prop

end AbelianCayleyHDX.XP

namespace AbelianCayleyHDX.XP
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem poly_eval_mono (p : Polynomial ℕ) {x y : ℕ} (h : x ≤ y) : p.eval x ≤ p.eval y := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i))

/-- A `Poly` function on Boolean words is computed by a multi-stack machine within a polynomial
time bound in any upper bound of the input length. -/
theorem outputsWithin_of_poly {F : List Bool → List Bool}
    (hF : Poly (fun w : List Bool => F w)) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : Polynomial ℕ), ∀ (w : List Bool) (N : ℕ),
      w.length ≤ N → HMBinPacking.OutputsWithin M w (F w) (p.eval N) := by
  let P : PolyProgram id id (id ∘ (F ∘ id)) :=
    BooleanLists.packProgram.comp (hF.program.comp BooleanLists.unpackProgram)
  refine ⟨⟨P.machine.tm, Equiv.refl _, Equiv.refl _⟩, P.time, fun w N hN => ?_⟩
  have h := P.outputs w
  have h' : Turing.TM2OutputsInTime P.machine.tm w (some (F w)) (P.time.eval N) :=
    ⟨h.toEvalsTo, le_trans h.steps_le_m (poly_eval_mono _ hN)⟩
  unfold HMBinPacking.OutputsWithin
  change Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w)
    (some (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (F w))) (P.time.eval N))
  have e1 : List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w = w := List.map_id w
  have e2 : List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (F w) = F w :=
    List.map_id (F w)
  rw [e1, e2]
  exact ⟨h'⟩

end AbelianCayleyHDX.XP

open ReplParity (Vec)
open RSListDecodingCapacity.AllRates
open OAI.MetricKMedian.Binary

namespace AbelianCayleyHDX.XE

open AbelianCayleyHDX.XP

lemma encNat_eq (m : ℕ) : encNat m = encNatB m := by
  unfold encNat encBits encNatB
  congr 2
  rw [Nat.digits_two_eq_bits, List.map_map]
  conv_rhs => rw [← List.map_id m.bits]
  congr 1; funext b; cases b <;> rfl

lemma encZMod_eq (x : ZMod 2) : encZMod x = cbit (decide (x = 1)) := by
  fin_cases x <;> rfl

def bitsOf {m : ℕ} (v : Vec m) : List Bool := (List.ofFn v).map (fun x => decide (x = 1))

lemma encVec_eq {m : ℕ} (v : Vec m) : encVec v = vecB m (bitsOf v) := by
  unfold encVec encList vecB bitsOf
  rw [List.length_ofFn, encNat_eq, List.flatMap_map]
  congr 1
  exact List.flatMap_congr (fun x _ => encZMod_eq x)

lemma encRat_eq (q : ℚ) : AbelianCayleyHDX.encRat q = encRatB q := by
  unfold AbelianCayleyHDX.encRat encRatB; rw [encNat_eq, encNat_eq]

lemma value_pow (m : ℕ) : Word.value (List.replicate m false ++ [true]) = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, List.cons_append, Word.value, ih]; simp [pow_succ]; ring


end AbelianCayleyHDX.XE


namespace AbelianCayleyHDX.XK

open Matrix

variable {M : ℕ}

abbrev V (M : ℕ) := Fin M → ZMod 2

lemma z2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by revert c; decide

lemma z2_add_self (c : ZMod 2) : c + c = 0 := by revert c; decide

/-- One step of the incremental kernel computation. -/
def kstep (h : V M) (K : List (V M)) : List (V M) :=
  K.map (fun k => k + (h ⬝ᵥ k) • K.getD (K.findIdx (fun k => decide (h ⬝ᵥ k ≠ 0))) 0)

/-- The common kernel of a list of rows. -/
def U (S : List (V M)) : Submodule (ZMod 2) (V M) :=
  ⨅ h ∈ S, LinearMap.ker (dotProductBilin (ZMod 2) (ZMod 2) h)

lemma mem_U {S : List (V M)} {v : V M} : v ∈ U S ↔ ∀ h ∈ S, h ⬝ᵥ v = 0 := by
  simp [U, Submodule.mem_iInf]

def Inv (S K : List (V M)) : Prop :=
  Submodule.span (ZMod 2) {x | x ∈ K} = U S ∧
    (K.filter (· ≠ 0)).length = Module.finrank (ZMod 2) (U S)

lemma span_filter (K : List (V M)) :
    Submodule.span (ZMod 2) {x | x ∈ K.filter (· ≠ 0)} = Submodule.span (ZMod 2) {x | x ∈ K} := by
  apply le_antisymm
  · apply Submodule.span_mono; intro x hx; exact (List.mem_filter.1 hx).1
  · rw [Submodule.span_le]
    intro x hx
    by_cases h0 : x = 0
    · rw [h0]; exact Submodule.zero_mem _
    · exact Submodule.subset_span (List.mem_filter.2 ⟨hx, by simpa using h0⟩)

/-- Under the invariant, the nonzero entries are linearly independent. -/
lemma inv_li {S K : List (V M)} (hI : Inv S K) :
    LinearIndependent (ZMod 2) (fun i : Fin (K.filter (· ≠ 0)).length => (K.filter (· ≠ 0)).get i) := by
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
  have hr : Set.range (fun i : Fin (K.filter (· ≠ 0)).length => (K.filter (· ≠ 0)).get i) =
      {x | x ∈ K.filter (· ≠ 0)} := by
    ext x; simp only [Set.mem_range, Set.mem_setOf_eq, List.mem_iff_get]
  unfold Set.finrank
  rw [hr, span_filter, hI.1, hI.2]

lemma inv_nodup {S K : List (V M)} (hI : Inv S K) : (K.filter (· ≠ 0)).Nodup := by
  have hli := inv_li hI
  rw [List.nodup_iff_injective_get]
  exact hli.injective

/-- **The step preserves the invariant.** -/
theorem inv_step {S K : List (V M)} (hI : Inv S K) (h : V M) : Inv (h :: S) (kstep h K) := by
  classical
  by_cases hall : ∀ k ∈ K, h ⬝ᵥ k = 0
  · -- nothing changes
    have hidx : K.findIdx (fun k => decide (h ⬝ᵥ k ≠ 0)) = K.length := by
      rw [List.findIdx_eq_length]; intro k hk; simpa using hall k hk
    have hK : kstep h K = K := by
      unfold kstep; rw [hidx]
      conv_rhs => rw [← List.map_id K]
      apply List.map_congr_left; intro k hk; simp [hall k hk]
    have hU : U (h :: S) = U S := by
      apply le_antisymm
      · intro v hv; rw [mem_U] at hv ⊢; exact fun g hg => hv g (List.mem_cons_of_mem _ hg)
      · intro v hv
        rw [mem_U]
        intro g hg
        rcases List.mem_cons.1 hg with rfl | hg
        · rw [← hI.1] at hv
          refine Submodule.span_induction (p := fun v _ => g ⬝ᵥ v = 0) ?_ ?_ ?_ ?_ hv
          · intro x hx; exact hall x hx
          · simp
          · intro x y _ _ hx hy; rw [dotProduct_add, hx, hy, add_zero]
          · intro c x _ hx; rw [dotProduct_smul, hx, smul_zero]
        · exact (mem_U.1 hv) g hg
    rw [hK, Inv, hU]; exact hI
  · push Not at hall
    obtain ⟨k0, hk0, hk0v⟩ := hall
    set l0 := K.findIdx (fun k => decide (h ⬝ᵥ k ≠ 0)) with hl0
    have hlt : l0 < K.length := List.findIdx_lt_length_of_exists ⟨k0, hk0, by simpa using hk0v⟩
    set kp := K.getD l0 0 with hkp
    have hkpK : kp = K[l0] := by rw [hkp, List.getD_eq_getElem _ _ hlt]
    have hkpv : h ⬝ᵥ kp = 1 := by
      have := List.findIdx_getElem (w := hlt)
      rw [← hkpK] at this
      simpa using (z2_cases _).resolve_left (by simpa using this)
    have hkpmem : kp ∈ K := by rw [hkpK]; exact List.getElem_mem _
    set K' := kstep h K with hK'
    have hK'eq : K' = K.map (fun k => k + (h ⬝ᵥ k) • kp) := rfl
    -- the new subspace
    have hsub : Submodule.span (ZMod 2) {x | x ∈ K'} ≤ U (h :: S) := by
      rw [Submodule.span_le]
      intro x hx
      simp only [Set.mem_setOf_eq, hK'eq, List.mem_map] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      rw [SetLike.mem_coe, mem_U]
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · rw [dotProduct_add, dotProduct_smul, hkpv, smul_eq_mul, mul_one, z2_add_self]
      · have hkU : k ∈ U S := hI.1 ▸ Submodule.subset_span hk
        have hpU : kp ∈ U S := hI.1 ▸ Submodule.subset_span hkpmem
        rw [dotProduct_add, dotProduct_smul, (mem_U.1 hkU) g hg, (mem_U.1 hpU) g hg]; simp
    have hspan : Submodule.span (ZMod 2) {x | x ∈ K'} = U (h :: S) := by
      refine le_antisymm hsub (fun v hv => ?_)
      have hvU : v ∈ U S := by
        rw [mem_U] at hv ⊢; exact fun g hg => hv g (List.mem_cons_of_mem _ hg)
      rw [← hI.1] at hvU
      -- `span K ≤ span K' ⊔ span {kp}`
      have hle : Submodule.span (ZMod 2) {x | x ∈ K} ≤
          Submodule.span (ZMod 2) {x | x ∈ K'} ⊔ Submodule.span (ZMod 2) {kp} := by
        rw [Submodule.span_le]
        intro k hk
        have e : k = (k + (h ⬝ᵥ k) • kp) + (h ⬝ᵥ k) • kp := by
          rw [add_assoc, ← add_smul, z2_add_self, zero_smul, add_zero]
        rw [SetLike.mem_coe, e]
        refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ?_))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
        simp only [Set.mem_setOf_eq, hK'eq, List.mem_map]; exact ⟨k, hk, rfl⟩
      obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 (hle hvU)
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      have hwU : w ∈ U (h :: S) := hsub hw
      have h1 := (mem_U.1 hv) h (List.mem_cons_self)
      have h2 := (mem_U.1 hwU) h (List.mem_cons_self)
      rw [dotProduct_add, h2, zero_add, dotProduct_smul, hkpv, smul_eq_mul, mul_one] at h1
      rw [h1, zero_smul, add_zero]; exact hw
    refine ⟨hspan, ?_⟩
    -- counting nonzero entries
    have hnd := inv_nodup hI
    have hkp0 : kp ≠ 0 := by intro h0; rw [h0, dotProduct_zero] at hkpv; exact zero_ne_one hkpv
    have hkpf : kp ∈ K.filter (· ≠ 0) := List.mem_filter.2 ⟨hkpmem, by simpa using hkp0⟩
    have hfun : (fun k => decide ((k + (h ⬝ᵥ k) • kp) ≠ 0)) =
        (fun k => decide (k ≠ 0) && decide (k ≠ kp)) := by
      funext k
      by_cases hk0 : k = 0
      · subst hk0; simp
      · rcases z2_cases (h ⬝ᵥ k) with hc | hc
        · have hne : k ≠ kp := by intro hkk; rw [hkk, hkpv] at hc; exact one_ne_zero hc
          simp only [hc, zero_smul, add_zero, hk0, hne, ne_eq, not_false_eq_true, decide_true,
            Bool.and_self]
        · have : k + kp = 0 ↔ k = kp := by
            constructor
            · intro hh
              have hkk : kp + kp = 0 := by ext i; exact z2_add_self _
              calc k = k + (kp + kp) := by rw [hkk, add_zero]
                _ = (k + kp) + kp := (add_assoc _ _ _).symm
                _ = kp := by rw [hh, zero_add]
            · rintro rfl; ext i; exact z2_add_self _
          simp only [hc, one_smul, ne_eq, this, hk0, not_false_eq_true, decide_true, Bool.true_and]
    have hcount : (K'.filter (· ≠ 0)).length + 1 = (K.filter (· ≠ 0)).length := by
      rw [hK'eq, List.filter_map, List.length_map]
      have e : K.filter ((fun k => decide (k ≠ 0)) ∘ fun k => k + (h ⬝ᵥ k) • kp) =
          (K.filter (· ≠ 0)).filter (fun k => k ≠ kp) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro k _
        have := congrFun hfun k
        simp only [Function.comp] at this ⊢
        rw [this, Bool.and_comm]
      have e2 : (K.filter (· ≠ 0)).filter (fun k => k ≠ kp) = (K.filter (· ≠ 0)).erase kp := by
        rw [List.Nodup.erase_eq_filter hnd]
        apply List.filter_congr; intro k _; by_cases hk : k = kp <;> simp [hk]
      rw [e, e2, List.length_erase_of_mem hkpf]
      have : 0 < (K.filter (· ≠ 0)).length := List.length_pos_of_mem hkpf
      omega
    -- the dimension drops by one
    let f : V M →ₗ[ZMod 2] ZMod 2 := dotProductBilin (ZMod 2) (ZMod 2) h
    have hf : ∀ v, f v = h ⬝ᵥ v := fun v => rfl
    have hW : U (h :: S) = LinearMap.ker f ⊓ U S := by
      ext v; simp only [Submodule.mem_inf, LinearMap.mem_ker, hf, mem_U, List.mem_cons]
      constructor
      · intro hv; exact ⟨hv h (Or.inl rfl), fun g hg => hv g (Or.inr hg)⟩
      · rintro ⟨h1, h2⟩ g (rfl | hg); exacts [h1, h2 g hg]
    have hsup : LinearMap.ker f ⊔ U S = ⊤ := by
      rw [eq_top_iff]; intro v _
      have hpU : kp ∈ U S := hI.1 ▸ Submodule.subset_span hkpmem
      have e : v = (v - (h ⬝ᵥ v) • kp) + (h ⬝ᵥ v) • kp := by abel
      rw [e]
      refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ hpU))
      rw [LinearMap.mem_ker, hf, dotProduct_sub, dotProduct_smul, hkpv, smul_eq_mul, mul_one,
        sub_self]
    have hrange : Module.finrank (ZMod 2) (LinearMap.range f) = 1 := by
      have : LinearMap.range f = ⊤ := by
        rw [eq_top_iff]; intro c _; exact ⟨c • kp, by rw [map_smul, hf, hkpv, smul_eq_mul, mul_one]⟩
      rw [this, finrank_top, Module.finrank_self]
    have hker := LinearMap.finrank_range_add_finrank_ker f
    rw [hrange] at hker
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (U S)
    rw [hsup, finrank_top, ← hW] at hdim
    have hlen := hI.2
    omega

/-! ### The whole computation -/

def K0 (M : ℕ) : List (V M) := (List.finRange M).map (fun i => Pi.single i 1)

def kernelList (rows : List (V M)) : List (V M) := rows.foldl (fun K h => kstep h K) (K0 M)

lemma U_nil : U ([] : List (V M)) = ⊤ := by
  ext v; simp [mem_U]

lemma inv_init : Inv [] (K0 M) := by
  refine ⟨?_, ?_⟩
  · rw [U_nil, eq_top_iff]
    have h := (Pi.basisFun (ZMod 2) (Fin M)).span_eq
    rw [← h]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    simp only [Pi.basisFun_apply, Set.mem_setOf_eq, K0, List.mem_map, List.mem_finRange, true_and]
    exact ⟨i, rfl⟩
  · rw [U_nil, finrank_top, Module.finrank_fin_fun]
    have : (K0 M).filter (· ≠ 0) = K0 M := by
      rw [List.filter_eq_self]
      intro x hx
      simp only [K0, List.mem_map, List.mem_finRange, true_and] at hx
      obtain ⟨i, rfl⟩ := hx
      simp only [ne_eq, decide_eq_true_eq]
      intro h0; have := congrFun h0 i; simp at this
    rw [this, K0, List.length_map, List.length_finRange]

lemma U_congr {S S' : List (V M)} (h : ∀ g, g ∈ S ↔ g ∈ S') : U S = U S' := by
  ext v; simp only [mem_U]; exact ⟨fun hv g hg => hv g ((h g).2 hg), fun hv g hg => hv g ((h g).1 hg)⟩

lemma inv_fold (rows : List (V M)) {S K : List (V M)} (hI : Inv S K) :
    Inv (rows.reverse ++ S) (rows.foldl (fun K h => kstep h K) K) := by
  induction rows generalizing S K with
  | nil => simpa using hI
  | cons h rows ih =>
    rw [List.foldl_cons, List.reverse_cons, List.append_assoc]
    exact ih (by simpa using inv_step hI h)

lemma U_ofFn {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) (S : List (V M))
    (hS : ∀ g, g ∈ S ↔ g ∈ List.ofFn H) : U S = AbelianCayleyHDX.kerF2 H := by
  ext v
  rw [mem_U, AbelianCayleyHDX.kerF2, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv; funext r
    exact hv (H r) ((hS _).2 (List.mem_ofFn.2 ⟨r, rfl⟩))
  · intro hv g hg
    obtain ⟨r, rfl⟩ := List.mem_ofFn.1 ((hS g).1 hg)
    exact congrFun hv r

/-- The computed basis of `ker H`. -/
def basisList {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) : List (V M) :=
  (kernelList (List.ofFn H)).filter (· ≠ 0)

theorem basisList_spec {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    Submodule.span (ZMod 2) {x | x ∈ basisList H} = AbelianCayleyHDX.kerF2 H ∧
    (basisList H).length = Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H) ∧
    LinearIndependent (ZMod 2) (fun i : Fin (basisList H).length => (basisList H).get i) := by
  have hI := inv_fold (List.ofFn H) inv_init
  have hU : U ((List.ofFn H).reverse ++ []) = AbelianCayleyHDX.kerF2 H :=
    U_ofFn H _ (fun g => by simp)
  refine ⟨?_, ?_, inv_li hI⟩
  · unfold basisList; rw [span_filter, ← hU]; exact hI.1
  · unfold basisList; rw [← hU]; exact hI.2

/-- The quotient map `v ↦ (bₗ ⬝ v)ₗ`. -/
noncomputable def phiMat {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    Matrix (Fin (Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H))) (Fin M) (ZMod 2) :=
  Matrix.of fun ℓ i => (basisList H).get (ℓ.cast (basisList_spec H).2.1.symm) i

noncomputable def phi {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    (Fin M → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H)) → ZMod 2) :=
  (phiMat H).mulVecLin

theorem phi_spec {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    Function.Surjective (phi H) ∧ LinearMap.ker (phi H) = AbelianCayleyHDX.rowspan H := by
  classical
  obtain ⟨hspan, hlen, hli⟩ := basisList_spec H
  set n := Module.finrank (ZMod 2) (AbelianCayleyHDX.kerF2 H)
  have hrows : LinearIndependent (ZMod 2) (fun ℓ : Fin n => phiMat H ℓ) := by
    have := hli.comp (Fin.cast hlen.symm) (Fin.cast_injective _)
    exact this
  have hrank : (phiMat H).rank = n := by
    rw [Matrix.rank_eq_finrank_span_row,
      show (phiMat H).row = fun ℓ => phiMat H ℓ from rfl, finrank_span_eq_card hrows,
      Fintype.card_fin]
  have hsurj : Function.Surjective (phi H) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fin_fun]
    exact hrank
  refine ⟨hsurj, ?_⟩
  -- `rowspan H ≤ ker φ`
  have hle : AbelianCayleyHDX.rowspan H ≤ LinearMap.ker (phi H) := by
    rw [AbelianCayleyHDX.rowspan, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    funext ℓ
    simp only [phi, Matrix.mulVecLin_apply, Pi.zero_apply, Matrix.mulVec, phiMat]
    have hb : (basisList H).get (ℓ.cast hlen.symm) ∈ AbelianCayleyHDX.kerF2 H := by
      rw [← hspan]; exact Submodule.subset_span (List.get_mem _ _)
    rw [AbelianCayleyHDX.kerF2, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hb
    have := congrFun hb r
    simp only [Matrix.mulVec, Pi.zero_apply] at this
    rw [dotProduct_comm]
    exact this
  have h1 := LinearMap.finrank_range_add_finrank_ker (phi H)
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_fin_fun] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker H.mulVecLin
  have h3 : Module.finrank (ZMod 2) (LinearMap.range H.mulVecLin) =
      Module.finrank (ZMod 2) (AbelianCayleyHDX.rowspan H) := by
    have := Matrix.rank_eq_finrank_span_row H
    rw [Matrix.rank] at this
    rw [this]; rfl
  have h5 : Module.finrank (ZMod 2) (Fin M → ZMod 2) = M := Module.finrank_fin_fun _
  have h4 : Module.finrank (ZMod 2) (LinearMap.ker H.mulVecLin) = n := rfl
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

end AbelianCayleyHDX.XK


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XP

/-- **Post-processing a machine's output by a polynomial-time function.** If `Mach` turns `x a`
into `W a` within `T a` steps and `F` is `Poly`, then one machine turns `x a` into `F (W a)` within
`T a + 2|W a| + 2 + P(|W a|)` steps. -/
theorem outputsWithin_comp {α : Type*} {Mach : Turing.TM2ComputableAux Bool Bool}
    {x W : α → List Bool} {T : α → ℕ}
    (hM : ∀ a, HMBinPacking.OutputsWithin Mach (x a) (W a) (T a))
    {F : List Bool → List Bool} (hF : Poly (fun w : List Bool => F w)) :
    ∃ (M' : Turing.TM2ComputableAux Bool Bool) (P : Polynomial ℕ), ∀ a,
      HMBinPacking.OutputsWithin M' (x a) (F (W a))
        (T a + (2 * (W a).length + 2) + P.eval (W a).length) := by
  classical
  let P0 : PolyProgram id id (id ∘ (F ∘ id)) :=
    BooleanLists.packProgram.comp (hF.program.comp BooleanLists.unpackProgram)
  let tm₂ := P0.machine.tm
  let tr : Mach.tm.Γ Mach.tm.k₁ → tm₂.Γ tm₂.k₀ := fun s => Mach.outputAlphabet s
  let M' : Turing.TM2ComputableAux Bool Bool :=
    ⟨ShiTM2.comp Mach.tm tm₂ tr false,
      (ShiTM2.compInputAlphabet Mach.tm tm₂ tr false).trans Mach.inputAlphabet,
      (ShiTM2.compOutputAlphabet Mach.tm tm₂ tr false).trans (Equiv.refl Bool)⟩
  refine ⟨M', P0.time, fun a => ?_⟩
  obtain ⟨h₁⟩ := hM a
  have h₂ : Turing.TM2OutputsInTime tm₂
      (((W a).map Mach.outputAlphabet.symm).map tr) (some (F (W a)))
      (P0.time.eval ((W a).map Mach.outputAlphabet.symm).length) := by
    have e : ((W a).map Mach.outputAlphabet.symm).map tr = W a := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (W a)]
      congr 1; funext s
      show Mach.outputAlphabet (Mach.outputAlphabet.symm s) = s
      exact Equiv.apply_symm_apply _ _
    rw [e, List.length_map]
    exact P0.outputs (W a)
  obtain ⟨h⟩ := ShiTM.comp_outputsInTime (inst := ShiTM2.compKDecEq Mach.tm tm₂) Mach.tm tm₂ tr
    false _ _ _ _ _ h₁ h₂
  rw [List.length_map] at h
  unfold HMBinPacking.OutputsWithin
  have e2 : List.map (⇑M'.outputAlphabet.symm) (F (W a)) = F (W a) := List.map_id _
  rw [e2]
  exact ⟨h⟩

end AbelianCayleyHDX.XP


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.XP

/-! ### Decoding a stream of `encNat` tokens -/

lemma value_bits (t : ℕ) : Word.value (Nat.bits t) = t := by
  induction t using Nat.binaryRec with
  | zero => simp [Word.value]
  | bit b n ih =>
    by_cases h : Nat.bit b n = 0
    · rw [h]; simp [Word.value]
    · rw [Nat.bits_append_bit n b (fun hn => by
        subst hn; cases b
        · exact absurd (by simp [Nat.bit]) h
        · rfl)]
      simp only [Word.value, ih]
      cases b <;> simp [Nat.bit] <;> ring

lemma bits_length_value_le (cur : List Bool) : (Nat.bits (Word.value cur)).length ≤ cur.length := by
  rw [Nat.size_eq_bits_len, Nat.size_le]
  induction cur with
  | nil => simp [Word.value]
  | cons b bs ih =>
    simp only [Word.value, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-- The decoder state: (inside a pair?, first bit of the pair, current bits, tokens so far). -/
abbrev DState := Bool × Bool × List Bool × List ℕ

def dstep (s : DState) (c : Bool) : DState :=
  if s.1 then
    (if s.2.1 then (false, s.2.1, [], s.2.2.2 ++ [Word.value s.2.2.1])
      else (false, s.2.1, s.2.2.1 ++ [c], s.2.2.2))
  else (true, c, s.2.2.1, s.2.2.2)

def decTokens (w : List Bool) : List ℕ := (w.foldl dstep (false, false, [], [])).2.2.2

lemma fold_pairs (bs : List Bool) (f : Bool) (cur : List Bool) (acc : List ℕ) (rest : List Bool) :
    (bs.flatMap (fun b => [false, b]) ++ rest).foldl dstep (false, f, cur, acc) =
      rest.foldl dstep (false, (if bs = [] then f else false), cur ++ bs, acc) := by
  induction bs generalizing f cur with
  | nil => simp
  | cons b bs ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.foldl_cons]
    rw [show dstep (dstep (false, f, cur, acc) false) b = (false, false, cur ++ [b], acc) by
      simp [dstep]]
    rw [ih]
    simp only [List.cons_ne_nil, if_false, List.append_assoc, List.singleton_append]
    by_cases hbs : bs = [] <;> simp [hbs]

lemma fold_encNat (t : ℕ) (f : Bool) (acc : List ℕ) (rest : List Bool) :
    (encNat t ++ rest).foldl dstep (false, f, [], acc) =
      rest.foldl dstep (false, true, [], acc ++ [t]) := by
  unfold encNat encBits
  rw [List.append_assoc, fold_pairs]
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.nil_append]
  congr 1
  simp only [dstep, if_true, Bool.false_eq_true, if_false]
  congr
  rw [Nat.digits_two_eq_bits, List.map_map]
  conv_rhs => rw [← value_bits t]
  congr 1
  conv_rhs => rw [← List.map_id t.bits]
  congr 1; funext b; cases b <;> rfl

lemma fold_tokens (L : List ℕ) (f : Bool) (acc : List ℕ) :
    ∃ f', (L.flatMap encNat).foldl dstep (false, f, [], acc) = (false, f', [], acc ++ L) := by
  induction L generalizing f acc with
  | nil => exact ⟨f, by simp⟩
  | cons t L ih =>
    rw [List.flatMap_cons, fold_encNat]
    obtain ⟨f', h⟩ := ih true (acc ++ [t])
    exact ⟨f', by rw [h, List.append_assoc, List.singleton_append]⟩

theorem decTokens_flatMap (L : List ℕ) : decTokens (L.flatMap encNat) = L := by
  unfold decTokens
  obtain ⟨f', h⟩ := fold_tokens L false []
  rw [h]; simp

lemma encList_length_append {α : Type} (ea : α → List Bool) (l : List α) (x : α) :
    (encodeList ea (l ++ [x])).length = (encodeList ea l).length + 2 * (ea x).length + 1 := by
  rw [EncodedList.append, List.length_append]
  simp [encodeList, quote_length]; omega

lemma encList_bool_length (l : List Bool) : (encodeList encodeBool l).length = 3 * l.length := by
  induction l with
  | nil => simp [encodeList]
  | cons b l ih => simp [encodeList, quote_length, encodeBool, ih]; ring

theorem dstep_size (st : DState) (c : Bool) :
    ((enc : DState → List Bool) (dstep st c)).length ≤
      ((enc : DState → List Bool) st).length + 2 * (2 * (encodeBool c).length + 1) := by
  obtain ⟨p, f, cur, acc⟩ := st
  change (encodePair encodeBool (encodePair encodeBool (encodePair (encodeList encodeBool)
      (encodeList Nat.bits))) (dstep (p, f, cur, acc) c)).length ≤
    (encodePair encodeBool (encodePair encodeBool (encodePair (encodeList encodeBool)
      (encodeList Nat.bits))) (p, f, cur, acc)).length + 2 * (2 * (encodeBool c).length + 1)
  unfold dstep
  cases p <;> cases f <;>
    simp only [Bool.false_eq_true, if_false, if_true, encodePair_length, encodeBool,
      List.length_singleton, encList_length_append, encList_bool_length, List.length_append,
      List.length_nil, mul_zero] <;> try omega
  all_goals (have := bits_length_value_le cur; omega)

theorem poly_decTokens : Poly (fun w : List Bool => decTokens w) := by
  let P : PolyProgram (encodePair (enc : DState → List Bool) encodeBool) (enc : DState → List Bool)
      (fun x : DState × Bool => dstep x.1 x.2) := by
    have h : Poly (fun x : DState × Bool => dstep x.1 x.2) := by unfold dstep; fun_prop
    exact h.program
  let Q := P.listFoldLinear false 2 (fun b a => dstep_size b a)
  have hQ : Poly (fun x : List Bool × DState => x.1.foldl (fun b a => dstep b a) x.2) := ⟨Q⟩
  have h2 : Poly (fun w : List Bool => (w.foldl (fun b a => dstep b a)
      ((false, false, [], []) : DState))) :=
    Poly.comp (f := fun x : List Bool × DState => x.1.foldl (fun b a => dstep b a) x.2) hQ
      (Poly.pair Poly.identity (OAI.MetricKMedian.Binary.Automatic.Poly.const _))
  have h3 := snd_comp (snd_comp (snd_comp h2))
  exact h3

end AbelianCayleyHDX.XP


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XK

open Matrix

variable {M : ℕ}

/-! ### Boolean-list implementation -/

def toV (M : ℕ) (l : List Bool) : V M := fun i => if l.getD i false then 1 else 0

def xorv (a b : List Bool) : List Bool := (a.zip b).map (fun p => xor p.1 p.2)

def dotB (a b : List Bool) : Bool :=
  decide (((a.zip b).filter (fun p => p.1 && p.2)).length % 2 = 1)

def kstepB (h : List Bool) (K : List (List Bool)) : List (List Bool) :=
  K.map (fun k => if dotB h k then xorv k (K.getD (K.findIdx (fun k => dotB h k)) []) else k)

def K0B (M : ℕ) : List (List Bool) :=
  (List.range M).map (fun i => (List.range M).map (fun c => decide (c = i)))

def kernelB (M : ℕ) (rows : List (List Bool)) : List (List Bool) :=
  rows.foldl (fun K h => kstepB h K) (K0B M)

def nzB (l : List Bool) : Bool := !((l.filter (fun b => b)).isEmpty)

def basisB (M : ℕ) (rows : List (List Bool)) : List (List Bool) := (kernelB M rows).filter nzB

/-! ### Correspondence -/

lemma toV_nil : toV M [] = 0 := by funext i; simp [toV]

lemma getD_eq (l : List Bool) (hl : l.length = M) (i : Fin M) : l.getD i false = l[i.1]'(by omega) := by
  rw [List.getD_eq_getElem]

lemma getD_xorv {a b : List Bool} (ha : a.length = M) (hb : b.length = M) {i : ℕ} (hi : i < M) :
    (xorv a b).getD i false = xor (a.getD i false) (b.getD i false) := by
  rw [List.getD_eq_getElem _ _ (by simp [xorv, ha, hb]; omega), List.getD_eq_getElem _ _ (by omega),
    List.getD_eq_getElem _ _ (by omega)]
  simp [xorv]

lemma toV_xorv {a b : List Bool} (ha : a.length = M) (hb : b.length = M) :
    toV M (xorv a b) = toV M a + toV M b := by
  funext i
  simp only [toV, Pi.add_apply, getD_xorv ha hb i.2]
  cases a.getD i false <;> cases b.getD i false <;> decide

lemma xorv_length {a b : List Bool} (ha : a.length = M) (hb : b.length = M) :
    (xorv a b).length = M := by simp [xorv, ha, hb]

lemma natCast_z2 (n : ℕ) : ((n : ℕ) : ZMod 2) = if n % 2 = 1 then 1 else 0 := by
  rw [← ZMod.natCast_mod]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> rw [h] <;> simp

lemma dotB_eq {a b : List Bool} (ha : a.length = M) (hb : b.length = M) :
    dotB a b = decide (toV M a ⬝ᵥ toV M b ≠ 0) := by
  have hA : a = List.ofFn (fun i : Fin M => a[i.1]'(by omega)) := by
    apply List.ext_getElem (by simp [ha]); intro n h1 h2; simp
  have hB : b = List.ofFn (fun i : Fin M => b[i.1]'(by omega)) := by
    apply List.ext_getElem (by simp [hb]); intro n h1 h2; simp
  have hzip : a.zip b = List.ofFn (fun i : Fin M => (a[i.1]'(by omega), b[i.1]'(by omega))) := by
    apply List.ext_getElem (by simp [ha, hb]); intro n h1 h2; simp
  have hcount : ((a.zip b).filter (fun p => p.1 && p.2)).length =
      (Finset.univ.filter fun i : Fin M => (a[i.1]'(by omega) && b[i.1]'(by omega)) = true).card := by
    rw [hzip, OAI.MetricKMedian.EncodingLists.length_filter_ofFn]
  have hdot : toV M a ⬝ᵥ toV M b =
      (((Finset.univ.filter fun i : Fin M => (a[i.1]'(by omega) && b[i.1]'(by omega)) = true).card
        : ℕ) : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    unfold dotProduct toV
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [getD_eq a ha i, getD_eq b hb i]
    cases a[i.1] <;> cases b[i.1] <;> simp
  unfold dotB
  rw [hcount, hdot, natCast_z2]
  generalize (Finset.univ.filter fun i : Fin M => (a[i.1]'(by omega) && b[i.1]'(by omega)) = true).card = c
  by_cases h : c % 2 = 1 <;> simp [h]

lemma toV_ofFn_single (i : ℕ) (hi : i < M) :
    toV M ((List.range M).map (fun c => decide (c = i))) = Pi.single ⟨i, hi⟩ 1 := by
  funext c
  simp only [toV]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h : c.1 = i
  · have : c = ⟨i, hi⟩ := Fin.ext h
    subst this; simp
  · have : c ≠ ⟨i, hi⟩ := fun h' => h (by rw [h'])
    simp [h, this]

lemma K0B_spec : (K0B M).map (toV M) = K0 M ∧ ∀ k ∈ K0B M, k.length = M := by
  refine ⟨?_, ?_⟩
  · apply List.ext_getElem (by simp [K0B, K0])
    intro n h1 h2
    have hn : n < M := by simpa [K0B] using h1
    simp only [K0B, K0, List.getElem_map, List.getElem_range, List.getElem_finRange]
    rw [toV_ofFn_single n hn]
    rfl
  · intro k hk
    simp only [K0B, List.mem_map, List.mem_range] at hk
    obtain ⟨i, -, rfl⟩ := hk
    simp

lemma findIdx_congr' {α : Type*} {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.findIdx p = l.findIdx q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.findIdx_cons, List.findIdx_cons, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

lemma kstepB_spec {h : List Bool} {K : List (List Bool)} (hh : h.length = M)
    (hK : ∀ k ∈ K, k.length = M) :
    (kstepB h K).map (toV M) = kstep (toV M h) (K.map (toV M)) ∧
      ∀ k ∈ kstepB h K, k.length = M := by
  have hd : ∀ k ∈ K, dotB h k = decide (toV M h ⬝ᵥ toV M k ≠ 0) :=
    fun k hk => dotB_eq hh (hK k hk)
  set l0 := K.findIdx (fun k => dotB h k) with hl0
  have hl0' : (K.map (toV M)).findIdx (fun k => decide (toV M h ⬝ᵥ k ≠ 0)) = l0 := by
    rw [List.findIdx_map, hl0]
    exact (findIdx_congr' (fun k hk => (hd k hk).symm))
  set kp := K.getD l0 [] with hkp
  have hkpV : (K.map (toV M)).getD l0 0 = toV M kp := by
    rw [hkp, ← toV_nil (M := M), List.getD_map]
  -- if some entry pairs to `1`, the pivot is a genuine entry
  have hpiv : ∀ k ∈ K, dotB h k = true → kp ∈ K := by
    intro k hk hdk
    have hlt : l0 < K.length := List.findIdx_lt_length_of_exists ⟨k, hk, hdk⟩
    rw [hkp, List.getD_eq_getElem _ _ hlt]; exact List.getElem_mem _
  refine ⟨?_, ?_⟩
  · unfold kstep kstepB
    rw [hl0', hkpV, List.map_map, List.map_map]
    apply List.map_congr_left
    intro k hk
    simp only [Function.comp]
    rw [← hl0, ← hkp]
    by_cases hdk : dotB h k = true
    · rw [if_pos hdk, toV_xorv (hK k hk) (hK kp (hpiv k hk hdk))]
      have : toV M h ⬝ᵥ toV M k = 1 := by
        rw [hd k hk] at hdk
        exact (z2_cases _).resolve_left (by simpa using hdk)
      rw [this, one_smul]
    · rw [if_neg hdk]
      have : toV M h ⬝ᵥ toV M k = 0 := by
        rw [hd k hk] at hdk; simpa using hdk
      rw [this, zero_smul, add_zero]
  · intro k hk
    simp only [kstepB, List.mem_map] at hk
    obtain ⟨k', hk', rfl⟩ := hk
    rw [← hl0, ← hkp]
    split_ifs with hdk
    · exact xorv_length (hK k' hk') (hK kp (hpiv k' hk' hdk))
    · exact hK k' hk'

lemma fold_spec (rows : List (List Bool)) (hrows : ∀ r ∈ rows, r.length = M)
    (K : List (List Bool)) (hK : ∀ k ∈ K, k.length = M) :
    (rows.foldl (fun K h => kstepB h K) K).map (toV M) =
      (rows.map (toV M)).foldl (fun K h => kstep h K) (K.map (toV M)) ∧
    ∀ k ∈ rows.foldl (fun K h => kstepB h K) K, k.length = M := by
  induction rows generalizing K with
  | nil => exact ⟨rfl, hK⟩
  | cons r rows ih =>
    have hr := hrows r List.mem_cons_self
    obtain ⟨e, hl⟩ := kstepB_spec hr hK
    obtain ⟨e', hl'⟩ := ih (fun r' hr' => hrows r' (List.mem_cons_of_mem _ hr')) _ hl
    refine ⟨?_, hl'⟩
    rw [List.foldl_cons, e', e]; rfl

lemma nzB_eq {k : List Bool} (hk : k.length = M) : nzB k = decide (toV M k ≠ 0) := by
  unfold nzB
  by_cases h : ∃ i, ∃ hi : i < k.length, k[i] = true
  · obtain ⟨i, hi, hki⟩ := h
    have h1 : (k.filter (fun b => b)).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff_exists_mem]
      exact ⟨true, List.mem_filter.2 ⟨by rw [← hki]; exact List.getElem_mem _, rfl⟩⟩
    have h2 : toV M k ≠ 0 := by
      intro h0
      have := congrFun h0 ⟨i, by omega⟩
      simp only [toV, Pi.zero_apply] at this
      rw [List.getD_eq_getElem _ _ hi, hki] at this
      simp at this
    rw [h1]; simp [h2]
  · push Not at h
    have h1 : (k.filter (fun b => b)).isEmpty = true := by
      rw [List.isEmpty_iff, List.filter_eq_nil_iff]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
      simpa using h i hi
    have h2 : toV M k = 0 := by
      funext i
      simp only [toV, Pi.zero_apply]
      rw [List.getD_eq_getElem _ _ (by omega)]
      simp [h i.1 (by omega)]
    rw [h1]; simp [h2]

theorem basisB_spec {R : ℕ} (H : Matrix (Fin R) (Fin M) (ZMod 2)) (rows : List (List Bool))
    (hrows : ∀ r ∈ rows, r.length = M) (hH : rows.map (toV M) = List.ofFn H) :
    (basisB M rows).map (toV M) = basisList H ∧ ∀ k ∈ basisB M rows, k.length = M := by
  obtain ⟨e, hl⟩ := fold_spec rows hrows (K0B M) K0B_spec.2
  refine ⟨?_, fun k hk => hl k (List.mem_filter.1 hk).1⟩
  unfold basisB basisList kernelList kernelB
  rw [← hH, ← K0B_spec.1, ← e, List.filter_map]
  congr 1
  apply List.filter_congr
  intro k hk
  simp only [Function.comp]
  rw [nzB_eq (hl k hk)]

/-! ### Polynomial time -/

section PolyK
open AbelianCayleyHDX.XP

variable {γ α β : Type} [Coding γ] [Coding α] [Coding β]

@[fun_prop] theorem zip_comp [Inhabited α] [Inhabited β] {f : γ → List α} {g : γ → List β}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => (f x).zip (g x)) :=
  Poly.comp Poly.list_zip (Poly.pair hf hg)

@[fun_prop] theorem xor_comp {f g : γ → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xor (f x) (g x)) :=
  Poly.comp (f := fun x : Bool × Bool => xor x.1 x.2)
    (⟨PolyProgram.boolXor⟩ : Poly (fun x : Bool × Bool => xor x.1 x.2)) (Poly.pair hf hg)

@[fun_prop] theorem and_comp {f g : γ → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x && g x) := Poly.comp Poly.bool_and (Poly.pair hf hg)

@[fun_prop] theorem not_comp {f : γ → Bool} (hf : Poly f) : Poly (fun x => !(f x)) :=
  Poly.comp Poly.bool_not hf

@[fun_prop] theorem isEmpty_comp {f : γ → List α} (hf : Poly f) : Poly (fun x => (f x).isEmpty) :=
  Poly.comp Poly.list_empty hf

@[fun_prop] theorem nat_mod_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x % g x) :=
  Poly.comp (⟨PolyProgram.natMod⟩ : Poly (fun x : ℕ × ℕ => x.1 % x.2)) (Poly.pair hf hg)

@[fun_prop] theorem nat_lt_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => decide (f x < g x)) := Poly.comp Poly.nat_lt (Poly.pair hf hg)

@[fun_prop] theorem nat_mul_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x * g x) := Poly.comp Poly.nat_mul (Poly.pair hf hg)

@[fun_prop] theorem getD_comp [Inhabited α] (a0 : α) {xs : γ → List α} {i : γ → ℕ} (hx : Poly xs)
    (hi : Poly i) : Poly (fun x => (xs x).getD (i x) a0) := by
  have := Poly.list_getD_comp a0 hx hi
  convert this using 2 with x
  rw [List.getD_eq_getElem?_getD]

@[fun_prop] theorem findIdx_ctx [Inhabited γ] [Inhabited β] {f : γ → β → Bool} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).findIdx (f x)) := Poly.list_findIdx hf ha

@[fun_prop] theorem filter_ctx [Inhabited γ] [Inhabited β] {f : γ → β → Bool} {as : γ → List β}
    (hf : Poly (fun x : γ × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).filter (f x)) := Poly.list_filter hf ha

@[fun_prop] theorem dotB_comp {f g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => dotB (f x) (g x)) := by unfold dotB; fun_prop

@[fun_prop] theorem xorv_comp {f g : γ → List Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => xorv (f x) (g x)) := by unfold xorv; fun_prop

end PolyK

lemma enc_bools (l : List Bool) :
    ((OAI.MetricKMedian.Binary.Automatic.enc : List Bool → List Bool) l).length = 3 * l.length :=
  AbelianCayleyHDX.XP.encList_bool_length l

lemma enc_map_le (K : List (List Bool)) (f : List Bool → List Bool)
    (hf : ∀ k ∈ K, (f k).length ≤ k.length) :
    ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) (K.map f)).length ≤
      ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) K).length := by
  induction K with
  | nil => simp
  | cons k K ih =>
    change (encodeList (encodeList encodeBool) (f k :: K.map f)).length ≤
      (encodeList (encodeList encodeBool) (k :: K)).length
    rw [EncodedList.cons_length, EncodedList.cons_length]
    have h1 := hf k List.mem_cons_self
    have h2 := ih (fun k' hk' => hf k' (List.mem_cons_of_mem _ hk'))
    change _ ≤ (encodeList (encodeList encodeBool) K).length at h2
    rw [AbelianCayleyHDX.XP.encList_bool_length, AbelianCayleyHDX.XP.encList_bool_length]
    have : (encodeList (encodeList encodeBool) (K.map f)).length ≤
        (encodeList (encodeList encodeBool) K).length := h2
    omega

lemma kstepB_size (K : List (List Bool)) (h : List Bool) :
    ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) (kstepB h K)).length ≤
      ((OAI.MetricKMedian.Binary.Automatic.enc : List (List Bool) → List Bool) K).length +
        0 * (2 * ((OAI.MetricKMedian.Binary.Automatic.enc : List Bool → List Bool) h).length + 1) := by
  rw [zero_mul, add_zero]
  apply enc_map_le
  intro k _
  by_cases hd : dotB h k = true
  · rw [if_pos hd]; simp [xorv]
  · rw [if_neg hd]

def K0B' (r : List ℕ) : List (List Bool) := r.map (fun i => r.map (fun c => decide (c = i)))

def basisB' (r : List ℕ) (rows : List (List Bool)) : List (List Bool) :=
  (rows.foldl (fun K h => kstepB h K) (K0B' r)).filter nzB

lemma basisB'_range (M : ℕ) (rows : List (List Bool)) : basisB' (List.range M) rows = basisB M rows := rfl

theorem poly_basisB' : Poly (fun x : List ℕ × List (List Bool) => basisB' x.1 x.2) := by
  have hstep : Poly (fun x : List (List Bool) × List Bool => kstepB x.2 x.1) := by
    unfold kstepB; fun_prop
  let Q := (hstep.program).listFoldLinear ([] : List Bool) 0 (fun b a => kstepB_size b a)
  have hQ : Poly (fun x : List (List Bool) × List (List Bool) =>
      x.1.foldl (fun b a => kstepB a b) x.2) := ⟨Q⟩
  have hK0 : Poly (fun x : List ℕ × List (List Bool) => K0B' x.1) := by unfold K0B'; fun_prop
  have h2 : Poly (fun x : List ℕ × List (List Bool) =>
      x.2.foldl (fun b a => kstepB a b) (K0B' x.1)) :=
    Poly.comp (f := fun x : List (List Bool) × List (List Bool) =>
      x.1.foldl (fun b a => kstepB a b) x.2) hQ (Poly.pair Poly.snd hK0)
  unfold basisB' nzB
  fun_prop

end AbelianCayleyHDX.XK


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.XH

open AbelianCayleyHDX.XP AbelianCayleyHDX.XK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F)) (h : ℕ)

/-! ### Ranges and powers of two from the pad -/

def rgP (pad : List Bool) (n : ℕ) : List ℕ := (List.range pad.length).filter (fun i => decide (i < n))

lemma rgP_eq (pad : List Bool) {n : ℕ} (hn : n ≤ pad.length) : rgP pad n = List.range n := by
  unfold rgP
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [hm, List.range_add, List.filter_append, List.filter_eq_self.2 (fun i hi => by simpa using hi),
    List.filter_eq_nil_iff.2 (fun i hi => by
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨j, -, rfl⟩ := hi; simp), List.append_nil]

def pw2 (pad : List Bool) (m : ℕ) : ℕ := Word.value ((rgP pad m).map (fun _ => false) ++ [true])

lemma pw2_eq (pad : List Bool) {m : ℕ} (hm : m ≤ pad.length) : pw2 pad m = 2 ^ m := by
  unfold pw2; rw [rgP_eq pad hm, List.map_const', List.length_range, AbelianCayleyHDX.XE.value_pow]

/-! ### The post-processor -/

def gT (x : List Bool × List Bool) : ℕ := (decTokens x.1).getD 0 0
def gN (x : List Bool × List Bool) : ℕ := (decTokens x.1).getD 1 0
def gRC (x : List Bool × List Bool) : List (List ℕ) :=
  (rgP x.2 (gN x)).map (fun i => (rgP x.2 (gT x)).map (fun k =>
    (decTokens x.1).getD (2 + i * (gT x + 1) + 1 + k) 0))
def gPows (x : List Bool × List Bool) : List ℕ := (rgP x.2 (gT x)).map (fun k => pw2 x.2 (2 * h * k))
def gQt (x : List Bool × List Bool) : ℕ := pw2 x.2 (2 * h * gT x)
def gM (x : List Bool × List Bool) : ℕ := (Fintype.card F - 1) * gQt h x
def gR (x : List Bool × List Bool) : ℕ :=
  gN x * (Fintype.card F - 1) * (gQt h x * (AbelianCayleyHDX.LF F).card)
noncomputable def gRows (x : List Bool × List Bool) : List (List Bool) :=
  (rgP x.2 (gR (F := F) h x)).map (fun ρ => (rgP x.2 (gM (F := F) h x)).map (fun ω =>
    bitN enc (rgP x.2 (gT x)) (gRC x) (gPows h x) (gQt h x) ρ ω))
noncomputable def Gpost (x : List Bool × List Bool) : List Bool :=
  encNatB (gR (F := F) h x) ++ encNatB (gM (F := F) h x) ++
    (encNatB (gRows enc h x).length ++ (gRows enc h x).flatMap (fun r => encNatB r.length ++ r.flatMap cbit))

section PolyH
variable {γ : Type} [Coding γ] [Inhabited γ]

@[fun_prop] theorem nat_div_comp {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => f x / g x) :=
  Poly.comp (f := fun x : ℕ × ℕ => x.1 / x.2)
    (⟨PolyProgram.natDiv⟩ : Poly (fun x : ℕ × ℕ => x.1 / x.2)) (Poly.pair hf hg)

@[fun_prop] theorem decTokens_comp' {f : γ → List Bool} (hf : Poly f) :
    Poly (fun x => decTokens (f x)) := Poly.comp poly_decTokens hf

@[fun_prop] theorem rgP_comp {f : γ → List Bool} {g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => rgP (f x) (g x)) := by unfold rgP; fun_prop

@[fun_prop] theorem pw2_comp {f : γ → List Bool} {g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => pw2 (f x) (g x)) := by unfold pw2; fun_prop

@[fun_prop] theorem uc_comp {f : γ → ℕ} (hf : Poly f) : Poly (fun x => uc enc (f x)) := by
  have : (fun x => uc enc (f x)) =
      fun x => if decide (f x < code enc 0) = true then f x else f x + 1 := by
    funext x; unfold uc; simp
  rw [this]; fun_prop

@[fun_prop] theorem tab_comp {T : List (List ℕ)} {f g : γ → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun x => tab T (f x) (g x)) := by unfold tab; fun_prop

@[fun_prop] theorem bitN_comp {fQt fρ fω : γ → ℕ} {ft : γ → List ℕ} {frc : γ → List (List ℕ)}
    {fp : γ → List ℕ} (h1 : Poly ft) (h2 : Poly frc) (h3 : Poly fp) (h4 : Poly fQt) (h5 : Poly fρ) (h6 : Poly fω) :
    Poly (fun x => bitN enc (ft x) (frc x) (fp x) (fQt x) (fρ x) (fω x)) := by
  unfold bitN; simp only []; fun_prop

end PolyH

theorem poly_Gpost : Poly (fun x : List Bool × List Bool => Gpost enc h x) := by
  unfold Gpost gRows gR gM gQt gPows gRC gN gT; fun_prop

end AbelianCayleyHDX.XH


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates
open ReplParity (Vec)

namespace AbelianCayleyHDX.XR

open AbelianCayleyHDX.XK AbelianCayleyHDX.XP

variable {R M : ℕ}

/-- The token stream of the machine output. -/
def toks (H : Matrix (Fin R) (Fin M) (ZMod 2)) : List ℕ :=
  [R, M, R] ++ (List.ofFn H).flatMap (fun row => M :: (List.ofFn row).map ZMod.val)

lemma W_eq (H : Matrix (Fin R) (Fin M) (ZMod 2)) :
    encNat R ++ encNat M ++ encList encVec (List.ofFn H) = (toks H).flatMap encNat := by
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold toks encList
  rw [hl]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  congr 3
  rw [List.flatMap_assoc]
  refine List.flatMap_congr (fun row _ => ?_)
  unfold encVec encList
  rw [List.length_ofFn, List.flatMap_cons, List.flatMap_map]
  rfl

lemma getD_flatMap_uniform {α : Type*} (L : List α) (f : α → List ℕ) (k : ℕ)
    (hf : ∀ x, (f x).length = k) {r t : ℕ} (hr : r < L.length) (ht : t < k) :
    (L.flatMap f).getD (r * k + t) 0 = (f L[r]).getD t 0 := by
  induction L generalizing r with
  | nil => simp at hr
  | cons x L ih =>
    rw [List.flatMap_cons]
    rcases r with _ | r
    · simp only [zero_mul, zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by rw [hf]; exact ht)]
    · rw [List.getD_append_right _ _ _ _ (by rw [hf]; nlinarith)]
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hr
      rw [hf, show (r + 1) * k + t - k = r * k + t by rw [add_mul, one_mul]; omega, ih hr]
      rfl

lemma toks_length (H : Matrix (Fin R) (Fin M) (ZMod 2)) : (toks H).length = 3 + R * (M + 1) := by
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold toks
  simp only [List.length_append, List.length_flatMap, List.length_cons, List.length_map,
    List.length_ofFn]
  rw [List.map_const', List.sum_replicate, hl, smul_eq_mul]
  simp

lemma toks_entry (H : Matrix (Fin R) (Fin M) (ZMod 2)) (r : Fin R) (c : Fin M) :
    (toks H).getD (3 + r.1 * (M + 1) + 1 + c.1) 0 = (H r c).val := by
  have hl : (List.ofFn H).length = R := List.length_ofFn
  unfold toks
  rw [show 3 + r.1 * (M + 1) + 1 + c.1 = 3 + (r.1 * (M + 1) + (1 + c.1)) by ring,
    List.getD_append_right _ _ _ _ (by simp), show [R, M, R].length = 3 from rfl,
    Nat.add_sub_cancel_left,
    getD_flatMap_uniform _ _ (M + 1) (fun row => by simp) (by rw [hl]; exact r.2) (by omega)]
  have e : (List.ofFn H)[r.1]'(by rw [hl]; exact r.2) = H r := List.getElem_ofFn _
  rw [e, show 1 + c.1 = c.1 + 1 by ring, List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- The post-processor's view of a row. -/
def bitsOfRow (row : Fin M → ZMod 2) : List Bool := (List.ofFn row).map (fun x => decide (x = 1))

lemma getD_bitsOfRow (row : Fin M → ZMod 2) (c : Fin M) :
    (bitsOfRow row).getD c false = decide (row c = 1) := by
  unfold bitsOfRow
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma toV_bitsOfRow (row : Fin M → ZMod 2) : toV M (bitsOfRow row) = row := by
  funext c
  simp only [toV, getD_bitsOfRow]
  rcases z2_cases (row c) with h | h <;> rw [h] <;> simp

lemma bitsOfRow_length (row : Fin M → ZMod 2) : (bitsOfRow row).length = M := by simp [bitsOfRow]

/-- Range below `n`, computed from a long enough list. -/
def rg (L : List ℕ) (n : ℕ) : List ℕ := (List.range L.length).filter (fun i => decide (i < n))

lemma rg_eq (L : List ℕ) {n : ℕ} (hn : n ≤ L.length) : rg L n = List.range n := by
  unfold rg
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  rw [hm, List.range_add, List.filter_append, List.filter_eq_self.2 (fun i hi => by simpa using hi),
    List.filter_eq_nil_iff.2 (fun i hi => by
      simp only [List.mem_map, List.mem_range] at hi
      obtain ⟨j, -, rfl⟩ := hi; simp), List.append_nil]

end AbelianCayleyHDX.XR


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.XH

open AbelianCayleyHDX.XP AbelianCayleyHDX.XK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F)) (h : ℕ)
variable {t : ℕ} {D : Finset (AbelianCayleyHDX.PG t F)} {reps : List (Fin t → F)}

/-- The tokens of the direction-set machine's output. -/
def htoks (t : ℕ) (reps : List (Fin t → F)) : List ℕ :=
  [t, reps.length] ++ reps.flatMap (fun a => t :: (List.ofFn a).map (code enc))

lemma hW_eq (reps : List (Fin t → F)) :
    encNat t ++ encList (AbelianCayleyHDX.encFVec enc) reps = (htoks enc t reps).flatMap encNat := by
  unfold htoks encList
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.append_assoc]
  congr 2
  rw [List.flatMap_assoc]
  refine List.flatMap_congr (fun a _ => ?_)
  unfold AbelianCayleyHDX.encFVec encList
  rw [List.length_ofFn, List.flatMap_cons, List.flatMap_map]
  rfl

lemma htoks_entry (reps : List (Fin t → F)) {i k : ℕ} (hi : i < reps.length) (hk : k < t) :
    (htoks enc t reps).getD (2 + i * (t + 1) + 1 + k) 0 = code enc (reps[i] ⟨k, hk⟩) := by
  unfold htoks
  rw [show 2 + i * (t + 1) + 1 + k = 2 + (i * (t + 1) + (k + 1)) by ring,
    List.getD_append_right _ _ _ _ (by simp), show [t, reps.length].length = 2 from rfl,
    Nat.add_sub_cancel_left,
    AbelianCayleyHDX.XR.getD_flatMap_uniform _ _ (t + 1) (fun a => by simp) hi (by omega),
    List.getD_cons_succ, List.getD_eq_getElem _ _ (by simp; exact hk)]
  simp

lemma hQ (hF : Fintype.card F = (2 ^ h) ^ 2) : Fintype.card F = 2 ^ (2 * h) := by
  rw [hF, ← pow_mul, mul_comm]

lemma hM (hF : Fintype.card F = (2 ^ h) ^ 2) (t : ℕ) :
    (Fintype.card F - 1) * Fintype.card F ^ t = ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t) := by
  rw [hF, pow_mul]

noncomputable def eΩ (hF : Fintype.card F = (2 ^ h) ^ 2) (t : ℕ) :
    AbelianCayleyHDX.Omega F t ≃ Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t)) :=
  (eΩ0 enc t).trans (finCongr (hM h hF t))

def Rn (t : ℕ) (reps : List (Fin t → F)) : ℕ :=
  reps.length * (Fintype.card F - 1) * (Fintype.card F ^ t * (AbelianCayleyHDX.LF F).card)

theorem Gpost_eq (hF : Fintype.card F = (2 ^ h) ^ 2) (hR : RepsSpec D reps) (pad : List Bool)
    (h1 : Rn t reps ≤ pad.length) (h2 : (Fintype.card F - 1) * Fintype.card F ^ t ≤ pad.length)
    (h3 : reps.length ≤ pad.length) (h4 : 2 * h * t ≤ pad.length) (h5 : t ≤ pad.length) :
    Gpost enc h (encNat t ++ encList (AbelianCayleyHDX.encFVec enc) reps, pad) =
      encNat (Rn t reps) ++ encNat (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t)) ++
        encList encVec (List.ofFn ((AbelianCayleyHDX.HD D).reindex (eR0 enc hR) (eΩ enc h hF t))) := by
  set x := (encNat t ++ encList (AbelianCayleyHDX.encFVec enc) reps, pad)
  have hdt : decTokens x.1 = htoks enc t reps := by
    simp only [x]; rw [hW_eq, decTokens_flatMap]
  have hT : gT x = t := by unfold gT; rw [hdt]; simp [htoks]
  have hN : gN x = reps.length := by unfold gN; rw [hdt]; simp [htoks]
  have hpw : ∀ k ≤ t, pw2 pad (2 * h * k) = Fintype.card F ^ k := by
    intro k hk
    rw [pw2_eq pad (le_trans (Nat.mul_le_mul_left _ hk) h4), hQ h hF, ← pow_mul]
  have hQt : gQt h x = Fintype.card F ^ t := by unfold gQt; rw [hT]; exact hpw t le_rfl
  have hPows : gPows h x = (List.range t).map (fun k => Fintype.card F ^ k) := by
    unfold gPows; rw [hT]; simp only [x]; rw [rgP_eq pad h5]
    apply List.map_congr_left; intro k hk; exact hpw k (List.mem_range.1 hk).le
  have hpows : ∀ k < t, (gPows h x).getD k 0 = Fintype.card F ^ k := by
    intro k hk; rw [hPows, List.getD_eq_getElem _ _ (by simp; exact hk)]; simp
  have hRC : gRC x = repCodes enc reps := by
    unfold gRC; rw [hT, hN, hdt]; simp only [x]; rw [rgP_eq pad h3, rgP_eq pad h5]
    apply List.ext_getElem (by simp [repCodes])
    intro i hi1 hi2
    have hi : i < reps.length := by simpa using hi1
    simp only [List.getElem_map, List.getElem_range, repCodes]
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    have hk : k < t := by simpa using hk1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [htoks_entry enc reps hi hk]
  have hMx : gM (F := F) h x = (Fintype.card F - 1) * Fintype.card F ^ t := by unfold gM; rw [hQt]
  have hRx : gR (F := F) h x = Rn t reps := by unfold gR Rn; rw [hQt, hN]
  set Mt := (AbelianCayleyHDX.HD D).reindex (eR0 enc hR) (eΩ enc h hF t) with hMt
  have hlenM : (List.ofFn Mt).length = Rn t reps := List.length_ofFn
  have hgetM : ∀ ρ (hρ : ρ < (List.ofFn Mt).length), (List.ofFn Mt)[ρ] = Mt ⟨ρ, by rwa [hlenM] at hρ⟩ :=
    fun ρ hρ => List.getElem_ofFn _
  have hrows : gRows enc h x = (List.ofFn Mt).map AbelianCayleyHDX.XE.bitsOf := by
    unfold gRows
    rw [hRx, hMx, hRC, hT]
    simp only [x]
    rw [rgP_eq pad h1, rgP_eq pad h2, rgP_eq pad h5]
    apply List.ext_getElem (by rw [List.length_map, List.length_range, List.length_map, hlenM])
    intro ρ hρ1 hρ2
    have hρ : ρ < Rn t reps := by simpa using hρ1
    simp only [List.getElem_map, List.getElem_range, AbelianCayleyHDX.XE.bitsOf]
    rw [hgetM ρ (by rw [hlenM]; exact hρ)]
    apply List.ext_getElem (by simp [hM h hF t])
    intro ω hω1 hω2
    have hω : ω < (Fintype.card F - 1) * Fintype.card F ^ t := by simpa using hω1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, hMt, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    rw [hQt, bitN_eq enc hR ⟨ρ, hρ⟩ ⟨ω, hω⟩ (gPows h x) hpows]
    rfl
  unfold Gpost
  rw [hRx, hMx, hrows, ← AbelianCayleyHDX.XE.encNat_eq, ← AbelianCayleyHDX.XE.encNat_eq, hM h hF t]
  unfold encList
  rw [AbelianCayleyHDX.XE.encNat_eq, List.length_map, List.flatMap_map, hlenM]
  simp only [AbelianCayleyHDX.XE.encNat_eq]
  congr 2
  refine List.flatMap_congr (fun r _ => ?_)
  rw [AbelianCayleyHDX.XE.encVec_eq]
  unfold vecB AbelianCayleyHDX.XE.bitsOf
  rw [List.length_map, List.length_ofFn]

end AbelianCayleyHDX.XH


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

namespace AbelianCayleyHDX.XL

open AbelianCayleyHDX.XP

/-- A loop run as a time-bounded machine computation, for arbitrary bounds. -/
theorem loop_outputs {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β ⊕ α}
    (P : PolyProgram ea (encodeLoop ea eb) f) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) :
    Nonempty (Turing.TM2OutputsInTime (Loop.machine P.machine).tm (ea a) (some (eb b))
      (n * P.passTime S)) := by
  obtain ⟨t, ht, htrace⟩ := P.run_loop h
  exact ⟨⟨⟨t, htrace.iterate_eq⟩, ht⟩⟩

lemma quote_eq (L : List Bool) : quote L = L.flatMap (fun b => [true, b]) ++ [false] := by
  induction L with
  | nil => rfl
  | cons b L ih => simp [quote, ih]

section
variable {γ : Type} [Coding γ] [Inhabited γ]

@[fun_prop] theorem quote_comp {f : γ → List Bool} (hf : Poly f) : Poly (fun x => quote (f x)) := by
  have : (fun x => quote (f x)) = fun x => (f x).flatMap (fun b => [true, b]) ++ [false] := by
    funext x; exact quote_eq _
  rw [this]; fun_prop

/-- The encoding of a value, as a word. -/
theorem enc_poly : Poly (fun x : γ => (enc x : List Bool)) :=
  ⟨BooleanLists.packProgram.recode (enc : γ → List Bool) (fun _ => rfl) (fun _ => rfl)⟩

@[fun_prop] theorem enc_comp {δ : Type} [Coding δ] [Inhabited δ] {f : γ → δ} (hf : Poly f) :
    Poly (fun x => (enc (f x) : List Bool)) := Poly.comp enc_poly hf

end

/-! ### The padding loop -/

abbrev PState := List Bool × ℕ × List Bool

def padBody (s : PState) : (List Bool × List Bool) ⊕ PState :=
  if s.2.1 = 0 then Sum.inl (s.1, s.2.2) else Sum.inr (s.1, s.2.1 - 1, s.2.2 ++ s.2.2)

def padBodyW (s : PState) : List Bool :=
  if decide (s.2.1 = 0) = true then false :: (quote s.1 ++ s.2.2)
  else true :: (enc ((s.1, s.2.1 - 1, s.2.2 ++ s.2.2) : PState) : List Bool)

lemma padBodyW_eq (s : PState) :
    padBodyW s = encodeLoop (enc : PState → List Bool) (encodePair id id) (padBody s) := by
  unfold padBodyW padBody
  by_cases h : s.2.1 = 0 <;> simp [h, encodeLoop, encodePair]

theorem padProgram : Nonempty (PolyProgram (enc : PState → List Bool)
    (encodeLoop (enc : PState → List Bool) (encodePair id id)) padBody) := by
  have h : Poly (fun s : PState => padBodyW s) := by unfold padBodyW; fun_prop
  let P1 : PolyProgram (enc : PState → List Bool) id (id ∘ padBodyW) :=
    h.program.comp BooleanLists.unpackProgram
  exact ⟨P1.recode id (fun _ => rfl) (fun s => by simp [padBodyW_eq])⟩

def padState (w : List Bool) (c : ℕ) (pad : List Bool) : PState := (w, c, pad)

lemma pad_run (w : List Bool) (S : ℕ) : ∀ (c : ℕ) (pad : List Bool),
    (∀ k ≤ c, (enc (padState w (c - k) (List.replicate (2 ^ k * pad.length) true)) : List Bool).length
      ≤ S) → (∀ x ∈ pad, x = true) →
    BoundedRun (enc : PState → List Bool) padBody S (c + 1) (padState w c pad)
      (w, List.replicate (2 ^ c * pad.length) true) := by
  intro c
  induction c with
  | zero =>
    intro pad hS hpad
    have hp : pad = List.replicate pad.length true := List.eq_replicate_iff.2 ⟨rfl, hpad⟩
    refine BoundedRun.stop ?_ ?_
    · have := hS 0 le_rfl; simpa [← hp] using this
    · simp [padBody, padState, ← hp]
  | succ c ih =>
    intro pad hS hpad
    have hp : pad = List.replicate pad.length true := List.eq_replicate_iff.2 ⟨rfl, hpad⟩
    refine BoundedRun.step ?_ (a' := padState w c (pad ++ pad)) ?_ ?_
    · have := hS 0 (Nat.zero_le _); simpa [← hp] using this
    · simp [padBody, padState]
    · have := ih (pad ++ pad) (fun k hk => by
          have := hS (k + 1) (by omega)
          rw [show c + 1 - (k + 1) = c - k by omega] at this
          rw [List.length_append, show 2 ^ k * (pad.length + pad.length) = 2 ^ (k + 1) * pad.length
            by ring]
          exact this) (fun x hx => by
          rcases List.mem_append.1 hx with h | h <;> exact hpad x h)
      rw [List.length_append, show 2 ^ c * (pad.length + pad.length) = 2 ^ (c + 1) * pad.length
        by ring] at this
      exact this

end AbelianCayleyHDX.XL


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.XH

open AbelianCayleyHDX.XP AbelianCayleyHDX.XK AbelianCayleyHDX.XL

/-! ### Composing machines with Boolean interfaces -/

def composeAux (A B : Turing.TM2ComputableAux Bool Bool) : Turing.TM2ComputableAux Bool Bool :=
  ⟨ShiTM2.comp A.tm B.tm (fun s => B.inputAlphabet.symm (A.outputAlphabet s))
      (B.inputAlphabet.symm false),
    (ShiTM2.compInputAlphabet A.tm B.tm _ _).trans A.inputAlphabet,
    (ShiTM2.compOutputAlphabet A.tm B.tm _ _).trans B.outputAlphabet⟩

theorem outputsWithin_compose {A B : Turing.TM2ComputableAux Bool Bool} {x W V : List Bool}
    {T T' : ℕ} (hA : HMBinPacking.OutputsWithin A x W T)
    (hB : HMBinPacking.OutputsWithin B W V T') :
    HMBinPacking.OutputsWithin (composeAux A B) x V (T + (2 * W.length + 2) + T') := by
  classical
  obtain ⟨h₁⟩ := hA
  obtain ⟨h₂⟩ := hB
  have e : (W.map A.outputAlphabet.symm).map (fun s => B.inputAlphabet.symm (A.outputAlphabet s)) =
      W.map B.inputAlphabet.symm := by
    rw [List.map_map]; congr 1; funext s; simp
  rw [← e] at h₂
  obtain ⟨h⟩ := ShiTM.comp_outputsInTime (inst := ShiTM2.compKDecEq A.tm B.tm) A.tm B.tm _ _ _ _ _ _ _
    h₁ h₂
  rw [List.length_map] at h
  exact ⟨h⟩

/-- A word-to-word program as a machine. -/
def auxOf {f : List Bool → List Bool} (P : PolyProgram id id f) : Turing.TM2ComputableAux Bool Bool :=
  ⟨P.machine.tm, Equiv.refl _, Equiv.refl _⟩

theorem outputsWithin_auxOf {f : List Bool → List Bool} (P : PolyProgram id id f) (w : List Bool) :
    HMBinPacking.OutputsWithin (auxOf P) w (f w) (P.time.eval w.length) := by
  have h := P.outputs w
  unfold HMBinPacking.OutputsWithin auxOf
  change Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w)
    (some (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (f w))) _)
  rw [show List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) w = w from List.map_id w,
    show List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (f w) = f w from
      List.map_id _]
  exact ⟨h⟩

/-- A raw loop as a machine. -/
def auxLoop {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {g : α → β ⊕ α}
    (P : PolyProgram ea (encodeLoop ea eb) g) : Turing.TM2ComputableAux Bool Bool :=
  ⟨(Loop.machine P.machine).tm, Equiv.refl _, Equiv.refl _⟩

theorem outputsWithin_auxLoop {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {g : α → β ⊕ α} (P : PolyProgram ea (encodeLoop ea eb) g) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea g S n a b) :
    HMBinPacking.OutputsWithin (auxLoop P) (ea a) (eb b) (n * P.passTime S) := by
  obtain ⟨h⟩ := loop_outputs P h
  unfold HMBinPacking.OutputsWithin auxLoop
  change Nonempty (Turing.TM2OutputsInTime (Loop.machine P.machine).tm
    (List.map (⇑(Equiv.refl ((Loop.machine P.machine).tm.Γ (Loop.machine P.machine).tm.k₀)).symm) (ea a))
    (some (List.map (⇑(Equiv.refl ((Loop.machine P.machine).tm.Γ
      (Loop.machine P.machine).tm.k₁)).symm) (eb b))) _)
  rw [show ∀ l : List Bool, List.map (⇑(Equiv.refl ((Loop.machine P.machine).tm.Γ
      (Loop.machine P.machine).tm.k₀)).symm) l = l from fun l => List.map_id l,
    show ∀ l : List Bool, List.map (⇑(Equiv.refl ((Loop.machine P.machine).tm.Γ
      (Loop.machine P.machine).tm.k₁)).symm) l = l from fun l => List.map_id l]
  exact ⟨h⟩

end AbelianCayleyHDX.XH

namespace AbelianCayleyHDX.XH

open AbelianCayleyHDX.XP AbelianCayleyHDX.XK AbelianCayleyHDX.XL

/-- A program with raw output as a machine. -/
def auxOf' {α : Type} {ea : α → List Bool} {f : α → List Bool} (P : PolyProgram ea id f) :
    Turing.TM2ComputableAux Bool Bool :=
  ⟨P.machine.tm, Equiv.refl _, Equiv.refl _⟩

theorem outputsWithin_auxOf' {α : Type} {ea : α → List Bool} {f : α → List Bool}
    (P : PolyProgram ea id f) (a : α) :
    HMBinPacking.OutputsWithin (auxOf' P) (ea a) (f a) (P.time.eval (ea a).length) := by
  have h := P.outputs a
  unfold HMBinPacking.OutputsWithin auxOf'
  change Nonempty (Turing.TM2OutputsInTime P.machine.tm
    (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) (ea a))
    (some (List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (f a))) _)
  rw [show List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₀)).symm) (ea a) = ea a from
      List.map_id _,
    show List.map (⇑(Equiv.refl (P.machine.tm.Γ P.machine.tm.k₁)).symm) (f a) = f a from
      List.map_id _]
  exact ⟨h⟩

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F)) (h : ℕ)

/-- The number of doubling steps. -/
def c0 (w : List Bool) : ℕ := 2 * h * (2 * (decTokens w).getD 0 0 + 2) + (AbelianCayleyHDX.LF F).card

noncomputable def initW (w : List Bool) : List Bool :=
  (Coding.encode ((w, c0 (F := F) h w, [true]) : PState) : List Bool)

theorem initProg : Nonempty (PolyProgram id id (initW (F := F) h)) := by
  have hI : Poly (fun w : List Bool => initW (F := F) h w) := by unfold initW c0; fun_prop
  exact ⟨((BooleanLists.packProgram.comp hI.program).comp BooleanLists.unpackProgram).congr _
    (fun _ => rfl)⟩

theorem gProg : Nonempty (PolyProgram (encodePair id id) id (Gpost enc h)) := by
  have hG := poly_Gpost enc h
  exact ⟨(((BooleanLists.packProgram.product BooleanLists.packProgram).comp hG.program).comp
    BooleanLists.unpackProgram).congr _ (fun _ => rfl)⟩

end AbelianCayleyHDX.XH

open RSListDecodingCapacity.AllRates
namespace AbelianCayleyHDX.XR

lemma digits_len_le (x : ℕ) : (Nat.digits 2 x).length ≤ x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · rw [Nat.digits_def' (by norm_num) hx, List.length_cons]
      have := ih (x / 2) (Nat.div_lt_self hx (by norm_num))
      omega

lemma encNat_len (x : ℕ) : (encNat x).length ≤ 2 * x + 2 := by
  unfold encNat encBits
  simp only [List.length_append, List.length_flatMap, List.length_cons, List.length_nil,
    List.length_map]
  rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
  have := digits_len_le x
  omega

lemma outputsWithin_mono {Mach : Turing.TM2ComputableAux Bool Bool} {x y : List Bool} {t t' : ℕ}
    (h : HMBinPacking.OutputsWithin Mach x y t) (ht : t ≤ t') :
    HMBinPacking.OutputsWithin Mach x y t' := by
  obtain ⟨h⟩ := h
  exact ⟨⟨h.toEvalsTo, le_trans h.steps_le_m ht⟩⟩


end AbelianCayleyHDX.XR


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

namespace AbelianCayleyHDX.XH

open AbelianCayleyHDX.XP AbelianCayleyHDX.XK AbelianCayleyHDX.XL

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] (enc : F ≃ Fin (Fintype.card F)) (h : ℕ)
variable {t : ℕ} {D : Finset (AbelianCayleyHDX.PG t F)} {reps : List (Fin t → F)}

lemma reps_le (hR : RepsSpec D reps) : reps.length ≤ Fintype.card F ^ t := by
  have hnd : reps.Nodup := by
    rw [List.nodup_iff_injective_get]
    intro i j hij
    apply (pointOf_bij hR).1
    have e : reps[i.1] = reps[j.1] := hij
    apply Subtype.ext
    simp only [pointOf]
    congr 1
  have := hnd.length_le_card
  simpa [Fintype.card_fun] using this

lemma encFVec_len (a : Fin t → F) :
    (AbelianCayleyHDX.encFVec enc a).length ≤ 2 * t + 2 + t * (2 * Fintype.card F + 2) := by
  unfold AbelianCayleyHDX.encFVec encList
  rw [List.length_append, List.length_ofFn, List.length_flatMap]
  have h1 := AbelianCayleyHDX.XR.encNat_len t
  have h2 : ((List.ofFn a).map fun x => (encNat (enc x).val).length).sum ≤
      (List.ofFn a).length * (2 * Fintype.card F + 2) := by
    have := List.sum_le_card_nsmul ((List.ofFn a).map fun x => (encNat (enc x).val).length)
      (2 * Fintype.card F + 2) (fun y hy => by
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
        have := AbelianCayleyHDX.XR.encNat_len (enc x).val
        have := (enc x).2
        omega)
    simpa using this
  rw [List.length_ofFn] at h2
  omega

lemma W_len_le (hR : RepsSpec D reps) :
    (encNat t ++ encList (AbelianCayleyHDX.encFVec enc) reps).length ≤
      (2 * Fintype.card F + 10) * (Fintype.card F ^ t + t + 1) ^ 2 := by
  have hN := reps_le hR
  unfold encList
  rw [List.length_append, List.length_append, List.length_flatMap]
  have h1 := AbelianCayleyHDX.XR.encNat_len t
  have h2 := AbelianCayleyHDX.XR.encNat_len reps.length
  have h3 : (reps.map fun a => (AbelianCayleyHDX.encFVec enc a).length).sum ≤
      reps.length * (2 * t + 2 + t * (2 * Fintype.card F + 2)) := by
    have := List.sum_le_card_nsmul (reps.map fun a => (AbelianCayleyHDX.encFVec enc a).length)
      (2 * t + 2 + t * (2 * Fintype.card F + 2)) (fun y hy => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact encFVec_len enc a)
    simpa using this
  set Qt := Fintype.card F ^ t
  set Q := Fintype.card F
  have h4 : reps.length * (2 * t + 2 + t * (2 * Q + 2)) ≤ Qt * ((2 * Q + 4) * (t + 1)) := by
    apply Nat.mul_le_mul hN; nlinarith
  set X := Qt + t + 1
  have hX1 : X ≤ X ^ 2 := by nlinarith
  have hX2 : Qt * (t + 1) ≤ X ^ 2 := by
    have : Qt ≤ X := by omega
    have : t + 1 ≤ X := by omega
    calc Qt * (t + 1) ≤ X * X := Nat.mul_le_mul ‹_› ‹_›
      _ = X ^ 2 := (sq X).symm
  have h5 : Qt * ((2 * Q + 4) * (t + 1)) ≤ (2 * Q + 4) * X ^ 2 := by
    calc Qt * ((2 * Q + 4) * (t + 1)) = (2 * Q + 4) * (Qt * (t + 1)) := by ring
      _ ≤ (2 * Q + 4) * X ^ 2 := Nat.mul_le_mul_left _ hX2
  have h6 : (2 * Q + 10) * X ^ 2 = (2 * Q + 4) * X ^ 2 + 6 * X ^ 2 := by ring
  omega

end AbelianCayleyHDX.XH

namespace AbelianCayleyHDX.XH

open AbelianCayleyHDX.XP AbelianCayleyHDX.XK AbelianCayleyHDX.XL

lemma enc_pstate_len (w : List Bool) (c : ℕ) (pad : List Bool) :
    (Coding.encode ((w, c, pad) : PState)).length = 6 * w.length + 2 + 2 * (Nat.bits c).length + 3 * pad.length := by
  change (encodePair (encodeList encodeBool) (encodePair Nat.bits (encodeList encodeBool))
    (w, c, pad)).length = _
  simp only [encodePair_length, AbelianCayleyHDX.XP.encList_bool_length]
  ring

lemma bits_len_le (c : ℕ) : (Nat.bits c).length ≤ c := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.2 (Nat.lt_two_pow_self)

end AbelianCayleyHDX.XH


open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open RSListDecodingCapacity.AllRates

open AbelianCayleyHDX AbelianCayleyHDX.XH AbelianCayleyHDX.XP AbelianCayleyHDX.XK
  AbelianCayleyHDX.XL in
theorem solution (h : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = (2 ^ h) ^ 2) (t : ℕ → ℕ) (D : ∀ j, Finset (PG (t j) F))
    (enc : F ≃ Fin (Fintype.card F)) (Mach : Turing.TM2ComputableAux Bool Bool)
    (p : Polynomial ℕ)
    (hMach : ∀ j, ∃ reps : List (Fin (t j) → F), reps.length = (D j).card ∧
      (∀ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha ∈ D j) ∧
      (∀ d ∈ D j, ∃ a ∈ reps, ∃ ha : a ≠ 0, Projectivization.mk F a ha = d) ∧
      HMBinPacking.OutputsWithin Mach (encNat j) (encNat (t j) ++ encList (encFVec enc) reps)
        (p.eval (t j))) :
    ∃ (R : ℕ → ℕ) (eR : ∀ j, RowIdx (D j) ≃ Fin (R j))
      (eΩ : ∀ j, Omega F (t j) ≃ Fin (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)))
      (Mach' : Turing.TM2ComputableAux Bool Bool) (p' : Polynomial ℕ), ∀ j,
      HMBinPacking.OutputsWithin Mach' (encNat j)
        (encNat (R j) ++ encNat (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j)) ++
          encList encVec (List.ofFn ((HD (D j)).reindex (eR j) (eΩ j))))
        (p'.eval (((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j))) := by
  classical
  choose reps hlen hmem hcov hout using hMach
  have hRS : ∀ j, RepsSpec (D j) (reps j) := fun j => ⟨hlen j, hmem j, hcov j⟩
  obtain ⟨Pi⟩ := initProg (F := F) h
  obtain ⟨Pg⟩ := gProg enc h
  obtain ⟨Pp⟩ := padProgram
  have hQ2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  -- bound polynomials
  let X : Polynomial ℕ := Polynomial.X
  let wP : Polynomial ℕ := Polynomial.C (2 * Fintype.card F + 10) * (2 * X + 1) ^ 2
  let cP : Polynomial ℕ := Polynomial.C (4 * h) * (X + 1) + Polynomial.C (AbelianCayleyHDX.LF F).card
  let eP : Polynomial ℕ := Polynomial.C (Fintype.card F ^ 2 * 2 ^ (AbelianCayleyHDX.LF F).card) * X ^ 2
  let sP : Polynomial ℕ := 6 * wP + 2 + 2 * cP + 3 * eP
  let iP : Polynomial ℕ := 6 * wP + 2 * cP + 5
  let gP : Polynomial ℕ := 2 * wP + 1 + eP
  let p' : Polynomial ℕ := p + (2 * wP + 2) + Pi.time.comp wP + (2 * iP + 2) +
    (cP + 1) * (Pp.time.comp sP + 2 * Pp.sizeBound.comp sP + 3) + (2 * gP + 2) + Pg.time.comp gP
  refine ⟨fun j => Rn (t j) (reps j), fun j => eR0 enc (hRS j), fun j => eΩ enc h hF (t j),
    composeAux (composeAux (composeAux Mach (auxOf Pi)) (auxLoop Pp)) (auxOf' Pg), p', fun j => ?_⟩
  set W := encNat (t j) ++ encList (encFVec enc) (reps j) with hW
  have hdt : decTokens W = htoks enc (t j) (reps j) := by rw [hW, hW_eq, decTokens_flatMap]
  set c := c0 (F := F) h W with hc
  have hcv : c = 2 * h * (2 * t j + 2) + (AbelianCayleyHDX.LF F).card := by
    rw [hc]; unfold c0; rw [hdt]; simp only [htoks]; rfl
  set pad := List.replicate (2 ^ c * [true].length) true with hpad
  set S := 6 * W.length + 2 + 2 * c + 3 * 2 ^ c with hS
  -- the pad loop
  have hrun := pad_run W S c [true] (fun k hk => by
      rw [padState, enc_pstate_len, List.length_replicate]
      have h1 := bits_len_le (c - k)
      have h2 : 2 ^ k * [true].length ≤ 2 ^ c := by
        simp only [List.length_singleton, mul_one]; exact Nat.pow_le_pow_right (by norm_num) hk
      omega) (fun x hx => by simpa using hx)
  have o1 := hout j
  have o2 := outputsWithin_auxOf Pi W
  have o3 := outputsWithin_auxLoop Pp hrun
  have o4 := outputsWithin_auxOf' Pg (W, pad)
  have e23 : initW (F := F) h W = Coding.encode (padState W c [true]) := rfl
  rw [e23] at o2
  have o := outputsWithin_compose (outputsWithin_compose (outputsWithin_compose o1 o2) o3) o4
  -- sizes
  have hN := reps_le (hRS j)
  have hLL : (AbelianCayleyHDX.LF F).card < 2 ^ (AbelianCayleyHDX.LF F).card := Nat.lt_two_pow_self
  have hplen : pad.length = 2 ^ c := by simp [hpad]
  have hQh : 2 ^ (2 * h) = Fintype.card F := (hQ h hF).symm
  have hpowc : (2 : ℕ) ^ c = Fintype.card F ^ 2 * (Fintype.card F ^ t j) ^ 2 *
      2 ^ (AbelianCayleyHDX.LF F).card := by
    rw [hcv, pow_add, pow_mul, hQh]; ring
  have hL1 : 1 ≤ 2 ^ (AbelianCayleyHDX.LF F).card := Nat.one_le_two_pow
  have hQt1 : 1 ≤ Fintype.card F ^ t j := Nat.one_le_pow _ _ (by omega)
  have htQ : t j < Fintype.card F ^ t j :=
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hQ2 _)
  have hhQ : 2 * h * t j ≤ Fintype.card F ^ t j := by
    rw [← hQh, ← pow_mul]; exact Nat.lt_two_pow_self.le
  have hQsq : Fintype.card F ≤ Fintype.card F ^ 2 := by nlinarith
  have hQtsq : Fintype.card F ^ t j ≤ (Fintype.card F ^ t j) ^ 2 := by nlinarith
  have hbase : Fintype.card F * Fintype.card F ^ t j * 2 ^ (AbelianCayleyHDX.LF F).card ≤ 2 ^ c := by
    rw [hpowc]; gcongr
  have hQt_le : Fintype.card F ^ t j ≤ Fintype.card F * Fintype.card F ^ t j *
      2 ^ (AbelianCayleyHDX.LF F).card := by
    calc Fintype.card F ^ t j = 1 * Fintype.card F ^ t j * 1 := by ring
      _ ≤ _ := by gcongr <;> omega
  have g1 : Rn (t j) (reps j) ≤ pad.length := by
    rw [hplen, hpowc]; unfold Rn
    have h1 : Fintype.card F - 1 ≤ Fintype.card F := Nat.sub_le _ _
    calc (reps j).length * (Fintype.card F - 1) * (Fintype.card F ^ t j * (AbelianCayleyHDX.LF F).card)
        ≤ Fintype.card F ^ t j * Fintype.card F ^ 2 *
            (Fintype.card F ^ t j * 2 ^ (AbelianCayleyHDX.LF F).card) := by
          gcongr; exact h1.trans hQsq
      _ = Fintype.card F ^ 2 * (Fintype.card F ^ t j) ^ 2 * 2 ^ (AbelianCayleyHDX.LF F).card := by
          ring
  have g2 : (Fintype.card F - 1) * Fintype.card F ^ t j ≤ pad.length := by
    rw [hplen]
    calc (Fintype.card F - 1) * Fintype.card F ^ t j ≤ Fintype.card F * Fintype.card F ^ t j * 1 := by
          rw [mul_one]; exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      _ ≤ Fintype.card F * Fintype.card F ^ t j * 2 ^ (AbelianCayleyHDX.LF F).card := by gcongr
      _ ≤ 2 ^ c := hbase
  have g3 : (reps j).length ≤ pad.length := by rw [hplen]; omega
  have g4 : 2 * h * t j ≤ pad.length := by rw [hplen]; omega
  have g5 : t j ≤ pad.length := by rw [hplen]; omega
  rw [Gpost_eq enc h hF (hRS j) pad g1 g2 g3 g4 g5] at o
  apply AbelianCayleyHDX.XR.outputsWithin_mono o
  -- the time bound
  set K := ((2 ^ h) ^ 2 - 1) * (2 ^ h) ^ (2 * t j) with hK
  have hKQ : K = (Fintype.card F - 1) * Fintype.card F ^ t j := (hM h hF (t j)).symm
  have hQt_K : Fintype.card F ^ t j ≤ K := by
    rw [hKQ]
    calc Fintype.card F ^ t j = 1 * Fintype.card F ^ t j := (one_mul _).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have ht_K : t j ≤ K := by omega
  have hW1 : W.length ≤ (2 * Fintype.card F + 10) * (2 * K + 1) ^ 2 := by
    have := W_len_le enc (hRS j)
    rw [← hW] at this
    calc W.length ≤ (2 * Fintype.card F + 10) * (Fintype.card F ^ t j + t j + 1) ^ 2 := this
      _ ≤ (2 * Fintype.card F + 10) * (2 * K + 1) ^ 2 := by gcongr; omega
  have hc1 : c ≤ 4 * h * (K + 1) + (AbelianCayleyHDX.LF F).card := by
    rw [hcv]; nlinarith
  have hpc1 : 2 ^ c ≤ Fintype.card F ^ 2 * 2 ^ (AbelianCayleyHDX.LF F).card * K ^ 2 := by
    rw [hpowc]
    calc Fintype.card F ^ 2 * (Fintype.card F ^ t j) ^ 2 * 2 ^ (AbelianCayleyHDX.LF F).card
        ≤ Fintype.card F ^ 2 * K ^ 2 * 2 ^ (AbelianCayleyHDX.LF F).card := by gcongr
      _ = _ := by ring
  have hinit : (Coding.encode (padState W c [true])).length ≤ 6 * W.length + 2 * c + 5 := by
    rw [padState, enc_pstate_len]
    have := bits_len_le c
    simp only [List.length_singleton]; omega
  have hpair : (encodePair id id (W, pad)).length = 2 * W.length + 1 + 2 ^ c := by
    rw [encodePair_length]; simp only [id, hplen]
  have hpair' : (encodePair id id (W, List.replicate (2 ^ c * [true].length) true)).length =
      2 * W.length + 1 + 2 ^ c := hpair
  -- evaluations of the bound polynomials
  have ewP : wP.eval K = (2 * Fintype.card F + 10) * (2 * K + 1) ^ 2 := by simp [wP, X]
  have ecP : cP.eval K = 4 * h * (K + 1) + (AbelianCayleyHDX.LF F).card := by simp [cP, X]
  have eeP : eP.eval K = Fintype.card F ^ 2 * 2 ^ (AbelianCayleyHDX.LF F).card * K ^ 2 := by
    simp [eP, X]
  have esP : sP.eval K = 6 * wP.eval K + 2 + 2 * cP.eval K + 3 * eP.eval K := by simp [sP]
  have eiP : iP.eval K = 6 * wP.eval K + 2 * cP.eval K + 5 := by simp [iP]
  have egP : gP.eval K = 2 * wP.eval K + 1 + eP.eval K := by simp [gP]
  have hSb : S ≤ sP.eval K := by rw [esP, ewP, ecP, eeP, hS]; omega
  have hp1 : p.eval (t j) ≤ p.eval K := poly_eval_mono _ ht_K
  have hp2 : Pi.time.eval W.length ≤ (Pi.time.comp wP).eval K := by
    rw [Polynomial.eval_comp]; exact poly_eval_mono _ (by rw [ewP]; exact hW1)
  have hp3 : Pp.passTime S ≤ (Pp.time.comp sP + 2 * Pp.sizeBound.comp sP + 3).eval K := by
    unfold PolyProgram.passTime
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
      Polynomial.eval_ofNat]
    have := poly_eval_mono Pp.time hSb
    have := poly_eval_mono Pp.sizeBound hSb
    omega
  have hp4 : (c + 1) * Pp.passTime S ≤ ((cP + 1) * (Pp.time.comp sP + 2 * Pp.sizeBound.comp sP + 3)).eval K := by
    rw [Polynomial.eval_mul]
    apply Nat.mul_le_mul _ hp3
    simp only [Polynomial.eval_add, Polynomial.eval_one]; rw [ecP]; omega
  have hp5 : Pg.time.eval (encodePair id id (W, pad)).length ≤ (Pg.time.comp gP).eval K := by
    rw [Polynomial.eval_comp]; exact poly_eval_mono _ (by rw [hpair, egP, ewP, eeP]; omega)
  have hlen1 : 2 * (encNat (t j) ++ encList (encFVec enc) (reps j)).length + 2 ≤
      (2 * wP + 2).eval K := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [ewP, ← hW]; omega
  have hlen2 : 2 * (Coding.encode (padState W c [true])).length + 2 ≤ (2 * iP + 2).eval K := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [eiP, ewP, ecP]; omega
  have hlen3 : 2 * (encodePair id id (W, List.replicate (2 ^ c * [true].length) true)).length + 2 ≤
      (2 * gP + 2).eval K := by
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat]
    rw [hpair', egP, ewP, eeP]; omega
  have hp'e : p'.eval K = p.eval K + (2 * wP + 2).eval K + (Pi.time.comp wP).eval K +
      (2 * iP + 2).eval K + ((cP + 1) * (Pp.time.comp sP + 2 * Pp.sizeBound.comp sP + 3)).eval K +
      (2 * gP + 2).eval K + (Pg.time.comp gP).eval K := by
    simp only [p', Polynomial.eval_add]
  rw [hp'e]

  omega
