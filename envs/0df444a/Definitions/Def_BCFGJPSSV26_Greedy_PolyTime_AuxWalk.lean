-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxWalk
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxWalk
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:09:29.158755+00:00
-- url     : https://prove2.me/theorems/3b062e21-f31c-4b83-aedc-e779207b33eb
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxWalk — Polynomial time of the core: the walk of step B
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxWalk` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The kinds of the points of the walk are encoded as tagged tuples
--   (`BCFGJPSSV26.Greedy.PT.encWK`). The walk (`BCFGJPSSV26.Greedy.Ctx.walkB`) runs `L` rounds
--   (`Ctx.roundB`), each of at most `|cur|` deletions (`Ctx.delStep`); a deletion cuts the current
--   sequence to `L` atoms and records one point. So every recorded sequence has at most
--   `|H'p| + 2L + 1` atoms, every atom comes from the inputs, the completions (facilities below `m`)
--   or the free copies of facilities of `Hp` (`BCFGJPSSV26.Greedy.PT.WalkP`), and there are at most
--   `1 + L (|H'p| + 2L + 2)` points (`BCFGJPSSV26.Greedy.PT.walkB_inv`). This bounds the encoded
--   states of both loops.
--
--   **Contents.** The module is published as a whole: 39 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxWalk`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxWalk.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxSearch
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_NatLength

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxWalk` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: the walk of step B

The kinds of the points of the walk are encoded as tagged tuples
(`BCFGJPSSV26.Greedy.PT.encWK`). The walk (`BCFGJPSSV26.Greedy.Ctx.walkB`) runs `L` rounds
(`Ctx.roundB`), each of at most `|cur|` deletions (`Ctx.delStep`); a deletion cuts the current
sequence to `L` atoms and records one point. So every recorded sequence has at most
`|H'p| + 2L + 1` atoms, every atom comes from the inputs, the completions (facilities below `m`)
or the free copies of facilities of `Hp` (`BCFGJPSSV26.Greedy.PT.WalkP`), and there are at most
`1 + L (|H'p| + 2L + 2)` points (`BCFGJPSSV26.Greedy.PT.walkB_inv`). This bounds the encoded
states of both loops.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### Encodings of kinds and of the walk -/

/-- Kinds, as tuples. -/
abbrev encWT : ℕ × AAtom × List AAtom × List AAtom × List AAtom ↪ List Bool :=
  encPair encNat (encPair encAt (encPair encSq (encPair encSq encSq)))

/-- The tuple of a kind: a tag, an atom and three sequences. -/
def wkT : Ctx.WKind → ℕ × AAtom × List AAtom × List AAtom × List AAtom
  | .init => (0, (0, 0), [], [], [])
  | .appendFree z => (1, (z, 0), [], [], [])
  | .removeComplete X h Y Z => (2, h, X, Y, Z)
  | .toRegular => (3, (0, 0), [], [], [])

/-- The kind of a tuple. -/
def wkOf (t : ℕ × AAtom × List AAtom × List AAtom × List AAtom) : Ctx.WKind :=
  if t.1 = 0 then .init else if t.1 = 1 then .appendFree t.2.1.1
  else if t.1 = 2 then .removeComplete t.2.2.1 t.2.1 t.2.2.2.1 t.2.2.2.2 else .toRegular

theorem wkOf_wkT (k : Ctx.WKind) : wkOf (wkT k) = k := by cases k <;> rfl

/-- Kinds. -/
def encWK : Ctx.WKind ↪ List Bool :=
  ⟨fun k ↦ encWT (wkT k), fun k k' h ↦ by
    have h' : wkT k = wkT k' := encWT.injective h
    rw [← wkOf_wkT k, ← wkOf_wkT k', h']⟩

/-- Points of the walk. -/
abbrev encPt : List AAtom × Ctx.WKind ↪ List Bool := encPair encSq encWK

/-- States of the walk. -/
abbrev encWS : List AAtom × List (List AAtom × Ctx.WKind) ↪ List Bool :=
  encPair encSq (encList encPt)

variable {α : Type} {input : α ↪ List Bool}

theorem wkTt {k : α → Ctx.WKind} (hk : ComputableInPolyTime k input encWK) :
    ComputableInPolyTime (fun a ↦ wkT (k a)) input encWT :=
  hk.of_enc_eq fun _ ↦ rfl

theorem wkInit : ComputableInPolyTime (fun _ : α ↦ Ctx.WKind.init) input encWK :=
  (const (encOut := encWT) (0, (0, 0), [], [], [])).of_enc_eq fun _ ↦ rfl

theorem wkTR : ComputableInPolyTime (fun _ : α ↦ Ctx.WKind.toRegular) input encWK :=
  (const (encOut := encWT) (3, (0, 0), [], [], [])).of_enc_eq fun _ ↦ rfl

theorem wkAF {z : α → ℕ} (hz : ComputableInPolyTime z input encNat) :
    ComputableInPolyTime (fun a ↦ Ctx.WKind.appendFree (z a)) input encWK :=
  ((const 1).prod ((hz.prod (const 0)).prod ((const []).prod ((const []).prod (const [])))))
    |>.of_enc_eq fun _ ↦ rfl

theorem wkRC {X Y Z : α → List AAtom} {h : α → AAtom} (hX : ComputableInPolyTime X input encSq)
    (hh : ComputableInPolyTime h input encAt) (hY : ComputableInPolyTime Y input encSq)
    (hZ : ComputableInPolyTime Z input encSq) :
    ComputableInPolyTime (fun a ↦ Ctx.WKind.removeComplete (X a) (h a) (Y a) (Z a)) input encWK :=
  ((const 2).prod (hh.prod (hX.prod (hY.prod hZ)))).of_enc_eq fun _ ↦ rfl

/-! ### Common prefixes -/

theorem cpl_eq (l l' : List AAtom) : Ctx.commonPrefixLen l l' =
    ((List.range (min l.length l'.length)).find? fun t ↦
      !decide (l.getD t (0, 0) = l'.getD t (0, 0))).getD (min l.length l'.length) := by
  induction l generalizing l' with
  | nil => cases l' <;> rfl
  | cons a l ih =>
    cases l' with
    | nil => rfl
    | cons b l' =>
      simp only [Ctx.commonPrefixLen, List.length_cons, Nat.add_min_add_right]
      rw [List.range_succ_eq_map, List.find?_cons]
      by_cases hab : a = b
      · subst hab
        simp only [List.getD_cons_zero, decide_true, Bool.not_true, ite_true, ih,
          List.find?_map]
        rcases h : (List.range (min l.length l'.length)).find? (fun t ↦
          !decide (l.getD t (0, 0) = l'.getD t (0, 0))) with _ | t
        · simp only [Option.getD_none]
          have : ((List.range (min l.length l'.length)).find? ((fun t ↦
              !decide ((a :: l).getD t (0, 0) = (a :: l').getD t (0, 0))) ∘ Nat.succ)) =
              none := by
            simpa [Function.comp_def, List.getD_cons_succ] using h
          rw [this]; rfl
        · have : ((List.range (min l.length l'.length)).find? ((fun t ↦
              !decide ((a :: l).getD t (0, 0) = (a :: l').getD t (0, 0))) ∘ Nat.succ)) =
              some t := by
            simpa [Function.comp_def, List.getD_cons_succ] using h
          rw [this]; rfl
      · simp [hab]

theorem cplU {l l' : α → List AAtom} (hl : ComputableInPolyTime l input encSq)
    (hl' : ComputableInPolyTime l' input encSq) :
    ComputableInPolyTime (fun a ↦ Ctx.commonPrefixLen (l a) (l' a)) input encUnary := by
  simp only [cpl_eq]
  have hmin : ComputableInPolyTime (fun a ↦ min (l a).length (l' a).length) input encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_min.comp ((lenL hl).prod (lenL hl')).tidy)
  exact optionGetDWithInput (findWithInput (unary_range' hmin)
    (bool_not.comp (decide_eq' (listGetDWithInput (hl.comp (fst _ _)) (snd _ _) (0, 0))
      (listGetDWithInput (hl'.comp (fst _ _)) (snd _ _) (0, 0))))) hmin

theorem isPrefixOf_eq {β : Type} [BEq β] [LawfulBEq β] [DecidableEq β] (l₁ l₂ : List β) :
    l₁.isPrefixOf l₂ = decide (l₁ = l₂.take l₁.length) := by
  rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, List.prefix_iff_eq_take, decide_eq_true_eq]

theorem takeS {l : α → List AAtom} {t : α → ℕ} (hl : ComputableInPolyTime l input encSq)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a ↦ (l a).take (t a)) input encSq :=
  .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hl.tidy ht.tidy)

theorem dropS {l : α → List AAtom} {t : α → ℕ} (hl : ComputableInPolyTime l input encSq)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a ↦ (l a).drop (t a)) input encSq :=
  .of_tidy (ComputableTidilyInPolyTime.listDropWithInput hl.tidy ht.tidy)

theorem isPrefixOfB {l l' : α → List AAtom} (hl : ComputableInPolyTime l input encSq)
    (hl' : ComputableInPolyTime l' input encSq) :
    ComputableInPolyTime (fun a ↦ (l a).isPrefixOf (l' a)) input encBool := by
  simp only [isPrefixOf_eq]
  exact decide_eq' hl (takeS hl' (lenL hl))

theorem setS {l : α → List AAtom} {t : α → ℕ} {v : α → AAtom}
    (hl : ComputableInPolyTime l input encSq) (ht : ComputableInPolyTime t input encUnary)
    (hv : ComputableInPolyTime v input encAt) :
    ComputableInPolyTime (fun a ↦ (l a).set (t a) (v a)) input encSq := by
  simp only [List.set_eq_take_append_cons_drop]
  exact itep (unary_lt' ht (lenL hl)) (listAppend' (takeS hl ht)
    (cons' hv (dropS hl (unary_add' ht (const 1))))) hl

/-! ### Certificates of a deletion -/

variable (c : Consts) {X : α → CoreIn}

theorem delStepS {p q : α → ℕ} {f : α → ℚ} {pre : α → List (List AAtom)}
    {st : α → List AAtom × List (List AAtom × Ctx.WKind)}
    (hX : ComputableInPolyTime X input encCI) (hp : ComputableInPolyTime p input encUnary)
    (hf : ComputableInPolyTime f input encRat) (hpre : ComputableInPolyTime pre input encSl)
    (hq : ComputableInPolyTime q input encUnary) (hst : ComputableInPolyTime st input encWS) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).delStep (p a) (f a) (pre a) (q a) (st a)) input
      encWS := by
  unfold Ctx.delStep
  have h1 : ComputableInPolyTime (fun a ↦ (st a).1) input encSq := (fst _ _).comp hst
  have h2 : ComputableInPolyTime (fun a ↦ (st a).2) input (encList encPt) := (snd _ _).comp hst
  have hXs := takeS h1 hq
  have hh : ComputableInPolyTime (fun a ↦ (st a).1.getD (q a) (0, 0)) input encAt :=
    listGetDWithInput h1 hq (0, 0)
  have hY := dropS h1 (unary_add' hq (const 1))
  have hZ := dropS (completeSeqS c hX (typ1B hp) hf (θseqQ (X := X) c hp) (flattenS hpre)
    (listAppend' hXs hY)) (unary_add' (lenL hXs) (lenL hY))
  have hcur := takeS (listAppend' (listAppend' hXs hY) hZ) (LU c hX)
  exact hcur.prod (listAppend' h2 (cons' (hcur.prod (wkRC hXs hh hY hZ)) (const [])))

/-! ### Invariants of the walk -/

/-- A sequence of at most `N` atoms satisfying `P`. -/
def PSeq (P : AAtom → Prop) (N : ℕ) (S : List AAtom) : Prop := S.length ≤ N ∧ ∀ a ∈ S, P a

/-- A kind whose atom and sequences satisfy `P` and have at most `N` atoms. -/
def PKind (P : AAtom → Prop) (N : ℕ) (k : Ctx.WKind) : Prop :=
  P (wkT k).2.1 ∧ PSeq P N (wkT k).2.2.1 ∧ PSeq P N (wkT k).2.2.2.1 ∧ PSeq P N (wkT k).2.2.2.2

/-- A point of the walk satisfying `P`, with sequences of at most `N` atoms. -/
def PEnt (P : AAtom → Prop) (N : ℕ) (e : List AAtom × Ctx.WKind) : Prop :=
  PSeq P N e.1 ∧ PKind P N e.2

theorem PSeq.mono {P : AAtom → Prop} {N N' : ℕ} {S : List AAtom} (h : PSeq P N S) (hN : N ≤ N') :
    PSeq P N' S := ⟨h.1.trans hN, h.2⟩

theorem PKind.mono {P : AAtom → Prop} {N N' : ℕ} {k : Ctx.WKind} (h : PKind P N k)
    (hN : N ≤ N') : PKind P N' k := ⟨h.1, h.2.1.mono hN, h.2.2.1.mono hN, h.2.2.2.mono hN⟩

theorem PEnt.mono {P : AAtom → Prop} {N N' : ℕ} {e : List AAtom × Ctx.WKind} (h : PEnt P N e)
    (hN : N ≤ N') : PEnt P N' e := ⟨h.1.mono hN, h.2.mono hN⟩

theorem pseq_nil (P : AAtom → Prop) (N : ℕ) : PSeq P N [] := ⟨Nat.zero_le _, by simp⟩

/-- What the walk needs of the atoms: the regular facilities below `m`, the atom `(0, 0)`, the
free and regular copies of the facilities of `Hp` and of `0`, and the atoms of `H'p`. -/
structure WalkP (C : Ctx) (P : AAtom → Prop) (Hp H'p : List AAtom) : Prop where
  reg : ∀ i < C.ip.m, P (i, 0)
  zero : P (0, 0)
  zero1 : P (0, 1)
  free : ∀ a ∈ Hp, P (a.1, 1) ∧ P (a.1, 0)
  start : ∀ a ∈ H'p, P a

theorem delStep_inv (C : Ctx) {P : AAtom → Prop} (hreg : ∀ i < C.ip.m, P (i, 0)) (hzero : P (0, 0))
    (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (q : ℕ) {N : ℕ} (hN : C.ip.L ≤ N)
    {st : List AAtom × List (List AAtom × Ctx.WKind)} (h1 : PSeq P N st.1) :
    PSeq P C.ip.L (C.delStep p f pre q st).1 ∧
      ∃ e, (C.delStep p f pre q st).2 = st.2 ++ [e] ∧ PEnt P N e := by
  obtain ⟨new, hnew, hlen, hat⟩ := completeSeq_eq C (typ1 p) f (C.θseq p) pre.flatten
    (st.1.take q ++ st.1.drop (q + 1))
  have hZ : (C.completeSeq (typ1 p) f (C.θseq p) pre.flatten
      (st.1.take q ++ st.1.drop (q + 1))).drop
        ((st.1.take q).length + (st.1.drop (q + 1)).length) = new := by
    rw [hnew, ← List.length_append, List.drop_left]
  have hPX : PSeq P N (st.1.take q) :=
    ⟨(List.length_take_le' _ _).trans h1.1, fun a ha ↦ h1.2 a (List.mem_of_mem_take ha)⟩
  have hPY : PSeq P N (st.1.drop (q + 1)) :=
    ⟨by have := h1.1; simp only [List.length_drop]; omega,
      fun a ha ↦ h1.2 a (List.mem_of_mem_drop ha)⟩
  have hPZ : PSeq P N new := ⟨hlen.trans hN, fun a ha ↦ by
    have := hat a ha
    rw [show a = (a.1, 0) from Prod.ext rfl this.2]
    exact hreg _ this.1⟩
  have hh : P (st.1.getD q (0, 0)) := by
    rw [List.getD_eq_getElem?_getD]
    rcases h : st.1[q]? with _ | v
    · exact hzero
    · exact h1.2 v (List.mem_of_getElem? h)
  have hcur : PSeq P C.ip.L ((st.1.take q ++ st.1.drop (q + 1) ++ new).take C.ip.L) := by
    refine ⟨List.length_take_le _ _, fun a ha ↦ ?_⟩
    rcases List.mem_append.1 (List.mem_of_mem_take ha) with ha | ha
    · rcases List.mem_append.1 ha with ha | ha
      · exact hPX.2 a ha
      · exact hPY.2 a ha
    · exact hPZ.2 a ha
  unfold Ctx.delStep
  simp only [hZ]
  exact ⟨hcur, _, rfl, hcur.mono hN, hh, hPX, hPY, hPZ⟩

theorem iterate_delStep_inv (C : Ctx) {P : AAtom → Prop} (hreg : ∀ i < C.ip.m, P (i, 0))
    (hzero : P (0, 0)) (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (q : ℕ) {N : ℕ}
    (hN : C.ip.L ≤ N) {st : List AAtom × List (List AAtom × Ctx.WKind)} (h1 : PSeq P N st.1)
    (t : ℕ) :
    PSeq P N ((C.delStep p f pre q)^[t] st).1 ∧ ∃ new, ((C.delStep p f pre q)^[t] st).2 =
      st.2 ++ new ∧ new.length = t ∧ ∀ e ∈ new, PEnt P N e := by
  induction t with
  | zero => exact ⟨h1, [], by simp, rfl, by simp⟩
  | succ t ih =>
    obtain ⟨hs, new, hnew, hlen, hent⟩ := ih
    rw [Function.iterate_succ_apply']
    obtain ⟨hs', e, he, hPe⟩ := delStep_inv C hreg hzero p f pre q hN hs
    refine ⟨hs'.mono hN, new ++ [e], by rw [he, hnew, List.append_assoc], by simp [hlen], ?_⟩
    intro e' he'
    rcases List.mem_append.1 he' with he' | he'
    · exact hent e' he'
    · rw [List.mem_singleton.1 he']; exact hPe

theorem getD_free {C : Ctx} {P : AAtom → Prop} {Hp H'p : List AAtom} (hW : WalkP C P Hp H'p)
    (q : ℕ) : P ((Hp.getD q (0, 0)).1, 1) ∧ P ((Hp.getD q (0, 0)).1, 0) := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : Hp[q]? with _ | v
  · exact ⟨hW.zero1, hW.zero⟩
  · exact hW.free v (List.mem_of_getElem? h)

theorem roundB_inv (C : Ctx) {P : AAtom → Prop} {Hp H'p : List AAtom} (hW : WalkP C P Hp H'p)
    (p : ℕ) (f : ℚ) (pre : List (List AAtom)) {N ℓ : ℕ} (hN : C.ip.L ≤ N) (hℓ : ℓ + 1 ≤ N)
    {st : List AAtom × List (List AAtom × Ctx.WKind)} (h1 : PSeq P ℓ st.1) :
    PSeq P (max C.ip.L (ℓ + 1)) (C.roundB p f pre Hp st).1 ∧
      ∃ new, (C.roundB p f pre Hp st).2 = st.2 ++ new ∧ new.length ≤ ℓ + 2 ∧
        ∀ e ∈ new, PEnt P N e := by
  have hl1 := h1.1
  unfold Ctx.roundB
  split_ifs with hpre
  · exact ⟨h1.mono (by omega), [], by simp, by simp, by simp⟩
  · simp only
    set q := Ctx.commonPrefixLen Hp st.1
    set z := (Hp.getD q (0, 0)).1
    obtain ⟨hz1, hz0⟩ := getD_free hW q
    have hc1 : PSeq P (max C.ip.L (ℓ + 1)) (st.1 ++ [(z, 1)]) := by
      refine ⟨by simp; omega, fun a ha ↦ ?_⟩
      rcases List.mem_append.1 ha with ha | ha
      · exact h1.2 a ha
      · rw [List.mem_singleton.1 ha]; exact hz1
    obtain ⟨hs, new, hnew, hlen, hent⟩ := iterate_delStep_inv C hW.reg hW.zero p f pre q
      (N := max C.ip.L (ℓ + 1)) (le_max_left _ _) (st := (st.1 ++ [(z, 1)],
        st.2 ++ [(st.1 ++ [(z, 1)], .appendFree z)])) hc1 (st.1.length - q)
    set s := (C.delStep p f pre q)^[st.1.length - q] (st.1 ++ [(z, 1)],
      st.2 ++ [(st.1 ++ [(z, 1)], .appendFree z)])
    have hc3 : PSeq P (max C.ip.L (ℓ + 1)) (s.1.set q (z, 0)) := by
      refine ⟨by rw [List.length_set]; exact hs.1, fun a ha ↦ ?_⟩
      rcases List.mem_or_eq_of_mem_set ha with ha | ha
      · exact hs.2 a ha
      · rw [ha]; exact hz0
    have hNm : max C.ip.L (ℓ + 1) ≤ N := max_le hN hℓ
    refine ⟨hc3, (st.1 ++ [(z, 1)], .appendFree z) :: (new ++ [(s.1.set q (z, 0), .toRegular)]),
      ?_, ?_, ?_⟩
    · simp only [hnew, List.append_assoc, List.cons_append, List.nil_append]
    · simp only [List.length_cons, List.length_append, hlen, List.length_nil]
      omega
    · intro e he
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at he
      rcases he with rfl | he | rfl
      · exact ⟨hc1.mono hNm, hz0, pseq_nil _ _, pseq_nil _ _, pseq_nil _ _⟩
      · exact (hent e he).mono hNm
      · exact ⟨hc3.mono hNm, hW.zero, pseq_nil _ _, pseq_nil _ _, pseq_nil _ _⟩

/-- **The invariant of the walk** after `t ≤ L` rounds. -/
theorem walkB_inv (C : Ctx) {P : AAtom → Prop} {Hp H'p : List AAtom} (hW : WalkP C P Hp H'p)
    (p : ℕ) (f : ℚ) (pre : List (List AAtom)) (t : ℕ) (ht : t ≤ C.ip.L) :
    PSeq P (max C.ip.L H'p.length + t) ((C.roundB p f pre Hp)^[t] (H'p, [(H'p, .init)])).1 ∧
      ((C.roundB p f pre Hp)^[t] (H'p, [(H'p, .init)])).2.length ≤
        1 + t * (H'p.length + 2 * C.ip.L + 2) ∧
      ∀ e ∈ ((C.roundB p f pre Hp)^[t] (H'p, [(H'p, .init)])).2,
        PEnt P (H'p.length + 2 * C.ip.L + 1) e := by
  induction t with
  | zero =>
    refine ⟨⟨by simp, hW.start⟩, by simp, ?_⟩
    intro e he
    rw [Function.iterate_zero_apply, List.mem_singleton] at he
    subst he
    exact ⟨⟨by simp only; omega, hW.start⟩, hW.zero, pseq_nil _ _, pseq_nil _ _, pseq_nil _ _⟩
  | succ t ih =>
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    obtain ⟨hs, new, hnew, hlen, hent⟩ := roundB_inv C hW p f pre (N := H'p.length + 2 * C.ip.L + 1)
      (by omega) (by omega) h1
    refine ⟨hs.mono (by omega), ?_, ?_⟩
    · rw [hnew, List.length_append]
      have : (t + 1) * (H'p.length + 2 * C.ip.L + 2) =
          t * (H'p.length + 2 * C.ip.L + 2) + (H'p.length + 2 * C.ip.L + 2) := by ring
      omega
    · intro e he
      rw [hnew] at he
      rcases List.mem_append.1 he with he | he
      · exact h3 e he
      · exact hent e he

/-! ### Encoded lengths of the walk -/

/-- A bound on an encoded point, for atoms of encoded length at most `σ` and sequences of at
most `N` atoms. -/
def entB (σ N : ℕ) : ℕ := 7 * (N * (2 * σ + 1)) + 2 * σ + 9

theorem len_PSeq {σ N : ℕ} {S : List AAtom} (h : PSeq (fun a ↦ (encAt a).length ≤ σ) N S) :
    (encSq S).length ≤ N * (2 * σ + 1) :=
  len_encList_le_of encAt h.1 h.2

theorem len_PEnt {σ N : ℕ} {e : List AAtom × Ctx.WKind}
    (h : PEnt (fun a ↦ (encAt a).length ≤ σ) N e) : (encPt e).length ≤ entB σ N := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e1 := len_PSeq h1
  have e3 := len_PSeq h3
  have e4 := len_PSeq h4
  have e5 := len_PSeq h5
  have htag : (encNat (wkT e.2).1).length ≤ 2 :=
    length_encNat_le_of_lt_two_pow (by cases e.2 <;> simp [wkT])
  rw [show (encPt e).length = 2 * (encSq e.1).length + 1 + (encWT (wkT e.2)).length from
    length_encPair e]
  simp only [encWT, length_encPair] at h2 ⊢
  unfold entB
  omega

theorem len_ents {σ N : ℕ} {l : List (List AAtom × Ctx.WKind)} {K : ℕ} (hK : l.length ≤ K)
    (h : ∀ e ∈ l, PEnt (fun a ↦ (encAt a).length ≤ σ) N e) :
    (encList encPt l).length ≤ K * (2 * entB σ N + 1) :=
  len_encList_le_of encPt hK fun e he ↦ len_PEnt (h e he)

theorem len_encAt_le_of_mem {a : AAtom} {S : List AAtom} (h : a ∈ S) :
    (encAt a).length ≤ (encSq S).length :=
  SizedListEncoding.length_elem_le (encA := encAt) (encL := encSq) S a h

/-- The atom bound of the walk certificates. -/
theorem walkP_len (C : Ctx) (Hp H'p : List AAtom) :
    WalkP C (fun a ↦ (encAt a).length ≤ (encSq Hp).length + (encSq H'p).length + 2 * C.ip.m + 3)
      Hp H'p where
  reg i hi := by have := len_encAt_reg (m := C.ip.m) (a := (i, 0)) ⟨hi, rfl⟩; omega
  zero := by simp [encNat_apply]
  zero1 := by simp [encNat_apply]
  free a ha := by
    have h := len_encAt_le_of_mem ha
    have h1 : (encNat 1).length = 1 := by simp [encNat_apply]
    have h0 : (encNat 0).length = 0 := by simp [encNat_apply]
    rw [len_encAt] at h
    simp only [len_encAt, h1, h0]
    constructor <;> omega
  start a ha := by have := len_encAt_le_of_mem ha; omega

end BCFGJPSSV26.Greedy.PT


