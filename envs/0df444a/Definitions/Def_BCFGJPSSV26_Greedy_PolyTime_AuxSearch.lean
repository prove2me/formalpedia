-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxSearch
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxSearch
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:07:26.18256+00:00
-- url     : https://prove2.me/theorems/ead69863-9332-472c-a7c5-be165f8f67ab
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxSearch — Polynomial time of the core: pairs, results, binary searches and bisection
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxSearch` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Pairs and results of the merge are encoded as tuples (`BCFGJPSSV26.Greedy.PT.encPr`,
--   `BCFGJPSSV26.Greedy.PT.encRs`). A binary search (`BCFGJPSSV26.Greedy.Ctx.searchStep`) keeps its
--   state below the initial upper end (`BCFGJPSSV26.Greedy.PT.searchStep_inv`), which bounds its
--   encoded states; this gives the certificates of the searches and of `Ctx.bisect`.
--
--   **Contents.** The module is published as a whole: 33 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxSearch`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxSearch.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxComplete

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxSearch` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: pairs, results, binary searches and bisection

Pairs and results of the merge are encoded as tuples (`BCFGJPSSV26.Greedy.PT.encPr`,
`BCFGJPSSV26.Greedy.PT.encRs`). A binary search (`BCFGJPSSV26.Greedy.Ctx.searchStep`) keeps its
state below the initial upper end (`BCFGJPSSV26.Greedy.PT.searchStep_inv`), which bounds its
encoded states; this gives the certificates of the searches and of `Ctx.bisect`.
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### Encodings of pairs and results -/

/-- Pairs, as tuples. -/
abbrev encPT : List (List AAtom) × List (List AAtom) × ℕ × ℕ ↪ List Bool :=
  encPair encSl (encPair encSl (encPair encNat encNat))

/-- The tuple of a pair. -/
def pairT (p : Ctx.Pair) : List (List AAtom) × List (List AAtom) × ℕ × ℕ := (p.H, p.H', p.b, p.b')

/-- The pair of a tuple. -/
def pairOf (t : List (List AAtom) × List (List AAtom) × ℕ × ℕ) : Ctx.Pair :=
  ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩

theorem pairOf_pairT (p : Ctx.Pair) : pairOf (pairT p) = p := by cases p; rfl

/-- Pairs. -/
def encPr : Ctx.Pair ↪ List Bool :=
  ⟨fun p ↦ encPT (pairT p), fun p q h ↦ by
    have h' : pairT p = pairT q := encPT.injective h
    rw [← pairOf_pairT p, ← pairOf_pairT q, h']⟩

/-- The tuple of a result: a tag, then a pair (`H` and `b` for a final result). -/
def resT : Ctx.Res → Bool × (List (List AAtom) × List (List AAtom) × ℕ × ℕ)
  | .done H b => (true, (H, [], b, 0))
  | .cont pr => (false, pairT pr)

/-- The result of a tuple. -/
def resOf (t : Bool × (List (List AAtom) × List (List AAtom) × ℕ × ℕ)) : Ctx.Res :=
  if t.1 then .done t.2.1 t.2.2.2.1 else .cont (pairOf t.2)

theorem resOf_resT (r : Ctx.Res) : resOf (resT r) = r := by
  cases r with
  | done H b => rfl
  | cont pr => simp only [resT, resOf, pairOf_pairT]; rfl

/-- Results. -/
def encRs : Ctx.Res ↪ List Bool :=
  ⟨fun r ↦ encPair encBool encPT (resT r), fun r s h ↦ by
    have h' : resT r = resT s := (encPair encBool encPT).injective h
    rw [← resOf_resT r, ← resOf_resT s, h']⟩

/-- The elimination of a result. -/
def resElim {β : Type} (r : Ctx.Res) (F : List (List AAtom) → ℕ → β) (G : Ctx.Pair → β) : β :=
  match r with
  | .done H b => F H b
  | .cont pr => G pr

variable {α : Type} {input : α ↪ List Bool}

theorem prMk {H H' : α → List (List AAtom)} {b b' : α → ℕ}
    (hH : ComputableInPolyTime H input encSl) (hH' : ComputableInPolyTime H' input encSl)
    (hb : ComputableInPolyTime b input encNat) (hb' : ComputableInPolyTime b' input encNat) :
    ComputableInPolyTime (fun a ↦ (⟨H a, H' a, b a, b' a⟩ : Ctx.Pair)) input encPr :=
  (hH.prod (hH'.prod (hb.prod hb'))).of_enc_eq fun _ ↦ rfl

theorem prT {p : α → Ctx.Pair} (hp : ComputableInPolyTime p input encPr) :
    ComputableInPolyTime (fun a ↦ pairT (p a)) input encPT :=
  hp.of_enc_eq fun _ ↦ rfl

theorem prOf {t : α → List (List AAtom) × List (List AAtom) × ℕ × ℕ}
    (ht : ComputableInPolyTime t input encPT) :
    ComputableInPolyTime (fun a ↦ pairOf (t a)) input encPr :=
  ht.of_enc_eq fun _ ↦ rfl

theorem prH {p : α → Ctx.Pair} (hp : ComputableInPolyTime p input encPr) :
    ComputableInPolyTime (fun a ↦ (p a).H) input encSl :=
  (fst _ _).comp (prT hp)

theorem prH' {p : α → Ctx.Pair} (hp : ComputableInPolyTime p input encPr) :
    ComputableInPolyTime (fun a ↦ (p a).H') input encSl :=
  ((fst _ _).comp (snd _ _)).comp (prT hp)

theorem prb {p : α → Ctx.Pair} (hp : ComputableInPolyTime p input encPr) :
    ComputableInPolyTime (fun a ↦ (p a).b) input encNat :=
  (((fst _ _).comp (snd _ _)).comp (snd _ _)).comp (prT hp)

theorem prb' {p : α → Ctx.Pair} (hp : ComputableInPolyTime p input encPr) :
    ComputableInPolyTime (fun a ↦ (p a).b') input encNat :=
  (((snd _ _).comp (snd _ _)).comp (snd _ _)).comp (prT hp)

theorem rsDone {H : α → List (List AAtom)} {b : α → ℕ} (hH : ComputableInPolyTime H input encSl)
    (hb : ComputableInPolyTime b input encNat) :
    ComputableInPolyTime (fun a ↦ Ctx.Res.done (H a) (b a)) input encRs :=
  ((const true).prod (hH.prod ((const []).prod (hb.prod (const 0))))).of_enc_eq fun _ ↦ rfl

theorem rsCont {p : α → Ctx.Pair} (hp : ComputableInPolyTime p input encPr) :
    ComputableInPolyTime (fun a ↦ Ctx.Res.cont (p a)) input encRs :=
  ((const false).prod (prT hp)).of_enc_eq fun _ ↦ rfl

theorem rsT {r : α → Ctx.Res} (hr : ComputableInPolyTime r input encRs) :
    ComputableInPolyTime (fun a ↦ resT (r a)) input (encPair encBool encPT) :=
  hr.of_enc_eq fun _ ↦ rfl

theorem resElim_eq {β : Type} (r : Ctx.Res) (F : List (List AAtom) → ℕ → β)
    (G : Ctx.Pair → β) :
    resElim r F G =
      if (resT r).1 then F (resT r).2.1 (resT r).2.2.2.1 else G (pairOf (resT r).2) := by
  cases r with
  | done H b => rfl
  | cont pr => simp only [resElim, resT, pairOf_pairT]; rfl

theorem rsElim {β : Type} {encB : β ↪ List Bool} {r : α → Ctx.Res}
    {F : α → List (List AAtom) → ℕ → β} {G : α → Ctx.Pair → β}
    (hr : ComputableInPolyTime r input encRs)
    (hF : ComputableInPolyTime (fun q : α × (List (List AAtom) × ℕ) ↦ F q.1 q.2.1 q.2.2)
      (encPair input (encPair encSl encNat)) encB)
    (hG : ComputableInPolyTime (fun q : α × Ctx.Pair ↦ G q.1 q.2) (encPair input encPr) encB) :
    ComputableInPolyTime (fun a ↦ resElim (r a) (F a) (G a)) input encB := by
  simp only [resElim_eq]
  have ht := rsT hr
  exact ite' ((fst _ _).comp ht) (hF.comp (id'.prod (((fst _ _).comp (snd _ _)).comp ht |>.prod
    ((((fst _ _).comp (snd _ _)).comp (snd _ _)).comp ((snd _ _).comp ht)))))
    (hG.comp (id'.prod (prOf ((snd _ _).comp ht))))

/-! ### Binary searches -/

/-- States of a binary search. -/
abbrev encSt : ℕ × ℕ × Option ℕ ↪ List Bool := encPair encNat (encPair encNat (encOption encNat))

theorem searchStep_eq (k : ℕ) (cf : ℕ → ℕ) (st : ℕ × ℕ × Option ℕ) :
    Ctx.searchStep k cf st = st.2.2.elim (if st.2.1 - st.1 ≤ 1 then st
      else if cf ((st.1 + st.2.1) / 2) = k then (st.1, st.2.1, some ((st.1 + st.2.1) / 2))
      else if decide (cf ((st.1 + st.2.1) / 2) < k) = decide (cf st.1 < k) then
        ((st.1 + st.2.1) / 2, st.2.1, none) else (st.1, (st.1 + st.2.1) / 2, none))
      fun _ ↦ st := by
  rcases st with ⟨lo, hi, _ | v⟩ <;> rfl

theorem searchStepS {k : α → ℕ} {cf : α → ℕ → ℕ} {st : α → ℕ × ℕ × Option ℕ}
    (hk : ComputableInPolyTime k input encNat)
    (hcf : ComputableInPolyTime (fun q : α × ℕ ↦ cf q.1 q.2) (encPair input encNat) encNat)
    (hst : ComputableInPolyTime st input encSt) :
    ComputableInPolyTime (fun a ↦ Ctx.searchStep (k a) (cf a) (st a)) input encSt := by
  simp only [searchStep_eq]
  have hlo : ComputableInPolyTime (fun a ↦ (st a).1) input encNat := (fst _ _).comp hst
  have hhi : ComputableInPolyTime (fun a ↦ (st a).2.1) input encNat :=
    ((fst _ _).comp (snd _ _)).comp hst
  have hmid : ComputableInPolyTime (fun a ↦ ((st a).1 + (st a).2.1) / 2) input encNat :=
    binDiv (binAdd hlo hhi) (const 2)
  have hcm : ComputableInPolyTime (fun a ↦ cf a (((st a).1 + (st a).2.1) / 2)) input encNat :=
    hcf.comp (id'.prod hmid)
  have hcl : ComputableInPolyTime (fun a ↦ cf a (st a).1) input encNat := hcf.comp (id'.prod hlo)
  refine optionElimWithInput (((snd _ _).comp (snd _ _)).comp hst) ?_ (hst.comp (fst _ _))
  exact itep (binary_le' (binary_sub' hhi hlo) (const 1)) hst
    (itep (decide_eq' hcm hk) (hlo.prod (hhi.prod ((optionSome _).comp hmid)))
      (itep (decide_eq' (binary_lt' hcm hk) (binary_lt' hcl hk))
        (hmid.prod (hhi.prod (const none))) (hlo.prod (hmid.prod (const none)))))

/-- The invariant of a binary search: everything at most `B`. -/
def SInv (B : ℕ) (st : ℕ × ℕ × Option ℕ) : Prop :=
  st.1 ≤ B ∧ st.2.1 ≤ B ∧ ∀ v, st.2.2 = some v → v ≤ B

theorem searchStep_inv (k : ℕ) (cf : ℕ → ℕ) {B : ℕ} {st : ℕ × ℕ × Option ℕ}
    (h : SInv B st) : SInv B (Ctx.searchStep k cf st) := by
  obtain ⟨lo, hi, o⟩ := st
  obtain ⟨hlo, hhi, ho⟩ := h
  simp only at hlo hhi ho
  have hmid : (lo + hi) / 2 ≤ B := by omega
  rcases o with _ | v
  · simp only [searchStep_eq, Option.elim]
    split_ifs
    · exact ⟨hlo, hhi, ho⟩
    · exact ⟨hlo, hhi, fun v hv ↦ by cases hv; exact hmid⟩
    · exact ⟨hmid, hhi, fun v hv ↦ by cases hv⟩
    · exact ⟨hlo, hmid, fun v hv ↦ by cases hv⟩
  · exact ⟨hlo, hhi, ho⟩

theorem len_encSt_le {B : ℕ} {st : ℕ × ℕ × Option ℕ} (h : SInv B st) :
    (encSt st).length ≤ 5 * (encNat B).length + 3 := by
  obtain ⟨lo, hi, o⟩ := st
  obtain ⟨hlo, hhi, ho⟩ := h
  simp only at hlo hhi ho
  have h1 := len_encNat_mono hlo
  have h2 := len_encNat_mono hhi
  have h3 : (encOption encNat o).length ≤ (encNat B).length + 1 := by
    rcases o with _ | v
    · simp
    · simp only [encOption_some, List.length_cons]
      have := len_encNat_mono (ho v rfl)
      omega
  simp only [encSt, length_encPair]
  omega

theorem searchIter {k : α → ℕ} {cf : α → ℕ → ℕ} {cnt B : α → ℕ}
    (hk : ComputableInPolyTime k input encNat)
    (hcf : ComputableInPolyTime (fun q : α × ℕ ↦ cf q.1 q.2) (encPair input encNat) encNat)
    (hcnt : ComputableInPolyTime cnt input encUnary) (hB : ComputableInPolyTime B input encNat) :
    ComputableInPolyTime (fun a ↦ (Ctx.searchStep (k a) (cf a))^[cnt a] (0, B a, none)) input
      encSt ∧ ∀ a, SInv (B a) ((Ctx.searchStep (k a) (cf a))^[cnt a] (0, B a, none)) := by
  have hstep : ComputableInPolyTime (fun p : α × (ℕ × ℕ × Option ℕ) ↦
      Ctx.searchStep (k p.1) (cf p.1) p.2) (encPair input encSt) encSt :=
    searchStepS (hk.comp (fst _ _)) (hcf.comp (((fst _ _).comp (fst _ _)).prod (snd _ _)))
      (snd _ _)
  exact iterateWith_spec (par := fun a ↦ a) (step := fun a st ↦ Ctx.searchStep (k a) (cf a) st)
    id' hcnt ((const 0).prod (hB.prod (const none))) hstep (fun a _ st ↦ SInv (B a) st)
    (fun a ↦ ⟨Nat.zero_le _, le_rfl, fun v hv ↦ by cases hv⟩)
    (fun a _ st _ h ↦ searchStep_inv _ _ h)
    (size := fun a ↦ 5 * (encNat (B a)).length + 3)
    (((PolyBounded.const 5).mul hB.polyBounded_length).add (.const 3))
    (fun a _ st _ h ↦ len_encSt_le h)

/-! ### Bisection -/

variable (c : Consts) {X : α → CoreIn}

/-- The binary search of the bisection. -/
def bisIter (C : Ctx) : ℕ × ℕ × Option ℕ :=
  (Ctx.searchStep C.ip.k (fun b ↦ nRegA (C.sol b)))^[C.ip.Pf] (0, 2 ^ C.ip.Pf, none)

theorem bisect_eq (C : Ctx) : C.bisect =
    if nRegA (C.sol 0) ≤ C.ip.k then .done (C.sol 0) 0
    else if nRegA (C.sol (2 ^ C.ip.Pf)) = C.ip.k then .done (C.sol (2 ^ C.ip.Pf)) (2 ^ C.ip.Pf)
    else (bisIter C).2.2.elim
      (.cont ⟨C.sol (bisIter C).2.1, C.sol (bisIter C).1, (bisIter C).2.1, (bisIter C).1⟩)
      fun b ↦ .done (C.sol b) b := by
  unfold Ctx.bisect
  split_ifs
  · rfl
  · rfl
  · unfold bisIter
    generalize (Ctx.searchStep C.ip.k (fun b ↦ nRegA (C.sol b)))^[C.ip.Pf] (0, 2 ^ C.ip.Pf, none)
      = st
    rcases st with ⟨lo, hi, _ | b⟩ <;> rfl

theorem bisIterS (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ bisIter (ctx c (X a))) input encSt := by
  have hcf : ComputableInPolyTime (fun q : α × ℕ ↦ nRegA ((ctx c (X q.1)).sol q.2))
      (encPair input encNat) encNat := toBin (nRegAU (solL c (hX.comp (fst _ _)) (snd _ _)))
  unfold bisIter
  exact (searchIter (k := fun a ↦ (ctx c (X a)).ip.k)
    (cf := fun a b ↦ nRegA ((ctx c (X a)).sol b)) (cnt := fun a ↦ (ctx c (X a)).ip.Pf)
    (B := fun a ↦ 2 ^ (ctx c (X a)).ip.Pf) (kB c hX) hcf (PfU c hX) (twoPfB c hX)).1

theorem bisectR (hX : ComputableInPolyTime X input encCI) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).bisect) input encRs := by
  simp only [bisect_eq]
  have hst := bisIterS c hX
  have hlo : ComputableInPolyTime (fun a ↦ (bisIter (ctx c (X a))).1) input encNat :=
    (fst _ _).comp hst
  have hhi : ComputableInPolyTime (fun a ↦ (bisIter (ctx c (X a))).2.1) input encNat :=
    ((fst _ _).comp (snd _ _)).comp hst
  have hop : ComputableInPolyTime (fun a ↦ (bisIter (ctx c (X a))).2.2) input
      (encOption encNat) := ((snd _ _).comp (snd _ _)).comp hst
  have hs0 := solL c hX (const 0)
  have hsP := solL c hX (twoPfB c hX)
  have h3 : ComputableInPolyTime (fun a ↦ (bisIter (ctx c (X a))).2.2.elim
      (.cont ⟨(ctx c (X a)).sol (bisIter (ctx c (X a))).2.1,
        (ctx c (X a)).sol (bisIter (ctx c (X a))).1, (bisIter (ctx c (X a))).2.1,
        (bisIter (ctx c (X a))).1⟩)
      fun b ↦ .done ((ctx c (X a)).sol b) b) input encRs :=
    optionElimWithInput hop (rsCont (prMk (solL c hX hhi) (solL c hX hlo) hhi hlo))
      (rsDone (solL c (hX.comp (fst _ _)) (snd _ _)) (snd _ _))
  have h2 := itep (decide_eq' (toBin (nRegAU hsP)) (kB c hX)) (rsDone hsP (twoPfB c hX)) h3
  exact itep (binary_le' (toBin (nRegAU hs0)) (kB c hX)) (rsDone hs0 (const 0)) h2

end BCFGJPSSV26.Greedy.PT


