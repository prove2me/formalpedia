-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMerge
-- name    : BCFGJPSSV26_Greedy_PolyTime_AuxMerge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T17:13:38.958373+00:00
-- url     : https://prove2.me/theorems/b0c47e13-1930-4998-bc2b-1c769535caa9
-- title:
--   BCFGJPSSV26.Greedy.PolyTime.AuxMerge — Polynomial time of the core: the steps of the merge
-- statement:
--   This is module `BCFGJPSSV26.Greedy.PolyTime.AuxMerge` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Certificates for `BCFGJPSSV26.Greedy.Ctx.binSearch`, `BCFGJPSSV26.Greedy.Ctx.firstFlip`,
--   `Ctx.stepC`, `Ctx.walkPhase`, `Ctx.phase` and `Ctx.mergeStep`, each a fixed composition of
--   certified functions, after rewriting its pattern matches as eliminations
--   (`BCFGJPSSV26.Greedy.PT.stepC_eq`, `BCFGJPSSV26.Greedy.PT.walkPhase_eq`, …).
--
--   **Contents.** The module is published as a whole: 29 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMerge`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/PolyTime/AuxMerge.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxRound

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.PolyTime.AuxMerge` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time of the core: the steps of the merge

Certificates for `BCFGJPSSV26.Greedy.Ctx.binSearch`, `BCFGJPSSV26.Greedy.Ctx.firstFlip`,
`Ctx.stepC`, `Ctx.walkPhase`, `Ctx.phase` and `Ctx.mergeStep`, each a fixed composition of
certified functions, after rewriting its pattern matches as eliminations
(`BCFGJPSSV26.Greedy.PT.stepC_eq`, `BCFGJPSSV26.Greedy.PT.walkPhase_eq`, …).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.PT

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

/-! ### Equations -/

/-- The binary search of `BinSearch`. -/
def binIter (C : Ctx) (f : ℚ) (pre : List (List AAtom)) (base : List AAtom) (z : ℕ) :
    ℕ × ℕ × Option ℕ :=
  (Ctx.searchStep C.ip.k (fun g ↦ C.cnt f pre (base ++ [(z, g + 1)])))^[C.ip.Pu]
    (0, 2 ^ C.ip.Pu, none)

theorem binSearch_eq (C : Ctx) (f : ℚ) (b : ℕ) (pre : List (List AAtom)) (base : List AAtom)
    (z : ℕ) : C.binSearch f b pre base z =
    if C.cnt f pre (base ++ [(z, 0 + 1)]) = C.ip.k then
      .done (C.complete f (pre ++ [base ++ [(z, 0 + 1)]])) b
    else if C.cnt f pre (base ++ [(z, 2 ^ C.ip.Pu + 1)]) = C.ip.k then
      .done (C.complete f (pre ++ [base ++ [(z, 2 ^ C.ip.Pu + 1)]])) b
    else (binIter C f pre base z).2.2.elim
      (.cont ⟨C.complete f (pre ++ [base ++ [(z, (binIter C f pre base z).1 + 1)]]),
        C.complete f (pre ++ [base ++ [(z, (binIter C f pre base z).2.1 + 1)]]), b, b⟩)
      fun g ↦ .done (C.complete f (pre ++ [base ++ [(z, g + 1)]])) b := by
  simp only [Ctx.binSearch]
  split_ifs
  · rfl
  · rfl
  · unfold binIter
    generalize (Ctx.searchStep C.ip.k (fun g ↦ C.cnt f pre (base ++ [(z, g + 1)])))^[C.ip.Pu]
      (0, 2 ^ C.ip.Pu, none) = st
    rcases st with ⟨lo, hi, _ | g⟩ <;> rfl

/-- The free copy of step C. -/
def stF (h : Option AAtom) : List AAtom := h.elim [] fun h ↦ [(h.1, 1)]

/-- The facility of the free copy of step C. -/
def stZ (h : Option AAtom) : ℕ := h.elim 0 (·.1)

/-- The sequences of step C. -/
def stPr (X Y Z : List AAtom) (h : Option AAtom) (r : ℕ) : List AAtom :=
  X ++ Y ++ Z.drop r ++ stF h

theorem stPr_fun (X Y Z : List AAtom) (h : Option AAtom) :
    stPr X Y Z h = fun r ↦ X ++ Y ++ Z.drop r ++ stF h := rfl

/-- The points of step C. -/
def stPts (X Y Z : List AAtom) (h : Option AAtom) : List (List AAtom) :=
  (X ++ Y ++ Z) :: (List.range (Z.length + 1)).map (stPr X Y Z h)

/-- The rest of step C after its first flip. -/
def stAfter (C : Ctx) (f : ℚ) (b : ℕ) (pre : List (List AAtom)) (X : List AAtom)
    (h : Option AAtom) (Y Z : List AAtom) (t : ℕ) : Ctx.Res :=
  if t = 0 then C.binSearch f b pre (X ++ Y ++ Z) (stZ h)
  else if C.cnt f pre (stPr X Y Z h t ++ [((Z.getD (t - 1) (0, 0)).1, 1)]) = C.ip.k then
    .done (C.complete f (pre ++ [stPr X Y Z h t ++ [((Z.getD (t - 1) (0, 0)).1, 1)]])) b
  else C.binSearch f b pre (stPr X Y Z h t) (Z.getD (t - 1) (0, 0)).1

theorem stepC_eq (C : Ctx) (f : ℚ) (b : ℕ) (pre : List (List AAtom)) (X : List AAtom)
    (h : Option AAtom) (Y Z : List AAtom) (dflt : Ctx.Res) : C.stepC f b pre X h Y Z dflt =
    ((stPts X Y Z h).find? fun W ↦ C.cnt f pre W = C.ip.k).elim
      ((Ctx.firstFlip C.ip.k ((stPts X Y Z h).map (C.cnt f pre))).elim dflt
        (stAfter C f b pre X h Y Z))
      fun W ↦ .done (C.complete f (pre ++ [W])) b := by
  cases h <;>
  · simp only [Ctx.stepC, stPts, stPr_fun, stF, Option.elim]
    split
    · rename_i W hW
      rw [hW]
    · rename_i hW
      rw [hW]
      simp only
      split
      · rename_i ht
        rw [ht]
        simp [stAfter, stZ]
      · rename_i t ht
        rw [ht]
        simp [stAfter, stPr, stF]
      · rename_i ht
        rw [ht]

/-- The elimination of a kind of a point of the walk. -/
def wkElim {β : Type} (k : Ctx.WKind) (d : β) (A : ℕ → β)
    (B : List AAtom → AAtom → List AAtom → List AAtom → β) : β :=
  if (wkT k).1 = 1 then A (wkT k).2.1.1
  else if (wkT k).1 = 2 then B (wkT k).2.2.1 (wkT k).2.1 (wkT k).2.2.2.1 (wkT k).2.2.2.2 else d

theorem walkPhase_eq (C : Ctx) (p : ℕ) (f : ℚ) (b : ℕ) (pre : List (List AAtom))
    (Hp H'p : List AAtom) (dflt : Ctx.Res) : C.walkPhase p f b pre Hp H'p dflt =
    (((C.walkB p f pre Hp H'p).find? fun w ↦ C.cnt f pre w.1 = C.ip.k).elim
      ((Ctx.firstFlip C.ip.k ((C.walkB p f pre Hp H'p).map fun w ↦ C.cnt f pre w.1)).elim
        (C.stepC f b pre Hp none []
          ((((C.walkB p f pre Hp H'p).reverse.headD ([], .init)).1).drop Hp.length) dflt)
        fun t ↦ wkElim ((C.walkB p f pre Hp H'p).getD (t + 1) ([], .init)).2 dflt
          (fun z ↦ C.binSearch f b pre ((C.walkB p f pre Hp H'p).getD t ([], .init)).1 z)
          fun X h Y Z ↦ C.stepC f b pre X (some h) Y Z dflt)
      fun w ↦ .done (C.complete f (pre ++ [w.1])) b) := by
  simp only [Ctx.walkPhase]
  split
  · rename_i w hw
    rw [hw]; rfl
  · rename_i hw
    rw [hw]
    split
    · rename_i t ht
      rw [ht]
      simp only [Option.elim]
      generalize ((C.walkB p f pre Hp H'p).getD (t + 1) ([], .init)).2 = k
      cases k <;> rfl
    · rename_i ht
      rw [ht]
      simp only [List.getLast?_eq_head?_reverse, List.headD_eq_head?_getD, Option.elim]

theorem phase_eq (C : Ctx) (p : ℕ) (pr : Ctx.Pair) : C.phase p pr =
    if nRegA (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])) = C.ip.k then
      .done (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])) pr.b
    else if sandwich (nRegA (C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])))
        (nRegA pr.H') C.ip.k then
      .cont ⟨C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []]), pr.H', pr.b, pr.b'⟩
    else C.walkPhase p (C.fhat pr.b) pr.b (pr.H.take p) (pr.H.getD p [])
      ((C.complete (C.fhat pr.b) (pr.H.take p ++ [pr.H'.getD p []])).getD p [])
      (.done pr.H pr.b) := rfl

theorem mergeStep_eq (C : Ctx) (r : Ctx.Res) (p : ℕ) :
    C.mergeStep r p = resElim r (fun H b ↦ .done H b) fun pr ↦ C.phase p pr := by
  cases r <;> rfl

/-! ### Certificates -/

variable {α : Type} {input : α ↪ List Bool} (c : Consts) {X : α → CoreIn}

theorem cmpL {f : α → ℚ} {pre : α → List (List AAtom)} {W : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hpre : ComputableInPolyTime pre input encSl) (hW : ComputableInPolyTime W input encSq) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).complete (f a) (pre a ++ [W a])) input encSl :=
  completeL c hX hf (listAppend' hpre (cons' hW (const [])))

theorem cntB {f : α → ℚ} {pre : α → List (List AAtom)} {W : α → List AAtom}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hpre : ComputableInPolyTime pre input encSl) (hW : ComputableInPolyTime W input encSq) :
    ComputableInPolyTime (fun a ↦ decide ((ctx c (X a)).cnt (f a) (pre a) (W a) =
      (ctx c (X a)).ip.k)) input encBool :=
  decide_eq' (toBin (cntU c hX hf hpre hW)) (kB c hX)

theorem binIterS {f : α → ℚ} {pre : α → List (List AAtom)} {base : α → List AAtom}
    {z : α → ℕ} (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hpre : ComputableInPolyTime pre input encSl) (hbase : ComputableInPolyTime base input encSq)
    (hz : ComputableInPolyTime z input encNat) :
    ComputableInPolyTime (fun a ↦ binIter (ctx c (X a)) (f a) (pre a) (base a) (z a)) input
      encSt := by
  have hcf : ComputableInPolyTime (fun q : α × ℕ ↦
      (ctx c (X q.1)).cnt (f q.1) (pre q.1) (base q.1 ++ [(z q.1, q.2 + 1)]))
      (encPair input encNat) encNat :=
    toBin (cntU c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hpre.comp (fst _ _))
      (listAppend' (hbase.comp (fst _ _)) (cons' ((hz.comp (fst _ _)).prod
        (binAdd (snd _ _) (const 1))) (const []))))
  unfold binIter
  exact (searchIter (k := fun a ↦ (ctx c (X a)).ip.k)
    (cf := fun a g ↦ (ctx c (X a)).cnt (f a) (pre a) (base a ++ [(z a, g + 1)]))
    (cnt := fun a ↦ (ctx c (X a)).ip.Pu) (B := fun a ↦ 2 ^ (ctx c (X a)).ip.Pu)
    (kB c hX) hcf (PuU c hX) (twoPuB c hX)).1

theorem binSearchR {f : α → ℚ} {b : α → ℕ} {pre : α → List (List AAtom)}
    {base : α → List AAtom} {z : α → ℕ} (hX : ComputableInPolyTime X input encCI)
    (hf : ComputableInPolyTime f input encRat) (hb : ComputableInPolyTime b input encNat)
    (hpre : ComputableInPolyTime pre input encSl) (hbase : ComputableInPolyTime base input encSq)
    (hz : ComputableInPolyTime z input encNat) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).binSearch (f a) (b a) (pre a) (base a) (z a))
      input encRs := by
  simp only [binSearch_eq]
  have hW {g : α → ℕ} (hg : ComputableInPolyTime g input encNat) :
      ComputableInPolyTime (fun a ↦ base a ++ [(z a, g a + 1)]) input encSq :=
    listAppend' hbase (cons' (hz.prod (binAdd hg (const 1))) (const []))
  have hst := binIterS c hX hf hpre hbase hz
  have hlo : ComputableInPolyTime (fun a ↦ (binIter (ctx c (X a)) (f a) (pre a) (base a)
      (z a)).1) input encNat := (fst _ _).comp hst
  have hhi : ComputableInPolyTime (fun a ↦ (binIter (ctx c (X a)) (f a) (pre a) (base a)
      (z a)).2.1) input encNat := ((fst _ _).comp (snd _ _)).comp hst
  have hW' : ComputableInPolyTime (fun q : α × ℕ ↦ base q.1 ++ [(z q.1, q.2 + 1)])
      (encPair input encNat) encSq :=
    listAppend' (hbase.comp (fst _ _)) (cons' ((hz.comp (fst _ _)).prod
      (binAdd (snd _ _) (const 1))) (const []))
  have h3 := optionElimWithInput (body := fun a g ↦ Ctx.Res.done ((ctx c (X a)).complete (f a)
      (pre a ++ [base a ++ [(z a, g + 1)]])) (b a)) (((snd _ _).comp (snd _ _)).comp hst)
    (rsCont (prMk (cmpL c hX hf hpre (hW hlo)) (cmpL c hX hf hpre (hW hhi)) hb hb))
    (rsDone (cmpL c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hpre.comp (fst _ _)) hW')
      (hb.comp (fst _ _)))
  exact itep (cntB c hX hf hpre (hW (const 0))) (rsDone (cmpL c hX hf hpre (hW (const 0))) hb)
    (itep (cntB c hX hf hpre (hW (twoPuB c hX)))
      (rsDone (cmpL c hX hf hpre (hW (twoPuB c hX))) hb) h3)

theorem takeG {β : Type} {e : β ↪ List Bool} {l : α → List β} {t : α → ℕ}
    (hl : ComputableInPolyTime l input (encList e)) (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a ↦ (l a).take (t a)) input (encList e) :=
  .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hl.tidy ht.tidy)

theorem sandwichB {x y k : α → ℕ} (hx : ComputableInPolyTime x input encNat)
    (hy : ComputableInPolyTime y input encNat) (hk : ComputableInPolyTime k input encNat) :
    ComputableInPolyTime (fun a ↦ sandwich (x a) (y a) (k a)) input encBool :=
  bool_or.comp ((bool_and' (binary_lt' hx hk) (binary_lt' hk hy)).prod
    (bool_and' (binary_lt' hy hk) (binary_lt' hk hx)))

theorem firstFlipO {k : α → ℕ} {cs : α → List ℕ} (hk : ComputableInPolyTime k input encNat)
    (hcs : ComputableInPolyTime cs input (encList encNat)) :
    ComputableInPolyTime (fun a ↦ Ctx.firstFlip (k a) (cs a)) input (encOption encUnary) :=
  findWithInput (unary_range' (unary_sub' (lenL hcs) (const 1)))
    (sandwichB (listGetDWithInput (hcs.comp (fst _ _)) (snd _ _) 0)
      (listGetDWithInput (hcs.comp (fst _ _)) (unary_add' (snd _ _) (const 1)) 0)
      (hk.comp (fst _ _)))

theorem stFS {h : α → Option AAtom} (hh : ComputableInPolyTime h input (encOption encAt)) :
    ComputableInPolyTime (fun a ↦ stF (h a)) input encSq :=
  optionElimWithInput hh (const []) (cons' (((fst _ _).comp (snd _ _)).prod (const 1)) (const []))

theorem stZB {h : α → Option AAtom} (hh : ComputableInPolyTime h input (encOption encAt)) :
    ComputableInPolyTime (fun a ↦ stZ (h a)) input encNat :=
  optionElimWithInput hh (const 0) ((fst _ _).comp (snd _ _))

theorem stPrS {Xs Ys Zs : α → List AAtom} {h : α → Option AAtom} {r : α → ℕ}
    (hXs : ComputableInPolyTime Xs input encSq) (hYs : ComputableInPolyTime Ys input encSq)
    (hZs : ComputableInPolyTime Zs input encSq)
    (hh : ComputableInPolyTime h input (encOption encAt))
    (hr : ComputableInPolyTime r input encUnary) :
    ComputableInPolyTime (fun a ↦ stPr (Xs a) (Ys a) (Zs a) (h a) (r a)) input encSq :=
  listAppend' (listAppend' (listAppend' hXs hYs) (dropS hZs hr)) (stFS hh)

theorem stAfterR {f : α → ℚ} {b : α → ℕ} {pre : α → List (List AAtom)}
    {Xs Ys Zs : α → List AAtom} {h : α → Option AAtom} {t : α → ℕ}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hb : ComputableInPolyTime b input encNat) (hpre : ComputableInPolyTime pre input encSl)
    (hXs : ComputableInPolyTime Xs input encSq)
    (hh : ComputableInPolyTime h input (encOption encAt))
    (hYs : ComputableInPolyTime Ys input encSq) (hZs : ComputableInPolyTime Zs input encSq)
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a ↦ stAfter (ctx c (X a)) (f a) (b a) (pre a) (Xs a) (h a) (Ys a)
      (Zs a) (t a)) input encRs := by
  unfold stAfter
  have hPr := stPrS hXs hYs hZs hh ht
  have hz : ComputableInPolyTime (fun a ↦ ((Zs a).getD (t a - 1) (0, 0)).1) input encNat :=
    (fst _ _).comp (listGetDWithInput hZs (unary_sub' ht (const 1)) (0, 0))
  have hW₀ := listAppend' hPr (cons' (hz.prod (const 1)) (const []))
  exact itep (decide_eq' ht (const 0))
    (binSearchR c hX hf hb hpre (listAppend' (listAppend' hXs hYs) hZs) (stZB hh))
    (itep (cntB c hX hf hpre hW₀) (rsDone (cmpL c hX hf hpre hW₀) hb)
      (binSearchR c hX hf hb hpre hPr hz))

theorem stepCR {f : α → ℚ} {b : α → ℕ} {pre : α → List (List AAtom)}
    {Xs Ys Zs : α → List AAtom} {h : α → Option AAtom} {dflt : α → Ctx.Res}
    (hX : ComputableInPolyTime X input encCI) (hf : ComputableInPolyTime f input encRat)
    (hb : ComputableInPolyTime b input encNat) (hpre : ComputableInPolyTime pre input encSl)
    (hXs : ComputableInPolyTime Xs input encSq)
    (hh : ComputableInPolyTime h input (encOption encAt))
    (hYs : ComputableInPolyTime Ys input encSq) (hZs : ComputableInPolyTime Zs input encSq)
    (hd : ComputableInPolyTime dflt input encRs) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).stepC (f a) (b a) (pre a) (Xs a) (h a) (Ys a)
      (Zs a) (dflt a)) input encRs := by
  simp only [stepC_eq]
  have hpts : ComputableInPolyTime (fun a ↦ stPts (Xs a) (Ys a) (Zs a) (h a)) input encSl :=
    cons' (listAppend' (listAppend' hXs hYs) hZs)
      (mapWithInput (unary_range' (unary_add' (lenL hZs) (const 1)))
        (stPrS (hXs.comp (fst _ _)) (hYs.comp (fst _ _)) (hZs.comp (fst _ _))
          (hh.comp (fst _ _)) (snd _ _)))
  have hfind := findWithInput (test := fun a W ↦ decide ((ctx c (X a)).cnt (f a) (pre a) W =
    (ctx c (X a)).ip.k)) hpts (cntB c (hX.comp (fst _ _)) (hf.comp (fst _ _))
      (hpre.comp (fst _ _)) (snd _ _))
  have hff := firstFlipO (kB c hX) (mapWithInput (f := fun a W ↦ (ctx c (X a)).cnt (f a) (pre a) W)
    hpts (toBin (cntU c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hpre.comp (fst _ _))
      (snd _ _))))
  have hA := stAfterR c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hb.comp (fst _ _))
    (hpre.comp (fst _ _)) (hXs.comp (fst _ _)) (hh.comp (fst _ _)) (hYs.comp (fst _ _))
    (hZs.comp (fst _ _)) (snd input encUnary)
  exact optionElimWithInput (body := fun a W ↦ Ctx.Res.done ((ctx c (X a)).complete (f a)
      (pre a ++ [W])) (b a)) hfind
    (optionElimWithInput (body := fun a t ↦ stAfter (ctx c (X a)) (f a) (b a) (pre a) (Xs a)
      (h a) (Ys a) (Zs a) t) hff hd hA)
    (rsDone (cmpL c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hpre.comp (fst _ _)) (snd _ _))
      (hb.comp (fst _ _)))

theorem wkElimR {β : Type} {encB : β ↪ List Bool} {k : α → Ctx.WKind} {d : α → β}
    {A : α → ℕ → β} {B : α → List AAtom → AAtom → List AAtom → List AAtom → β}
    (hk : ComputableInPolyTime k input encWK) (hd : ComputableInPolyTime d input encB)
    (hA : ComputableInPolyTime (fun q : α × ℕ ↦ A q.1 q.2) (encPair input encNat) encB)
    (hB : ComputableInPolyTime (fun q : α × (AAtom × List AAtom × List AAtom × List AAtom) ↦
      B q.1 q.2.2.1 q.2.1 q.2.2.2.1 q.2.2.2.2)
      (encPair input (encPair encAt (encPair encSq (encPair encSq encSq)))) encB) :
    ComputableInPolyTime (fun a ↦ wkElim (k a) (d a) (A a) (B a)) input encB := by
  unfold wkElim
  have ht := wkTt hk
  exact itep (decide_eq' ((fst _ _).comp ht) (const 1))
    (hA.comp (id'.prod ((fst _ _).comp ((fst _ _).comp ((snd _ _).comp ht)))))
    (itep (decide_eq' ((fst _ _).comp ht) (const 2)) (hB.comp (id'.prod ((snd _ _).comp ht))) hd)

theorem walkPhaseR {p : α → ℕ} {f : α → ℚ} {b : α → ℕ} {pre : α → List (List AAtom)}
    {Hp H'p : α → List AAtom} {dflt : α → Ctx.Res}
    (hX : ComputableInPolyTime X input encCI) (hp : ComputableInPolyTime p input encUnary)
    (hf : ComputableInPolyTime f input encRat) (hb : ComputableInPolyTime b input encNat)
    (hpre : ComputableInPolyTime pre input encSl) (hHp : ComputableInPolyTime Hp input encSq)
    (hH'p : ComputableInPolyTime H'p input encSq) (hd : ComputableInPolyTime dflt input encRs) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).walkPhase (p a) (f a) (b a) (pre a) (Hp a)
      (H'p a) (dflt a)) input encRs := by
  simp only [walkPhase_eq]
  have hpts := walkBS c hX hp hf hpre hHp hH'p
  have hfind := findWithInput (test := fun a w ↦ decide ((ctx c (X a)).cnt (f a) (pre a) w.1 =
    (ctx c (X a)).ip.k)) hpts (cntB c (hX.comp (fst _ _)) (hf.comp (fst _ _))
      (hpre.comp (fst _ _)) ((fst _ _).comp (snd _ _)))
  have hff := firstFlipO (kB c hX) (mapWithInput (f := fun a w ↦
    (ctx c (X a)).cnt (f a) (pre a) w.1) hpts (toBin (cntU c (hX.comp (fst _ _))
      (hf.comp (fst _ _)) (hpre.comp (fst _ _)) ((fst _ _).comp (snd _ _)))))
  have hrev := ComputableTidilyInPolyTime.listReverseWithInput hpts.tidy
  have hlast := ComputableInPolyTime.of_tidy (ComputableTidilyInPolyTime.listHeadDWithInput
    (([] : List AAtom), Ctx.WKind.init) hrev)
  have hnone := stepCR c hX hf hb hpre hHp (const none) (const [])
    (dropS ((fst _ _).comp hlast) (lenL hHp)) hd
  have hpts' := hpts.comp (fst input encUnary)
  have hk : ComputableInPolyTime (fun q : α × ℕ ↦ (((ctx c (X q.1)).walkB (p q.1) (f q.1)
      (pre q.1) (Hp q.1) (H'p q.1)).getD (q.2 + 1) ([], .init)).2) (encPair input encUnary)
      encWK := (snd _ _).comp (listGetDWithInput hpts' (unary_add' (snd _ _) (const 1)) ([], .init))
  have hpt : ComputableInPolyTime (fun q : α × ℕ ↦ (((ctx c (X q.1)).walkB (p q.1) (f q.1)
      (pre q.1) (Hp q.1) (H'p q.1)).getD q.2 ([], .init)).1) (encPair input encUnary) encSq :=
    (fst _ _).comp (listGetDWithInput hpts' (snd _ _) ([], .init))
  have hA : ComputableInPolyTime (fun q : (α × ℕ) × ℕ ↦ (ctx c (X q.1.1)).binSearch (f q.1.1)
      (b q.1.1) (pre q.1.1) (((ctx c (X q.1.1)).walkB (p q.1.1) (f q.1.1) (pre q.1.1) (Hp q.1.1)
        (H'p q.1.1)).getD q.1.2 ([], .init)).1 q.2) (encPair (encPair input encUnary) encNat)
      encRs :=
    binSearchR c (hX.comp ((fst _ _).comp (fst _ _))) (hf.comp ((fst _ _).comp (fst _ _)))
      (hb.comp ((fst _ _).comp (fst _ _))) (hpre.comp ((fst _ _).comp (fst _ _)))
      (hpt.comp (fst _ _)) (snd _ _)
  have hB : ComputableInPolyTime (fun q : (α × ℕ) × (AAtom × List AAtom × List AAtom ×
      List AAtom) ↦ (ctx c (X q.1.1)).stepC (f q.1.1) (b q.1.1) (pre q.1.1) q.2.2.1 (some q.2.1)
        q.2.2.2.1 q.2.2.2.2 (dflt q.1.1))
      (encPair (encPair input encUnary) (encPair encAt (encPair encSq (encPair encSq encSq))))
      encRs :=
    stepCR c (hX.comp ((fst _ _).comp (fst _ _))) (hf.comp ((fst _ _).comp (fst _ _)))
      (hb.comp ((fst _ _).comp (fst _ _))) (hpre.comp ((fst _ _).comp (fst _ _)))
      ((fst _ _).comp ((snd _ _).comp (snd _ _))) ((optionSome _).comp ((fst _ _).comp (snd _ _)))
      ((fst _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
      ((snd _ _).comp ((snd _ _).comp ((snd _ _).comp (snd _ _))))
      (hd.comp ((fst _ _).comp (fst _ _)))
  have hsome := wkElimR (k := fun q : α × ℕ ↦ (((ctx c (X q.1)).walkB (p q.1) (f q.1)
      (pre q.1) (Hp q.1) (H'p q.1)).getD (q.2 + 1) ([], .init)).2) (d := fun q ↦ dflt q.1)
    (A := fun q z ↦ (ctx c (X q.1)).binSearch (f q.1) (b q.1) (pre q.1)
      (((ctx c (X q.1)).walkB (p q.1) (f q.1) (pre q.1) (Hp q.1) (H'p q.1)).getD q.2
        ([], .init)).1 z)
    (B := fun q Xs h Ys Zs ↦ (ctx c (X q.1)).stepC (f q.1) (b q.1) (pre q.1) Xs (some h) Ys Zs
      (dflt q.1)) hk (hd.comp (fst _ _)) hA hB
  exact optionElimWithInput (body := fun a w ↦ Ctx.Res.done ((ctx c (X a)).complete (f a)
      (pre a ++ [w.1])) (b a)) hfind
    (optionElimWithInput (body := fun a t ↦ wkElim (((ctx c (X a)).walkB (p a) (f a) (pre a)
        (Hp a) (H'p a)).getD (t + 1) ([], .init)).2 (dflt a)
        (fun z ↦ (ctx c (X a)).binSearch (f a) (b a) (pre a) (((ctx c (X a)).walkB (p a) (f a)
          (pre a) (Hp a) (H'p a)).getD t ([], .init)).1 z)
        fun Xs h Ys Zs ↦ (ctx c (X a)).stepC (f a) (b a) (pre a) Xs (some h) Ys Zs (dflt a))
      hff hnone hsome)
    (rsDone (cmpL c (hX.comp (fst _ _)) (hf.comp (fst _ _)) (hpre.comp (fst _ _))
      ((fst _ _).comp (snd _ _))) (hb.comp (fst _ _)))

theorem phaseR {p : α → ℕ} {pr : α → Ctx.Pair} (hX : ComputableInPolyTime X input encCI)
    (hp : ComputableInPolyTime p input encUnary) (hpr : ComputableInPolyTime pr input encPr) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).phase (p a) (pr a)) input encRs := by
  simp only [phase_eq]
  have hb := prb hpr
  have hH := prH hpr
  have hH' := prH' hpr
  have hf := fhatQ c hX hb
  have hpre := takeG hH hp
  have hH'' := cmpL c hX hf hpre (listGetDWithInput hH' hp [])
  exact itep (decide_eq' (toBin (nRegAU hH'')) (kB c hX)) (rsDone hH'' hb)
    (ite' (sandwichB (toBin (nRegAU hH'')) (toBin (nRegAU hH')) (kB c hX))
      (rsCont (prMk hH'' hH' hb (prb' hpr)))
      (walkPhaseR c hX hp hf hb hpre (listGetDWithInput hH hp []) (listGetDWithInput hH'' hp [])
        (rsDone hH hb)))

theorem mergeStepR {r : α → Ctx.Res} {p : α → ℕ} (hX : ComputableInPolyTime X input encCI)
    (hr : ComputableInPolyTime r input encRs) (hp : ComputableInPolyTime p input encUnary) :
    ComputableInPolyTime (fun a ↦ (ctx c (X a)).mergeStep (r a) (p a)) input encRs := by
  simp only [mergeStep_eq]
  exact rsElim (F := fun _ H b ↦ Ctx.Res.done H b) (G := fun a pr ↦ (ctx c (X a)).phase (p a) pr)
    hr (rsDone ((fst _ _).comp (snd _ _)) ((snd _ _).comp (snd _ _)))
    (phaseR c (hX.comp (fst _ _)) (hp.comp (fst _ _)) (snd _ _))

end BCFGJPSSV26.Greedy.PT


