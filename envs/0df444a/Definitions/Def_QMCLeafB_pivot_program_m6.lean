-- Prove2me | Definitions.Def_QMCLeafB_pivot_program_m6
-- name    : QMCLeafB_pivot_program_m6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:23:38.66019+00:00
-- url     : https://prove2.me/theorems/0684e60d-9722-4bb4-b144-43d53ee97ab0
-- title:
--   QMCLeafB pivot_program_m6
-- statement:
--   # leaf B phase 10 — brick `pivot-program` (swarm `smw02tv7j`, member m6, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sep_oracle_m1
import Definitions.Def_QMCLeafB_poly_loop_toolkit
/-
# leaf B phase 10 — brick `pivot-program` (swarm `smw02tv7j`, member m6, direction d1)

The LDLT descent of `SepOracle.split` re-packaged as an `Automatic.Poly` loop, with the exact
location of what is *not* closable in the exact-rational fragment.

## Machine-checked here (EXIT=0, no `sorry`, no `axiom`, standard three)

**§0–§1 the step, unconditionally.**  `SepOracle.split`'s pivot recursion is not a search (m6's
`pivot_existence`: `pivot_nonneg`, `headRow_eq_zero_of_psd`, `split_psd_of_psd`): pivot index `0`,
one rational comparison on `X₀₀`, one zero-row test.  `pivStep` is that step on a row-coded block
`Rows = List (List ℚ)` plus the LDLT accumulator `Acc` (pivot `a` and head row `b` of each branch,
most recent first), and `poly_pivStep : Poly (fun st => pivStep st)` is proved with **no
hypotheses** — the five branches of `brStop/brNeg/brZero/brDrop/brSchur`, both `Sum` injections,
`Poly.ite`/`Poly.ite_prop`, `list_map`/`zip`/`head`/`tail`, `rat_*`.

**§2 the loop.**  `pivStep_snd_length` (an `inr` step strictly shrinks the block, so the descent is
≤ `k+1` steps), `runPivFuel_bounded` (the `BoundedRun` witness), and
`poly_runPiv : Poly (fun st => runPiv st)` from `PolyLoop.poly_loop` with `iterations = X + 1`, plus
**one** hypothesis `SizeProfile sizes` — every visited state's encoded length ≤ `sizes.eval` of the
input's.  `poly_verdict_comp` is the shape the round slot consumes.

**§3 the profile is the whole problem.**  With the library's `HasHeight`, `schurRows_height` gives
the exact per-step growth `L ↦ 4L + 1`, `height_iterate_naive` gives `5^j (L+1)` after `j` steps,
and `no_linear_profile` machine-checks that no linear budget survives it (the same argument kills
every polynomial).  So the exact-rational descent is **not** a `PolyProgram` by this route: the
true height is `O(k·H)` (entries of the k-th Schur complement are ratios of leading minors) and the
proof needs the Sylvester / Desnanot–Jacobi identity, absent from Mathlib (m3's phase-9 crux
warning, measured there as slope ≈ H per pivot step).  The remaining route is m3's *snapped*
descent (heights reset by `hasHeight_snapDiv`) with `RelaxKit`'s `relaxBodyLE` margins, at the price
of the stability bound `max|W − snap cX| ≤ n·2^{-D}`.

**§4 the mathematics of one step, bound to `SepOracle`.**  `psd_of_schur_child` / `psd_of_tail_child`
(completion of squares; the `ok` transfer the descent needs), `witness_pivot_neg` /
`witness_schur` / `witness_tail` (the `cut` lift), `okReport_of_psd` / `goodCut_of_violated` (the two
`Response` branches in consumer form), and `liftStep`/`liftWitness` (`poly_liftStep`) for the
accumulated lift through the pivot stack.

**§5 the two residual obligations, named** (as `def`s — nothing is assumed): `SizeProfile` (O1, §3
shows why it is not free) and `SchurBridge` (O2: `toMat`/`Code`, that the program's row operations
are `SepOracle`'s `schur`/`tail` — pure list `getD`/`getElem?` bookkeeping, not analysis).

## See also

`REPORT.md` in this directory: what closes, what does not, and what the phase-10 merge must state.
-/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.PolyLoop

namespace QMCLeafB.PivotProgram

/-! ## 0.  The state and one exact LDLT step -/

abbrev Rows : Type := List (List ℚ)
abbrev Acc : Type := List (ℚ × List ℚ)
abbrev St : Type := Rows × Acc
abbrev Ans : Type := Bool × List ℚ

def headRowD (rows : Rows) : List ℚ := rows.head?.getD []
def piv (rows : Rows) : ℚ := (headRowD rows).head?.getD 0
def headTail (rows : Rows) : List ℚ := (headRowD rows).tail
def rowSq (v : List ℚ) : ℚ := (v.map fun q => q * q).sum
def dotL (x y : List ℚ) : ℚ := ((x.zip y).map fun p => p.1 * p.2).sum
def qformRows (rows : Rows) (b : List ℚ) : ℚ := ((rows.zip b).map fun p => p.2 * dotL p.1 b).sum
def negWitness (rows : Rows) : List ℚ := 1 :: (rows.tail.map fun _ => (0 : ℚ))
def dropRows (rows : Rows) : Rows := rows.tail.map List.tail
def schurRowStep (a : ℚ) (b : List ℚ) (p : List ℚ × ℚ) : List ℚ :=
  (p.1.tail.zip b).map fun s => s.1 - p.2 * s.2 / a
def schurRows (rows : Rows) : Rows :=
  (rows.tail.zip (headTail rows)).map fun p => schurRowStep (piv rows) (headTail rows) p
def zeroWitness (rows : Rows) : List ℚ :=
  (-(qformRows (dropRows rows) (headTail rows) + 1) / (2 * rowSq (headTail rows))) :: headTail rows

/-! ### 0.1  The five branches, as functions -/

def brStop (_ : St) : Ans ⊕ St := Sum.inl (false, [])
def brNeg (st : St) : Ans ⊕ St := Sum.inl (true, negWitness st.1)
def brZero (st : St) : Ans ⊕ St := Sum.inl (true, zeroWitness st.1)
def brDrop (st : St) : Ans ⊕ St := Sum.inr (dropRows st.1, st.2)
def brSchur (st : St) : Ans ⊕ St := Sum.inr (schurRows st.1, (piv st.1, headTail st.1) :: st.2)

/-- **One exact LDLT descent step** (fixed pivot `0`, no search). -/
def pivStep (st : St) : Ans ⊕ St :=
  if st.1.isEmpty then brStop st
  else if piv st.1 < 0 then brNeg st
  else if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDrop st else brZero st)
  else brSchur st

def stepBody : St → Ans ⊕ St := pivStep

/-! ## 1.  The step is a `Poly` program (unconditional) -/

theorem poly_rat_sum : Poly (List.sum : List ℚ → ℚ) := ⟨PolyProgram.ratSum⟩

theorem poly_pr_fstFst {α β γ : Type} [Coding α] [Coding β] [Coding γ] :
    Poly (fun x : (α × β) × γ => x.1.1) :=
  Poly.comp (f := (Prod.fst : α × β → α)) (g := Prod.fst) Poly.fst Poly.fst

theorem poly_pr_fstSnd {α β γ : Type} [Coding α] [Coding β] [Coding γ] :
    Poly (fun x : (α × β) × γ => x.1.2) :=
  Poly.comp (f := (Prod.snd : α × β → β)) (g := Prod.fst) Poly.snd Poly.fst

theorem poly_pr_sndFst {α β γ : Type} [Coding α] [Coding β] [Coding γ] :
    Poly (fun x : α × (β × γ) => x.2.1) :=
  Poly.comp (f := (Prod.fst : β × γ → β)) (g := Prod.snd) Poly.fst Poly.snd

theorem poly_pr_sndSnd {α β γ : Type} [Coding α] [Coding β] [Coding γ] :
    Poly (fun x : α × (β × γ) => x.2.2) :=
  Poly.comp (f := (Prod.snd : β × γ → γ)) (g := Prod.snd) Poly.snd Poly.snd

theorem poly_comp_fst {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {f : α → γ} (hf : Poly f) : Poly (fun x : α × β => f x.1) := Poly.comp hf Poly.fst

theorem poly_comp_snd {α β γ : Type} [Coding α] [Coding β] [Coding γ]
    {f : β → γ} (hf : Poly f) : Poly (fun x : α × β => f x.2) := Poly.comp hf Poly.snd

theorem poly_const' {α β : Type} [Coding α] [Coding β] (b : β) : Poly (fun _ : α => b) :=
  Automatic.Poly.const b

theorem poly_headRowD : Poly (fun rows : Rows => headRowD rows) :=
  Poly.list_head_comp (α := Rows) (β := List ℚ) ([] : List ℚ) Poly.identity

theorem poly_piv : Poly (fun rows : Rows => piv rows) :=
  Poly.comp (f := fun v : List ℚ => v.head?.getD (0 : ℚ)) (g := fun rows : Rows => headRowD rows)
    (Poly.list_head (0 : ℚ)) poly_headRowD

theorem poly_headTail : Poly (fun rows : Rows => headTail rows) :=
  Poly.comp (f := (List.tail : List ℚ → List ℚ)) (g := fun rows : Rows => headRowD rows)
    Poly.list_tail poly_headRowD

theorem poly_sq : Poly (fun q : ℚ => q * q) :=
  Poly.comp (f := fun x : ℚ × ℚ => x.1 * x.2) (g := fun q : ℚ => (q, q)) Poly.rat_mul
    (Poly.pair Poly.identity Poly.identity)

theorem poly_rowSq : Poly (fun v : List ℚ => rowSq v) := by
  have hmap : Poly (fun v : List ℚ => v.map fun q => q * q) :=
    Poly.list_map (f := fun (_ : List ℚ) (q : ℚ) => q * q) (as := fun v : List ℚ => v)
      (Poly.comp (f := fun q : ℚ => q * q) (g := Prod.snd) poly_sq Poly.snd) Poly.identity
  exact Poly.comp (f := (List.sum : List ℚ → ℚ))
    (g := fun v : List ℚ => v.map fun q => q * q) poly_rat_sum hmap

theorem poly_dotL : Poly (fun p : List ℚ × List ℚ => dotL p.1 p.2) := by
  have hmap : Poly (fun p : List ℚ × List ℚ => (p.1.zip p.2).map fun q => q.1 * q.2) :=
    Poly.list_map (f := fun (_ : List ℚ × List ℚ) (q : ℚ × ℚ) => q.1 * q.2)
      (as := fun p : List ℚ × List ℚ => p.1.zip p.2)
      (Poly.comp (f := fun y : ℚ × ℚ => y.1 * y.2) (g := Prod.snd) Poly.rat_mul Poly.snd)
      Poly.list_zip
  exact Poly.comp (f := (List.sum : List ℚ → ℚ))
    (g := fun p : List ℚ × List ℚ => (p.1.zip p.2).map fun q => q.1 * q.2) poly_rat_sum hmap

theorem poly_qformRows : Poly (fun p : Rows × List ℚ => qformRows p.1 p.2) := by
  have hzip : Poly (fun p : Rows × List ℚ => p.1.zip p.2) := Poly.list_zip
  have hdot : Poly (fun x : (Rows × List ℚ) × (List ℚ × ℚ) => dotL x.2.1 x.1.2) :=
    Poly.comp (f := fun y : List ℚ × List ℚ => dotL y.1 y.2)
      (g := fun x : (Rows × List ℚ) × (List ℚ × ℚ) => (x.2.1, x.1.2)) poly_dotL
      (Poly.pair (poly_pr_sndFst (α := Rows × List ℚ) (β := List ℚ) (γ := ℚ))
        (poly_pr_fstSnd (α := Rows) (β := List ℚ) (γ := List ℚ × ℚ)))
  have hprod : Poly (fun x : (Rows × List ℚ) × (List ℚ × ℚ) => x.2.2 * dotL x.2.1 x.1.2) :=
    Poly.comp (f := fun y : ℚ × ℚ => y.1 * y.2)
      (g := fun x : (Rows × List ℚ) × (List ℚ × ℚ) => (x.2.2, dotL x.2.1 x.1.2)) Poly.rat_mul
      (Poly.pair (poly_pr_sndSnd (α := Rows × List ℚ) (β := List ℚ) (γ := ℚ)) hdot)
  have hmap : Poly (fun p : Rows × List ℚ => (p.1.zip p.2).map fun q => q.2 * dotL q.1 p.2) :=
    Poly.list_map (f := fun (p : Rows × List ℚ) (q : List ℚ × ℚ) => q.2 * dotL q.1 p.2)
      (as := fun p : Rows × List ℚ => p.1.zip p.2) hprod hzip
  exact Poly.comp (f := (List.sum : List ℚ → ℚ))
    (g := fun p : Rows × List ℚ => (p.1.zip p.2).map fun q => q.2 * dotL q.1 p.2)
    poly_rat_sum hmap

theorem poly_negWitness : Poly (fun rows : Rows => negWitness rows) := by
  have hmap : Poly (fun rows : Rows => rows.tail.map fun _ => (0 : ℚ)) :=
    Poly.list_map (f := fun (_ : Rows) (_ : List ℚ) => (0 : ℚ)) (as := fun rows : Rows => rows.tail)
      (Poly.comp (f := fun (_ : List ℚ) => (0 : ℚ))
        (g := (Prod.snd : Rows × List ℚ → List ℚ)) (poly_const' (α := List ℚ) (β := ℚ) 0) Poly.snd)
      Poly.list_tail
  have hpair : Poly (fun rows : Rows => ((1 : ℚ), rows.tail.map fun _ => (0 : ℚ))) :=
    Poly.pair (poly_const' (α := Rows) (β := ℚ) 1) hmap
  exact Poly.comp (f := fun x : ℚ × List ℚ => x.1 :: x.2)
    (g := fun rows : Rows => ((1 : ℚ), rows.tail.map fun _ => (0 : ℚ))) Poly.list_cons hpair

theorem poly_dropRows : Poly (fun rows : Rows => dropRows rows) :=
  Poly.list_map (f := fun (_ : Rows) (row : List ℚ) => row.tail) (as := fun rows : Rows => rows.tail)
    (Poly.comp (f := (List.tail : List ℚ → List ℚ)) (g := (Prod.snd : Rows × List ℚ → List ℚ))
      Poly.list_tail Poly.snd) Poly.list_tail

theorem poly_schurRowStep :
    Poly (fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => schurRowStep x.1.1 x.1.2 x.2) := by
  have htail : Poly (fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => x.2.1.tail) :=
    Poly.comp (f := (List.tail : List ℚ → List ℚ))
      (g := fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => x.2.1) Poly.list_tail
      (poly_pr_sndFst (α := ℚ × List ℚ) (β := List ℚ) (γ := ℚ))
  have hb : Poly (fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => x.1.2) :=
    poly_pr_fstSnd (α := ℚ) (β := List ℚ) (γ := List ℚ × ℚ)
  have hzip : Poly (fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => x.2.1.tail.zip x.1.2) :=
    Poly.comp (f := fun y : List ℚ × List ℚ => y.1.zip y.2)
      (g := fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => (x.2.1.tail, x.1.2)) Poly.list_zip
      (Poly.pair htail hb)
  have hinner : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) =>
      y.2.1 - y.1.2.2 * y.2.2 / y.1.1.1) := by
    have ha : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => y.1.1.1) :=
      poly_comp_fst (poly_pr_fstFst (α := ℚ) (β := List ℚ) (γ := List ℚ × ℚ))
    have hbi : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => y.1.2.2) :=
      poly_comp_fst (poly_pr_sndSnd (α := ℚ × List ℚ) (β := List ℚ) (γ := ℚ))
    have hs1 : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => y.2.1) :=
      poly_pr_sndFst (α := (ℚ × List ℚ) × (List ℚ × ℚ)) (β := ℚ) (γ := ℚ)
    have hs2 : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => y.2.2) :=
      poly_pr_sndSnd (α := (ℚ × List ℚ) × (List ℚ × ℚ)) (β := ℚ) (γ := ℚ)
    have hmul : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => y.1.2.2 * y.2.2) :=
      Poly.comp (f := fun z : ℚ × ℚ => z.1 * z.2)
        (g := fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => (y.1.2.2, y.2.2)) Poly.rat_mul
        (Poly.pair hbi hs2)
    have hdiv : Poly (fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) =>
        y.1.2.2 * y.2.2 / y.1.1.1) :=
      Poly.comp (f := fun z : ℚ × ℚ => z.1 / z.2)
        (g := fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) => (y.1.2.2 * y.2.2, y.1.1.1))
        Poly.rat_div (Poly.pair hmul ha)
    exact Poly.comp (f := fun z : ℚ × ℚ => z.1 - z.2)
      (g := fun y : ((ℚ × List ℚ) × (List ℚ × ℚ)) × (ℚ × ℚ) =>
        (y.2.1, y.1.2.2 * y.2.2 / y.1.1.1)) Poly.rat_sub (Poly.pair hs1 hdiv)
  exact Poly.list_map (f := fun (x : (ℚ × List ℚ) × (List ℚ × ℚ)) (s : ℚ × ℚ) =>
      s.1 - x.2.2 * s.2 / x.1.1)
    (as := fun x : (ℚ × List ℚ) × (List ℚ × ℚ) => x.2.1.tail.zip x.1.2) hinner hzip

theorem poly_schurRows : Poly (fun rows : Rows => schurRows rows) := by
  have hzip : Poly (fun rows : Rows => rows.tail.zip (headTail rows)) :=
    Poly.comp (f := fun x : List (List ℚ) × List ℚ => x.1.zip x.2)
      (g := fun rows : Rows => (rows.tail, headTail rows)) Poly.list_zip
      (Poly.pair Poly.list_tail poly_headTail)
  have hpiv : Poly (fun x : Rows × (List ℚ × ℚ) => piv x.1) :=
    Poly.comp (f := fun rows : Rows => piv rows) (g := Prod.fst) poly_piv Poly.fst
  have hhead : Poly (fun x : Rows × (List ℚ × ℚ) => headTail x.1) :=
    Poly.comp (f := fun rows : Rows => headTail rows) (g := Prod.fst) poly_headTail Poly.fst
  have hstep : Poly (fun x : Rows × (List ℚ × ℚ) => schurRowStep (piv x.1) (headTail x.1) x.2) :=
    Poly.comp (f := fun y : (ℚ × List ℚ) × (List ℚ × ℚ) => schurRowStep y.1.1 y.1.2 y.2)
      (g := fun x : Rows × (List ℚ × ℚ) => ((piv x.1, headTail x.1), x.2)) poly_schurRowStep
      (Poly.pair (Poly.pair hpiv hhead) Poly.snd)
  exact Poly.list_map (f := fun (rows : Rows) (p : List ℚ × ℚ) =>
      schurRowStep (piv rows) (headTail rows) p)
    (as := fun rows : Rows => rows.tail.zip (headTail rows)) hstep hzip

/-! ### 1.2  The zero-pivot witness and the whole step -/

theorem poly_zw_num : Poly (fun rows : Rows =>
    -(qformRows (dropRows rows) (headTail rows) + 1)) := by
  have hq : Poly (fun rows : Rows => qformRows (dropRows rows) (headTail rows)) :=
    Poly.comp (f := fun p : Rows × List ℚ => qformRows p.1 p.2)
      (g := fun rows : Rows => (dropRows rows, headTail rows)) poly_qformRows
      (Poly.pair poly_dropRows poly_headTail)
  have hq1 : Poly (fun rows : Rows => qformRows (dropRows rows) (headTail rows) + 1) :=
    Poly.comp (f := fun z : ℚ × ℚ => z.1 + z.2)
      (g := fun rows : Rows => (qformRows (dropRows rows) (headTail rows), 1)) Poly.rat_add
      (Poly.pair hq (poly_const' (α := Rows) (β := ℚ) 1))
  exact Poly.comp (f := fun q : ℚ => -q)
    (g := fun rows : Rows => qformRows (dropRows rows) (headTail rows) + 1) Poly.rat_neg hq1

theorem poly_zeroWitness : Poly (fun rows : Rows => zeroWitness rows) := by
  have hden : Poly (fun rows : Rows => 2 * rowSq (headTail rows)) :=
    Poly.comp (f := fun z : ℚ × ℚ => z.1 * z.2)
      (g := fun rows : Rows => (2, rowSq (headTail rows))) Poly.rat_mul
      (Poly.pair (poly_const' (α := Rows) (β := ℚ) 2)
        (Poly.comp (f := fun v : List ℚ => rowSq v) (g := headTail) poly_rowSq poly_headTail))
  have hdiv : Poly (fun rows : Rows =>
      -(qformRows (dropRows rows) (headTail rows) + 1) / (2 * rowSq (headTail rows))) :=
    Poly.comp (f := fun z : ℚ × ℚ => z.1 / z.2)
      (g := fun rows : Rows =>
        (-(qformRows (dropRows rows) (headTail rows) + 1), 2 * rowSq (headTail rows)))
      Poly.rat_div (Poly.pair poly_zw_num hden)
  exact Poly.comp (f := fun z : ℚ × List ℚ => z.1 :: z.2)
    (g := fun rows : Rows =>
      (-(qformRows (dropRows rows) (headTail rows) + 1) / (2 * rowSq (headTail rows)), headTail rows))
    Poly.list_cons (Poly.pair hdiv poly_headTail)

theorem poly_brStop : Poly brStop :=
  poly_sumInl_comp (poly_const' (α := St) (β := Ans) (false, []))

theorem poly_brNeg : Poly brNeg :=
  poly_sumInl_comp
    (Poly.pair (poly_const' (α := St) (β := Bool) true)
      (Poly.comp (f := fun rows : Rows => negWitness rows) (g := Prod.fst) poly_negWitness Poly.fst))

theorem poly_brZero : Poly brZero :=
  poly_sumInl_comp
    (Poly.pair (poly_const' (α := St) (β := Bool) true)
      (Poly.comp (f := fun rows : Rows => zeroWitness rows) (g := Prod.fst) poly_zeroWitness Poly.fst))

theorem poly_brDrop : Poly brDrop :=
  poly_sumInr_comp
    (Poly.pair (Poly.comp (f := fun rows : Rows => dropRows rows) (g := Prod.fst) poly_dropRows Poly.fst)
      Poly.snd)

theorem poly_brSchur : Poly brSchur :=
  poly_sumInr_comp
    (Poly.pair (Poly.comp (f := fun rows : Rows => schurRows rows) (g := Prod.fst) poly_schurRows Poly.fst)
      (Poly.comp (f := fun z : (ℚ × List ℚ) × Acc => z.1 :: z.2)
        (g := fun st : St => ((piv st.1, headTail st.1), st.2)) Poly.list_cons
        (Poly.pair (Poly.pair
          (Poly.comp (f := fun rows : Rows => piv rows) (g := Prod.fst) poly_piv Poly.fst)
          (Poly.comp (f := fun rows : Rows => headTail rows) (g := Prod.fst) poly_headTail Poly.fst))
          Poly.snd)))

/-- **The step is a `Poly` program.** -/
theorem poly_pivStep : Poly (fun st : St => pivStep st) := by
  have hEmpty : Poly (fun st : St => st.1.isEmpty) :=
    Poly.comp (f := (List.isEmpty : Rows → Bool)) (g := Prod.fst) Poly.list_empty Poly.fst
  have hpiv : Poly (fun st : St => piv st.1) := Poly.comp poly_piv Poly.fst
  have hhead : Poly (fun st : St => headTail st.1) := Poly.comp poly_headTail Poly.fst
  have hneg : Poly (fun st : St => decide (piv st.1 < 0)) :=
    Poly.rat_lt_comp hpiv (poly_const' (α := St) (β := ℚ) 0)
  have hzero : Poly (fun st : St => decide (piv st.1 = 0)) :=
    Poly.rat_eq_comp hpiv (poly_const' (α := St) (β := ℚ) 0)
  have hsq : Poly (fun st : St => rowSq (headTail st.1)) :=
    Poly.comp (f := fun v : List ℚ => rowSq v) (g := fun st : St => headTail st.1) poly_rowSq hhead
  have hsqz : Poly (fun st : St => decide (rowSq (headTail st.1) = 0)) :=
    Poly.rat_eq_comp hsq (poly_const' (α := St) (β := ℚ) 0)
  have inner : Poly (fun st : St =>
      if rowSq (headTail st.1) = 0 then brDrop st else brZero st) :=
    Poly.ite_prop (p := fun st : St => rowSq (headTail st.1) = 0) hsqz poly_brDrop poly_brZero
  have mid : Poly (fun st : St =>
      if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDrop st else brZero st)
      else brSchur st) :=
    Poly.ite_prop (p := fun st : St => piv st.1 = 0) hzero inner poly_brSchur
  have outer : Poly (fun st : St =>
      if piv st.1 < 0 then brNeg st
      else (if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDrop st else brZero st)
        else brSchur st)) :=
    Poly.ite_prop (p := fun st : St => piv st.1 < 0) hneg poly_brNeg mid
  have top : Poly (fun st : St =>
      if st.1.isEmpty then brStop st
      else (if piv st.1 < 0 then brNeg st
        else (if piv st.1 = 0 then (if rowSq (headTail st.1) = 0 then brDrop st else brZero st)
          else brSchur st))) :=
    Poly.ite (p := fun st : St => st.1.isEmpty) hEmpty poly_brStop outer
  exact top


/-! ## 2.  The descent as a bounded run, and `Poly` for it -/

theorem dropRows_length (rows : Rows) : (dropRows rows).length = rows.tail.length := by
  simp [dropRows]

theorem schurRows_length (rows : Rows) : (schurRows rows).length ≤ rows.tail.length := by
  simp only [schurRows, List.length_map, List.length_zip]
  omega

/-- **The step strictly shrinks the block** on the `inr` branch: this is what makes the bounded
run terminate in at most `k + 1` steps. -/
theorem pivStep_snd_length {st st' : St} (h : pivStep st = Sum.inr st') :
    st'.1.length < st.1.length := by
  have hne : st.1 ≠ [] := by
    intro hnil
    unfold pivStep at h
    rw [if_pos (by simp [hnil])] at h
    cases h
  have htail : st.1.tail.length < st.1.length := by
    rw [List.length_tail]
    have : 0 < st.1.length := List.length_pos_of_ne_nil hne
    omega
  unfold pivStep at h
  rw [if_neg (by simpa using hne)] at h
  by_cases h2 : piv st.1 < 0
  · rw [if_pos h2] at h
    cases h
  · rw [if_neg h2] at h
    by_cases h3 : piv st.1 = 0
    · rw [if_pos h3] at h
      by_cases h4 : rowSq (headTail st.1) = 0
      · rw [if_pos h4] at h
        have hEq : (dropRows st.1, st.2) = st' := Sum.inr.inj h
        have hfst : st'.1 = dropRows st.1 := by rw [← hEq]
        rw [hfst, dropRows_length]
        exact htail
      · rw [if_neg h4] at h
        cases h
    · rw [if_neg h3] at h
      have hEq : (schurRows st.1, (piv st.1, headTail st.1) :: st.2) = st' := Sum.inr.inj h
      have hfst : st'.1 = schurRows st.1 := by rw [← hEq]
      rw [hfst]
      exact lt_of_le_of_lt (schurRows_length st.1) htail

/-- The fuel-driven descent. -/
def runPivFuel : ℕ → St → Ans
  | 0, _ => (false, [])
  | (n + 1), st =>
    match pivStep st with
    | Sum.inl a => a
    | Sum.inr st' => runPivFuel n st'

/-- The descent: the number of rows is enough fuel. -/
def runPiv (st : St) : Ans := runPivFuel st.1.length st

theorem runPivFuel_zero (st : St) : runPivFuel 0 st = (false, []) := rfl

theorem runPivFuel_succ (n : ℕ) (st : St) :
    runPivFuel (n + 1) st
      = (match pivStep st with
        | Sum.inl a => a
        | Sum.inr st' => runPivFuel n st') := rfl

/-- **The bounded run**: from a state with at most `n` rows, all inside the size budget `S`, the
descent is a `BoundedRun` of at most `n + 1` steps. -/
theorem runPivFuel_bounded (S : ℕ)
    (hprof : ∀ st' : St, (enc st').length ≤ S → ∀ st'' : St,
      pivStep st' = Sum.inr st'' → (enc st'').length ≤ S) :
    ∀ (n : ℕ) (st : St), st.1.length ≤ n → (enc st).length ≤ S →
      ∃ m ≤ n + 1, BoundedRun (Coding.encode (α := St)) pivStep S m st (runPivFuel n st) := by
  intro n
  induction n with
  | zero =>
      intro st hk hS
      have hnil : st.1 = [] := by
        have h0 : st.1.length = 0 := by omega
        exact List.eq_nil_of_length_eq_zero h0
      have hempty : st.1.isEmpty = true := by simp [hnil]
      have hstep : pivStep st = Sum.inl (false, []) := by
        unfold pivStep brStop
        rw [if_pos hempty]
      exact ⟨1, by omega, BoundedRun.stop hS hstep⟩
  | succ n ih =>
      intro st hk hS
      rw [runPivFuel_succ]
      cases hstep : pivStep st with
      | inl a => exact ⟨1, by omega, BoundedRun.stop hS hstep⟩
      | inr st' =>
          have hlt : st'.1.length < st.1.length := pivStep_snd_length hstep
          have hS' : (enc st').length ≤ S := hprof st hS st' hstep
          obtain ⟨m, hm, hrun⟩ := ih st' (by omega) hS'
          exact ⟨m + 1, by omega, BoundedRun.step hS hstep hrun⟩

/-- The block never has more rows than the encoding of the state: the fuel is available. -/
theorem rows_length_le_enc (st : St) : st.1.length ≤ (enc st).length := by
  have h1 : st.1.length ≤ (enc st.1).length :=
    EncodedList.length_le (ea := (enc : List ℚ → List Bool)) st.1
  have h2 : (enc st.1).length ≤ (enc st).length := by
    have e : (enc st : List Bool) =
        encodePair (enc : Rows → List Bool) (enc : Acc → List Bool) st := rfl
    rw [e, encodePair_length]
    omega
  exact h1.trans h2

/-- **The pivot descent is a `Poly` program**, from **one** size-profile hypothesis `hprof`: the
encoded length of every state reachable from `a` stays inside the polynomial `sizes` evaluated at
the input's encoded length.  §3 measures that hypothesis: it is the Schur-height statement. -/
theorem poly_runPiv (sizes : Polynomial ℕ)
    (hprof : ∀ (a st : St), (enc st).length ≤ sizes.eval (enc a).length →
      ∀ st' : St, pivStep st = Sum.inr st' → (enc st').length ≤ sizes.eval (enc a).length)
    (hsize0 : ∀ a : St, (enc a).length ≤ sizes.eval (enc a).length) :
    Poly (fun st : St => runPiv st) := by
  refine QMCLeafB.PolyLoop.poly_loop (f := pivStep) poly_pivStep
    (fun st : St => runPiv st) (Polynomial.X + 1) sizes ?_
  intro a
  obtain ⟨m, hm, hrun⟩ :=
    runPivFuel_bounded (sizes.eval (enc a).length) (hprof a) a.1.length a le_rfl (hsize0 a)
  refine ⟨m, ?_, hrun⟩
  have h1 := rows_length_le_enc a
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  omega


/-! ## 3.  The Schur height, and why the size profile is the whole problem

`poly_runPiv` needs one hypothesis: every visited state's encoded length stays inside a fixed
polynomial of the input's encoded length.  This section measures the per-step growth of the *exact*
rational block, machine-checked with the library's `HasHeight`
(`|q.num| ≤ 2^L ∧ q.den ≤ 2^L`, closed under `mul`/`div`/`add`/`sub`/`mono`).

The answer is `4L + 1` per Schur step (`schurRows_height`), hence at most `5^j (L+1)` after `j`
steps (`height_iterate_naive`): exponential in the depth, which here is the number of rows.  So no
polynomial profile follows from this induction (`no_linear_profile` is the machine-checked instance
for the linear family; the same argument kills every polynomial), and m3's phase-9 measurement says
the true height is `O(k·H)` because the entries of the `k`-th Schur complement are ratios of leading
minors — whose proof needs the Sylvester / Desnanot–Jacobi identity, absent from Mathlib.

Consequence for phase 10: the *exact-rational* oracle is not a `PolyProgram` by this route.  The
snapped descent (heights reset by `hasHeight_snapDiv`; `RelaxKit`'s `relaxBodyLE` margins) is the
only remaining route, at the price of m3's stability bound `max|W − snap cX| ≤ n·2^{-D}`. -/

/-- The equations of the block accessors, for case analysis. -/
theorem headRowD_nil : headRowD ([] : Rows) = [] := rfl
theorem headRowD_cons (r : List ℚ) (rs : Rows) : headRowD (r :: rs) = r := rfl
theorem piv_nil : piv ([] : Rows) = 0 := rfl
theorem piv_cons (r : List ℚ) (rs : Rows) : piv (r :: rs) = r.head?.getD 0 := rfl
theorem headTail_nil : headTail ([] : Rows) = [] := rfl
theorem headTail_cons (r : List ℚ) (rs : Rows) : headTail (r :: rs) = r.tail := rfl

/-- Pair membership in a `zip`. -/
theorem mem_zip_pair {α β : Type} {a : α} {b : β} {l₁ : List α} {l₂ : List β}
    (h : (a, b) ∈ l₁.zip l₂) : a ∈ l₁ ∧ b ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩ | h
          · exact ⟨List.mem_cons_self .., List.mem_cons_self ..⟩
          · obtain ⟨ha, hb⟩ := ih h
            exact ⟨List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb⟩

/-- Every entry of the block has height `≤ L`. -/
def RowsHeight (rows : Rows) (L : ℕ) : Prop := ∀ v ∈ rows, ∀ q ∈ v, HasHeight q L

theorem RowsHeight.mono {rows : Rows} {L M : ℕ} (h : RowsHeight rows L) (hLM : L ≤ M) :
    RowsHeight rows M := fun v hv q hq => (h v hv q hq).mono hLM

theorem RowsHeight.tail {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    RowsHeight rows.tail L := fun v hv => h v (List.mem_of_mem_tail hv)

theorem RowsHeight.headRowD {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    ∀ q ∈ headRowD rows, HasHeight q L := by
  intro q hq
  cases rows with
  | nil => rw [headRowD_nil] at hq; exact absurd hq (List.not_mem_nil)
  | cons r rs =>
      rw [headRowD_cons] at hq
      exact h r (List.mem_cons_self ..) q hq

theorem RowsHeight.headTail {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    ∀ q ∈ headTail rows, HasHeight q L := by
  intro q hq
  cases rows with
  | nil => rw [headTail_nil] at hq; exact absurd hq (List.not_mem_nil)
  | cons r rs =>
      rw [headTail_cons] at hq
      exact h r (List.mem_cons_self ..) q (List.mem_of_mem_tail hq)

theorem RowsHeight.piv {rows : Rows} {L : ℕ} (h : RowsHeight rows L) : HasHeight (piv rows) L := by
  cases rows with
  | nil => rw [piv_nil]; exact HasHeight.zero L
  | cons r rs =>
      rw [piv_cons]
      cases r with
      | nil => exact HasHeight.zero L
      | cons q qs =>
          exact h (q :: qs) (List.mem_cons_self ..) q (List.mem_cons_self ..)

/-- One Schur row update raises the entry height to `4L + 1`. -/
theorem schurRowStep_height {a bi : ℚ} {b row : List ℚ} (L : ℕ)
    (ha : HasHeight a L) (hbi : HasHeight bi L) (hb : ∀ q ∈ b, HasHeight q L)
    (hr : ∀ q ∈ row, HasHeight q L) :
    ∀ q ∈ schurRowStep a b (row, bi), HasHeight q (4 * L + 1) := by
  intro q hq
  simp only [schurRowStep, List.mem_map] at hq
  obtain ⟨⟨x, y⟩, hs, hqx⟩ := hq
  obtain ⟨hx, hy⟩ := mem_zip_pair hs
  rw [← hqx]
  have h1 : HasHeight (bi * y) (L + L) := hbi.mul (hb y hy)
  have h2 : HasHeight (bi * y / a) (L + L + L) := h1.div ha
  have h3 : HasHeight (x - bi * y / a) (L + (L + L + L) + 1) :=
    (hr x (List.mem_of_mem_tail hx)).sub h2
  exact h3.mono (by omega)

/-- **The per-step Schur height growth**: `L ↦ 4L + 1`. -/
theorem schurRows_height {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    RowsHeight (schurRows rows) (4 * L + 1) := by
  intro v hv q hq
  simp only [schurRows, List.mem_map] at hv
  obtain ⟨⟨row, bi⟩, hp, hvq⟩ := hv
  obtain ⟨hrow, hbi⟩ := mem_zip_pair hp
  rw [← hvq] at hq
  exact schurRowStep_height L h.piv (h.headTail bi hbi) h.headTail
    (fun q hq => h _ (List.mem_of_mem_tail hrow) q hq) q hq

theorem dropRows_height {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    RowsHeight (dropRows rows) L := by
  intro v hv q hq
  simp only [dropRows, List.mem_map] at hv
  obtain ⟨row, hrow, rfl⟩ := hv
  exact h row (List.mem_of_mem_tail hrow) q (List.mem_of_mem_tail hq)

/-- The block after one step, whatever the branch (`inl` branches leave it alone). -/
def stepRows (rows : Rows) : Rows :=
  if rows.isEmpty then []
  else if piv rows < 0 then rows
  else if piv rows = 0 then (if rowSq (headTail rows) = 0 then dropRows rows else rows)
  else schurRows rows

theorem stepRows_height {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    RowsHeight (stepRows rows) (4 * L + 1) := by
  unfold stepRows
  by_cases h1 : rows.isEmpty
  · rw [if_pos h1]
    intro v hv
    exact absurd hv (List.not_mem_nil)
  · rw [if_neg h1]
    by_cases h2 : piv rows < 0
    · rw [if_pos h2]; exact h.mono (by omega)
    · rw [if_neg h2]
      by_cases h3 : piv rows = 0
      · rw [if_pos h3]
        by_cases h4 : rowSq (headTail rows) = 0
        · rw [if_pos h4]; exact (dropRows_height h).mono (by omega)
        · rw [if_neg h4]; exact h.mono (by omega)
      · rw [if_neg h3]; exact schurRows_height h

/-- **The naive profile is exponential**: after `j` exact steps the entry height is at most
`5^j (L + 1)`. -/
theorem height_iterate_naive (j : ℕ) {rows : Rows} {L : ℕ} (h : RowsHeight rows L) :
    RowsHeight ((stepRows^[j]) rows) (5 ^ j * (L + 1)) := by
  induction j with
  | zero => simpa using h.mono (by omega)
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      refine (stepRows_height ih).mono ?_
      have h5 : 1 ≤ 5 ^ j := Nat.one_le_pow j 5 (by norm_num)
      have hx : 1 ≤ 5 ^ j * (L + 1) := by
        have h2 : 1 ≤ L + 1 := by omega
        calc 1 = 1 * 1 := (Nat.one_mul 1).symm
          _ ≤ 5 ^ j * (L + 1) := Nat.mul_le_mul h5 h2
      rw [pow_succ]
      nlinarith

theorem quad_aux : ∀ C : ℕ, C * (C + 2) ≤ 4 * 5 ^ C := by
  intro C
  induction C with
  | zero => norm_num
  | succ C ih =>
      have hpos : 1 ≤ 5 ^ C := Nat.one_le_pow C 5 (by norm_num)
      have h2 : 2 * C + 3 ≤ 16 * 5 ^ C := by nlinarith
      rw [pow_succ]
      nlinarith

/-- **No linear profile can dominate the naive bound** — the machine-checked instance of the
obstruction.  It shows that the profile hypothesis of `poly_runPiv` cannot be discharged by an
induction on the exact step: `C * (j+1)` (any linear size budget at depth `j`) is eventually beaten
by the height `5^j`. -/
theorem no_linear_profile : ∀ C : ℕ, ∃ j : ℕ, C * (j + 1) < 5 ^ j := by
  intro C
  refine ⟨C + 1, ?_⟩
  have h1 := quad_aux C
  have hpos : 1 ≤ 5 ^ C := Nat.one_le_pow C 5 (by norm_num)
  rw [pow_succ]
  nlinarith


/-! ## 4.  The mathematics of one step, bound to `SepOracle`'s own objects

These are the *induction ingredients* of the `Response` binding.  Everything is stated on
`SepOracle`'s `qf`/`tail`/`headRow`/`schur` (m1's brick), so nothing is re-derived:

* `psd_of_schur_child`, `psd_of_tail_child` — the **`ok` transfer**: PSD of the child block lifts
  to PSD of the parent (completion of squares, resp. the zero-row collapse).  This is the direction
  the descent needs (the other direction is m1's `schur_nonneg`/`tail_nonneg`).
* `witness_pivot_neg`, `witness_schur`, `witness_tail` — the **`cut` lift**: a violated direction
  of a child becomes an explicit violated direction of the parent (`δ₀`, the Schur lift
  `y ↦ (−(b·y)/a, y)`, and the zero-`cons` lift).
* `okReport_of_psd`, `goodCut_of_violated` — the two `Response` branches, in consumer form
  (`SepOracle.OkReport`, `SepOracle.GoodCut`).
* `liftStep`/`liftWitness` — the accumulated lift through the pivot stack that the descent's answer
  needs; `poly_liftStep` is its one-step `Poly` fact.
-/

/-- **PSD transfer, Schur branch.**  If `a = X₀₀ > 0` and the Schur complement of `X` at `a` is
PSD, then `X` is PSD: complete the square. -/
theorem psd_of_schur_child {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ} {a : ℚ}
    (hsym : ∀ i j, X i j = X j i) (ha : X 0 0 = a) (ha0 : 0 < a)
    (h : ∀ y : Fin k → ℚ, 0 ≤ QMCLeafB.SepOracle.qf (QMCLeafB.SepOracle.schur X a) y) :
    ∀ x : Fin (k + 1) → ℚ, 0 ≤ QMCLeafB.SepOracle.qf X x := by
  intro x
  set y : Fin k → ℚ := fun j => x j.succ with hy
  have hx : x = Fin.cons (x 0) y := by
    rw [hy]
    exact (Fin.cons_self_tail x).symm
  rw [hx, QMCLeafB.SepOracle.qf_cons X hsym, ha]
  have hschur : QMCLeafB.SepOracle.qf (QMCLeafB.SepOracle.schur X a) y
      = QMCLeafB.SepOracle.qf (QMCLeafB.SepOracle.tail X) y
        - a⁻¹ * (QMCLeafB.SepOracle.headRow X ⬝ᵥ y) ^ 2 := by
    rw [QMCLeafB.SepOracle.schur, QMCLeafB.SepOracle.qf_sub, QMCLeafB.SepOracle.qf_smulQ,
      QMCLeafB.SepOracle.qf_vecMulVecQ]
    ring
  have hsquare : a * (x 0 + (QMCLeafB.SepOracle.headRow X ⬝ᵥ y) / a) ^ 2
      = a * (x 0) ^ 2 + 2 * x 0 * (QMCLeafB.SepOracle.headRow X ⬝ᵥ y)
        + (QMCLeafB.SepOracle.headRow X ⬝ᵥ y) ^ 2 / a := by
    field_simp
    ring
  have hnonneg : 0 ≤ a * (x 0 + (QMCLeafB.SepOracle.headRow X ⬝ᵥ y) / a) ^ 2 :=
    mul_nonneg ha0.le (sq_nonneg _)
  have hchild := h y
  rw [hschur] at hchild
  have hinv : a⁻¹ * (QMCLeafB.SepOracle.headRow X ⬝ᵥ y) ^ 2
      = (QMCLeafB.SepOracle.headRow X ⬝ᵥ y) ^ 2 / a := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hinv] at hchild
  linarith

/-- **PSD transfer, drop branch.**  If `X₀₀ = 0`, the head row vanishes and the tail block is PSD,
then `X` is PSD. -/
theorem psd_of_tail_child {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ}
    (hsym : ∀ i j, X i j = X j i) (h00 : X 0 0 = 0)
    (hrow : QMCLeafB.SepOracle.headRow X = 0)
    (h : ∀ y : Fin k → ℚ, 0 ≤ QMCLeafB.SepOracle.qf (QMCLeafB.SepOracle.tail X) y) :
    ∀ x : Fin (k + 1) → ℚ, 0 ≤ QMCLeafB.SepOracle.qf X x := by
  intro x
  have hx : x = Fin.cons (x 0) (fun j => x j.succ) := (Fin.cons_self_tail x).symm
  rw [hx, QMCLeafB.SepOracle.qf_cons X hsym, h00, hrow]
  simpa using h (fun j => x j.succ)

/-- **Witness lift, negative pivot**: `X₀₀ < 0` is violated by `δ₀`. -/
theorem witness_pivot_neg {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ} (h : X 0 0 < 0) :
    QMCLeafB.SepOracle.qf X (QMCLeafB.SepOracle.delta 0) < 0 := by
  rw [QMCLeafB.SepOracle.qf_delta]
  exact h

/-- **Witness lift, Schur branch**: m1's `qf_schur` read as a lift of violated directions. -/
theorem witness_schur {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ}
    (hsym : ∀ i j, X i j = X j i) {a : ℚ} (ha : X 0 0 = a) (ha0 : a ≠ 0) {y : Fin k → ℚ}
    (h : QMCLeafB.SepOracle.qf (QMCLeafB.SepOracle.schur X a) y < 0) :
    QMCLeafB.SepOracle.qf X
      (Fin.cons (-(QMCLeafB.SepOracle.headRow X ⬝ᵥ y) / a) y) < 0 := by
  rw [QMCLeafB.SepOracle.qf_schur X hsym ha ha0]
  exact h

/-- **Witness lift, drop branch**: a violated direction of the tail, prefixed by `0`. -/
theorem witness_tail {k : ℕ} {X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ}
    (hsym : ∀ i j, X i j = X j i) (h00 : X 0 0 = 0) {w : Fin k → ℚ}
    (h : QMCLeafB.SepOracle.qf (QMCLeafB.SepOracle.tail X) w < 0) :
    QMCLeafB.SepOracle.qf X (Fin.cons 0 w) < 0 := by
  rw [QMCLeafB.SepOracle.qf_cons X hsym, h00]
  simpa using h

/-- The `ok` branch in consumer form: `SepOracle.OkReport` from the three `ok` facts. -/
def okReport_of_psd {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    {cX : Matrix (Fin n) (Fin n) ℚ} (hpsd : QMCLeafB.SepOracle.PSD cX)
    (hdiag : QMCLeafB.SepOracle.unitDiag cX) (htr : t ≤ QMCLeafB.SepOracle.frob A cX) :
    QMCLeafB.SepOracle.OkReport n A t cX :=
  QMCLeafB.SepOracle.okReport_of_ok ⟨hpsd, hdiag, htr⟩

/-- The `cut` branch in consumer form: a violated direction is a `GoodCut`. -/
def goodCut_of_violated {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} {t : ℚ}
    {cX : Matrix (Fin n) (Fin n) ℚ} {v : Fin n → ℚ}
    (h : QMCLeafB.SepOracle.qf cX v < 0) : QMCLeafB.SepOracle.GoodCut A t cX :=
  QMCLeafB.SepOracle.Split.violated_cut h

/-- One level of the accumulated witness lift: `v ↦ (−(b·v)/a, v)`. -/
def liftStep (v : List ℚ) (p : ℚ × List ℚ) : List ℚ := -(dotL p.2 v) / p.1 :: v

/-- The lift through a whole pivot stack (most recent pivot first). -/
def liftWitness (acc : Acc) (v : List ℚ) : List ℚ := acc.foldl liftStep v

theorem poly_liftStep :
    Poly (fun x : List ℚ × (ℚ × List ℚ) => liftStep x.1 x.2) := by
  have hdot : Poly (fun x : List ℚ × (ℚ × List ℚ) => dotL x.2.2 x.1) :=
    Poly.comp (f := fun p : List ℚ × List ℚ => dotL p.1 p.2)
      (g := fun x : List ℚ × (ℚ × List ℚ) => (x.2.2, x.1)) poly_dotL
      (Poly.pair (poly_pr_sndSnd (α := List ℚ) (β := ℚ) (γ := List ℚ)) Poly.fst)
  have hneg : Poly (fun x : List ℚ × (ℚ × List ℚ) => -(dotL x.2.2 x.1)) :=
    Poly.comp (f := fun q : ℚ => -q) (g := fun x : List ℚ × (ℚ × List ℚ) => dotL x.2.2 x.1)
      Poly.rat_neg hdot
  have hdiv : Poly (fun x : List ℚ × (ℚ × List ℚ) => -(dotL x.2.2 x.1) / x.2.1) :=
    Poly.comp (f := fun p : ℚ × ℚ => p.1 / p.2)
      (g := fun x : List ℚ × (ℚ × List ℚ) => (-(dotL x.2.2 x.1), x.2.1)) Poly.rat_div
      (Poly.pair hneg (poly_pr_sndFst (α := List ℚ) (β := ℚ) (γ := List ℚ)))
  exact Poly.comp (f := fun p : ℚ × List ℚ => p.1 :: p.2)
    (g := fun x : List ℚ × (ℚ × List ℚ) => (-(dotL x.2.2 x.1) / x.2.1, x.1)) Poly.list_cons
    (Poly.pair hdiv Poly.fst)

/-! ## 5.  The two remaining obligations, named

Nothing below is assumed; both are `def`s, recorded so the coordinator can state the residual
precisely (and so that no `sorry` enters this file). -/

/-- **(O1) the size profile** — the hypothesis of `poly_runPiv`.  §3 shows it cannot be discharged
by an induction on the exact Schur step; m3's snapped descent is the route that makes it true. -/
def SizeProfile (sizes : Polynomial ℕ) : Prop :=
  ∀ (a st : St), (enc st).length ≤ sizes.eval (enc a).length →
    ∀ st' : St, pivStep st = Sum.inr st' → (enc st').length ≤ sizes.eval (enc a).length

/-- A row code at a fixed dimension. -/
def Code (k : ℕ) (X : Matrix (Fin k) (Fin k) ℚ) (rows : Rows) : Prop :=
  rows.length = k ∧ ∀ i j : Fin k, (rows.getD i.1 []).getD j.1 0 = X i j

/-- The matrix read off a row code. -/
def toMat (k : ℕ) (rows : Rows) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => (rows.getD i.1 []).getD j.1 0

/-- **(O2) the rows-to-matrix bridge** — that the program's row operations are `SepOracle`'s block
operations, so §4's transfer lemmas apply to the program's run.  This is pure list index
bookkeeping (`getD` of `map`/`zip`/`tail` against `Fin.succ`), not analysis. -/
def SchurBridge : Prop :=
  ∀ (k : ℕ) (X : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) (rows : Rows),
    Code (k + 1) X rows →
      (toMat k (schurRows rows)
          = QMCLeafB.SepOracle.schur X (X 0 0)
        ∧ toMat k (dropRows rows) = QMCLeafB.SepOracle.tail X)


/-! ### 5.1  The interface the round slot consumes

`poly_runPiv` is exactly the `Poly` fact a separation-oracle slot needs: run the descent, then read
the answer through any `Poly` verdict map.  (`hprof` is (O1); the caller supplies `sizes` from the
`CertSize` ledger as the loop toolkit's recipe prescribes.) -/

theorem poly_verdict_comp {β : Type} [Coding β] (verdict : Ans → β) (hv : Poly verdict)
    (sizes : Polynomial ℕ) (hprof : SizeProfile sizes)
    (hsize0 : ∀ a : St, (enc a).length ≤ sizes.eval (enc a).length) :
    Poly (fun st : St => verdict (runPiv st)) :=
  Poly.comp hv (poly_runPiv sizes hprof hsize0)

/-! ## 5.2  End-to-end demo on m1's three test matrices

`SepOracle`'s own demos are `bad2 = [[1,2],[2,1]]` (Schur complement `−3`), `badZ = [[0,1],[1,0]]`
(zero pivot, nonzero head row) and `good2 = [[1,0],[0,1]]` (certified PSD).  The descent below is the
`Poly` program of §1–§2 verbatim; the lifted witnesses are §4's `liftStep`, and the violation is
`decide`-checked against `SepOracle.qf`. -/

/-- `1 2 / 2 1` as a row code (m1's `bad2`). -/
def demoBad2 : Rows := [[1, 2], [2, 1]]
/-- `0 1 / 1 0` as a row code (m1's `badZ`). -/
def demoBadZ : Rows := [[0, 1], [1, 0]]
/-- `1 0 / 0 1` as a row code (m1's `good2`). -/
def demoGood2 : Rows := [[1, 0], [0, 1]]

-- the descent: `bad2` reaches a negative pivot at the second block, `badZ` fires the zero-pivot
-- witness at the top, `good2` runs to `k = 0`

-- the accumulated lift turns an answer into a full-length direction

/-- `bad2`: the descent stops with `(true, [1])` at the `1×1` block, and the lift through the one
pivot `(1, [2])` gives `(−2, 1)`.  Checked against the program's own quadratic form `qformRows` on
the row code, so the pipeline descent → answer → accumulated lift → violation is exercised end to
end. -/
theorem demo_bad2_witness :
    qformRows demoBad2 (liftWitness [(1, [2])] [1]) < 0 := by
  simp only [liftWitness, liftStep, List.foldl_cons, List.foldl_nil, qformRows, dotL, demoBad2,
    List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.getD_cons_zero, List.getD_cons_succ]
  norm_num

/-- `badZ`: the zero-pivot witness `(−1/2, 1)` is a violated direction of the same code. -/
theorem demo_badZ_witness :
    qformRows demoBadZ (liftWitness [] [(-1 / 2), 1]) < 0 := by
  simp only [liftWitness, liftStep, List.foldl_cons, List.foldl_nil, qformRows, dotL, demoBadZ,
    List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.getD_cons_zero, List.getD_cons_succ]
  norm_num

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.PivotProgram.poly_pivStep
#print axioms QMCLeafB.PivotProgram.pivStep_snd_length
#print axioms QMCLeafB.PivotProgram.runPivFuel_bounded
#print axioms QMCLeafB.PivotProgram.poly_runPiv
#print axioms QMCLeafB.PivotProgram.schurRows_height
#print axioms QMCLeafB.PivotProgram.height_iterate_naive
#print axioms QMCLeafB.PivotProgram.no_linear_profile
#print axioms QMCLeafB.PivotProgram.psd_of_schur_child
#print axioms QMCLeafB.PivotProgram.psd_of_tail_child
#print axioms QMCLeafB.PivotProgram.witness_pivot_neg
#print axioms QMCLeafB.PivotProgram.witness_schur
#print axioms QMCLeafB.PivotProgram.witness_tail
#print axioms QMCLeafB.PivotProgram.poly_liftStep
#print axioms QMCLeafB.PivotProgram.poly_verdict_comp
#print axioms QMCLeafB.PivotProgram.demo_bad2_witness
#print axioms QMCLeafB.PivotProgram.demo_badZ_witness
#print axioms QMCLeafB.PivotProgram.okReport_of_psd
#print axioms QMCLeafB.PivotProgram.goodCut_of_violated

end QMCLeafB.PivotProgram


