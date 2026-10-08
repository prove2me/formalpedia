-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_CellThm
-- name    : CK_CKLaneM07_CE_CellThm
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T14:11:22.093483+00:00
-- url     : https://prove2.me/theorems/5138feab-b14f-4b99-b913-984f76130932
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.CellThm` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.CellThm` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.CellThm` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.CellThm (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/CellThm.lean)

import Definitions.Def_CK_CKLaneM07_CE_Bridge

-- ===== source module CKLaneM07.CE.CellThm =====
section

/-!
# Lane M07 / CE-stat: cell theorems and the cover reduction for S.3 row 4

* `CellConcl cl`: every retained stationary Case-E point whose chart `(A, t_C)` lies in the (closed,
  exact dyadic) box of `cl` has `0 ≤ canonicalPureGap`.
* `cell_mode0 … cell_mode3`: `CellConcl` from the Boolean stage checks of chain v2 (modes 1–3 are
  vacuous: the box contains no Case-E point, by `chart_order`, the retained cutoff, `λ < 1`).
* `coverOK`: a Boolean slab/chain cover check of a rectangle by cell boxes; `rowOfCover` turns a
  cover of `[1/20, 21/200] × [1/80000, 1/100]` into `CKLaneN1.CEStat.A3LeafUnion`.
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open GeneralCK CKLaneN1.CEStat GeneralCK.SmallMeanPhiCutoff

/-- the closed box of a cell, in units `2^-PB` -/
def CellV.Box (cl : CellV) (A t : ℝ) : Prop :=
  |A * SC - cl.A0| ≤ cl.hA ∧ |t * SC - cl.T0| ≤ cl.hT

/-- the row-level conclusion owned by a cell -/
def CellConcl (cl : CellV) : Prop :=
  ∀ e f c : ℝ, Point e f c → cl.Box (chartA e f c) (chartTC f c) →
    0 ≤ canonicalPureGap (entropyInverse e) c e f

theorem box_coords {cl : CellV} (h0 : V2.chk0 cl = true) {A t : ℝ} (hb : cl.Box A t) :
    ∃ x y : ℝ, |x| ≤ 1 ∧ |y| ≤ 1 ∧ A = ((cl.A0 : ℝ) + (cl.hA : ℝ) * x) / SC ∧
      t = ((cl.T0 : ℝ) + (cl.hT : ℝ) * y) / SC := by
  unfold V2.chk0 at h0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  obtain ⟨hA, hT⟩ := h0
  have hA' : (0 : ℝ) < cl.hA := by exact_mod_cast hA
  have hT' : (0 : ℝ) < cl.hT := by exact_mod_cast hT
  have hS := SC_pos
  have := hA'.ne'
  have := hT'.ne'
  have := hS.ne'
  refine ⟨(A * SC - cl.A0) / cl.hA, (t * SC - cl.T0) / cl.hT, ?_, ?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hA', div_le_one hA']; exact hb.1
  · rw [abs_div, abs_of_pos hT', div_le_one hT']; exact hb.2
  · field_simp; ring
  · field_simp; ring

section cellthm

variable {K : ℕ} {cl : CellV} {w : WitV}

theorem cell_mode0 (h0 : V2.chk0 cl = true) (h1 : V2.chkA K cl w = true)
    (h2 : V2.chkC K cl w = true) (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true)
    (h5 : V2.chkL K cl w = true) (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true)
    (h8 : V2.chkb K cl w = true) (h9 : V2.chkD K w = true) (h10 : V2.chkUE K w = true)
    (hfin : V2.finG K cl w = true) : CellConcl cl := by
  intro e f c hP hb
  obtain ⟨x, y, hx, hy, hA, hT⟩ := box_coords h0 hb
  have hR := realOf_valid hP.1
  have hAx : EnclAt x y (realOf e f c).A cl.A := (encl_cellA x y cl).congr hA.symm
  have hTy : EnclAt x y (realOf e f c).tC cl.tC := (encl_celltC x y cl).congr hT.symm
  have hG := sound_mode0 hx hy (realOf e f c) hR hAx hTy h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hfin
  rw [realOf_G hP.1] at hG
  have hL := log2_pos'
  nlinarith

theorem cell_mode1 (h0 : V2.chk0 cl = true) (h1 : V2.chkA K cl w = true)
    (h2 : V2.chkC K cl w = true) (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true)
    (h5 : V2.chkL K cl w = true) (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true)
    (h8 : V2.chkb K cl w = true) (hfin : V2.finE cl w = true) : CellConcl cl := by
  intro e f c hP hb
  obtain ⟨x, y, hx, hy, hA, hT⟩ := box_coords h0 hb
  have hR := realOf_valid hP.1
  have hAx : EnclAt x y (realOf e f c).A cl.A := (encl_cellA x y cl).congr hA.symm
  have hTy : EnclAt x y (realOf e f c).tC cl.tC := (encl_celltC x y cl).congr hT.symm
  have h := sound_mode1 hx hy (realOf e f c) hR hAx hTy h1 h2 h3 h4 h5 h6 h7 h8 hfin
  change chartTC f c < entropyInverse f at h
  exact absurd h (not_lt.mpr (chart_order hP.1).1.le)

theorem cell_mode2 (h0 : V2.chk0 cl = true) (h1 : V2.chkA K cl w = true)
    (h2 : V2.chkC K cl w = true) (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true)
    (h5 : V2.chkL K cl w = true) (h6 : V2.chka K cl w = true) (h7 : V2.chkE K cl w = true)
    (hfin : V2.finF K cl w = true) : CellConcl cl := by
  intro e f c hP hb
  obtain ⟨x, y, hx, hy, hA, hT⟩ := box_coords h0 hb
  have hR := realOf_valid hP.1
  have hAx : EnclAt x y (realOf e f c).A cl.A := (encl_cellA x y cl).congr hA.symm
  have hTy : EnclAt x y (realOf e f c).tC cl.tC := (encl_celltC x y cl).congr hT.symm
  have h := sound_mode2 hx hy (realOf e f c) hR hAx hTy h1 h2 h3 h4 h5 h6 h7 hfin
  rw [realOf_c (ptFacts hP.1)] at h
  change entropyInverse e + c ≤ 1 / 10000 at h
  have h2 := hP.2
  unfold retainedCutoff at h2
  linarith

theorem cell_mode3 (h0 : V2.chk0 cl = true) (h1 : V2.chkA K cl w = true)
    (h2 : V2.chkC K cl w = true) (h3 : V2.chkU K cl w = true) (h4 : V2.chkB K cl w = true)
    (h5 : V2.chkL K cl w = true) (hfin : V2.finL K cl w = true) : CellConcl cl := by
  intro e f c hP hb
  obtain ⟨x, y, hx, hy, hA, hT⟩ := box_coords h0 hb
  have hR := realOf_valid hP.1
  have hAx : EnclAt x y (realOf e f c).A cl.A := (encl_cellA x y cl).congr hA.symm
  have hTy : EnclAt x y (realOf e f c).tC cl.tC := (encl_celltC x y cl).congr hT.symm
  have h := sound_mode3 hx hy (realOf e f c) hR hAx hTy h1 h2 h3 h4 h5 hfin
  rw [realOf_lam (ptFacts hP.1)] at h
  have hl := (chart_lambda_mem hP.1.1 hP.1.2.1).2
  unfold chartLambda at hl
  linarith

end cellthm

/-! ## covers -/

/-- chained closed intervals covering `[lo, hi]` -/
def chainCover (lo hi : ℤ) : List (ℤ × ℤ) → Bool
  | [] => false
  | (l, u) :: rest => decide (l ≤ lo) && (decide (hi ≤ u) || chainCover u hi rest)

theorem chainCover_sound : ∀ (L : List (ℤ × ℤ)) (lo hi : ℤ), chainCover lo hi L = true →
    ∀ t : ℝ, (lo : ℝ) ≤ t → t ≤ hi → ∃ p ∈ L, (p.1 : ℝ) ≤ t ∧ t ≤ p.2
  | [], _, _, h => by simp [chainCover] at h
  | (l, u) :: rest, lo, hi, h => by
      intro t hlo hhi
      simp only [chainCover, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨hl, hr⟩ := h
      have hl' : (l : ℝ) ≤ lo := by exact_mod_cast hl
      by_cases htu : t ≤ u
      · exact ⟨(l, u), List.mem_cons_self, le_trans hl' hlo, htu⟩
      · push Not at htu
        rcases hr with hr | hr
        · have : (hi : ℝ) ≤ u := by exact_mod_cast hr
          linarith
        · obtain ⟨p, hp, hp'⟩ := chainCover_sound rest u hi hr t htu.le hhi
          exact ⟨p, List.mem_cons_of_mem _ hp, hp'⟩

/-- a horizontal slab `[lo, hi]` (in `t_C`, units `2^-PB`) with the indices of its cells, left to right -/
structure Slab where
  lo : ℤ
  hi : ℤ
  idx : List ℕ

def dfltCell : CellV := ⟨0, 0, 0, 0⟩

def slabOK (cells : List CellV) (A0 A1 : ℤ) (s : Slab) : Bool :=
  s.idx.all (fun i => decide (i < cells.length) &&
    decide ((cells.getD i dfltCell).T0 - (cells.getD i dfltCell).hT ≤ s.lo) &&
    decide (s.hi ≤ (cells.getD i dfltCell).T0 + (cells.getD i dfltCell).hT)) &&
  chainCover A0 A1 (s.idx.map fun i =>
    ((cells.getD i dfltCell).A0 - (cells.getD i dfltCell).hA,
      (cells.getD i dfltCell).A0 + (cells.getD i dfltCell).hA))

def coverOK (cells : List CellV) (A0 A1 T0 T1 : ℤ) (slabs : List Slab) : Bool :=
  chainCover T0 T1 (slabs.map fun s => (s.lo, s.hi)) && slabs.all (slabOK cells A0 A1)

theorem coverOK_sound {cells : List CellV} {A0 A1 T0 T1 : ℤ} {slabs : List Slab}
    (h : coverOK cells A0 A1 T0 T1 slabs = true) {A t : ℝ}
    (hA0 : (A0 : ℝ) ≤ A * SC) (hA1 : A * SC ≤ A1) (hT0 : (T0 : ℝ) ≤ t * SC) (hT1 : t * SC ≤ T1) :
    ∃ cl ∈ cells, cl.Box A t := by
  unfold coverOK at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hc, hs⟩ := h
  obtain ⟨p, hp, hp1, hp2⟩ := chainCover_sound _ T0 T1 hc (t * SC) hT0 hT1
  rw [List.mem_map] at hp
  obtain ⟨s, hsm, rfl⟩ := hp
  have hsok := hs s hsm
  unfold slabOK at hsok
  rw [Bool.and_eq_true, List.all_eq_true] at hsok
  obtain ⟨hall, hch⟩ := hsok
  obtain ⟨q, hq, hq1, hq2⟩ := chainCover_sound _ A0 A1 hch (A * SC) hA0 hA1
  rw [List.mem_map] at hq
  obtain ⟨i, him, rfl⟩ := hq
  have hi := hall i him
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  obtain ⟨⟨hlen, hlo⟩, hhi⟩ := hi
  refine ⟨cells.getD i dfltCell, ?_, ?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
    exact List.getElem_mem hlen
  · simp only at hq1 hq2
    push_cast at hq1 hq2
    rw [abs_le]; constructor <;> linarith
  · have hlo' : (((cells.getD i dfltCell).T0 - (cells.getD i dfltCell).hT : ℤ) : ℝ) ≤ s.lo := by
      exact_mod_cast hlo
    have hhi' : (s.hi : ℝ) ≤ (((cells.getD i dfltCell).T0 + (cells.getD i dfltCell).hT : ℤ) : ℝ) := by
      exact_mod_cast hhi
    simp only at hp1 hp2
    push_cast at hlo' hhi' hp1 hp2
    rw [abs_le]; constructor <;> linarith

/-- S.3 row 4 from a verified cover of `[1/20, 21/200] × [1/80000, 1/100]` by cells with
`CellConcl`. -/
theorem rowOfCover {cells : List CellV} {A0 A1 T0 T1 : ℤ} {slabs : List Slab}
    (hcov : coverOK cells A0 A1 T0 T1 slabs = true)
    (hA0 : (A0 : ℝ) ≤ 1 / 20 * SC) (hA1 : 21 / 200 * SC ≤ (A1 : ℝ))
    (hT0 : (T0 : ℝ) ≤ 1 / 80000 * SC) (hT1 : 1 / 100 * SC ≤ (T1 : ℝ))
    (hcells : ∀ cl ∈ cells, CellConcl cl) : A3LeafUnion := by
  intro e f c hP ht0 ht1 ha0 ha1
  have hS := SC_pos
  obtain ⟨cl, hcl, hb⟩ := coverOK_sound hcov (A := chartA e f c) (t := chartTC f c)
    (by nlinarith) (by nlinarith) (by nlinarith) (by nlinarith)
  exact hcells cl hcl e f c hP hb

end CKLaneM07.CE

end


