-- Prove2me | Definitions.Def_TetrisHard_Rows_PaddedSoundness
-- name    : TetrisHard_Rows_PaddedSoundness
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-19T10:27:57.991771+00:00
-- url     : https://prove2.me/theorems/170403bc-1d68-45a3-94bb-db6da082968e
-- title:
--   Upper-board truncation, zero-waste bucket play, and bucket-height state predicates for Theorem 6.5
-- statement:
--   Canonical bucket-state definitions for the no-case soundness analysis of the padded reservoir game in Theorem 6.5 and Appendix C.
--
--   1. **Truncated upper board and zero-waste bucket play.** Given a board $B$ and row threshold $c \ge 0$, $\mathrm{dropRows}(B,c)$ removes the bottom $c$ rows of $B$. For $s$ active buckets inside a $6s'+3$-wide `BucketFrame` of bucket height $H'$, the inductive relation $\mathrm{NoRGSeqPlay}_R(s,s',H',U,S,\mathbf{u},U')$ records a row-deletion-free play of a piece sequence $S \subseteq \{\mathrm{LG},\mathrm{LS},\mathrm{Sq},\mathrm{I}\}^*$ in which each settled piece $u_i$ lands inside the vertical strip $[0,H')$ of some bucket $j \in \{0,\dots,s-1\}$. A bucket $j$ is strictly fillable ($\mathrm{FillableStrict}$) from $U$ if some continuation reaches $\mathrm{BucketFull}$ at height $H'$, and $U$ is $\mathrm{AllFillableStrict}$ if every bucket $j < s$ is strictly fillable.
--   2. **Single-bucket and multi-bucket height profiles.** Following Section 5.3 and Appendix C.1-C.2, we formalize the parameterized bucket occupancy patterns (`unpreppedPat`, `overflatPat`, `triggerHappyPat`, `iUpPat`, `shortPlateauPat`, `tallPlateauPat`, `addNotchLG`, `weirdPlateauPat`), the corresponding single-bucket predicates at height $h \le H'$ ($\mathrm{UnpreppedAt}$, $\mathrm{OverflatAt}$, $\mathrm{UnderflatAt}$, $\mathrm{TriggerHappyAt}$, $\mathrm{TallPlateauAt}$, $\mathrm{WeirdPlateauAt}$, $\mathrm{DeadPlateau}$), and the multi-bucket configurations $\mathrm{AllUnpreppedHeights}(U,s,H',\mathbf{h})$, $\mathrm{OneOverflatState}(U,s,H',j_0,h_0,\mathbf{h})$, and $\mathrm{DeadTriggerState}(U,s,H',j_{\mathrm{dp}},j_{\mathrm{th}},h_{\mathrm{th}},\mathbf{h})$.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 5.3-5.4 (pp. 12-18), Section 6.2 (pp. 19-21), and Appendix C.1-C.2 (pp. 25-33), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reservoir
import Definitions.Def_TetrisHard_Rows_PaddedGapReduction

set_option autoImplicit false

namespace TetrisHard.Rows.Padded

open TetrisHard.Rows

/-- Drop the bottom `cut` rows of a board `B`. -/
def dropRows (B : Board) (cut : ℕ) : Board where
  height := B.height - cut
  width := B.width
  cell := fun y x => B.cell ⟨cut + y.val, by omega⟩ x

/-- Exact piece-by-piece play on the upper board `U` without row deletions, where every piece
belongs to `[.LG, .LS, .Sq, .I]` and lands strictly inside `[0, H')` of some bucket `j : Fin s`. -/
inductive NoRGSeqPlay (R : Rotation) (s s' H' : ℕ) :
    Board → List Piece → List PieceState → Board → Prop
  | nil (U) : NoRGSeqPlay R s s' H' U [] [] U
  | step {U U' t ts u us} (j : Fin s) :
      t ∈ ([.LG, .LS, .Sq, .I] : List Piece) →
      BucketFrame U s' H' →
      InBucket j.val u →
      (∀ z ∈ u.cells, 0 ≤ z.2 ∧ z.2 < (H' : ℤ)) →
      Trajectory R U t u →
      NoRGSeqPlay R s s' H' (U.insert u) ts us U' →
      NoRGSeqPlay R s s' H' U (t :: ts) (u :: us) U'

/-- Bucket `j` can be filled to `BucketFull` via a zero-waste non-`RG` play inside `[0, H')`. -/
def FillableStrict (R : Rotation) (s s' H' : ℕ) (U : Board) (j : Fin s) : Prop :=
  ∃ ts us U_end, NoRGSeqPlay R s s' H' U ts us U_end ∧ BucketFull U_end j.val H'

/-- Every bucket `j : Fin s` is `FillableStrict`. -/
def AllFillableStrict (R : Rotation) (s s' H' : ℕ) (U : Board) : Prop :=
  ∀ j : Fin s, FillableStrict R s s' H' U j

/-- Standard single-bucket occupancy profile building blocks (Section 5.3 & Appendix C.1). -/
def unpreppedPat (h gap : ℕ) (x y : ℕ) : Bool :=
  decide (x < 5 ∧ y < h ∧ ¬ (x = gap ∧ h ≤ y + 4))

def overflatPat (h : ℕ) (x y : ℕ) : Bool :=
  decide (x < 5 ∧ y < h)

def triggerHappyPat (h : ℕ) (x y : ℕ) : Bool :=
  decide (x < 5 ∧ y + 1 < h ∧ ¬ (x = 2 ∧ y + 2 = h))

def iUpPat (h : ℕ) (x y : ℕ) : Bool :=
  unpreppedPat h 2 x y || decide (x = 0 ∧ h ≤ y ∧ y < h + 4)

def shortPlateauPat (h : ℕ) (x y : ℕ) : Bool :=
  unpreppedPat h 0 x y ||
    decide (((x = 1 ∨ x = 2) ∧ h ≤ y ∧ y < h + 3) ∨ ((x = 3 ∨ x = 4) ∧ y = h))

def tallPlateauPat (h : ℕ) (x y : ℕ) : Bool :=
  decide (x < 5 ∧ y < h ∧ ¬ (x = 0 ∧ h ≤ y + 9))

def addNotchLG (pat : ℕ → ℕ → Bool) (r : ℕ) (x y : ℕ) : Bool :=
  pat x y || decide ((x = 2 ∧ y = r + 1) ∨ (2 ≤ x ∧ x ≤ 4 ∧ y = r))

def weirdPlateauPat (h : ℕ) (x y : ℕ) : Bool :=
  addNotchLG (addNotchLG (unpreppedPat h 0) h) (h + 6) x y ||
    decide ((x = 1 ∨ x = 2) ∧ (y = h + 8 ∨ y = h + 9))

/-- Named single-bucket states with explicit height `h ≤ H'` (Section 5.3 & Appendix C.1). -/
def UnpreppedAt (U : Board) (j H' h : ℕ) : Prop :=
  ∃ gap : ℕ, 4 ≤ h ∧ h ≤ H' ∧ (h + 1) % 6 = 5 ∧ (gap = 0 ∨ gap = 2) ∧
    BucketPattern U j H' (unpreppedPat h gap)

def OverflatAt (U : Board) (j H' h : ℕ) : Prop :=
  6 ≤ h ∧ h ≤ H' ∧ h % 6 = 0 ∧ BucketPattern U j H' (overflatPat h)

def UnderflatAt (U : Board) (j H' h : ℕ) : Prop :=
  4 ≤ h ∧ h ≤ H' ∧ (h + 1) % 6 = 5 ∧ BucketPattern U j H' (overflatPat h)

def TriggerHappyAt (U : Board) (j H' h : ℕ) : Prop :=
  6 ≤ h ∧ h ≤ H' ∧ (h + 1) % 6 = 5 ∧ BucketPattern U j H' (triggerHappyPat h)

def TallPlateauAt (U : Board) (j H' h : ℕ) : Prop :=
  9 ≤ h ∧ h ≤ H' ∧ (h + 2) % 6 = 5 ∧ BucketPattern U j H' (tallPlateauPat h)

def WeirdPlateauAt (U : Board) (j H' h : ℕ) : Prop :=
  4 ≤ h ∧ h + 12 ≤ H' ∧ (h + 1) % 6 = 5 ∧ BucketPattern U j H' (weirdPlateauPat h)

def DeadPlateau (U : Board) (j H' : ℕ) : Prop :=
  (∃ h, TallPlateauAt U j H' h) ∨ (∃ h, WeirdPlateauAt U j H' h)

/-- Named multi-bucket state predicates across `Fin s` (Appendix C.2). -/
def AllUnpreppedHeights (U : Board) (s H' : ℕ) (h : Fin s → ℕ) : Prop :=
  ∀ j : Fin s, UnpreppedAt U j.val H' (h j)

def OneOverflatState (U : Board) (s H' : ℕ) (j₀ : Fin s) (h₀ : ℕ) (h : Fin s → ℕ) : Prop :=
  OverflatAt U j₀.val H' h₀ ∧ ∀ k : Fin s, k ≠ j₀ → UnpreppedAt U k.val H' (h k)

def DeadTriggerState (U : Board) (s H' : ℕ) (j_dp j_th : Fin s) (h_th : ℕ) (h : Fin s → ℕ) : Prop :=
  j_dp ≠ j_th ∧ DeadPlateau U j_dp.val H' ∧ TriggerHappyAt U j_th.val H' h_th ∧
    ∀ k : Fin s, k ≠ j_dp → k ≠ j_th → UnpreppedAt U k.val H' (h k)

end TetrisHard.Rows.Padded


