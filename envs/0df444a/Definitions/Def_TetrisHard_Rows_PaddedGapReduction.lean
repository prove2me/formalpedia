-- Prove2me | Definitions.Def_TetrisHard_Rows_PaddedGapReduction
-- name    : TetrisHard_Rows_PaddedGapReduction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-19T06:47:22.803474+00:00
-- url     : https://prove2.me/theorems/a32863f7-7da7-4a44-b97a-b9ad2c4f560f
-- title:
--   Radius-padded reservoir board, game, and gap amplification parameters for Theorem 6.5
-- statement:
--   Radius-padded reservoir construction for Theorem 6.5 ($p^{1-\varepsilon}$ inapproximability of cleared rows) uniformly accommodating arbitrary admissible reasonable rotation models $R$ of any local neighborhood radius $\rho$.
--
--   1. **Maximum vertical jump.** Because $R.\mathrm{rule}$ is defined on a finite domain of $(2\rho+1)\times(2\rho+1)$ occupancy patches, $\mathrm{maxJump}(R)$ bounds the maximum vertical displacement $|d_y|$ of any single rotation step.
--   2. **Padded reservoir board.** For fixed padding parameters $\mathrm{pad} \ge \max(\rho,2)+2$, chimney parameter $K \ge \mathrm{maxJump}(R)+2$, staging height $\sigma \ge 5\max(\rho,2)+12$, and even reservoir height $r$, $\mathrm{paddedReservoirBoard}(P,\mathrm{pad},K,\sigma,r)$ has odd width $6(s+\mathrm{pad})+3$ (matching the `BucketFrame` width invariant for $s+\mathrm{pad}$ buckets) and places above the $r$-row reservoir: a two-row $\mathrm{RG}$ second lock, a $4K$-row one-cell-wide chimney, a $12\cdot\mathrm{pad}$-row buffer shaft isolating $(2\rho+1)\times(2\rho+1)$ bucket patches from the reservoir, and the base board $G(P)$ widened by $6\cdot\mathrm{pad}$ filled columns.
--   3. **Amplified game and threshold.** $\mathrm{paddedReservoirGame}$ appends $3\cdot\mathrm{pad}+K$ vertical $\mathrm{I}$ pieces, one $\mathrm{RG}$ key, and $r(6(s+\mathrm{pad})+2)/4$ squares to $\mathrm{basePieces}(P)$. With no-case cumulative bound $a(P) = 4(|S_0|+3\cdot\mathrm{pad}+K+1)+h_0+12\cdot\mathrm{pad}$ and piece factor $M(P)$, setting $r_k(P)=2(a(P)M(P)+1)^k$ defines $\mathrm{paddedGapGame}_{\mathrm{pad},K,\sigma,k}(w)$.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, Section 3 (p. 7), Section 5.3 (pp. 12-14), Section 6.2 and Figure 9(b) (pp. 19-21), Theorem 6.5 (p. 21), https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_GapReduction

set_option autoImplicit false

namespace TetrisHard.Rows.Padded

open TetrisHard.Rows

instance : Fintype Piece where
  elems := {.Sq, .LG, .RG, .LS, .RS, .I, .T}
  complete := fun p => by cases p <;> simp

/-- Maximum vertical displacement `|d.2|` over all entries in `R.rule`. -/
noncomputable def maxJump (R : Rotation) : ℕ :=
  letI : DecidableEq (Fin (2 * R.radius + 1) → Fin (2 * R.radius + 1) → Bool) :=
    Classical.decEq _
  Finset.univ.sup fun (x : Piece × Fin 4 × Bool × Bool ×
      (Fin (2 * R.radius + 1) → Fin (2 * R.radius + 1) → Bool)) =>
    match R.rule x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 with
    | none => 0
    | some d => d.2.natAbs

/-- Padded reservoir board with `6 * pad` dummy columns on the right (matching `BucketFrame`
width `6 * (s + pad) + 3`), a `12 * pad` buffer shaft, and a `4 * K` chimney above the
second `.RG` lock. -/
def paddedReservoirBoard (P : ThreePartition) (pad K staging r : ℕ) : Board where
  height := r + 2 + 4 * K + 12 * pad + (baseBoard P staging).height
  width := 6 * (P.s + pad) + 3
  cell := fun y x =>
    if y.val < r then decide (x.val = 0)
    else if y.val = r then decide (x.val ≠ 6 * (P.s + pad))
    else if y.val = r + 1 then decide (x.val < 6 * (P.s + pad))
    else if y.val < r + 2 + 4 * K then decide (x.val ≠ 6 * (P.s + pad) - 1)
    else if y.val < r + 2 + 4 * K + 12 * pad then decide (x.val ≠ 6 * P.s + 2)
    else if x.val < 6 * P.s + 3 then
      (baseBoard P staging).occupied (x.val, (y.val : ℤ) - (r + 2 + 4 * K + 12 * pad))
    else decide (y.val < r + 2 + 4 * K + 12 * pad + baseHeight P)

def paddedReservoirGame (P : ThreePartition) (pad K staging r : ℕ) : Game :=
  { board := paddedReservoirBoard P pad K staging r
    pieces := basePieces P ++ List.replicate (3 * pad) .I ++
      List.replicate K .I ++ [.RG] ++ List.replicate (r * (6 * (P.s + pad) + 2) / 4) .Sq }

/-- Cumulative cleared-row bound in a "no" instance of `paddedReservoirGame`, independent of `r`. -/
def paddedNoBound (P : ThreePartition) (pad K st : ℕ) : ℕ :=
  4 * ((basePieces P).length + 3 * pad + K + 1) + (baseBoard P st).height + 12 * pad

/-- Factor satisfying `|pieces| ≤ paddedPieceFactor P pad K * r` for all `1 ≤ r`. -/
def paddedPieceFactor (P : ThreePartition) (pad K : ℕ) : ℕ :=
  (basePieces P).length + 3 * pad + K + 1 + 6 * (P.s + pad) + 3

/-- Explicit even reservoir height for exponent parameter `k`. -/
def paddedGapRows (P : ThreePartition) (pad K st k : ℕ) : ℕ :=
  2 * (paddedNoBound P pad K st * paddedPieceFactor P pad K + 1) ^ k

/-- Amplified padded Tetris game attached to a binary word. -/
noncomputable def paddedGapGame (pad K st k : ℕ) (w : List Bool) : Game :=
  paddedReservoirGame (normInstance w) pad K st (paddedGapRows (normInstance w) pad K st k)

end TetrisHard.Rows.Padded


