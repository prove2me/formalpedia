-- Prove2me | Definitions.Def_TwoBoxMemory_Saddle
-- name    : TwoBoxMemory_Saddle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:48.821392+00:00
-- url     : https://prove2.me/theorems/aada3552-d0b3-4ac9-a9dc-bd0fb2197d0c
-- title:
--   The non-tie positive saddle: greedy word $W$, series $H_A,H_B$, saddle cost, margin $d_h$, separation
-- statement:
--   Fix $r,s\in(0,1)$ and an index $\beta>0$; $p=1-r$, $t=1-s$.
--
--   1. **Greedy word.** Merge the decreasing lists $(\beta r^i)_{i\ge0}$ and $(s^j)_{j\ge0}$: after $i$ commands $A$ and $j$ commands $B$, the next command is $A$ if $\beta r^i>s^j$ and $B$ if $s^j>\beta r^i$. The result is the word $W=W_0W_1\cdots$.
--   2. **Wrong-location series.** $n_j=\#\{i\ge0:\beta r^i>s^j\}$, $m_i=\#\{j\ge0:s^j>\beta r^i\}$, $H_A=\sum_{j\ge0}r^{n_j}$, $H_B=\sum_{i\ge0}s^{m_i}$, $u=1/p-H_B$, $v=1/t-H_A$.
--   3. **Saddle cost and priors.** For $D>0$: $C=Dv/u$, $\pi_A=Ct\beta/(Ct\beta+Dp)$, $\pi_B=Dp/(Ct\beta+Dp)$, $G=CDpt/(Ct\beta+Dp)$.
--   4. **Saddle.** $(r,s,\beta,D)$ is a *non-tie positive saddle with irrational logarithmic failure ratio* if $r,s\in(0,1)$, $\log r/\log s$ is irrational, $\beta>0$, $\beta r^i\ne s^j$ for all $i,j\ge0$, $u>0$, $v>0$ and $D>0$.
--   5. **First-departure margin.** $d_h=G\min_{i,j\ge0,\ i+j\le h}|\beta r^i-s^j|$.
--   6. **Exponential separation.** There are $a,c>0$ with $|\beta r^i-s^j|\ge a\,e^{-c(i+j)}$ for all $i,j\ge0$.
--
--   These objects state every lower and upper memory bound of the mission.
--
--   **Formalization Note** Commands are `Fin 2` ($0=A$). The greedy rule chooses $A$ iff $s^j<\beta r^i$; a tie would go to $B$, which never happens under the non-tie hypothesis. The counts are cardinalities of sets that are finite for $r,s\in(0,1)$, $\beta>0$, and $H_A,H_B$ are sums of summable series (proved in the verification file). The cost is not a free parameter: it is $Dv/u$.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §6, (6.1)–(6.2), pp.8–9 (PDF 10–11); §B.1, (B.1)–(B.3), p.21 (PDF 23); (B.8), p.22 (PDF 24); (B.13), p.24 (PDF 26)

import Mathlib

namespace TwoBoxMemory

/-!
# The non-tie positive saddle: greedy word, wrong-location series, saddle cost, departure margin

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§6, (6.1)–(6.2), pp.8–9 (PDF 10–11); §B.1, (B.1)–(B.2), p.21 (PDF 23); (B.8), p.22 (PDF 24);
(B.13), p.24 (PDF 26).

For failure probabilities `r, s ∈ (0, 1)` and an index `β > 0`, merging the decreasing lists
`(β r^i)_{i ≥ 0}` and `(s^j)_{j ≥ 0}` in decreasing order gives the greedy word `W`: after `i`
commands `A` and `j` commands `B`, the next command is `A` if `β r^i > s^j` and `B` if
`s^j > β r^i`. With `n_j = #{i : β r^i > s^j}`, `m_i = #{j : s^j > β r^i}`,
`H_A = ∑_j r^{n_j}`, `H_B = ∑_i s^{m_i}`, `u = 1/p − H_B`, `v = 1/t − H_A` (`p = 1 − r`,
`t = 1 − s`), the saddle cost is `C = D v / u`, the priors are
`π_A = C t β / (C t β + D p)`, `π_B = D p / (C t β + D p)`, and `G = C D p t / (C t β + D p)`.
The first-departure margin is `d_h = G min_{i + j ≤ h} |β r^i − s^j|`.

**Formalization Note.**
* Commands are `Fin 2` with `0 = A`, `1 = B`. `greedyCounts h = (N_A(h), N_B(h))` counts the
  commands strictly before time `h`.
* The greedy rule chooses `A` iff `s^j < β r^i`, so a tie would go to `B`; under the non-tie
  hypothesis (B.1) ties never occur and the tie-break is irrelevant.
* `nCnt`, `mCnt` are `Nat.card`s of sets that are finite for `r, s ∈ (0, 1)`, `β > 0`;
  `H_A`, `H_B` are `tsum`s of series that are summable under these hypotheses ((B.3); proved in the
  verification file), so no junk value arises.
* `IsSaddle r s β D` bundles exactly the standing hypotheses of §6 / §B.1: `r, s ∈ (0, 1)`,
  `log r / log s` irrational, `β > 0`, non-tie, `u > 0`, `v > 0`, `D > 0`. The cost is not a
  free parameter: it is `saddleCost r s β D = D v / u`.
* `departureMargin` takes the minimum over the nonempty finite set of pairs `(i, j)` with
  `i + j ≤ h`, as a `Finset.inf'`.
-/

noncomputable section

/-- `(N_A(h), N_B(h))` along the greedy word: the numbers of `A` and `B` commands strictly before
time `h`. -/
def greedyCounts (r s β : ℝ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | h + 1 =>
    let c := greedyCounts r s β h
    if s ^ c.2 < β * r ^ c.1 then (c.1 + 1, c.2) else (c.1, c.2 + 1)

/-- The greedy word `W`: command `A` (`0`) at time `h` iff `β r^{N_A(h)} > s^{N_B(h)}`. -/
def greedyWord (r s β : ℝ) (h : ℕ) : Fin 2 :=
  if s ^ (greedyCounts r s β h).2 < β * r ^ (greedyCounts r s β h).1 then 0 else 1

/-- `n_j = #{i ≥ 0 : β r^i > s^j}`. -/
def nCnt (r s β : ℝ) (j : ℕ) : ℕ := Nat.card {i : ℕ | s ^ j < β * r ^ i}

/-- `m_i = #{j ≥ 0 : s^j > β r^i}`. -/
def mCnt (r s β : ℝ) (i : ℕ) : ℕ := Nat.card {j : ℕ | β * r ^ i < s ^ j}

/-- The wrong-location series `H_A = ∑_{j ≥ 0} r^{n_j}`. -/
def HA (r s β : ℝ) : ℝ := ∑' j : ℕ, r ^ nCnt r s β j

/-- The wrong-location series `H_B = ∑_{i ≥ 0} s^{m_i}`. -/
def HB (r s β : ℝ) : ℝ := ∑' i : ℕ, s ^ mCnt r s β i

/-- `u = 1/p − H_B`, `p = 1 − r`. -/
def uSaddle (r s β : ℝ) : ℝ := 1 / (1 - r) - HB r s β

/-- `v = 1/t − H_A`, `t = 1 − s`. -/
def vSaddle (r s β : ℝ) : ℝ := 1 / (1 - s) - HA r s β

/-- The saddle cost `C = D v / u` of (6.1)/(B.2). -/
def saddleCost (r s β D : ℝ) : ℝ := D * vSaddle r s β / uSaddle r s β

/-- The prior `π_A = C t β / (C t β + D p)` of (B.2), at the saddle cost. -/
def piA (r s β D : ℝ) : ℝ :=
  saddleCost r s β D * (1 - s) * β / (saddleCost r s β D * (1 - s) * β + D * (1 - r))

/-- The prior `π_B = D p / (C t β + D p)` of (B.2), at the saddle cost. -/
def piB (r s β D : ℝ) : ℝ :=
  D * (1 - r) / (saddleCost r s β D * (1 - s) * β + D * (1 - r))

/-- `G = C D p t / (C t β + D p)` of (6.1)/(B.2), at the saddle cost. -/
def Gconst (r s β D : ℝ) : ℝ :=
  saddleCost r s β D * D * (1 - r) * (1 - s) /
    (saddleCost r s β D * (1 - s) * β + D * (1 - r))

/-- The non-tie condition (B.1): `β r^i ≠ s^j` for all integers `i, j ≥ 0`. -/
def IsNonTie (r s β : ℝ) : Prop := ∀ i j : ℕ, β * r ^ i ≠ s ^ j

/-- A non-tie positive saddle with irrational logarithmic failure ratio (§6, §B.1). -/
def IsSaddle (r s β D : ℝ) : Prop :=
  0 < r ∧ r < 1 ∧ 0 < s ∧ s < 1 ∧ Irrational (Real.log r / Real.log s) ∧ 0 < β ∧
    IsNonTie r s β ∧ 0 < uSaddle r s β ∧ 0 < vSaddle r s β ∧ 0 < D

/-- The pairs `(i, j)` of nonnegative integers with `i + j ≤ h`. -/
def indexPairs (h : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (h + 1) ×ˢ Finset.range (h + 1)).filter fun q => q.1 + q.2 ≤ h

lemma indexPairs_nonempty (h : ℕ) : (indexPairs h).Nonempty :=
  ⟨(0, 0), by simp [indexPairs]⟩

/-- The minimal index gap `min_{i + j ≤ h} |β r^i − s^j|`. -/
def minIndexGap (r s β : ℝ) (h : ℕ) : ℝ :=
  (indexPairs h).inf' (indexPairs_nonempty h) fun q => |β * r ^ q.1 - s ^ q.2|

/-- The first-departure margin `d_h = G min_{i + j ≤ h} |β r^i − s^j|` of (6.2)/(B.8). -/
def departureMargin (r s β D : ℝ) (h : ℕ) : ℝ :=
  Gconst r s β D * minIndexGap r s β h

/-- Exponential separation (B.13): there are `a, c > 0` with
`|β r^i − s^j| ≥ a e^{−c(i+j)}` for all integers `i, j ≥ 0`. -/
def Sep (r s β : ℝ) : Prop :=
  ∃ a > 0, ∃ c > 0, ∀ i j : ℕ, a * Real.exp (-(c * ((i : ℝ) + j))) ≤ |β * r ^ i - s ^ j|

end

end TwoBoxMemory


