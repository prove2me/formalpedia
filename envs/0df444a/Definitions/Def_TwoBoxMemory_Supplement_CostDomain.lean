-- Prove2me | Definitions.Def_TwoBoxMemory_Supplement_CostDomain
-- name    : TwoBoxMemory_Supplement_CostDomain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:13:02.669324+00:00
-- url     : https://prove2.me/theorems/f527652d-9be1-4f7e-a81d-df35897d2eea
-- title:
--   A-first series $H_A$, $v$, ties $\beta_{ab}$, cost intervals $I_{ab}$ and the tied greedy words $W^\pm$
-- statement:
--   Let $r,s\in(0,1)$, $p=1-r$, $t=1-s$. For an index ratio $\beta>0$ merge the decreasing sequences $\beta r^i$ and $s^j$ ($i,j\ge0$), using $A$ before $B$ at equality. The wrong-location sums are
--
--   $$H_A(\beta)=\sum_{j\ge0}r^{n_j(\beta)},\quad n_j(\beta)=\#\{i\ge0:\beta r^i\ge s^j\},\qquad H_B(\beta)=\sum_{i\ge0}s^{m_i(\beta)},\quad m_i(\beta)=\#\{j\ge0:s^j>\beta r^i\},$$
--
--   and $u(\beta)=1/p-H_B(\beta)$, $v(\beta)=1/t-H_A(\beta)$. The **ties** are $\beta_{ab}=s^b/r^a$ ($a,b\ge0$). With $u^+,v^+$ the values of $u,v$ at $\beta_{ab}$ and $u^-,v^-$ their left limits there,
--
--   $$I_{ab}=\{R>0:\ Ru^+<v^+,\ Ru^->v^-\},\qquad I(r,s)=\bigcup_{a,b\ge0}I_{ab}.$$
--
--   At $\beta_{ab}$ the **tied greedy words** are $W^+$ (A first at ties: after $i$ A's and $j$ B's the next command is $A$ iff $\beta r^i\ge s^j$) and $W^-$ (B first: $A$ iff $\beta r^i>s^j$). The prior of the tie is
--
--   $$\pi_A=\frac{Cts^b}{Cts^b+Dpr^a},\qquad \pi_B=\frac{Dpr^a}{Cts^b+Dpr^a}.$$
--
--   These objects state the full-measure cost-domain theorem (Theorem E.3) and the covering theorem (Theorem F.2).
--
--   **Formalization Note** $m_i$, $H_B$, $u$ and $W^-$ are the published `mCnt`, `HB`, `uSaddle`, `greedyWord` (strict comparison); $n_j$, $H_A$, $v$ use the weak comparison of (E.1) and are new. Left limits are `Function.leftLim`; $u$ and $v$ are monotone on $(0,\infty)$, so they exist.
-- source:
--   Qi, Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds, STOC 2027 submission (manuscript sha256 ac04a467…), §E.1, (E.1)–(E.7), pp.41–42 (PDF 43–44)

import Mathlib
import Definitions.Def_TwoBoxMemory_Saddle

namespace TwoBoxMemory.Supplement

/-!
# The A-first wrong-location series, the ties `β_ab`, the strict-mixture cost intervals `I_ab`

Q. Qi, *Finite-Memory Search: Rational Compilation and Arithmetic Lower Bounds*, STOC 2027
submission manuscript (sha256 ac04a4671341b3d97536a68e5b00e26e3176b9042928eba8b2c02d62c6159d65),
§E.1, (E.1)–(E.7), pp.41–42 (PDF 43–44).

For `r, s ∈ (0, 1)`, `p = 1 − r`, `t = 1 − s` and an index ratio `β > 0`, merge the decreasing
sequences `β r^i` and `s^j`, using `A` before `B` at equality; this defines the greedy word
`w⁺_β`. Its wrong-location sums are (E.1)
`H_A(β) = ∑_{j ≥ 0} r^{n_j(β)}`, `n_j(β) = #{i ≥ 0 : β r^i ≥ s^j}`,
`H_B(β) = ∑_{i ≥ 0} s^{m_i(β)}`, `m_i(β) = #{j ≥ 0 : s^j > β r^i}`,
and (E.2) `u(β) = 1/p − H_B(β)`, `v(β) = 1/t − H_A(β)`. The ties are
`β_ab = s^b / r^a` (E.3). With `u⁺, v⁺` the values of `u, v` at `β_ab` and `u⁻, v⁻` their left
limits, (E.6) `I_ab = {R > 0 : R u⁺ < v⁺, R u⁻ > v⁻}` and `I(r, s) = ⋃_{a,b ≥ 0} I_ab`.
At a tie the two greedy words are `W⁺` (A first) and `W⁻` (B first) (E.4); the prior (E.7) is
`π_A = C t s^b / (C t s^b + D p r^a)`, `π_B = D p r^a / (C t s^b + D p r^a)`.

**Formalization Note.**
* `m_i`, `H_B`, `u` are the published `TwoBoxMemory.mCnt`, `HB`, `uSaddle` (strict inequality
  `β r^i < s^j`): they are reused. `n_j` uses the **weak** inequality `s^j ≤ β r^i`, unlike the
  published `nCnt` (strict), so `nCntW`, `HAW`, `vW` are new.
* `n_j` is a `Nat.card` of a set that is finite for `r ∈ (0, 1)`, `β > 0`; `H_A` is a `tsum` of a
  series summable under these hypotheses (`r^{n_j} < s^j/β`, (E.8)), so no junk value arises for
  `β > 0`.
* `u⁻`, `v⁻` are `Function.leftLim` at `β_ab > 0`. `u` and `v` are monotone on `(0, ∞)`
  (Lemma E.2), so the left limits exist and `leftLim` returns them.
* `W⁺` is `greedyWordW` (A at ties, `s^j ≤ β r^i`), defined like the published `greedyWord`
  (B at ties, `s^j < β r^i`); at `β = β_ab` the published `greedyWord r s β_ab` is `W⁻`.
* Commands are `Fin 2` with `0 = A`, `1 = B`.
-/

noncomputable section

/-- `n_j(β) = #{i ≥ 0 : β r^i ≥ s^j}` of (E.1) (weak inequality). -/
def nCntW (r s β : ℝ) (j : ℕ) : ℕ := Nat.card {i : ℕ | s ^ j ≤ β * r ^ i}

/-- `H_A(β) = ∑_{j ≥ 0} r^{n_j(β)}` of (E.1). -/
def HAW (r s β : ℝ) : ℝ := ∑' j : ℕ, r ^ nCntW r s β j

/-- `v(β) = 1/t − H_A(β)` of (E.2). -/
def vW (r s β : ℝ) : ℝ := 1 / (1 - s) - HAW r s β

/-- The tie ratio `β_ab = s^b / r^a` of (E.3). -/
def betaTie (r s : ℝ) (a b : ℕ) : ℝ := s ^ b / r ^ a

/-- `u⁺ = u(β_ab)`. -/
def uPlus (r s : ℝ) (a b : ℕ) : ℝ := TwoBoxMemory.uSaddle r s (betaTie r s a b)

/-- `v⁺ = v(β_ab)`. -/
def vPlus (r s : ℝ) (a b : ℕ) : ℝ := vW r s (betaTie r s a b)

/-- `u⁻`: the left limit of `u` at `β_ab`. -/
def uMinus (r s : ℝ) (a b : ℕ) : ℝ :=
  Function.leftLim (TwoBoxMemory.uSaddle r s) (betaTie r s a b)

/-- `v⁻`: the left limit of `v` at `β_ab`. -/
def vMinus (r s : ℝ) (a b : ℕ) : ℝ := Function.leftLim (vW r s) (betaTie r s a b)

/-- The open cost interval `I_ab = {R > 0 : R u⁺ < v⁺, R u⁻ > v⁻}` of (E.6) (possibly empty or
unbounded). -/
def Iab (r s : ℝ) (a b : ℕ) : Set ℝ :=
  {R : ℝ | 0 < R ∧ R * uPlus r s a b < vPlus r s a b ∧ vMinus r s a b < R * uMinus r s a b}

/-- The strict-mixture cost domain `I(r, s) = ⋃_{a,b ≥ 0} I_ab`. -/
def Icost (r s : ℝ) : Set ℝ := ⋃ (a : ℕ) (b : ℕ), Iab r s a b

/-- `(N_A(h), N_B(h))` along the A-first greedy word `w⁺_β`. -/
def greedyCountsW (r s β : ℝ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | h + 1 =>
    let c := greedyCountsW r s β h
    if s ^ c.2 ≤ β * r ^ c.1 then (c.1 + 1, c.2) else (c.1, c.2 + 1)

/-- The A-first greedy word `w⁺_β`: command `A` (`0`) at time `h` iff
`β r^{N_A(h)} ≥ s^{N_B(h)}`. -/
def greedyWordW (r s β : ℝ) (h : ℕ) : Fin 2 :=
  if s ^ (greedyCountsW r s β h).2 ≤ β * r ^ (greedyCountsW r s β h).1 then 0 else 1

/-- `W⁺` of (E.4): the A-first greedy word at the tie `β_ab`. -/
def wordPlus (r s : ℝ) (a b : ℕ) : ℕ → Fin 2 := greedyWordW r s (betaTie r s a b)

/-- `W⁻` of (E.4): the B-first greedy word at the tie `β_ab` (the published `greedyWord`). -/
def wordMinus (r s : ℝ) (a b : ℕ) : ℕ → Fin 2 := TwoBoxMemory.greedyWord r s (betaTie r s a b)

/-- The prior `π_A = C t s^b / (C t s^b + D p r^a)` of (E.7). -/
def piAab (r s C D : ℝ) (a b : ℕ) : ℝ :=
  C * (1 - s) * s ^ b / (C * (1 - s) * s ^ b + D * (1 - r) * r ^ a)

/-- The prior `π_B = D p r^a / (C t s^b + D p r^a)` of (E.7). -/
def piBab (r s C D : ℝ) (a b : ℕ) : ℝ :=
  D * (1 - r) * r ^ a / (C * (1 - s) * s ^ b + D * (1 - r) * r ^ a)

end

end TwoBoxMemory.Supplement


