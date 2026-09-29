-- Prove2me | Definitions.Def_MasekPaterson_FourRussians_algorithms
-- name    : MasekPaterson_FourRussians_algorithms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T23:02:43.219982+00:00
-- url     : https://prove2.me/theorems/c3e73bf3-44ca-490c-978b-fb181d3d8506
-- title:
--   Algorithm Y (submatrix steps) and Algorithm Z (block assembly) of Masek–Paterson
-- statement:
--   Let $\gamma$ be a cost function with replacement, deletion and insertion costs $R_{a,b}$, $D_a$, $I_a$.
--
--   **Algorithm Y.** Given strings $C = C_1 \cdots C_m$ and $D = D_1 \cdots D_m$ and step vectors $R = \langle R(1), \dots, R(m) \rangle$ and $S = \langle S(1), \dots, S(m)\rangle$, set $T(i, 0) = R(i)$ and $U(0, i) = S(i)$ for $1 \le i \le m$, and for $i = 1, \dots, m$ and $j = 1, \dots, m$ (row by row)
--
--   $$T(i,j) = \min\{R_{C_i,D_j} - U(i-1,j),\ D_{C_i},\ I_{D_j} + T(i,j-1) - U(i-1,j)\},$$
--
--   $$U(i,j) = \min\{R_{C_i,D_j} - T(i,j-1),\ D_{C_i} + U(i-1,j) - T(i,j-1),\ I_{D_j}\}.$$
--
--   The output is the pair of final step vectors $R' = \langle T(1,m), \dots, T(m,m)\rangle$ and $S' = \langle U(m,1), \dots, U(m,m)\rangle$. Here $T$ holds vertical steps and $U$ horizontal steps; $R$ is the left column and $S$ the top row of a submatrix, $R'$ its right column and $S'$ its bottom row. In the paper this output is stored for every pair of length-$m$ strings and every pair of length-$m$ step vectors, and $\mathrm{Fetch}(R, S, C, D)$ returns it.
--
--   **Algorithm Z.** Given strings $A, B$ and a block size $m$, let $a = \lfloor |A|/m \rfloor$ and $b = \lfloor |B|/m \rfloor$. Set
--
--   $$P(i, 0) = \langle D_{A_{(i-1)m+1}}, \dots, D_{A_{im}}\rangle \ (1 \le i \le a), \qquad Q(0, j) = \langle I_{B_{(j-1)m+1}}, \dots, I_{B_{jm}}\rangle \ (1 \le j \le b),$$
--
--   and for $i = 1, \dots, a$ and $j = 1, \dots, b$ let $\langle P(i,j), Q(i,j)\rangle$ be Algorithm Y's output on the strings $A^{(i-1)m+1, im}$, $B^{(j-1)m+1, jm}$ and the step vectors $R = P(i, j-1)$, $S = Q(i-1, j)$. The algorithm returns
--
--   $$\mathrm{cost} = \sum_{i=1}^{a} \mathrm{Sum}(P(i, 0)) + \sum_{j=1}^{b} \mathrm{Sum}(Q(a, j)),$$
--
--   where $\mathrm{Sum}$ adds the components of a vector.
--
--   These are the two phases of the Masek–Paterson "four Russians" edit-distance algorithm: Algorithm Y precomputes the final step vectors of every possible $m \times m$ submatrix, and Algorithm Z assembles the full matrix of steps block by block from that table.
--
--   **Formalization Note** Both algorithms are transcribed literally from the pseudo-code; neither refers to $\delta$. `algYCell … i j` is the pair $(T(i,j), U(i,j))$ and `blockY γ m C D R S` is $(R', S')$; `algZCell … i j` is $(P(i,j), Q(i,j))$ and `algZ γ m A B` is the returned cost. Vectors are functions on `Fin m` (entry `k` is the paper's entry $k+1$). Cells the pseudo-code never assigns are $0$ (never read by an assigned cell). The block $A^{(i-1)m+1, im}$ is taken only when $im \le |A|$, which for $m \ge 1$ is $i \le \lfloor |A|/m \rfloor$. The paper's pseudo-code prints the assignment as $\langle P(i,j), U(i,j)\rangle := \mathrm{Fetch}(\dots)$; the $U$ is a misprint for $Q$, since $Q(|A|/m, j)$ is read in the last line. The Store/Fetch memory is not modelled: the table is the function `blockY` itself.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 22, Section 2.1, Algorithm Y; p. 24, Section 2.2, Algorithm Z

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
open MasekPaterson.Shared

namespace MasekPaterson.FourRussians

variable {α : Type*}

/-- Algorithm Y's two step matrices, computed together: `algYCell γ m C D R S i j` is the pair
`(T(i, j), U(i, j))` for `1 ≤ i, j ≤ m`, with the boundary cells `T(i, 0) := R(i)` and
`U(0, j) := S(j)` (`1 ≤ i, j ≤ m`) and, for `1 ≤ i, j ≤ m`,
`T(i,j) := min{R_{C_i,D_j} − U(i−1,j), D_{C_i}, I_{D_j} + T(i,j−1) − U(i−1,j)}` and
`U(i,j) := min{R_{C_i,D_j} − T(i,j−1), D_{C_i} + U(i−1,j) − T(i,j−1), I_{D_j}}`.
Strings and step vectors are 1-based in the paper: `C_i` is `C ⟨i-1, _⟩`, `R(i)` is
`R ⟨i-1, _⟩`. Cells the algorithm never assigns (outside the ranges above, and the unused
component of a boundary cell) are `0`. -/
noncomputable def algYCell (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ) :
    ℕ → ℕ → ℝ × ℝ
  | 0, 0 => (0, 0)
  | i + 1, 0 => (if h : i < m then R ⟨i, h⟩ else 0, 0)
  | 0, j + 1 => (0, if h : j < m then S ⟨j, h⟩ else 0)
  | i + 1, j + 1 =>
    if h : i < m ∧ j < m then
      -- `Tl` is `T(i+1, j)` and `Uu` is `U(i, j+1)` in the paper's 1-based coordinates
      let Tl := (algYCell γ m C D R S (i + 1) j).1
      let Uu := (algYCell γ m C D R S i (j + 1)).2
      let r := replCost γ (C ⟨i, h.1⟩) (D ⟨j, h.2⟩)
      let d := delCost γ (C ⟨i, h.1⟩)
      let n := insCost γ (D ⟨j, h.2⟩)
      (min (min (r - Uu) d) (n + Tl - Uu), min (min (r - Tl) (d + Uu - Tl)) n)
    else (0, 0)

/-- Algorithm Y's matrix `T` of vertical steps. -/
noncomputable def algY_T (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ)
    (i j : ℕ) : ℝ :=
  (algYCell γ m C D R S i j).1

/-- Algorithm Y's matrix `U` of horizontal steps. -/
noncomputable def algY_U (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ)
    (i j : ℕ) : ℝ :=
  (algYCell γ m C D R S i j).2

/-- Algorithm Y on one submatrix (the value it stores, and `Fetch` returns): for strings
`C, D` of length `m` and initial step vectors `R` (left column, vertical steps) and `S`
(top row, horizontal steps), the final step vectors `R' = ⟨T(1,m), …, T(m,m)⟩` (right column)
and `S' = ⟨U(m,1), …, U(m,m)⟩` (bottom row). -/
noncomputable def blockY (γ : EditOp α → ℝ) (m : ℕ) (C D : Fin m → α) (R S : Fin m → ℝ) :
    (Fin m → ℝ) × (Fin m → ℝ) :=
  (fun k => algY_T γ m C D R S (k.val + 1) m, fun k => algY_U γ m C D R S m (k.val + 1))

/-- The `(b+1)`-th length-`m` block `A^{bm+1, bm+m}` of `A` as a vector `Fin m → α`
(its `k`-th entry, 0-based, is `A_{bm+k+1}`), when it fits: `(b+1) m ≤ |A|`. -/
def blockStr (A : List α) (m b : ℕ) (h : (b + 1) * m ≤ A.length) : Fin m → α :=
  fun k => A[b * m + k.val]'(by
    have hk := k.isLt
    have : (b + 1) * m = b * m + m := Nat.succ_mul b m
    omega)

/-- Algorithm Z's matrices, computed together: `algZCell γ m A B i j = (P(i, j), Q(i, j))`.
With `a = |A|/m` and `b = |B|/m`:
`P(i, 0) := ⟨D_{A_{(i−1)m+1}}, …, D_{A_{im}}⟩` for `1 ≤ i ≤ a`,
`Q(0, j) := ⟨I_{B_{(j−1)m+1}}, …, I_{B_{jm}}⟩` for `1 ≤ j ≤ b`, and for `1 ≤ i ≤ a`,
`1 ≤ j ≤ b`, `⟨P(i,j), Q(i,j)⟩ := Fetch(P(i,j−1), Q(i−1,j), A^{(i−1)m+1,im}, B^{(j−1)m+1,jm})`
where `Fetch(R, S, C, D)` is Algorithm Y's result `blockY γ m C D R S`. Cells the algorithm
never assigns are the zero vector. -/
noncomputable def algZCell (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) :
    ℕ → ℕ → (Fin m → ℝ) × (Fin m → ℝ)
  | 0, 0 => (0, 0)
  | i + 1, 0 =>
    (if h : (i + 1) * m ≤ A.length then fun k => delCost γ (blockStr A m i h k) else 0, 0)
  | 0, j + 1 =>
    (0, if h : (j + 1) * m ≤ B.length then fun k => insCost γ (blockStr B m j h k) else 0)
  | i + 1, j + 1 =>
    if h : (i + 1) * m ≤ A.length ∧ (j + 1) * m ≤ B.length then
      blockY γ m (blockStr A m i h.1) (blockStr B m j h.2)
        (algZCell γ m A B (i + 1) j).1 (algZCell γ m A B i (j + 1)).2
    else (0, 0)

/-- Algorithm Z's matrix `P` of column step vectors. -/
noncomputable def algZ_P (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) (i j : ℕ) : Fin m → ℝ :=
  (algZCell γ m A B i j).1

/-- Algorithm Z's matrix `Q` of row step vectors. -/
noncomputable def algZ_Q (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) (i j : ℕ) : Fin m → ℝ :=
  (algZCell γ m A B i j).2

/-- The value `cost` returned by Algorithm Z:
`∑_{i=1}^{|A|/m} Sum(P(i, 0)) + ∑_{j=1}^{|B|/m} Sum(Q(|A|/m, j))`. -/
noncomputable def algZ (γ : EditOp α → ℝ) (m : ℕ) (A B : List α) : ℝ :=
  (∑ i ∈ Finset.Icc 1 (A.length / m), ∑ k, algZ_P γ m A B i 0 k) +
    ∑ j ∈ Finset.Icc 1 (B.length / m), ∑ k, algZ_Q γ m A B (A.length / m) j k

end MasekPaterson.FourRussians


