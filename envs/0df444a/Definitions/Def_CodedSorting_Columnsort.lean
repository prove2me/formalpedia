-- Prove2me | Definitions.Def_CodedSorting_Columnsort
-- name    : CodedSorting_Columnsort
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:08:00.654635+00:00
-- url     : https://prove2.me/theorems/c0f09eff-60cf-4b22-aa11-e051cb9c38bc
-- title:
--   Column sorting, the transpose of Columnsort, and the eight-step procedure
-- statement:
--   An array of $c$ columns of $r$ records is stored by column: the record in column $c'$ and row $q$ is at position $c'r+q$. **Column sorting** sorts each column independently and increasingly.
--
--   For $s$ columns of $r$ records, the **transpose** $\pi$ moves the record at position $j$ to $\pi(j)=(j\bmod s)r+\lfloor j/s\rfloor$, and its inverse moves the record at position $dr+q$ ($q<r$) to $sq+d$. The **eight-step Columnsort** procedure is:
--
--   1. sort each column;
--   2. apply $\pi$;
--   3. sort each column;
--   4. apply $\pi^{-1}$;
--   5. sort each column;
--   6. prepend $r/2$ records $-\infty$ and append $r/2$ records $+\infty$, giving $s+1$ columns of $r$ records;
--   7. sort each of the $s+1$ columns;
--   8. delete the first and last $r/2$ records.
--
--   The result is an array of $sr$ entries over the records extended by $\pm\infty$.
--
--   For a $4t$-bit index split into four $t$-bit fields numbered $1,\dots,4$ from the highest, the **adjacent field interchange** at positions $i+1,i+2$ is the address-field interchange of width $t$ with no intervening coordinate, the higher fields as prefix and the lower fields as suffix.
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §7.1, Proposition 7.1 and its proof, pp.27–28 (PDF 28–29)

import Mathlib
import Definitions.Def_CodedSorting_BitArray

namespace CodedSorting

/-! # Columnsort and the transpose as address-field interchanges

arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §7.1, Proposition 7.1, pp.27–28.
An array of `c` columns of `r` records is stored by column: the record in column `col` and row `q`
is at position `col·r + q`. -/

theorem colIdx_lt {c C r q : ℕ} (hc : c < C) (hq : q < r) : c * r + q < C * r := by
  nlinarith

/-- Sort each of the `c` columns (of `r` entries each) of an array increasingly and independently:
the entry at row `q` of column `col` becomes the `q`-th smallest entry of that column (with
multiplicity). -/
def colSort {β : Type} [LinearOrder β] (c r : ℕ) (A : Fin (c * r) → β) : Fin (c * r) → β :=
  fun j =>
    have hr : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h | h
      · subst h; exact absurd j.2 (by simp)
      · exact h
    have hcol : j.val / r < c := Nat.div_lt_of_lt_mul (lt_of_lt_of_eq j.2 (mul_comm c r))
    let col := (List.ofFn (fun q : Fin r => A ⟨(j.val / r) * r + q, colIdx_lt hcol q.2⟩)).mergeSort
      (fun a b => decide (a ≤ b))
    col.get ⟨j.val % r, by simp [col, List.length_mergeSort]; exact Nat.mod_lt _ hr⟩

/-- The transpose rearrangement `π` of step 2 (p.27): the record at position `j` moves to
`π(j) = (j mod s)·r + ⌊j/s⌋`. -/
def transposeIdx (s r j : ℕ) : ℕ := (j % s) * r + j / s

/-- The inverse rearrangement `π⁻¹` of step 4 (p.27): the record at position `d·r + q` (`q < r`)
moves back to position `s·q + d`. -/
def transposeInvIdx (s r i : ℕ) : ℕ := s * (i % r) + i / r

theorem transposeIdx_lt {s r j : ℕ} (hj : j < s * r) : transposeIdx s r j < s * r := by
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp at hj
    · exact h
  exact colIdx_lt (Nat.mod_lt _ hs) (Nat.div_lt_of_lt_mul hj)

theorem transposeInvIdx_lt {s r i : ℕ} (hi : i < s * r) : transposeInvIdx s r i < s * r := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h; simp at hi
    · exact h
  have h1 : i % r < r := Nat.mod_lt _ hr
  have h2 : i / r < s := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi)
  unfold transposeInvIdx
  nlinarith

theorem shift_lt {s r j : ℕ} (hj : j < s * r) : j + r / 2 < (s + 1) * r := by
  have := Nat.div_le_self r 2
  nlinarith

/-- **The eight-step Columnsort procedure** (Proposition 7.1, proof, p.27) on an array `A` of `s`
columns of `r` records, returning the array after step 8 with entries in `WithBot (WithTop α)`
(`⊥ = −∞` and `⊤ = +∞` are the padding records):
1. sort each column;
2. move the record at position `j` to `π(j) = (j mod s)·r + ⌊j/s⌋`;
3. sort each column;
4. move the record at position `d·r + q` back to `s·q + d` (`π⁻¹`);
5. sort each column;
6. prepend `r/2` copies of `−∞` and append `r/2` copies of `+∞`, giving `s + 1` columns of `r`
   records (when `r` is even);
7. sort each of the `s + 1` columns;
8. delete the first and last `r/2` records. -/
def columnsortLifted {α : Type} [LinearOrder α] (s r : ℕ) (A : Fin (s * r) → α) :
    Fin (s * r) → WithBot (WithTop α) :=
  let A1 := colSort s r A
  let A2 : Fin (s * r) → α := fun i => A1 ⟨transposeInvIdx s r i, transposeInvIdx_lt i.2⟩
  let A3 := colSort s r A2
  let A4 : Fin (s * r) → α := fun j => A3 ⟨transposeIdx s r j, transposeIdx_lt j.2⟩
  let A5 := colSort s r A4
  let B6 : Fin ((s + 1) * r) → WithBot (WithTop α) := fun j =>
    if j.val < r / 2 then ⊥
    else if h : j.val - r / 2 < s * r then ((A5 ⟨j.val - r / 2, h⟩ : WithTop α) : WithBot (WithTop α))
    else ((⊤ : WithTop α) : WithBot (WithTop α))
  let B7 := colSort (s + 1) r B6
  fun j => B7 ⟨j.val + r / 2, shift_lt j.2⟩

/-- The interchange of the adjacent `t`-bit fields at positions `i + 1` and `i + 2` (numbered
`1, …, 4` from the highest) of a `4t`-bit index, `i ∈ {0, 1, 2}` (p.28: "Numbering field positions
from highest to lowest, interchange positions 3, 4, then 2, 3, then 1, 2"). It is the address-field
interchange of §6.1 with width `u = t`, no intervening coordinate (`G = 1`), the lower
`2 − i` fields as the suffix (`ℓ = 2^{t(2−i)}`) and the higher fields as the prefix. -/
def fieldSwapAdj (t : ℕ) (i : Fin 3) (j : ℕ) : ℕ :=
  interchangeIndex 1 (2 ^ (t * (2 - (i : ℕ)))) t j

end CodedSorting


