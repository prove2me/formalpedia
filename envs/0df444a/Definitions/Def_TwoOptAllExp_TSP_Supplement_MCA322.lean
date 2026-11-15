-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA322
-- name    : TwoOptAllExp_TSP_Supplement_MCA322
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:43:27.446573+00:00
-- url     : https://prove2.me/theorems/ee38b7fe-59c0-4862-81d3-b93d2fcf7967
-- title:
--   The $(3,2,2)$-MCA instance $I_n$ of Section 3 and the flip sequence $S_n$
-- statement:
--   For $n\ge0$ the instance $I_n$ has $6n+2$ variables: $v_{0,1},v_{0,6}$ in layer $0$ and $v_{i,1},\dots,v_{i,6}$ in layer $i\in[n]$. Its $4n+1$ constraints are $C_0(v_{0,1},v_{0,6})$ and, for $i\in[n]$,
--   $C_{i,1}(v_{i-1,1},v_{i,1},v_{i,3})$, $C_{i,2}(v_{i-1,6},v_{i,2},v_{i,4})$, $C_{i,3}(v_{i,2},v_{i,3},v_{i,5})$, $C_{i,4}(v_{i,4},v_{i,5},v_{i,6})$.
--   With $P_i=2^{i+3}$ and arguments listed in the order $00,01,10,11$ resp. $000,001,\dots,111$, the weight tables are (Tables 1–2)
--
--   $$C_0:\ (14,1,15,16),\qquad C_{i,1}:\ (P_i,1,P_i+1,2P_i,0,1,P_i+1,P_i),\qquad C_{i,2}:\ (2,0,0,14,2,12,12,14),$$
--   $$C_{i,3}:\ (P_i+9,P_i+8,0,P_i+6,P_i,0,P_i+2,P_i+3),\qquad C_{i,4}:\ (13,0,0,0,0,0,0,1).$$
--
--   The initial assignment is all zero. The flip sequence $S_n$ is defined by $S_0=(v_{0,1},v_{0,6})$ and $S_i=(v_{i,1},S_{i-1},v_{i,2},v_{i,3},S_{i-1},v_{i,4},v_{i,5},v_{i,6})$ for $i\ge1$.
--
--   This is the family behind Lemma 6 and Theorem 2.
--
--   **Formalization Note** Variables are $\{0,\dots,6n+1\}$ with $v_{0,1}\mapsto0$, $v_{0,6}\mapsto1$, $v_{i,j}\mapsto 2+6(i-1)+(j-1)$; constraints are numbered $C_0\mapsto0$, $C_{i,k}\mapsto1+4(i-1)+(k-1)$. Table rows are indexed by the arguments read as a binary number, first argument most significant. $S_n$ is defined by the recursion only, not by any improvement property.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §3, p. 8, Tables 1–2, p. 9; Lemma 6 (1)–(2), p. 9

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA

namespace TwoOptAllExp.TSP.Supplement.MCA322

/-! # The (3,2,2)-MCA instance `I_n` of Section 3

Heimann, Hoang and Hougardy, November 2, 2026 preprint (STOC 2027 submission #112), §3,
pp. 8–9, Tables 1–2, and Lemma 6, p. 9. The instance has `n + 1` layers: layer `0` has the
variables `v_{0,1}, v_{0,6}` and the constraint `C_0`; layer `i ∈ [n]` has the variables
`v_{i,1}, …, v_{i,6}` and the constraints `C_{i,1}, …, C_{i,4}`. Value `true` is `1` (red, ◦) and
`false` is `0` (green, •). -/

/-- The index of the variable `v_{i,j}` in `{0, …, 6n+1}`: `v_{0,1} ↦ 0`, `v_{0,6} ↦ 1`, and
`v_{i,j} ↦ 2 + 6(i-1) + (j-1)` for `1 ≤ i ≤ n`, `1 ≤ j ≤ 6`. -/
def varIdx (i j : ℕ) : ℕ :=
  if i = 0 then (if j = 1 then 0 else 1) else 2 + 6 * (i - 1) + (j - 1)

/-- The variable `v_{i,j}` of `I_n` (meaningful for `i = 0, j ∈ {1, 6}` and `1 ≤ i ≤ n`,
`1 ≤ j ≤ 6`; there `varIdx i j < 6n + 2`). -/
def v (n i j : ℕ) : Fin (6 * n + 2) :=
  ⟨varIdx i j % (6 * n + 2), Nat.mod_lt _ (by omega)⟩

/-- The index of a row of a weight table: the arguments `(a_1, …, a_p)` read as a binary number
with `a_1` most significant, so that the rows `00, 01, 10, 11` (resp. `000, …, 111`) of Tables 1
and 2 are the rows `0, 1, 2, 3` (resp. `0, …, 7`). -/
def rowIdx (a : List Bool) : ℕ :=
  a.foldl (fun acc x => 2 * acc + (if x then 1 else 0)) 0

/-- `P_i = 2^{i+3}` (proof of Lemma 6, p. 10). -/
def P (i : ℕ) : ℤ := 2 ^ (i + 3)

/-- The layer `i ∈ [n]` and the position `k ∈ {1,2,3,4}` of the constraint numbered `c ≥ 1`:
the constraints are numbered `C_0 ↦ 0` and `C_{i,k} ↦ 1 + 4(i-1) + (k-1)`. -/
def layerOf (c : ℕ) : ℕ := (c - 1) / 4 + 1

/-- See `layerOf`. -/
def posOf (c : ℕ) : ℕ := (c - 1) % 4 + 1

/-- The ordered scope of the constraint numbered `c` (p. 8):
`C_0(v_{0,1}, v_{0,6})`, `C_{i,1}(v_{i-1,1}, v_{i,1}, v_{i,3})`, `C_{i,2}(v_{i-1,6}, v_{i,2}, v_{i,4})`,
`C_{i,3}(v_{i,2}, v_{i,3}, v_{i,5})`, `C_{i,4}(v_{i,4}, v_{i,5}, v_{i,6})`. -/
def scope (n c : ℕ) : List (Fin (6 * n + 2)) :=
  if c = 0 then [v n 0 1, v n 0 6] else
    let i := layerOf c
    match posOf c with
    | 1 => [v n (i - 1) 1, v n i 1, v n i 3]
    | 2 => [v n (i - 1) 6, v n i 2, v n i 4]
    | 3 => [v n i 2, v n i 3, v n i 5]
    | _ => [v n i 4, v n i 5, v n i 6]

/-- The rows of the weight table of the constraint numbered `c`, in the order `00, 01, 10, 11`
(Table 1) or `000, 001, …, 111` (Table 2), with `P_i = 2^{i+3}`. -/
def entries (c : ℕ) : List ℤ :=
  if c = 0 then [14, 1, 15, 16] else
    let p := P (layerOf c)
    match posOf c with
    | 1 => [p, 1, p + 1, 2 * p, 0, 1, p + 1, p]
    | 2 => [2, 0, 0, 14, 2, 12, 12, 14]
    | 3 => [p + 9, p + 8, 0, p + 6, p, 0, p + 2, p + 3]
    | _ => [13, 0, 0, 0, 0, 0, 0, 1]

/-- The (3,2,2)-MCA instance `I_n` of Section 3 (p. 8, Tables 1–2): `6n + 2` variables and the
`4n + 1` constraints `C_0` and `C_{i,k}`, `i ∈ [n]`, `k ∈ [4]`. -/
def inst (n : ℕ) : MCAInstance where
  N := 6 * n + 2
  m := 4 * n + 1
  scope c := scope n c.val
  table c a := (entries c.val).getD (rowIdx (List.ofFn a)) 0

/-- The flip sequence `S_i` of Lemma 6 (p. 9), as a sequence of variables of `I_n`:
`S_0 = (v_{0,1}, v_{0,6})` and
`S_i = (v_{i,1}, S_{i-1}, v_{i,2}, v_{i,3}, S_{i-1}, v_{i,4}, v_{i,5}, v_{i,6})` for `i ≥ 1`. -/
def S (n : ℕ) : ℕ → List (Fin (6 * n + 2))
  | 0 => [v n 0 1, v n 0 6]
  | i + 1 => [v n (i + 1) 1] ++ S n i ++ [v n (i + 1) 2, v n (i + 1) 3] ++ S n i ++
      [v n (i + 1) 4, v n (i + 1) 5, v n (i + 1) 6]

/-- The all-zero initial assignment of `I_n` (p. 9). -/
def σ₀ (n : ℕ) : Fin (6 * n + 2) → Bool := fun _ => false

end TwoOptAllExp.TSP.Supplement.MCA322


