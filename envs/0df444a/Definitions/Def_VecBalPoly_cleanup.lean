-- Prove2me | Definitions.Def_VecBalPoly_cleanup
-- name    : VecBalPoly_cleanup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:12:03.628199+00:00
-- url     : https://prove2.me/theorems/4b1ef3b1-6032-4bc6-83ae-1133066f18a8
-- title:
--   Cleanup and the initial state of Algorithm 2.2
-- statement:
--   **Cleanup** transforms a state in three stages:
--   1. *Freezing.* Every $j\in V$ with $|x_j|=1$ has its retained contributions $a_{ij}x_j$ added to $c_i$ and is removed from every $T_i$ and then from $V$.
--   2. *Dominant-entry removal.* In each row, while some retained $j$ has $a_{ij}^2>q_i/K$, the least such $j$ is removed: $c_i\leftarrow c_i+a_{ij}x_j$, $T_i\leftarrow T_i\setminus\{j\}$, and $q_i$ is recomputed.
--   3. *Scales.* For a row that is medium afterwards, let $a_i^*=\max_{j\in T_i}|a_{ij}|$ and let $r=a_i^*2^k$ with $k\ge0$ least such that $r^2\ge q_i$. If the row has just become medium (it was large before, or this is the initial cleanup), $r_i\leftarrow\min\{K,r\}$; otherwise $r_i\leftarrow\min\{r_i,r\}$.
--
--   The **initial state** has $x=0$, $V=[n]$, $c_i=0$ and $T_i=\{j:a_{ij}\ne0\}$.
--
--   **Formalization Note** The paper removes dominant entries in lexicographic order of $(i,j)$. A removal changes only its own row's $q_i$, so processing each row with the least $j$ first gives the same result. Removal in a row is iterated $n$ times, which exhausts it.
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), (2.1)–(2.2), p.4 (PDF p.5); §2.4, p.5 (PDF p.6); Algorithm 2.2, p.6

import Mathlib
import Definitions.Def_VecBalPoly_q

namespace VecBalPoly

open Classical

variable {m n : ℕ}

/-- One dominant-entry removal in row `i` (2.1)–(2.2): if some retained `j ∈ T` has
`a²ᵢⱼ > q/K` (with `q = ∑_{j∈T} a²ᵢⱼ`), remove the least such `j` from `T`, add `aᵢⱼxⱼ` to the
offset, and record `j` as removed by the dominant rule; otherwise do nothing. The triple is
`(Tᵢ, cᵢ, Domᵢ)`. -/
noncomputable def domRound (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m)
    (s : Finset (Fin n) × ℝ × Finset (Fin n)) : Finset (Fin n) × ℝ × Finset (Fin n) :=
  if h : (s.1.filter (fun j => (∑ k ∈ s.1, A i k ^ 2) / K < A i j ^ 2)).Nonempty then
    let j := (s.1.filter (fun j => (∑ k ∈ s.1, A i k ^ 2) / K < A i j ^ 2)).min' h
    (s.1.erase j, s.2.1 + A i j * x j, insert j s.2.2)
  else s

/-- Dominant-entry removal in row `i` until no entry qualifies: `n` rounds of `domRound` (each
round removes one entry or none, and `Tᵢ` has at most `n` entries). -/
noncomputable def domRemove (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin m)
    (s : Finset (Fin n) × ℝ × Finset (Fin n)) : Finset (Fin n) × ℝ × Finset (Fin n) :=
  (domRound A x i)^[n] s

/-- The scale candidate of row `i` with retained set `T`: start from `a⋆ = max_{j∈T} |aᵢⱼ|` and
double until `r² ≥ q`, i.e. `a⋆ · 2^k` with `k` the least natural number with
`q ≤ (a⋆2^k)²`. -/
noncomputable def scaleCand (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (T : Finset (Fin n)) : ℝ :=
  let astar := if hT : T.Nonempty then T.sup' hT (fun j => |A i j|) else 0
  if hk : ∃ k : ℕ, (∑ j ∈ T, A i j ^ 2) ≤ (astar * 2 ^ k) ^ 2 then astar * 2 ^ Nat.find hk
  else 0

/-- The scale update of row `i` with new retained set `T`, given the state `st` before cleanup:
a row that is medium after cleanup gets `min{K, r}` if it has just become medium (it was large in
`st`, or this is the initial cleanup), and `min{rᵢ, r}` otherwise; every other row keeps its
scale. -/
noncomputable def newScale (A : Matrix (Fin m) (Fin n) ℝ) (init : Bool) (st : St m n)
    (T : Finset (Fin n)) (i : Fin m) : ℝ :=
  if 0 < ∑ j ∈ T, A i j ^ 2 ∧ ∑ j ∈ T, A i j ^ 2 ≤ K ^ 2 then
    (if init = true ∨ IsLarge A st i then min K (scaleCand A i T)
      else min (st.r i) (scaleCand A i T))
  else st.r i

/-- **Cleanup (§2.4).** In order:
1. *freezing*: the coordinates `j ∈ V` with `|xⱼ| = 1` have their retained contributions added
   to `cᵢ`, are removed from every `Tᵢ`, and then from `V`;
2. *dominant-entry removal*: in each row, repeatedly remove the least retained `j` with
   `a²ᵢⱼ > qᵢ/K`, adding `aᵢⱼxⱼ` to `cᵢ` and recomputing `qᵢ`;
3. *reclassification and scales*: every row that is medium afterwards gets the scale of
   `newScale` (newly medium rows `min{K, r}`, others `min{rᵢ, r}`).

`init = true` marks the initial cleanup, at which all medium rows are treated as newly medium.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.1, (2.1)–(2.2), p.4 (PDF p.5); §2.4, p.5 (PDF p.6); Algorithm 2.2, p.6.

**Formalization Note** The paper removes dominant entries in lexicographic order of `(i, j)`.
A removal in row `i` changes only `qᵢ`, so the rows are independent and processing each row with
least `j` first gives the same result. Freezing a coordinate `j` with `|xⱼ| ≥ 1` is the same as
`|xⱼ| = 1` on the algorithm's states, which stay in the cube. -/
noncomputable def cleanup (A : Matrix (Fin m) (Fin n) ℝ) (init : Bool) (st : St m n) : St m n :=
  let Fz := st.V.filter (fun j => ¬ |st.x j| < 1)
  let R := fun i => domRemove A st.x i
    (st.T i \ Fz, st.c i + ∑ j ∈ st.T i ∩ Fz, A i j * st.x j, st.Dom i)
  { x := st.x
    V := st.V \ Fz
    T := fun i => (R i).1
    c := fun i => (R i).2.1
    r := fun i => newScale A init st (R i).1 i
    Dom := fun i => (R i).2.2 }

/-- **The initial state** of Algorithm 2.2: `x = 0`, `V = [n]`, `cᵢ = 0`,
`Tᵢ = {j : aᵢⱼ ≠ 0}`, no entry removed yet; the scales are set by the initial cleanup.
Source: ibid., Algorithm 2.2, p.6 (PDF p.7). -/
noncomputable def initState (A : Matrix (Fin m) (Fin n) ℝ) : St m n :=
  { x := 0
    V := Finset.univ
    T := fun i => Finset.univ.filter (fun j => A i j ≠ 0)
    c := 0
    r := 0
    Dom := fun _ => ∅ }

end VecBalPoly


