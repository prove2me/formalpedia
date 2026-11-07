-- Prove2me | Definitions.Def_AlmostMMS_headCount
-- name    : AlmostMMS_headCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:47:39.798286+00:00
-- url     : https://prove2.me/theorems/5a7d2d24-798e-455d-a936-a8a4d8e09111
-- title:
--   Definition 3.1, p.20 — head threshold $h_i$ and tail value $T_i$
-- statement:
--   For an integer $q>0$ the **head threshold** of agent $i$ is $h_i=|\{e : v_i(e)\ge 1/q\}|$. The **tail value** is
--   $$
--   T_i=\sum_{e>h_i} v_i(e),
--   $$
--   and $\overline T=\frac1n\sum_{i\in N}T_i$ is the average tail value, whose size separates the two cases of the proof.
--
--   **Formalization Note** The item $e_j$ with $j>h_i$ is the position `e` with $h_i\le$ `e.val`.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 3.1, p.20; p.25

import Mathlib

namespace AlmostMMS

open Finset

open Classical in
/-- **Head threshold** `h_i = |{e : v_i(e) ≥ 1/q}|` (Definition 3.1, p.20).
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…). -/
noncomputable def headCount {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ) (i : Fin n) : ℕ :=
  (univ.filter fun e => 1 / (q : ℝ) ≤ v i e).card

/-- **Tail value** `T_i = ∑_{e > h_i} v_i(e)` (Definition 3.1, p.20). The item `e_j` with `j > h_i` is
a position `e` with `h_i ≤ e.val`. -/
noncomputable def tailVal {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ) (i : Fin n) : ℝ :=
  ∑ e with headCount v q i ≤ e.val, v i e

/-- **Average tail value** `T̄ = (1/n) ∑_{i ∈ N} T_i` (p.25). -/
noncomputable def avgTail {n m : ℕ} (v : Fin n → Fin m → ℝ) (q : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, tailVal v q i

end AlmostMMS


