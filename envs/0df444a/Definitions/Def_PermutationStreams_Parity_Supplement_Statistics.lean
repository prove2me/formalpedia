-- Prove2me | Definitions.Def_PermutationStreams_Parity_Supplement_Statistics
-- name    : PermutationStreams_Parity_Supplement_Statistics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:12.661057+00:00
-- url     : https://prove2.me/theorems/e7e8300a-7656-48b0-8988-aa4c4d4b0e1c
-- title:
--   The permutation statistics $T$, $Q$, $W$, $M_i$, $E_{312}$, decreasing runs and $U$
-- statement:
--   For a permutation $\pi=\pi_1\cdots\pi_n$ of $[n]$ and integers $d,n\ge 0$:
--
--   1. $T(d)=d(d+1)/2$ and $Q(n)=\sum_{v=1}^n v^2$.
--   2. The **weighted inversion number** $W(\pi)=\sum_{i<j,\ \pi_i>\pi_j}(\pi_i-\pi_j)$.
--   3. The **prefix maximum** $M_i=\max\{\pi_1,\dots,\pi_i\}$, and
--   $$
--   E_{312}(\pi)=\sum_{i=1}^n T(M_i-\pi_i)-W(\pi).
--   $$
--   4. The **maximal contiguous decreasing runs** $R_1,\dots,R_k$ of $\pi$ (a new run starts at position $i+1$ exactly when $\pi_i<\pi_{i+1}$); the **bottom** $b_r$ of $R_r$ is its last, hence smallest, value, and $b(h)$ is the bottom of the run containing the value $h$. Then
--   $$
--   U(\pi)=\sum_{r=1}^k\sum_{h\in R_r}T(h-b_r)=\sum_{h=1}^n T(h-b(h)).
--   $$
--
--   These are the integer statistics whose values decide 312- and 231-avoidance in the paper's logarithmic-space algorithms.
--
--   **Formalization Note** All quantities are integers computed in ℤ on the 1-based values $\pi_i=$ `π i + 1`. A run is encoded by its last position: position $j$ is a run end when it is the last position or $\pi_j<\pi_{j+1}$, and the run of position $i$ ends at the first run end $\ge i$.
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §3 p. 5 (T, Q), §5.1 p. 9 (W), §5.2 p. 9 (M_i, E312), §5.3 p. 11 (runs, b_r, b(h), U)

import Mathlib

namespace PermutationStreams.Parity.Supplement

/-! Braverman–Zamir §3 p.5, §5.1 p.9, §5.2 p.9, §5.3 p.11. A permutation `π` of `[n]` is an
`Equiv.Perm (Fin n)`: position `i : Fin n` stands for `i + 1` and the value `π i` for `π i + 1`.
Every statistic below is evaluated on the 1-based values, in `ℤ`. -/

/-- `T(d) = d(d+1)/2` (the division is exact for every integer `d`). -/
def T (d : ℤ) : ℤ := d * (d + 1) / 2

/-- `Q(n) = ∑_{v=1}^n v²`. -/
def Q (n : ℕ) : ℤ := ∑ v ∈ Finset.range n, ((v : ℤ) + 1) ^ 2

/-- The 1-based value `π_i = π i + 1` at the 0-based position `i`. -/
def val {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : ℤ := (π i : ℤ) + 1

/-- The weighted inversion number `W(π) = ∑_{i<j, π_i > π_j} (π_i − π_j)`. -/
def W {n : ℕ} (π : Equiv.Perm (Fin n)) : ℤ :=
  ∑ q ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun q => q.1 < q.2 ∧ π q.2 < π q.1),
    (val π q.1 - val π q.2)

/-- The prefix maximum `M_i = max{π_1, …, π_i}` (1-based values, through position `i`). -/
def prefMax {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : ℤ :=
  (((Finset.univ.filter (fun j : Fin n => j ≤ i)).image (fun j => (π j : ℕ) + 1)).sup id : ℕ)

/-- `E312(π) = ∑_{i=1}^n T(M_i − π_i) − W(π)`, in `ℤ`. -/
def E312 {n : ℕ} (π : Equiv.Perm (Fin n)) : ℤ :=
  (∑ i : Fin n, T (prefMax π i - val π i)) - W π

/-- Position `j` is the last position of its maximal contiguous decreasing run: it is the last
position of `π`, or the next value is larger (a new run starts at `j + 1`). -/
def IsRunEnd {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : Prop :=
  ∀ h : (j : ℕ) + 1 < n, π j < π ⟨(j : ℕ) + 1, h⟩

open Classical in
/-- The last position of the maximal decreasing run containing position `i`: the first run end
at or after `i`. (The last position `n - 1` is a run end, so the set is nonempty.) -/
noncomputable def runEndPos {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  (Finset.univ.filter (fun j : Fin n => i ≤ j ∧ IsRunEnd π j)).min'
    ⟨⟨n - 1, by have := i.isLt; omega⟩, by
      have hi := i.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Fin.le_def.mpr (by simp only; omega), fun h => absurd h (by simp only; omega)⟩⟩

/-- `b(h)` for the value at position `i`: the bottom (last, hence smallest, value) of its run. -/
noncomputable def runBottom {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : ℤ :=
  val π (runEndPos π i)

/-- `U(π) = ∑_r ∑_{h ∈ R_r} T(h − b_r) = ∑_h T(h − b(h))`. -/
noncomputable def U {n : ℕ} (π : Equiv.Perm (Fin n)) : ℤ :=
  ∑ i : Fin n, T (val π i - runBottom π i)

end PermutationStreams.Parity.Supplement


