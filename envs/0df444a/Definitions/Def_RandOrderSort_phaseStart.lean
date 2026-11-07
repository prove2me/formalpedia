-- Prove2me | Definitions.Def_RandOrderSort_phaseStart
-- name    : RandOrderSort_phaseStart
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:07.824596+00:00
-- url     : https://prove2.me/theorems/06c8ba6b-fbd9-41a9-a1e0-ad420635bb58
-- title:
--   The integer schedule of EmpiricalSort, displays (8)–(15)
-- statement:
--   With $T=512$ and $n\ge 16T$, the growing phases are indexed by $j=0,\dots,J$, where
--   $$t_j=T2^j,\qquad J=\max\{j\ge 0:t_j\le n/8\},\qquad L=J+1,\qquad m=2t_J=t_L,\qquad N=n-m.$$
--   The shrinking phases are indexed by $i=1,\dots,k$, where
--   $$k=\lfloor\log_2 N\rfloor-7,\qquad b_i=2^{k-i},\qquad \lambda=\frac{4N}{3\cdot 2^k},\qquad B=\lfloor\lambda\rfloor-3,$$
--   $$S_0=0,\quad S_k=N,\quad S_i=\Bigl\lfloor N-\frac{2N}{3\cdot 2^i}\Bigr\rfloor\ (1\le i<k),\qquad M_1=S_1,\quad M_i=(S_i-S_{i-1})+\lceil M_{i-1}/4\rceil\ (2\le i\le k),$$
--   with phase lengths $n_i=\lfloor 3M_i/4\rfloor$ for $i<k$ and $n_k=M_k$, and balanced bucket capacities (the first $M_i\bmod b_i$ buckets get one cell more).
--
--   The module also numbers all phases by one index $p$ ($p=j$ for a growing phase, $p=L+i-1$ for a shrinking phase) and gives each phase's first arrival, length, leaf count, prefix size, capacities and fresh block. Every quantity is a function of $n$ alone.
--
--   **Formalization Note** Floors and ceilings are taken in $\mathbb Q$ exactly as printed. Natural-number subtraction appears in $N$, $k$, $B$ and $S_i-S_{i-1}$; for $n\ge 8192$ none of them truncates. Arrivals are 0-based: growing phase $j$ places arrivals $t_j,\dots,2t_j-1$, and shrinking phase $i$ places arrivals $m+Q_{i-1},\dots,m+Q_i-1$, with $Q_i=n_1+\dots+n_i$.
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), §§3.2–3.3, pp.13–14, displays (8), (10), (12)–(15); §4.1.1, p.20 (F)

import Mathlib

namespace RandOrderSort

/-! # The integer schedule of EmpiricalSort (§§3.2–3.3, pp.13–14, displays (8)–(15))

Kang, Fan, arXiv:2610.15438 (version of 2026-11-01), §3.2, p.13: "Fix T = 512. For n < 16T = 8192,
place arrivals consecutively and stop. For n ≥ 16T, place the first T arrivals in the first T
cells. Set t_j = T2^j, J = max{j ≥ 0 : t_j ≤ n/8}, L = J + 1. (8)" … "write m = 2t_J = t_L,
N = n − m. (10)" §3.3, pp.13–14: (12) `k = ⌊log₂ N⌋ − 7`, `b_i = 2^{k−i}`, `λ = 4N/(3·2^k)`,
`B = ⌊λ⌋ − 3`; (13) `n_i = ⌊3M_i/4⌋` for a nonfinal phase, `n_k = M_k`; (14) `S_0 = 0`, `S_k = N`,
`S_i = ⌊N − 2N/(3·2^i)⌋` (`1 ≤ i < k`); `M_1 = S_1`; (15) `M_i = (S_i − S_{i−1}) + ⌈M_{i−1}/4⌉`
(`2 ≤ i ≤ k`); balanced capacities `d_i + 1` for the first `r_i` buckets and `d_i` for the rest,
where `M_i = b_i d_i + r_i`, `0 ≤ r_i < b_i`.

**Formalization Note.**
* Every quantity is a function of `n` alone. They are meaningful for `n ≥ 8192`; for smaller `n`
  the algorithm places consecutively and they are not used.
* Floors and ceilings are taken in `ℚ` exactly as printed (`Nat.floor`, `Nat.ceil`). `ℕ`
  subtraction appears in `N = n − m`, `k = ⌊log₂ N⌋ − 7`, `B = ⌊λ⌋ − 3` and `S_i − S_{i−1}`; for
  `n ≥ 8192` none of them truncates (`m ≤ n/4`, `N ≥ 6144`, `λ ≥ 512/3`, `S` nondecreasing —
  Lemma 3.1).
* Phases are numbered by one index `p`: `p = j` is growing phase `j` (`0 ≤ j ≤ J`) and
  `p = L + i − 1` is shrinking phase `i` (`1 ≤ i ≤ k`). Arrivals are 0-based, so growing phase `j`
  places arrivals `t_j, …, 2t_j − 1` and shrinking phase `i` places arrivals
  `m + Q_{i−1}, …, m + Q_i − 1` with `Q_i = n_1 + ⋯ + n_i`.
-/

/-- `T = 512`. -/
def T : ℕ := 512

/-- `t_j = T 2^j` (8). -/
def tj (j : ℕ) : ℕ := T * 2 ^ j

/-- `J = max{j ≥ 0 : t_j ≤ n/8}` (8) (the maximum exists for `n ≥ 8T`; `t_j > j`, so it is at
most `n`). -/
def J (n : ℕ) : ℕ := Nat.findGreatest (fun j => ((tj j : ℚ) ≤ (n : ℚ) / 8)) n

/-- `L = J + 1`, the number of growing phases (8). -/
def L (n : ℕ) : ℕ := J n + 1

/-- `m = 2t_J = t_L` (10). -/
def m (n : ℕ) : ℕ := 2 * tj (J n)

/-- `N = n − m` (10). -/
def N (n : ℕ) : ℕ := n - m n

/-- `k = ⌊log₂ N⌋ − 7`, the number of shrinking phases (12). -/
def k (n : ℕ) : ℕ := Nat.log 2 (N n) - 7

/-- `b_i = 2^{k−i}`, the bucket count of shrinking phase `i` (12). -/
def b (n i : ℕ) : ℕ := 2 ^ (k n - i)

/-- `λ = 4N/(3·2^k)`, the ideal bucket capacity (12). -/
def lam (n : ℕ) : ℚ := 4 * (N n : ℚ) / (3 * 2 ^ k n)

/-- `B = ⌊λ⌋ − 3` (12). -/
def B (n : ℕ) : ℕ := ⌊lam n⌋₊ - 3

/-- The allocation endpoints `S_i` (14): `S_0 = 0`, `S_k = N`, `S_i = ⌊N − 2N/(3·2^i)⌋` for
`1 ≤ i < k` (and `N` beyond `k`). -/
def S (n i : ℕ) : ℕ :=
  if i = 0 then 0
  else if k n ≤ i then N n
  else ⌊(N n : ℚ) - 2 * (N n : ℚ) / (3 * 2 ^ i)⌋₊

/-- `M_i`, the available empty cells of shrinking phase `i` after its allocation: `M_1 = S_1` and
(15) `M_i = (S_i − S_{i−1}) + ⌈M_{i−1}/4⌉`. -/
def M (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => S n 1
  | (i + 2) => (S n (i + 2) - S n (i + 1)) + ⌈((M n (i + 1) : ℚ) / 4)⌉₊

/-- The length of shrinking phase `i` (13): `n_i = ⌊3M_i/4⌋` if `i < k`, and `n_k = M_k`. -/
def nPh (n i : ℕ) : ℕ := if i < k n then ⌊(3 * (M n i : ℚ)) / 4⌋₊ else M n i

/-- `Q_i = n_1 + ⋯ + n_i` (`Q_0 = 0`), the arrivals placed by the first `i` shrinking phases. -/
def Q (n i : ℕ) : ℕ := ∑ r ∈ Finset.Icc 1 i, nPh n r

/-- The capacity of bucket `ℓ` (0-based, left to right) in shrinking phase `i`: with
`M_i = b_i d_i + r_i`, `0 ≤ r_i < b_i`, the first `r_i` buckets get `d_i + 1` and the rest `d_i`. -/
def shrinkCap (n i ℓ : ℕ) : ℕ :=
  if ℓ < M n i % b n i then M n i / b n i + 1 else M n i / b n i

/-- The number of phases `L + k`. -/
def numPhases (n : ℕ) : ℕ := L n + k n

/-- The first arrival (0-based) of phase `p`: `t_j` for growing phase `j = p`, and `m + Q_{i−1}`
for shrinking phase `i = p − L + 1`. -/
def phaseStart (n p : ℕ) : ℕ := if p < L n then tj p else m n + Q n (p - L n)

/-- The number of arrivals of phase `p`: `t_j` (growing), `n_i` (shrinking). -/
def phaseLen (n p : ℕ) : ℕ := if p < L n then tj p else nPh n (p - L n + 1)

/-- The number of leaves (buckets) of phase `p`: `g_j = t_j/T = 2^j` (growing), `b_i` (shrinking). -/
def phaseLeaves (n p : ℕ) : ℕ := if p < L n then 2 ^ p else b n (p - L n + 1)

/-- The size of the prefix whose keys build the tree of phase `p`: `t_j` (growing), and the fixed
tree's `m` (shrinking; Algorithm 1, line 12). -/
def phasePrefix (n p : ℕ) : ℕ := if p < L n then tj p else m n

/-- The capacity of bucket `ℓ` in phase `p`: `2T` in growing phases (§3.2), the balanced
capacities in shrinking phases (§3.3). -/
def phaseCap (n p ℓ : ℕ) : ℕ := if p < L n then 2 * T else shrinkCap n (p - L n + 1) ℓ

/-- The size of the fresh block appended at the start of phase `p` (Algorithm 1, lines 8 and 15):
`2T` for `j = 0`, `3t_j/2` for growing `j ≥ 1`, `S_1 − t_J` for shrinking `i = 1`, and
`S_i − S_{i−1}` for shrinking `i ≥ 2`. -/
def phaseFresh (n p : ℕ) : ℕ :=
  if p = 0 then 2 * T
  else if p < L n then 3 * tj p / 2
  else if p = L n then S n 1 - tj (J n)
  else S n (p - L n + 1) - S n (p - L n)

/-- `F`, the number of nonempty fresh allocations after the initial block (§4.1.1, p.20). -/
def F (n : ℕ) : ℕ := ((Finset.range (numPhases n)).filter (fun p => 0 < phaseFresh n p)).card

/-- The phase of arrival `t ≥ T` (for `n ≥ 8192`): the last phase that has started by time `t`. -/
def phaseOf (n t : ℕ) : ℕ :=
  ((Finset.range (numPhases n)).filter (fun p => phaseStart n p ≤ t)).card - 1

end RandOrderSort


