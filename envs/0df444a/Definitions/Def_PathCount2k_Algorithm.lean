-- Prove2me | Definitions.Def_PathCount2k_Algorithm
-- name    : PathCount2k_Algorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:45:21.237285+00:00
-- url     : https://prove2.me/theorems/1eeaa042-4623-4679-90ab-dfd4f3836f62
-- title:
--   §2.12 — the complete algorithm: capped $\xi$ sampler, median of means, linear-time median, `countPaths`
-- statement:
--   On input a directed graph with $n$ vertices and $m$ arcs, an integer $k\ge1$ and $0<\varepsilon,\delta<1$, the algorithm of §2.12:
--   1. returns $n$ if $k=1$ and $0$ if $k>n$;
--   2. sets $D=k$, $\Gamma=k!\,k^{k-1}$, $R=\lceil216K_k\varepsilon^{-2}\rceil$, $q=2\lceil\log_2(2/\delta)\rceil+1$, $T=Rq\,kn(1+k^2)$ and $J=\lceil\log_4(2(T+1)/\delta)\rceil$;
--   3. for each of $q$ groups runs $R$ trials; each trial draws its $kn(1+k^2)$ scalars from $\xi$ with a rejection sampler on fair bits (four bits per attempt, at most $J$ attempts; an exhausted draw makes the whole run return $0$), runs the dynamic program and adds $Z_0^2$ to $A_j$;
--   4. returns $\hat N=\mathrm{median}(A_1,\dots,A_q)/(R\Gamma)$, the median being selected with $O(q)$ comparisons.
--
--   The random-bit budget is $4TJ$ (Lemma 2.15) when $2\le k\le n$ and $0$ otherwise.
--
--   **Formalization Note** The tape is read left to right; a 4-bit block $u=8b_0+4b_1+2b_2+b_3$ is rejected if $u\ge12$ and otherwise decoded $0$–$5\mapsto0$, $6,7\mapsto1$, $8,9\mapsto-1$, $10\mapsto2$, $11\mapsto-2$. Within a trial the vector coordinates are drawn first (vertex-major), then the matrix entries (position, vertex, row, column). Each draw is charged one operation; its bits are counted by the tape length. The parameters are computed by charged counting, doubling and quadrupling loops. The median is median-of-medians selection.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), §2.12, p.17; Lemma 2.15 and its proof, p.14

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work
import Definitions.Def_PathCount2k_Gaussian
import Definitions.Def_PathCount2k_DP

open CapacitatedAssort.General

namespace PathCount2k

/-! # The complete algorithm of §2.12 as a charged program on a fair-bit tape

Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), …*, STOC 2027 submission
manuscript (Nov 2026), §2.12, p.17, with the bounded sampler of Lemma 2.15, p.14.

**Formalization Note.**
1. *Tape.* Randomness is a tape `t : ℕ → Bool` of fair bits read left to right from a cursor;
   `countPaths` receives `b : Fin L → Bool` with `L = bitBudget n k ε δ` and reads `false` past
   `L` (it never gets there, Lemma 2.15).
2. *Sampler.* One draw of `ξ` (Lemma 2.15's proof, p.14) reads a 4-bit block `b₀b₁b₂b₃` as
   `u = 8b₀ + 4b₁ + 2b₂ + b₃ ∈ {0, …, 15}`, rejects `u ≥ 12`, and decodes `0–5 ↦ 0`, `6, 7 ↦ 1`,
   `8, 9 ↦ −1`, `10 ↦ 2`, `11 ↦ −2`; at most `J` attempts, after which the whole run returns `0`
   (§2.12 step 2: "If any sample exhausts its allowance, immediately return zero").
3. *Draw order.* Trials are processed group by group (`j = 1, …, q`), trial by trial
   (`ℓ = 1, …, R`). Within a trial the `k·n` vector coordinates are drawn first (vertex-major:
   index `v·k + j`), then the `k·n·k²` matrix entries (index `n·k + ((i·n + v)·k + a)·k + b` for
   entry `(a, b)` of `H_{i,v}`), with `D = k`.
4. *Charges.* Each scalar draw is charged one operation regardless of its number of attempts;
   its bits are accounted by the tape length (the paper counts sampling in fair random bits,
   Lemma 2.15). The DP charges are those of `Definitions.Def_PathCount2k_DP`. Accumulating
   `A_j ← A_j + Z₀²` costs 2, initializing `A_j` costs 1, the median selection charges its
   comparisons (`select`), the final `R·Γ` and division cost 2. The parameters are computed by
   charged loops: `R` by a counting loop (`2R + 4`), `⌈log₂(2/δ)⌉` by a doubling loop (`2r + 4`),
   `T` by 6 products, `J` by a quadrupling loop (`2J + 4`), `Γ = k!·k^{k−1}` by `2k + 1` products.
5. *Median.* Linear-time selection (median of medians, groups of 5) on the `q` integers
   `A₁, …, A_q`; "The median can be selected using `O(q)` comparisons" (p.18). -/

/-- The 4-bit block at cursor `pos`, as an integer in `{0, …, 15}`. -/
def block (t : ℕ → Bool) (pos : ℕ) : ℕ :=
  8 * (t pos).toNat + 4 * (t (pos + 1)).toNat + 2 * (t (pos + 2)).toNat + (t (pos + 3)).toNat

/-- The decoding of an accepted block `u ∈ {0, …, 11}` (Lemma 2.15's proof, p.14: "assign six to
zero, two to each of `1, −1`, and one to each of `2, −2`"). -/
def xiDecode (u : ℕ) : ℤ :=
  if u < 6 then 0 else if u < 8 then 1 else if u < 10 then -1 else if u = 10 then 2 else -2

/-- **One capped draw of `ξ`** with at most `J` attempts, from cursor `pos`; returns the value
(`none` if the allowance is exhausted) and the new cursor. -/
def drawXi (t : ℕ → Bool) : ℕ → ℕ → Option ℤ × ℕ
  | 0, pos => (none, pos)
  | J + 1, pos =>
      if block t pos < 12 then (some (xiDecode (block t pos)), pos + 4) else drawXi t J (pos + 4)

/-- `c` consecutive capped draws; `none` as soon as one draw is exhausted. -/
def drawList (t : ℕ → Bool) (J : ℕ) : ℕ → ℕ → Option (List ℤ) × ℕ
  | 0, pos => (some [], pos)
  | c + 1, pos =>
      match drawXi t J pos with
      | (none, p') => (none, p')
      | (some x, p') =>
          match drawList t J c p' with
          | (none, p'') => (none, p'')
          | (some xs, p'') => (some (x :: xs), p'')

/-- The vertex vectors of a trial from its draws (`g_v(j)` is draw `v·k + j`). -/
def vecOf (n k : ℕ) (xs : List ℤ) : Fin n → Fin k → ℤ :=
  fun v j => xs.getD (v.val * k + j.val) 0

/-- The matrices of a trial from its draws, `D = k` (entry `(a, b)` of `H_{i,v}` is draw
`n·k + ((i·n + v)·k + a)·k + b`). -/
def matOf (n k : ℕ) (xs : List ℤ) : Fin k → Fin n → Fin k → Fin k → ℤ :=
  fun i v a b => xs.getD (n * k + ((i.val * n + v.val) * k + a.val) * k + b.val) 0

/-- **Selection** of the `i`-th smallest element (0-based) of a list of integers by the
median-of-medians algorithm (groups of five, three-way partition around the median of the group
medians), with a recursion budget `fuel`. Every comparison is charged: `10` per group of at most
five (sorting it), `2` per element per partition. -/
def select : ℕ → List ℤ → ℕ → Work ℤ
  | 0, _, _ => pure 0
  | fuel + 1, xs, i =>
      if xs.length ≤ 5 then do
        charge 10
        return (xs.insertionSort (· ≤ ·)).getD i 0
      else do
        let groups := xs.toChunks 5
        charge (10 * groups.length)
        let meds := groups.map fun gr => (gr.insertionSort (· ≤ ·)).getD (gr.length / 2) 0
        let piv ← select fuel meds (meds.length / 2)
        charge (2 * xs.length)
        let lo := xs.filter (· < piv)
        let eq := xs.filter (· = piv)
        let hi := xs.filter (piv < ·)
        if i < lo.length then select fuel lo i
        else if i < lo.length + eq.length then return piv
        else select fuel hi (i - lo.length - eq.length)

/-- The median (the `(⌊q/2⌋ + 1)`-th smallest) of a list of `q` integers, by `select` with budget
`q + 1` (every recursive call is on a strictly shorter list). -/
def selectMedian (xs : List ℤ) : Work ℤ := select (xs.length + 1) xs (xs.length / 2)

/-- **Steps 3–4 of §2.12** for given `R`, `q`, `J`, `Γ`, with `D = k` (p.17): "For each `j ∈ [q]`,
initialize `A_j = 0` and perform `R` independent trials. In each trial, generate the vectors and
matrices of Definition 2.16 using the bounded sampler. Run the dynamic program of Section 2.10,
and retain its integer `Z_{0,j,ℓ} = z b₀` … Update `A_j ← A_j + Z²_{0,j,ℓ}`." Then "Select the
median of `A₁, …, A_q` and return the exact rational number `N̂ = median(A₁, …, A_q)/(RΓ)`." An
exhausted draw returns `0` at once. Returns the output and the final cursor (bits read). -/
noncomputable def amplify (n k : ℕ) (A : List (Fin n × Fin n)) (R q J Γ : ℕ) (t : ℕ → Bool) :
    Work (ℝ × ℕ) := do
  let mut pos := 0
  let mut sums : List ℤ := []
  for _j in List.range q do
    charge 1
    let mut acc : ℤ := 0
    for _l in List.range R do
      let res := drawList t J (k * n * (1 + k ^ 2)) pos
      charge (k * n * (1 + k ^ 2))
      pos := res.2
      match res.1 with
      | none => return (0, pos)
      | some xs =>
          let z ← dp n k k A (vecOf n k xs) (matOf n k xs)
          charge 2
          acc := acc + z * z
    sums := acc :: sums
  let med ← selectMedian sums
  charge 2
  return ((med : ℝ) / ((R : ℝ) * (Γ : ℝ)), pos)

/-- `R = ⌈216 K_k ε⁻²⌉`, §2.12 step 2, p.17. -/
noncomputable def paramR (k : ℕ) (ε : ℝ) : ℕ := ⌈216 * Kk k / ε ^ 2⌉₊

/-- `⌈log₂(2/δ)⌉`, so that `q = 2⌈log₂(2/δ)⌉ + 1`, §2.12 step 2, p.17. -/
noncomputable def paramr (δ : ℝ) : ℕ := ⌈Real.logb 2 (2 / δ)⌉₊

/-- `q = 2⌈log₂(2/δ)⌉ + 1`, §2.12 step 2, p.17. -/
noncomputable def paramq (δ : ℝ) : ℕ := 2 * paramr δ + 1

/-- `T = Rq·kn(1 + k²)`, the number of scalar samples, §2.12 step 2, p.17. -/
noncomputable def paramT (n k : ℕ) (ε δ : ℝ) : ℕ := paramR k ε * paramq δ * k * n * (1 + k ^ 2)

/-- `J = ⌈log₄(2(T + 1)/δ)⌉`, the attempts per sample, §2.12 step 2, p.17. -/
noncomputable def paramJ (n k : ℕ) (ε δ : ℝ) : ℕ :=
  ⌈Real.logb 4 (2 * ((paramT n k ε δ : ℝ) + 1) / δ)⌉₊

/-- `Γ = k!·k^{k−1}`, §2.12 step 2, p.17. -/
def Gamma (k : ℕ) : ℕ := Nat.factorial k * k ^ (k - 1)

/-- **The random-bit budget** `4TJ` of Lemma 2.15 (p.14) when `2 ≤ k ≤ n`, and `0` in the trivial
cases of §2.12 step 1. -/
noncomputable def bitBudget (n k : ℕ) (ε δ : ℝ) : ℕ :=
  if 2 ≤ k ∧ k ≤ n then 4 * paramT n k ε δ * paramJ n k ε δ else 0

/-- **The algorithm of §2.12** (p.17) on input `G = (Fin n, A)` given by its arc list `A`, an
integer `k ≥ 1` and `0 < ε, δ < 1`, with fair-bit tape `b` of length `bitBudget n k ε δ`.
1. "Handle the trivial cases. If `k = 1`, return `n`. If `k > n`, return zero."
2. "Choose the parameters. Set `D = k` and `Γ = k! k^{k−1}`, and let `R = ⌈216 K_k ε⁻²⌉` and
   `q = 2⌈log₂(2/δ)⌉ + 1`. … `T = Rq kn(1 + k²)`. … allow at most `J = ⌈log₄(2(T+1)/δ)⌉` attempts".
3–4. `amplify` (groups, trials, DP, median, division).

The output is `((countPaths n A k ε δ b).run 0).1` and the operation count is
`((countPaths n A k ε δ b).run 0).2`. -/
noncomputable def countPaths (n : ℕ) (A : List (Fin n × Fin n)) (k : ℕ) (ε δ : ℝ)
    (b : Fin (bitBudget n k ε δ) → Bool) : Work ℝ := do
  charge 1
  if k = 1 then return (n : ℝ)
  charge 1
  if n < k then return 0
  let R := paramR k ε
  charge (2 * R + 4)
  let r := paramr δ
  charge (2 * r + 4)
  let q := 2 * r + 1
  charge 6
  let J := paramJ n k ε δ
  charge (2 * J + 4)
  let Γ := Gamma k
  charge (2 * k + 1)
  let t : ℕ → Bool := fun i => if h : i < bitBudget n k ε δ then b ⟨i, h⟩ else false
  let res ← amplify n k A R q J Γ t
  return res.1

end PathCount2k


