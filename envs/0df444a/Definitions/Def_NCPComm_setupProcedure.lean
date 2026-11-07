-- Prove2me | Definitions.Def_NCPComm_setupProcedure
-- name    : NCPComm_setupProcedure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:02:55.852328+00:00
-- url     : https://prove2.me/theorems/0e915ca5-6e55-43f9-ab48-2695da11af11
-- title:
--   The setup procedure of Figure 4.9.1, and the parameter regime of Proposition 4.7
-- statement:
--   This is the zero-communication procedure of Figure 4.9.1. Alice holds $a\in\{0,1\}^N$ and Bob holds $b\in\{0,1\}^N$ (the light indicator on the first block $[N]$). The shared randomness is a uniform permutation $\pi$ of $[2N]$.
--
--   1. Bob sets $b'=(\mathbf 1_N-b)\,\|\,\vec 0_N$ and $p$ the indicator of $\{N+1,\dots,N+K\}$, and outputs $p_{\mathrm{heavy}}=\pi(b'+p)$ and $p_{\mathrm{light}}=\vec 1_{2N}-p_{\mathrm{heavy}}$.
--   2. Alice draws a Poissonized sample of mean $s$ from the canonical $D_0([2K])$ over $[2N]$, with heavy and light counts $h_i,\ell_i$. She aborts if $\ell_j>0$ for some $j\ge3$ or if $h_2<|a|$, then sets $h_2\leftarrow h_2-|a|$. She aborts if the histogram does not fit the heavy reserve $\{N+1,\dots,N+K\}$ or the light reserve $\{N+K+1,\dots,2N\}$.
--   3. Otherwise she allocates the multiplicities to the two reserves, plants $a$ as doubletons on the first block, and outputs the result relabelled by $\pi$.
--
--   The module also defines the input size $|a|=\lfloor\frac{s^2}{64K}e^{-s/(4K)}\rfloor$, the gap $g(N,K,s)$ of Proposition 4.7, and the regime of that proposition along sequences: for all large $n$, with $N=3n$, $\sqrt N<K<N$ and $3K<N$, $s\ge C_1\sqrt N$, and $s=o(\min\{K,N/\sqrt K\})$.
--
--   **Formalization Note** Labels are 0-based: the first block is $[0,N)$, the heavy reserve $[N,N+K)$ and the light reserve $[N+K,2N)$. The page lets Alice "choose" pairwise disjoint vectors of the given sizes independently of $\pi$. The definition fixes one such choice, assigning multiplicities in increasing order along the reserve, and the choice affects no law because the output is relabelled by the uniform $\pi$. Abort is the outcome `none`. An allocation is impossible exactly when some cumulative histogram exceeds the reserve size. No fixed exponent $k$ with $K=N^k$ is required by the regime.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Figure 4.9.1, p.23; Proposition 4.7, p.21

import Mathlib
import Definitions.Def_NCPComm_idealSetup
import Definitions.Def_NCPComm_SolvesExactGapDisj

open scoped NNReal ENNReal

namespace NCPComm

/-- `|a| = ⌊(s²/(64K)) e^{-s/(4K)}⌋`: Alice's input size in Proposition 4.7, p.21, and Figure 4.9.1,
p.23 (Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027
submission, manuscript sha256 714c0353…). -/
noncomputable def inputSizeA (K : ℕ) (s : ℝ≥0) : ℕ :=
  ⌊(s : ℝ) ^ 2 / (64 * K) * Real.exp (-(s : ℝ) / (4 * K))⌋₊

/-- `g(N, K, s) := ⌊(s²/4)(e^{-s/(2(2N/3-2K))}/(2(2N/3-2K)) - e^{-s/(2(2N-2K))}/(2(2N-2K))) + 1/2⌋`
(Proposition 4.7, p.21). -/
noncomputable def gapG (N K : ℕ) (s : ℝ≥0) : ℕ :=
  ⌊(s : ℝ) ^ 2 / 4 *
      (Real.exp (-(s : ℝ) / (2 * (2 * (N : ℝ) / 3 - 2 * K))) / (2 * (2 * (N : ℝ) / 3 - 2 * K))
        - Real.exp (-(s : ℝ) / (2 * (2 * (N : ℝ) - 2 * K))) / (2 * (2 * (N : ℝ) - 2 * K)))
      + 1 / 2⌋₊

/-- The cumulative histogram `h_1 + ⋯ + h_i`. -/
def cumHist (h : ℕ → ℕ) (i : ℕ) : ℕ := ∑ t ∈ Finset.Icc 1 i, h t

/-- The allocation rule for steps 3b and 3c of Figure 4.9.1: reserve position `j` receives the
multiplicity `i` with `h_1 + ⋯ + h_{i-1} ≤ j < h_1 + ⋯ + h_i`, and `0` when there is none. Thus
exactly `h_i` positions receive multiplicity `i`.

**Formalization Note** The page lets Alice "choose" pairwise disjoint vectors of the given sizes
independently of `π`. This fixes one such choice. The choice does not affect any law of the
procedure, because the output is relabelled by the uniform `π`. -/
noncomputable def allocMult (h : ℕ → ℕ) (j : ℕ) : ℕ := sInf {i | 1 ≤ i ∧ j < cumHist h i}

/-- Steps 3a to 3d of Figure 4.9.1, p.23, before the relabelling by `π`, on Alice's canonical sample
`o` over `[2N]`: abort (`none`) if some `ℓ_j > 0` with `j ≥ 3`, if `h_2 < |a|`, or if the histogram
after setting `h_2 ← h_2 - |a|` does not fit the heavy reserve (size `K`) or the light reserve (size
`N - K`). Otherwise the count vector is `2` on `a` and `0` elsewhere on the first block `[N]`, and it
follows the allocation rule on the two reserves.

**Formalization Note** Labels are 0-based: the first block is `[0, N)`, the heavy reserve
`{N+1,…,N+K}` is `[N, N+K)` and the light reserve `{N+K+1,…,2N}` is `[N+K, 2N)`. "If this is
impossible" holds exactly when some cumulative histogram exceeds the reserve size. -/
noncomputable def aliceCounts (N K : ℕ) (a : Fin N → Bool) (o : SetupOutcome (2 * N)) :
    Option (Fin (2 * N) → ℕ) :=
  open Classical in
  let h' : ℕ → ℕ := Function.update (heavyCount o) 2 (heavyCount o 2 - weight a)
  let ℓ : ℕ → ℕ := lightCount o
  if (∃ j, 3 ≤ j ∧ 0 < ℓ j) ∨ heavyCount o 2 < weight a ∨ (∃ i, K < cumHist h' i)
      ∨ (∃ i, N - K < cumHist ℓ i) then none
  else some fun x =>
    if hx : x.val < N then (if a ⟨x.val, hx⟩ = true then 2 else 0)
    else if x.val < N + K then allocMult h' (x.val - N)
    else allocMult ℓ (x.val - (N + K))

/-- Alice's output on shared randomness `π`: she draws her own canonical sample, independently of
`π` and of Bob's input, runs `aliceCounts` and relabels by `π`, with `(π(v))(y) = v(π⁻¹(y))`. -/
noncomputable def aliceOutput (N K : ℕ) (s : ℝ≥0) (a : Fin N → Bool)
    (π : Equiv.Perm (Fin (2 * N))) : PMF (Option (Fin (2 * N) → ℕ)) :=
  (canonicalSetup (2 * N) (2 * K) s).map fun o =>
    (aliceCounts N K a o).map fun w => fun y => w (π.symm y)

/-- Bob's vector `b′ + p` of Figure 4.9.1, steps 1 and 2: the complement of `b` on the first block
`[N]` and `1` on the heavy reserve `[N, N+K)`. -/
def bobHeavyBase (N K : ℕ) (b : Fin N → Bool) (x : Fin (2 * N)) : Bool :=
  if hx : x.val < N then !(b ⟨x.val, hx⟩) else decide (x.val < N + K)

/-- Bob's output `p_heavy = π(b′ + p)`. -/
def bobHeavy (N K : ℕ) (b : Fin N → Bool) (π : Equiv.Perm (Fin (2 * N))) : Fin (2 * N) → Bool :=
  fun y => bobHeavyBase N K b (π.symm y)

/-- Bob's output `p_light = 1 - p_heavy`. -/
def bobLight (N K : ℕ) (b : Fin N → Bool) (π : Equiv.Perm (Fin (2 * N))) : Fin (2 * N) → Bool :=
  fun y => !(bobHeavy N K b π y)

/-- The zero-communication setup procedure of Figure 4.9.1, p.23: the shared randomness is a uniform
permutation `π` of `[2N]`, Bob's output reads only `(b, π)`, Alice's reads only `(a, π)` and her own
coins. Abort is the outcome `none`. -/
noncomputable def setupProcedure (N K : ℕ) (s : ℝ≥0) (a b : Fin N → Bool) :
    PMF (Option (SetupOutcome (2 * N))) :=
  (PMF.uniformOfFintype (Equiv.Perm (Fin (2 * N)))).bind fun π =>
    (aliceOutput N K s a π).map fun w? =>
      w?.map fun w => ⟨bobLight N K b π, bobHeavy N K b π, w⟩

/-- The parameters of Proposition 4.7, p.21, along a sequence of source parameters `N = 3n`,
`K = K(n)`, `s = s(n)`: for all large `n`, `√N < K < N` (that is, `log_N K ∈ (1/2, 1)`) and
`3K < N` (the standing assumption of p.19); for all large `n`, `s ≥ C₁√N`; and
`s = o(min{K, N/√K})`.

**Formalization Note** The page writes `K = N^k` with `k ∈ (0.5, 1)`. No fixed `k` is required. -/
def InRegime (C₁ : ℝ) (K : ℕ → ℕ) (s : ℕ → ℝ≥0) : Prop :=
  (∀ᶠ n : ℕ in Filter.atTop, Real.sqrt (3 * n) < K n ∧ (K n : ℝ) < 3 * n ∧ 3 * K n < 3 * n) ∧
  (∀ᶠ n : ℕ in Filter.atTop, C₁ * Real.sqrt (3 * n) ≤ (s n : ℝ)) ∧
  Filter.Tendsto (fun n : ℕ => (s n : ℝ) / min (K n : ℝ) (3 * n / Real.sqrt (K n)))
    Filter.atTop (nhds 0)

end NCPComm


