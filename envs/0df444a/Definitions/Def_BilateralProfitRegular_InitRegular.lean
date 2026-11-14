-- Prove2me | Definitions.Def_BilateralProfitRegular_InitRegular
-- name    : BilateralProfitRegular_InitRegular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-13T19:19:51.435694+00:00
-- url     : https://prove2.me/theorems/65ef81a8-3c33-4427-a0e6-99152e263a3c
-- title:
--   Algorithm 7 (Initialize regular), with Algorithm 4 (Initialize mhr) as its step 1
-- statement:
--   **Algorithm 4 (Initialize mhr).** The set $\{0,\dots,K\}$ is bisected recursively. For each interval $I$ with midpoint $k_I=\lfloor(\min I+\max I)/2\rfloor$, the algorithm samples the pairs
--   $$S_I=\{(r,k_I):r\in I,\ k_I\ge r\}\cup\{(k_I,r):r\in I,\ k_I<r\},$$
--   and $S$ is the union of the $S_I$. For $\delta=1,1/2,1/4,\dots$ with $\delta\ge1/K$, it posts each $(i/K,j/K)$ with $(i,j)\in S$ for $N=\lceil2^{16}\log(2T)/\delta\rceil$ fresh rounds and records the trade frequencies $\bar P_{ij}$. For $1\le i<j\le K-1$ it estimates
--   $$\hat\mu(i/K,j/K)=\frac{j-i}{K}\cdot\frac{\bar P_{ik}\bar P_{kj}}{\max\{\bar P_{ik},\bar P_{kj},\bar P_{kk}\}},\qquad 0/0=0,$$
--   where $k$ is the midpoint of the first split separating $i$ and $j$, and $\hat\mu=0$ elsewhere. It returns the first $\delta$ with $\max\hat\mu\ge3\delta/2$, or "no trigger".
--
--   **Algorithm 7 (Initialize regular),** with $K=\lceil1/\eta\rceil$, runs in seven steps:
--
--   1. Run Algorithm 4. Return "no trigger" if it does, or if $\delta<2^{16}/K$.
--   2. Post each pair of $S$ for $n=\lceil2^{38}\log(2T)/\delta\rceil$ new rounds. Reconstruct $\widehat P$ by (48), with $\widehat P(i/K,i/K)=\bar P_{ii}$ and zero when $i=0$ or $j=K$.
--   3. Set $\hat\mu=(q-p)\widehat P$ and $\hat\mu^\star_K=\max_{\mathcal A}\hat\mu$. Retain the pairs with $\hat\mu\ge(1-2^{-13})\hat\mu^\star_K$.
--   4. Group the retained pairs in a fixed order. A pair $x=(p,q)$ joins a root $w=(u,v)$ if both crosses $(p,v),(u,q)$ lie in $\mathcal T$, have $\hat\mu\ge0.99\hat\mu^\star_K$, and satisfy $|\tfrac12\log(\widehat P(p,v)/\widehat P(u,q))|\le0.01$. Otherwise it starts a new group.
--   5. Take the convex hull of each group.
--   6. Divide $[-D,D]$, with $D=\operatorname{artanh}(1/\sqrt{2000})$, into the fewest equal intervals of length at most $\tfrac12\sqrt{\eta/\delta}$.
--   7. Return $\delta$ and one candidate $(\mathcal K_i,w_i,\theta_i,\widehat P(w_i))$ per (hull, endpoint).
--
--   The definition also gives the full run's regret $\sum_t(\mu^\star-\mu(a_t))$ and the law of the trade bits.
--
--   **Formalization Note**
--   - *Randomness.* The full execution, run to completion, is driven by i.i.d. uniforms indexed by (stage, pair, round). A round at $e$ trades iff its uniform is below $P(e/K)$.
--   - *Bisection (reading).* $I=\{m,\dots,M\}$ splits into $\{m,\dots,k_I\}$ and $\{k_I+1,\dots,M\}$, so the separating midpoint $k$ satisfies $i\le k<j$.
--   - *Grouping.* The order of step 4 is a parameter, a duplicate-free list of all of $\mathcal A$. A pair joins the earliest created root that passes all tests.
--   - *Conventions.* $\widehat P=0$ for $i>j$, where it is never used before the $\mathcal T$ test. Logarithms are natural.
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Algorithm 4, p.31 (PDF 33); Algorithm 7, p.40 (PDF 42)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Auxiliary

namespace BilateralProfitRegular

open MeasureTheory Classical

/-! # Algorithm 7 (Initialize regular), with Algorithm 4 (Initialize mhr) as its step 1

Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…): Algorithm 4, p.31
(PDF 33); Algorithm 7, p.40 (PDF 42). Both post fixed price pairs `(i/K, j/K)` of the grid for a
prescribed number of fresh rounds and use only the empirical trade frequencies, so the full
execution ("running until it is finished, without stopping at `T`", Lemma 6.4) is a function of
the trade bits.

**Formalization Note.**
* Randomness: an i.i.d. family `U` of uniforms on `[0, 1]` indexed by
  `(stage, (i, j), m)`, where stage `some h` is scale `δ = 2^{-h}` of Algorithm 4 and stage
  `none` is step 2 of Algorithm 7; the `m`-th round at pair `(i, j)` in that stage trades iff
  `U < P(i/K, j/K)`, which is a fresh Bernoulli(`P(i/K, j/K)`) trade bit. Only the bits enter the
  algorithm (`prob` is the trade-probability function; the algorithm reads it only through
  these bits).
* Bisection (Algorithm 4, reading): an interval `I = {m, …, M}` with `m < M` is split into
  `{m, …, k_I}` and `{k_I + 1, …, M}`, `k_I = ⌊(m + M)/2⌋`; the "midpoint of the first recursive
  split separating `i` and `j`" is `k_I` of the deepest interval containing both, so
  `i ≤ k_I < j`. The recursion depth is bounded by a fuel `K + 1`, which is never exhausted.
* `0/0 = 0` in (48) is Lean's division by zero. `P̂(i/K, j/K) = 0` also for `i > j` (pairs outside
  `𝒯`, which the paper does not define and which the algorithm uses only after checking
  membership in `𝒯`).
* `µ̂⋆_K` is the maximum of `µ̂ ≥ 0` over `𝒜 = G_K ∩ 𝒯`, computed as a fold of `max` from `0`
  (`µ̂(0, 0) = 0`).
* Step 4, "a fixed order": the order is a parameter `ord`, a duplicate-free list of all index
  pairs of `𝒜`; the lemmas are stated for every such order. A retained pair joins the
  **earliest created** root that passes all tests (reading: the paper does not say which root
  when several pass).
* Step 6: `D = artanh(1/√2000)`; the fewest equal intervals of length `≤ ½√(η/δ)` covering
  `[−D, D]` number `m = ⌈2D / (½√(η/δ))⌉`, with endpoints `−D + k·2D/m`, `k = 0, …, m`.
* `K = ⌈1/η⌉`. Logarithms are natural; `2^16`, `2^38`, `2^{-13}` are powers of two. -/

/-- The intervals `(min I, max I)` of the recursive bisection of `{m, …, M}` (fuel `f`). -/
def bisect : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | 0, m, M => [(m, M)]
  | f + 1, m, M =>
    if m < M then (m, M) :: (bisect f m ((m + M) / 2) ++ bisect f ((m + M) / 2 + 1) M)
    else [(m, M)]

/-- `S_I = {(r, k_I) : r ∈ I, k_I ≥ r} ∪ {(k_I, r) : r ∈ I, k_I < r}`. -/
def sampledPairs (I : ℕ × ℕ) : List (ℕ × ℕ) :=
  ((List.range (I.2 + 1)).filter fun r => I.1 ≤ r).map fun r =>
    if r ≤ (I.1 + I.2) / 2 then (r, (I.1 + I.2) / 2) else ((I.1 + I.2) / 2, r)

/-- The sampled index set `S = ⋃_I S_I` of Algorithm 4 for the bisection of `{0, …, K}`. -/
def sampleSet (K : ℕ) : Finset (ℕ × ℕ) :=
  ((bisect (K + 1) 0 K).flatMap sampledPairs).toFinset

/-- The midpoint `k` of the first recursive split of `{m, …, M}` separating `i < j` (fuel `f`). -/
def sepMid : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, m, M, _, _ => (m + M) / 2
  | f + 1, m, M, i, j =>
    if j ≤ (m + M) / 2 then sepMid f m ((m + M) / 2) i j
    else if (m + M) / 2 < i then sepMid f ((m + M) / 2 + 1) M i j
    else (m + M) / 2

/-- The reconstruction `P̄_ik P̄_kj / max{P̄_ik, P̄_kj, P̄_kk}` (Algorithm 4; eq. (48)) from the
frequencies `Fr`, `k` the separating midpoint. -/
noncomputable def recon (K : ℕ) (Fr : ℕ × ℕ → ℝ) (i j : ℕ) : ℝ :=
  Fr (i, sepMid (K + 1) 0 K i j) * Fr (sepMid (K + 1) 0 K i j, j) /
    max (Fr (i, sepMid (K + 1) 0 K i j))
      (max (Fr (sepMid (K + 1) 0 K i j, j)) (Fr (sepMid (K + 1) 0 K i j, sepMid (K + 1) 0 K i j)))

/-- The grid point `(i/K, j/K)`. -/
noncomputable def gpt (K : ℕ) (e : ℕ × ℕ) : ℝ × ℝ := ((e.1 : ℝ) / K, (e.2 : ℝ) / K)

/-- The index pairs of `𝒜 = G_K ∩ 𝒯`: `0 ≤ i ≤ j ≤ K`. -/
def actList (K : ℕ) : List (ℕ × ℕ) :=
  ((List.range (K + 1)).product (List.range (K + 1))).filter fun e => e.1 ≤ e.2

/-- A processing order for step 4: a duplicate-free list of exactly the index pairs of `𝒜`. -/
def IsOrder (K : ℕ) (ord : List (ℕ × ℕ)) : Prop :=
  ord.Nodup ∧ ∀ e, e ∈ ord ↔ e.1 ≤ e.2 ∧ e.2 ≤ K

/-- The empirical trade frequency of the first `N` rounds at pair `e` in stage `s`. -/
noncomputable def freq (K : ℕ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (s : Option ℕ) (N : ℕ) (e : ℕ × ℕ) : ℝ :=
  (∑ m ∈ Finset.range N, if ((U (s, e, m)) : ℝ) < prob (gpt K e) then (1 : ℝ) else 0) / N

/-- The scale `δ_h = 2^{-h}` of Algorithm 4. -/
noncomputable def scale (h : ℕ) : ℝ := (1 / 2 : ℝ) ^ h

/-- The number of rounds per sampled pair at scale `δ_h` in Algorithm 4:
`N = ⌈2^16 log(2T)/δ_h⌉`. -/
noncomputable def mhrRounds (T h : ℕ) : ℕ := ⌈(2 : ℝ) ^ 16 * Real.log (2 * T) / scale h⌉₊

/-- Algorithm 4's estimate `µ̂(i/K, j/K)` at scale `δ_h`: `(j − i)/K · recon` for
`1 ≤ i < j ≤ K − 1`, and `0` otherwise. -/
noncomputable def mhrEst (T K : ℕ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (h : ℕ) (e : ℕ × ℕ) : ℝ :=
  if 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ K - 1 then
    ((e.2 : ℝ) - e.1) / K * recon K (freq K prob U (some h) (mhrRounds T h)) e.1 e.2
  else 0

/-- Algorithm 4 triggers at scale `δ_h` (tested only when `δ_h ≥ 1/K`):
`max_{e ∈ G_K} µ̂(e) ≥ 3δ_h/2`. -/
def mhrTriggers (T K : ℕ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (h : ℕ) : Prop :=
  (2 : ℕ) ^ h ≤ K ∧ ∃ e ∈ actList K, 3 * scale h / 2 ≤ mhrEst T K prob U h e

/-- The index `h` of the scale at which Algorithm 4 returns (`none`: "no trigger"). -/
noncomputable def mhrScale (T K : ℕ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : Option ℕ :=
  (List.range (K + 1)).find? fun h => decide (mhrTriggers T K prob U h)

/-- The grid resolution `K = ⌈1/η⌉`. -/
noncomputable def gridK (η : ℝ) : ℕ := ⌈1 / η⌉₊

/-- Step 2's number of rounds per sampled pair, `n = ⌈2^38 log(2T)/δ⌉`. -/
noncomputable def step2Rounds (T : ℕ) (δ : ℝ) : ℕ := ⌈(2 : ℝ) ^ 38 * Real.log (2 * T) / δ⌉₊

/-- Step 2's estimate `P̂(i/K, j/K)` (eq. (48) for `1 ≤ i < j ≤ K − 1`; `P̄_ii` on the diagonal
`1 ≤ i ≤ K − 1`; `0` otherwise). -/
noncomputable def phat (T K : ℕ) (δ : ℝ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (e : ℕ × ℕ) : ℝ :=
  if 1 ≤ e.1 ∧ e.1 < e.2 ∧ e.2 ≤ K - 1 then
    recon K (freq K prob U none (step2Rounds T δ)) e.1 e.2
  else if e.1 = e.2 ∧ 1 ≤ e.1 ∧ e.1 ≤ K - 1 then freq K prob U none (step2Rounds T δ) e
  else 0

/-- Step 3's estimate `µ̂(p, q) = (q − p) P̂(p, q)` at a grid index. -/
noncomputable def muhat (T K : ℕ) (δ : ℝ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (e : ℕ × ℕ) : ℝ :=
  ((e.2 : ℝ) - e.1) / K * phat T K δ prob U e

/-- `µ̂⋆_K = max_{e ∈ 𝒜} µ̂(e)`. -/
noncomputable def muhatStar (T K : ℕ) (δ : ℝ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : ℝ :=
  (actList K).foldl (fun acc e => max acc (muhat T K δ prob U e)) 0

/-- Step 4's tests for assigning `x = (p, q)` to the root `w = (u, v)`: both crosses `(p, v)`,
`(u, q)` lie in `𝒯`, have estimated profit at least `0.99 µ̂⋆_K`, and
`|½ log(P̂(p, v)/P̂(u, q))| ≤ 0.01`. -/
def passes (T K : ℕ) (δ : ℝ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (x w : ℕ × ℕ) : Prop :=
  x.1 ≤ w.2 ∧ w.1 ≤ x.2 ∧
  99 / 100 * muhatStar T K δ prob U ≤ muhat T K δ prob U (x.1, w.2) ∧
  99 / 100 * muhatStar T K δ prob U ≤ muhat T K δ prob U (w.1, x.2) ∧
  |1 / 2 * Real.log (phat T K δ prob U (x.1, w.2) / phat T K δ prob U (w.1, x.2))| ≤ 1 / 100

/-- Assign `x` to the earliest created group whose root passes all tests, or open a new group
with root `x`. Groups are `(root, members)`. -/
noncomputable def addToGroups (T K : ℕ) (δ : ℝ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) (x : ℕ × ℕ) :
    List ((ℕ × ℕ) × List (ℕ × ℕ)) → List ((ℕ × ℕ) × List (ℕ × ℕ))
  | [] => [(x, [x])]
  | g :: gs =>
    if passes T K δ prob U x g.1 then (g.1, g.2 ++ [x]) :: gs
    else g :: addToGroups T K δ prob U x gs

/-- Steps 3–4: the groups formed from the retained pairs
`{e ∈ 𝒜 : µ̂(e) ≥ (1 − 2^{-13}) µ̂⋆_K}`, processed in the order `ord`. -/
noncomputable def groups (T K : ℕ) (δ : ℝ) (ord : List (ℕ × ℕ)) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : List ((ℕ × ℕ) × List (ℕ × ℕ)) :=
  (ord.filter fun e =>
      decide ((1 - (2 : ℝ) ^ (-13 : ℤ)) * muhatStar T K δ prob U ≤ muhat T K δ prob U e)).foldl
    (fun gs x => addToGroups T K δ prob U x gs) []

/-- Step 6: the half-width `D = artanh(1/√2000)`. -/
noncomputable def offsetRange : ℝ := Real.artanh (1 / Real.sqrt 2000)

/-- Step 6: the number `m` of intervals. -/
noncomputable def numIntervals (η δ : ℝ) : ℕ :=
  ⌈2 * offsetRange / (1 / 2 * Real.sqrt (η / δ))⌉₊

/-- Step 6: the offsets `θ_k = −D + k·2D/m`, `k = 0, …, m`. -/
noncomputable def offsets (η δ : ℝ) : List ℝ :=
  (List.range (numIntervals η δ + 1)).map fun k =>
    -offsetRange + k * (2 * offsetRange / numIntervals η δ)

/-- Steps 2–7 at the scale `δ` returned by step 1: the candidate list
`(𝒦_i, w_i, θ_i, P̂(w_i))`, one per (group hull, offset). -/
noncomputable def candidates (T : ℕ) (η δ : ℝ) (ord : List (ℕ × ℕ)) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : List Candidate :=
  (groups T (gridK η) δ ord prob U).flatMap fun g =>
    (offsets η δ).map fun θ =>
      { region := convexHull ℝ {y | ∃ e ∈ g.2, y = gpt (gridK η) e}
        root := gpt (gridK η) g.1
        offset := θ
        est := phat T (gridK η) δ prob U g.1 }

/-- The output of Algorithm 7 run to completion: `none` ("no trigger") or `some (δ, candidates)`.
Step 1 returns "no trigger" if Algorithm 4 does, or if `δ < 2^16/K`. -/
noncomputable def initRegular (T : ℕ) (η : ℝ) (ord : List (ℕ × ℕ)) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : Option (ℝ × List Candidate) :=
  match mhrScale T (gridK η) prob U with
  | none => none
  | some h =>
    if scale h < (2 : ℝ) ^ 16 / gridK η then none
    else some (scale h, candidates T η (scale h) ord prob U)

/-- The scales tested by Algorithm 4 in the run (`δ_h ≥ 1/K`, up to the trigger). -/
noncomputable def testedScales (T K : ℕ) (prob : ℝ × ℝ → ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : List ℕ :=
  (List.range (K + 1)).filter fun h =>
    decide ((2 : ℕ) ^ h ≤ K ∧ ∀ h' ∈ mhrScale T K prob U, h ≤ h')

/-- The regret `∑_{rounds} (µ⋆ − µ(a_t))` of the full run of Algorithm 7 for the environment
`E`: every tested scale posts each pair of `S` for `N` rounds, and step 2 (run iff step 1 passes
both tests) posts each pair of `S` for `n` rounds. -/
noncomputable def initRegret (E : MechanismDesign.BilateralTrade.Environment) (T : ℕ) (η : ℝ)
    (U : Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) : ℝ :=
  let K := gridK η
  let gapS : ℝ := ∑ e ∈ sampleSet K, (muStar E - mu E (gpt K e))
  (∑ h ∈ (testedScales T K (P E) U).toFinset, (mhrRounds T h : ℝ) * gapS) +
    match mhrScale T K (P E) U with
    | none => 0
    | some h => if scale h < (2 : ℝ) ^ 16 / K then 0 else (step2Rounds T (scale h) : ℝ) * gapS

/-- The law of the uniforms `U` driving Algorithm 7. -/
noncomputable def initCoinLaw : Measure (Option ℕ × (ℕ × ℕ) × ℕ → unitInterval) :=
  Measure.infinitePi fun _ => (volume : Measure unitInterval)

end BilateralProfitRegular


