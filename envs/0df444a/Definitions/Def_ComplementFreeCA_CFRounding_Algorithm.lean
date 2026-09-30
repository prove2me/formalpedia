-- Prove2me | Definitions.Def_ComplementFreeCA_CFRounding_Algorithm
-- name    : ComplementFreeCA_CFRounding_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:13:27.684978+00:00
-- url     : https://prove2.me/theorems/21bef02f-25f3-4650-9a97-f6f487d67fb1
-- title:
--   The complement-free rounding algorithm: item counts, layers, and steps (iii)–(iv)
-- statement:
--   Fix a preallocation $\sigma=(S_1,\dots,S_n)$, i.e. bundles that need not be disjoint.
--
--   1. The **count** of item $j$ is the number of bidders $i$ with $j\in S_i$.
--   2. For $r\ge 1$ the **layer** $S_i^r$ is
--   $$S_i^r=\{\,j\in S_i \mid j \text{ appears in exactly } r-1 \text{ of the sets } S_1,\dots,S_{i-1}\,\}.$$
--   3. The **duplication bound** is $k=\lfloor 3\log m/\log\log m\rfloor$ (natural logarithm).
--   4. **Step (iii).** An index $r$ with $1\le r\le k$ is a *best layer* if it maximizes $\sum_i v_i(S_i^r)$ over $1\le r\le k$.
--   5. **Step (iv).** With $T_i=S_i^r$, a bidder $i_0$ is an *admissible step-(iv) choice* if, whenever some bidder $i$ has $v_i(M)\ge\sum_{i'}v_{i'}(T_{i'})$, the bidder $i_0$ has this property too.
--   6. The **output** of steps (iii)–(iv) for $\sigma$, $r$ and $i_0$: if $v_{i_0}(M)\ge\sum_i v_i(T_i)$, bidder $i_0$ receives all of $M$ and every other bidder receives $\emptyset$; otherwise bidder $i$ receives $T_i$.
--
--   These are the objects of the $O(\log m/\log\log m)$-approximation algorithm for complement-free bidders in Section 3.1 of the paper.
--
--   **Formalization Note** The layer index keeps the paper's 1-based convention; it is used only for $1\le r\le k$ (for $r=0$ the natural-number subtraction $r-1$ would coincide with $r=1$). The paper writes $k=O(\log m/\log\log m)$; the threshold $3\log m/\log\log m$ comes from Lemma 3.1 as used in §3.1.1, and the floor makes "count $>k$" equivalent to "count $>3\log m/\log\log m$". The choices of $r$ in step (iii) and of the bidder in step (iv), which the paper leaves open, are parameters constrained by predicates, so theorems about the output hold for every admissible choice.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 5, §3.1, algorithm steps (i)–(iv); p. 6, Lemma 3.1 (the threshold 3 log m / log log m)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

namespace ComplementFreeCA.CFRounding

/-- The number of bidders `i` whose bundle `σ i` contains item `j`, i.e. how many times `j`
appears in `{Sᵢ}ᵢ`. -/
def count {n m : ℕ} (σ : Fin n → Finset (Fin m)) (j : Fin m) : ℕ :=
  (Finset.univ.filter fun i => j ∈ σ i).card

/-- The layer `Sᵢʳ = {j ∈ Sᵢ | j appears in exactly r − 1 of the sets S₁, …, S_{i−1}}`
of step (ii) of the algorithm (p. 5), with the paper's 1-based index `r` (used for
`1 ≤ r ≤ k`). -/
def layer {n m : ℕ} (σ : Fin n → Finset (Fin m)) (i : Fin n) (r : ℕ) : Finset (Fin m) :=
  (σ i).filter fun j => (Finset.univ.filter fun i' => i' < i ∧ j ∈ σ i').card = r - 1

/-- The duplication bound `k = ⌊3 log m / log log m⌋` (natural logarithm), the threshold of
Lemma 3.1 (p. 6) rounded down to an integer. -/
noncomputable def kOf (m : ℕ) : ℕ :=
  ⌊3 * Real.log m / Real.log (Real.log m)⌋₊

/-- Step (iii) (p. 5): `r` is an index with `1 ≤ r ≤ k` maximizing `∑ᵢ vᵢ(Sᵢʳ)`. -/
def IsBestLayer {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin n → Finset (Fin m))
    (k r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ k ∧
    ∀ r', 1 ≤ r' → r' ≤ k → welfare v (fun i => layer σ i r') ≤ welfare v (fun i => layer σ i r)

/-- Step (iv) (p. 5): the bidder `i₀` chosen when some bidder `i` has
`vᵢ(M) ≥ ∑ᵢ vᵢ(Tᵢ)`; if such a bidder exists, `i₀` is one of them. -/
def IsStepFourChoice {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (T : Fin n → Finset (Fin m))
    (i₀ : Fin n) : Prop :=
  (∃ i, welfare v T ≤ v i Finset.univ) → welfare v T ≤ v i₀ Finset.univ

/-- The allocation output by steps (iii)–(iv) (p. 5) for the preallocation `σ`, the layer
index `r` and the step-(iv) bidder `i₀`: with `Tᵢ = Sᵢʳ`, if `v_{i₀}(M) ≥ ∑ᵢ vᵢ(Tᵢ)` then
`i₀` receives all items and the other bidders nothing, otherwise bidder `i` receives `Tᵢ`. -/
noncomputable def algOutput {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin n → Finset (Fin m)) (r : ℕ)
    (i₀ : Fin n) : Fin n → Finset (Fin m) :=
  open Classical in
  if welfare v (fun i => layer σ i r) ≤ v i₀ Finset.univ then
    fun i => if i = i₀ then Finset.univ else ∅
  else
    fun i => layer σ i r

end ComplementFreeCA.CFRounding


