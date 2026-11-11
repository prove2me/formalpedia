-- Prove2me | Definitions.Def_HuffmanMPC_Main_Subroutines
-- name    : HuffmanMPC_Main_Subroutines
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:26:37.133716+00:00
-- url     : https://prove2.me/theorems/f68973a0-e13b-4eed-83a1-4fbd47963d22
-- title:
--   Problems 4.4 and 3.2, Bounded-Ratio Huffman Coding and Iterative-State Reconstruction as MPC problems
-- statement:
--   **Problem 4.4 (block table).** Input $\ell,u,\lfloor\sigma\rfloor$ and a sorted block $0<w_1\le\dots\le w_s\le\varphi w_1$ with $1\le\ell\le u$ and $s\le 2^u$. Output, for every $b\in\{s,\dots,b_{\max}\}$ with $b_{\max}=\min\{2^u,s2^{u-\ell}\}$, a record $(b,\mu(B,b),h,x,y,z)$: the largest $x$ entries at depth $h$, the next $y$ at $h+1$ and the smallest $z$ at $h+2$ form a feasible assignment for budget $b$ of cost $\mu(B,b)$. Envelope: $\max\{1,\log_\sigma b_{\max}\}$ rounds, $\sigma$ local words, $b_{\max}\max\{1,\log_\sigma b_{\max}\}$ total memory, $b_{\max}(\max\{1,\log_\sigma b_{\max}\}\max\{1,\log_2 b_{\max}\}+\max\{1,\log_2 u\})$ work.
--
--   **Problem 3.2 (table merge).** Inside an instance of size $m$ and ratio parameter $\lambda\ge1$ (so $\ell,u$ as above), input $\ell,u,\lfloor\eta\rfloor,|A_1|,|A_2|$ and the tables $(b,\mu(A_j,b))$, $b\in\mathcal B(A_j)$. Output, for each $b\in\mathcal B(A_1\uplus A_2)$, a record $(b,\mu(A,b),b_1,b_2)$ with $b_1+b_2=b$, $b_j\in\mathcal B(A_j)$, $\mu(A_1,b_1)+\mu(A_2,b_2)=\mu(A,b)$. Envelope of Lemma 5.5.
--
--   **Bounded-Ratio Huffman Coding.** Input $\ell,u,\lfloor\eta\rfloor$ and a bounded-ratio list; output $\mu(A)$ and a nonincreasing optimal depth vector $h_1\ge\cdots\ge h_m$, as in Section 3.1. Envelope of Lemma 5.6.
--
--   **Iterative-State Reconstruction.** Input $\tau$ and pairs $(f_i,h_i)$ of a bounded-ratio list with $\lambda>1$, an optimal depth vector and $\tau>f_m$. Output the cost and multiset of the threshold stopping state for $\tau$. Envelope of Lemma 6.5.
--
--   **Formalization Note** The scale bounding the word universe includes the table range, the parameters and an upper bound on the frequencies (an index component). Real parameters $\sigma,\eta,\lambda$ stay real in the envelopes; the program receives $\lfloor\sigma\rfloor$, $\lfloor\eta\rfloor$, $\ell$ and $u$.
-- source:
--   Masoud Seddighin, Saeed Seddighin, Massively Parallel Algorithms for Huffman Coding, STOC 2027 submission #377 (October 2026), SHA-256 f63f78c8ea11dfeb34be181f681ce85dc9fd1fa2def1da4a30b231073a8166ba, Problem 4.4 and Lemma 4.5, pp. 15–16 (PDF 16–17); Problem 3.2 and Lemma 5.5, pp. 20–23 (PDF 21–24); Lemma 5.6, p. 24 (PDF 25); §6 and Lemma 6.5, pp. 25, 30 (PDF 26, 31)

import Definitions.Def_HuffmanMPC_Main_Uniform
import Definitions.Def_HuffmanMPC_Main_Budgets

set_option autoImplicit false

namespace HuffmanMPC.Main

/-! ### Problem 4.4 and Lemma 4.5: the table of one block -/

/-- `b_max = min{2^u, s 2^(u-ℓ)}`. -/
def blockBudgetMax (s lo hi : ℕ) : ℕ := min (2 ^ hi) (s * 2 ^ (hi - lo))

/-- A sorted positive block with ratio at most `φ`: `0 < w₁ ≤ ⋯ ≤ w_s ≤ φ w₁`. -/
def IsPhiBlock (w : Frequencies) : Prop :=
  Positive w ∧ w.Pairwise (· ≤ ·) ∧ (w.getLast! : ℝ) ≤ phi * (w.getD 0 0 : ℝ)

/-- On the sorted block of length `m`: the `z` smallest entries get depth `h+2`,
the next `y` depth `h+1`, and the remaining (largest) entries depth `h`. -/
def windowDepths (m h y z : ℕ) : Fin m → ℕ :=
  fun i => if i.val < z then h + 2 else if i.val < z + y then h + 1 else h

/-- One output record of the block table for budget `b`: the value `μ(B,b)` and the
counts `x, y, z` at depths `h, h+1, h+2` of an assignment attaining it. -/
def BlockTableRecord (w : Frequencies) (lo hi b : ℕ) (rec : List ℕ) : Prop :=
  ∃ v h x y z : ℕ, rec = [b, v, h, x, y, z] ∧ x + y + z = w.length ∧
    BudgetFeasible w lo hi b (windowDepths w.length h y z) ∧
    depthCost w (windowDepths w.length h y z) = v ∧
    budgetOptimum w lo hi b = (v : ℕ∞)

structure BlockIndex where
  sigma : ℝ
  size : ℕ
  lo : ℕ
  hi : ℕ
  bound : ℕ

/-- Problem 4.4. Input words: `ℓ, u, ⌊σ⌋`, then the block in sorted order.
Output: one record for every budget `b ∈ {s, …, b_max}`. -/
noncomputable def blockProblem : MPCProblem BlockIndex where
  Instance _ := Frequencies
  scale i := ⌈i.sigma⌉₊ + i.size + blockBudgetMax i.size i.lo i.hi + i.hi +
    (i.hi + 1) * i.size * i.bound
  input {i} w := [i.lo, i.hi, ⌊i.sigma⌋₊] ++ w
  valid {i} w := 2 ≤ i.sigma ∧ w.length = i.size ∧ 1 ≤ i.size ∧ IsPhiBlock w ∧
    1 ≤ i.lo ∧ i.lo ≤ i.hi ∧ i.size ≤ 2 ^ i.hi ∧ ∀ x ∈ w, x ≤ i.bound
  output {i} w out := ∃ rs : List (List ℕ), EmitsRecords out rs ∧
    List.Forall₂ (fun b rec => BlockTableRecord w i.lo i.hi b rec)
      (List.range' i.size (blockBudgetMax i.size i.lo i.hi + 1 - i.size)) rs

/-- Lemma 4.5's bounds, logarithms clamped below by one. -/
noncomputable def blockEnvelope : ResourceEnvelope BlockIndex where
  rounds i := max 1 (Real.logb i.sigma (blockBudgetMax i.size i.lo i.hi))
  localSpace i := i.sigma
  aggregate i := (blockBudgetMax i.size i.lo i.hi : ℝ) *
    max 1 (Real.logb i.sigma (blockBudgetMax i.size i.lo i.hi))
  work i := (blockBudgetMax i.size i.lo i.hi : ℝ) *
    (max 1 (Real.logb i.sigma (blockBudgetMax i.size i.lo i.hi)) *
      max 1 (Real.logb 2 (blockBudgetMax i.size i.lo i.hi)) + max 1 (Real.logb 2 i.hi))

/-! ### Problem 3.2 and Lemma 5.5: merging two tables -/

/-- The relevant budgets `B(I)` in increasing order. -/
def relevantBudgetList (a : Frequencies) (lo hi : ℕ) : List ℕ :=
  List.range' a.length (budgetMax a lo hi + 1 - a.length)

/-- The table of `a` as input words `[tag, b, μ(a,b)]`, `b ∈ B(a)` increasing. -/
noncomputable def tableWords (tag : ℕ) (a : Frequencies) (lo hi : ℕ) : List ℕ :=
  (relevantBudgetList a lo hi).flatMap fun b => [tag, b, (budgetOptimum a lo hi b).toNat]

/-- One record `[b, μ(A,b), b₁, b₂]` of the merged table with a minimizing split. -/
def MergeTableRecord (a₁ a₂ : Frequencies) (lo hi b : ℕ) (rec : List ℕ) : Prop :=
  ∃ v b₁ b₂ : ℕ, rec = [b, v, b₁, b₂] ∧ b₁ + b₂ = b ∧
    b₁ ∈ relevantBudgets a₁ lo hi ∧ b₂ ∈ relevantBudgets a₂ lo hi ∧
    budgetOptimum (a₁ ++ a₂) lo hi b = (v : ℕ∞) ∧
    budgetOptimum a₁ lo hi b₁ + budgetOptimum a₂ lo hi b₂ = (v : ℕ∞)

structure MergeIndex where
  m : ℕ
  lam : ℝ
  eta : ℝ
  size₁ : ℕ
  size₂ : ℕ
  bound : ℕ

/-- Problem 3.2 inside a bounded-ratio instance on `m` frequencies with ratio
parameter `λ`, so `ℓ, u` are those of Corollary 4.2.  Input words:
`ℓ, u, ⌊η⌋, |A₁|, |A₂|`, then the two child tables. -/
noncomputable def mergeProblem : MPCProblem MergeIndex where
  Instance _ := Frequencies × Frequencies
  scale i := i.m + ⌈i.eta⌉₊ + 2 ^ upperDepth i.m i.lam +
    (upperDepth i.m i.lam + 1) * i.m * i.bound
  input {i} x := [lowerDepth i.m i.lam, upperDepth i.m i.lam, ⌊i.eta⌋₊, x.1.length, x.2.length] ++
    tableWords 1 x.1 (lowerDepth i.m i.lam) (upperDepth i.m i.lam) ++
    tableWords 2 x.2 (lowerDepth i.m i.lam) (upperDepth i.m i.lam)
  valid {i} x := 2 ≤ i.m ∧ 1 ≤ i.lam ∧ 2 ≤ i.eta ∧
    x.1.length = i.size₁ ∧ x.2.length = i.size₂ ∧ 1 ≤ i.size₁ ∧ 1 ≤ i.size₂ ∧
    i.size₁ + i.size₂ ≤ i.m ∧ Positive x.1 ∧ Positive x.2 ∧
    ∀ f ∈ x.1 ++ x.2, f ≤ i.bound
  output {i} x out := ∃ rs : List (List ℕ), EmitsRecords out rs ∧
    List.Forall₂ (fun b rec => MergeTableRecord x.1 x.2
        (lowerDepth i.m i.lam) (upperDepth i.m i.lam) b rec)
      (relevantBudgetList (x.1 ++ x.2) (lowerDepth i.m i.lam) (upperDepth i.m i.lam)) rs

/-- Lemma 5.5's bounds, with `α = log_φ 2`. -/
noncomputable def mergeEnvelope : ResourceEnvelope MergeIndex where
  rounds i := (1 + Real.logb i.eta ((i.size₁ + i.size₂ : ℕ) : ℝ)) *
    (1 + Real.logb i.eta ((min i.size₁ i.size₂ : ℕ) : ℝ))
  localSpace i := i.eta * i.lam ^ (2 * alpha)
  aggregate i := ((i.size₁ + i.size₂ : ℕ) : ℝ) * i.eta * i.lam ^ (4 * alpha) *
    (1 + Real.logb i.eta ((i.size₁ + i.size₂ : ℕ) : ℝ)) ^ 2 *
    Real.log (2 * ((i.size₁ + i.size₂ : ℕ) : ℝ) * i.eta * i.lam)
  work i := ((i.size₁ + i.size₂ : ℕ) : ℝ) * i.eta * i.lam ^ (4 * alpha) *
    (1 + Real.logb i.eta ((i.size₁ + i.size₂ : ℕ) : ℝ)) ^ 2 *
    Real.log (2 * ((i.size₁ + i.size₂ : ℕ) : ℝ) * i.eta * i.lam)

/-! ### Lemma 5.6: Bounded-Ratio Huffman Coding -/

structure RatioIndex where
  m : ℕ
  lam : ℝ
  eta : ℝ
  bound : ℕ

/-- Input words: `ℓ, u, ⌊η⌋`, then the sorted frequencies.  Output: the optimum
encoded length `[0, μ]` and one record `[i+1, hᵢ]` per frequency, for a
nonincreasing optimal depth vector `h`, as specified in Section 3.1. -/
noncomputable def boundedRatioProblem : MPCProblem RatioIndex where
  Instance _ := Frequencies
  scale i := i.m + ⌈i.eta⌉₊ + 2 ^ upperDepth i.m i.lam +
    (upperDepth i.m i.lam + 1) * i.m * i.bound
  input {i} a := [lowerDepth i.m i.lam, upperDepth i.m i.lam, ⌊i.eta⌋₊] ++ a
  valid {i} a := 2 ≤ i.eta ∧ a.length = i.m ∧ BoundedRatio a i.lam ∧ ∀ f ∈ a, f ≤ i.bound
  output a out := ∃ h : Fin a.length → ℕ, OptimalDepths a h ∧ Antitone h ∧
    EmitsRecords out ([0, optimum a] :: (List.finRange a.length).map fun j => [j.val + 1, h j])

/-- Lemma 5.6's bounds. -/
noncomputable def boundedRatioEnvelope : ResourceEnvelope RatioIndex where
  rounds i := (1 + Real.logb i.eta i.m) ^ 2 * Real.log (2 + Real.log i.lam)
  localSpace i := i.eta * i.lam ^ (2 * alpha)
  aggregate i := (i.m : ℝ) * i.eta * i.lam ^ (4 * alpha) * (1 + Real.logb i.eta i.m) ^ 2 *
    Real.log (2 * i.m * i.eta * i.lam) * Real.log (2 + Real.log i.lam)
  work i := (i.m : ℝ) * i.eta * i.lam ^ (4 * alpha) * (1 + Real.logb i.eta i.m) ^ 2 *
    Real.log (2 * i.m * i.eta * i.lam) * Real.log (2 + Real.log i.lam)

/-! ### Lemma 6.5: Iterative-State Reconstruction -/

structure ReconInstance where
  freqs : Frequencies
  depths : List ℕ
  tau : ℕ

structure ReconIndex where
  m : ℕ
  lam : ℝ
  bound : ℕ

/-- Input words: `τ`, then the pairs `fᵢ, hᵢ` in sorted order.  Output: the merge
cost `[0, c]` and one record `[1, f]` per frequency of the stopping state, i.e.
of Huffman's algorithm stopped just before its first merge with an operand
greater than `τ` (or at its final state). -/
noncomputable def reconstructionProblem : MPCProblem ReconIndex where
  Instance _ := ReconInstance
  scale i := i.m + i.bound * (i.m + 1) ^ 2
  input x := x.tau :: (x.freqs.zip x.depths).flatMap fun p => [p.1, p.2]
  valid {i} x := 1 < i.lam ∧ x.freqs.length = i.m ∧ BoundedRatio x.freqs i.lam ∧
    ∃ hlen : x.depths.length = x.freqs.length,
      OptimalDepths x.freqs (fun j => x.depths[j.val]'(by rw [hlen]; exact j.isLt)) ∧
      x.freqs.getLast! < x.tau ∧ x.tau ≤ i.bound ∧ ∀ f ∈ x.freqs, f ≤ i.bound
  output x out := EmitsRecords out
    ([0, (stoppingState x.freqs x.tau).1] :: (stoppingState x.freqs x.tau).2.map fun f => [1, f])

/-- Lemma 6.5's bounds, with `α = log_φ 2`. -/
noncomputable def reconstructionEnvelope : ResourceEnvelope ReconIndex where
  rounds i := 1 + Real.logb i.lam i.m
  localSpace i := (1 + Real.log i.lam) * i.lam ^ alpha
  aggregate i := (i.m : ℝ) * i.lam ^ alpha * (1 + Real.log i.lam) *
    (1 + Real.logb i.lam i.m) * Real.log (2 * i.m * i.lam)
  work i := (i.m : ℝ) * i.lam ^ alpha * (1 + Real.log i.lam) *
    (1 + Real.logb i.lam i.m) * Real.log (2 * i.m * i.lam)

end HuffmanMPC.Main


