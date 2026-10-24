-- Prove2me | Definitions.Def_APrioriTSP_Sampling_LP
-- name    : APrioriTSP_Sampling_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:27.053821+00:00
-- url     : https://prove2.me/theorems/0f074880-8fba-40a5-9a86-5adf13554a3f
-- title:
--   §2, pp. 8–14 — hop sums C_k, (Sampling-OP), buckets (9), δ1 and δ2 of Lemma 14, (Sampling-LP) and (Dual-Sampling-LP)
-- statement:
--   The optimization problems of §2 of Blauth, Neuwohner, Puhlmann and Vygen (pp. 8–14).
--
--   **Hop sums** (p. 8). Let $T = (v_0, v_1, \dots, v_{n-1})$ be a tour with $v_0 = d$ the depot, and put $v_j := v_0$ for $j < 0$ or $j > n - 1$. For $k \ge 1$ and a number $p$,
--   $$C_k = p^2 \sum_{j \in \mathbb Z} c(v_j, v_{j+k}).$$
--
--   **(Sampling-OP)** (p. 9). For a sequence $(C_i)_{i \ge 1}$:
--   $$\min \sum_{i=1}^\infty (1-p)^{i-1} C_i \quad\text{s.t.}\quad C_i \ge 0\ (6),\qquad C_i + C_j \ge C_{i+j}\ (7),$$
--   $$\sum_{k=1}^\infty (1-\sigma p)^{k-1}\Big(\alpha C_k + 2p \sum_{i=1}^{k-1} \min\{C_i, C_{k-i}\}\Big) \ge \sigma^{-2}\quad (8).$$
--
--   **Buckets** (9), p. 10. For odd $b$ and $i \ge 0$, $B_i = \sum_{j=\max\{1,\, ib - (b-1)/2\}}^{ib + (b-1)/2} C_j$.
--
--   **Error constants** (Lemma 14, p. 12):
--   $$\delta_1 = \frac{4\beta}{e^{N\sigma\beta}(e^{\sigma\beta} - 1)},\qquad \delta_2 = \Big(\alpha + \frac{2\beta}{e^{N\sigma\beta}(e^{\sigma\beta}-1)}\Big)\cdot\frac{e^{-N\sigma\beta}}{(1 - e^{-\sigma\beta})^2}\cdot(1 + N - e^{-\sigma\beta} N).$$
--
--   **(Sampling-LP)** (p. 12), variables $B_0, \dots, B_N$ and $M_{i,j}$ ($0 \le i \le j \le N$): minimize $\sum_{i=0}^N e^{-(i+1/2)\beta} B_i$ subject to
--   $$(\alpha + \delta_1)\sum_{k=0}^N e^{-(k-1)\sigma\beta} B_k + \delta_2 B_1 + 4\beta \sum_{j=0}^N \sum_{i=0}^j e^{-(i+j-1)\sigma\beta} M_{i,j} \ge \sigma^{-2}\quad(13),$$
--   $B_i + B_j \ge B_{i+j}$ for $1 \le i \le j \le N$, $i + j \le N$ (14); $B_i \ge M_{i,j}$ (15) and $B_j \ge M_{i,j}$ (16) for $0 \le i \le j \le N$; $B, M \ge 0$ (17).
--
--   **(Dual-Sampling-LP)** (p. 13), variables $x_{i,j}$ (dual to (14)), $v_{i,j}, w_{i,j}$ (dual to (15), (16)) and $y$ (dual to (13)): maximize $\sigma^{-2} y$ subject to $4\beta e^{-(i+j-1)\sigma\beta} y \le v_{i,j} + w_{i,j}$ for $0 \le i \le j \le N$ (18),
--   $$(\alpha+\delta_1) e^{-(k-1)\sigma\beta} y + \sum_{j=k}^N v_{k,j} + \sum_{j=0}^k w_{j,k} + \mathbb 1_{k=1}\delta_2 y + \mathbb 1_{k>0}\Big(\sum_{i=1}^{\min\{k,N-k\}} x_{i,k} + \sum_{i=k}^{N-k} x_{k,i} - \sum_{\substack{1\le i\le j\le N\\ i+j=k}} x_{i,j}\Big) \le e^{-(k+1/2)\beta}$$
--   for $0 \le k \le N$ (19), and $x, y, v, w \ge 0$ (20).
--
--   These are the successive relaxations of §2: Lemma 11 bounds (2) by (Sampling-OP), Proposition 12 and Lemmas 13 and 14 pass to buckets, Lemma 15 bounds (2) by (Sampling-LP), and Corollary 16 by any dual-feasible point.
--
--   **Formalization Note** Sequences are functions `ℕ → ℝ` (the entry `C 0` is unused). The ℤ-indexed sum of $C_k$ is taken over $-k \le j \le n - 1$: every other summand is $c(d, d)$, which is $0$ on an instance. (8) and the objective of (Sampling-OP) are `tsum`s with the index shift $k \mapsto k + 1$; for $C$ satisfying (6)–(7), $C_k \le k C_1$ and both series converge when $0 < \sigma p < 1$, $0 < p \le 1$, so no feasible point is lost. Exponents such as $-(k-1)\sigma\beta$ and $-(i+j-1)\sigma\beta$ are computed in $\mathbb R$ after casting, so $k = 0$ and $i = j = 0$ give the printed positive exponents. In the bucket limits and in (19) every natural-number subtraction is exact on the printed ranges ($b$ odd; $k \le N$). The nonnegativity (20) of $x$ is imposed on the index set of (14), which is where $x$ has variables; (19) only reads $x$ there.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 8 (C_k), p. 9 ((Sampling-OP), (6)–(8)), p. 10 (buckets (9)), p. 12 (Lemma 14's δ1, δ2; (Sampling-LP), (13)–(17)), p. 13 ((Dual-Sampling-LP), (18)–(20))

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

open Finset

variable {V : Type}

/-- The customer at position `j ∈ ℤ` of the tour `T = (v_0, …, v_{n-1})`, with `v_j := d` (the
depot) for `j < 0` or `j > n - 1` (§2.1, p. 8). -/
def tourVertex (d : V) (T : List V) (j : ℤ) : V :=
  if 0 ≤ j then T.getD j.toNat d else d

/-- The hop sum `C_k = p² · Σ_{j∈ℤ} c(v_j, v_{j+k})` of §2.1 (p. 8) for the tour `T` from the
depot `d`. When `c d d = 0` every summand with `j < -k` or `j > n - 1` vanishes (both endpoints
are the depot), so the sum is taken over `-k ≤ j ≤ n - 1`. -/
noncomputable def hopC (c : V → V → ℝ) (p : ℝ) (d : V) (T : List V) (k : ℕ) : ℝ :=
  p ^ 2 * ∑ j ∈ Finset.Icc (-(k : ℤ)) ((T.length : ℤ) - 1),
    c (tourVertex d T j) (tourVertex d T (j + k))

/-- Feasibility for (Sampling-OP) (p. 9), constraints (6)–(8), for `C : ℕ → ℝ` (the entry
`C 0` is unused). Constraint (8) is written with the index shift `k ↦ k + 1`:
`Σ_{k≥0} (1 − σp)^k (α C_{k+1} + 2p Σ_{i=1}^{k} min{C_i, C_{k+1-i}}) ≥ σ^{-2}`. -/
def SamplingOPFeasible (α σ p : ℝ) (C : ℕ → ℝ) : Prop :=
  (∀ i, 1 ≤ i → 0 ≤ C i) ∧
  (∀ i j, 1 ≤ i → 1 ≤ j → C (i + j) ≤ C i + C j) ∧
  1 / σ ^ 2 ≤ ∑' k : ℕ, (1 - σ * p) ^ k *
    (α * C (k + 1) + 2 * p * ∑ i ∈ Finset.Icc 1 k, min (C i) (C (k + 1 - i)))

/-- The objective `Σ_{i≥1} (1 − p)^{i−1} C_i` of (Sampling-OP), shifted `i ↦ i + 1`. -/
noncomputable def samplingOPObj (p : ℝ) (C : ℕ → ℝ) : ℝ :=
  ∑' i : ℕ, (1 - p) ^ i * C (i + 1)

/-- The bucket `B_i = Σ_{j = max{1, ib − (b−1)/2}}^{ib + (b−1)/2} C_j` of (9), p. 10, for odd `b`
(then `(b - 1) / 2` is exact, and the ℕ subtraction `i * b - (b - 1) / 2` is exact for `i ≥ 1`
and gives the printed lower limit `max{1, ·} = 1` at `i = 0`). -/
def bucket (b : ℕ) (C : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc (max 1 (i * b - (b - 1) / 2)) (i * b + (b - 1) / 2), C j

/-- `δ₁ = 4β / (e^{Nσβ}(e^{σβ} − 1))` (Lemma 14, p. 12). -/
noncomputable def delta1 (β σ : ℝ) (N : ℕ) : ℝ :=
  4 * β / (Real.exp (N * σ * β) * (Real.exp (σ * β) - 1))

/-- `δ₂ = (α + 2β / (e^{Nσβ}(e^{σβ} − 1))) · e^{−Nσβ} / (1 − e^{−σβ})² · (1 + N − e^{−σβ} N)`
(Lemma 14, p. 12). -/
noncomputable def delta2 (α β σ : ℝ) (N : ℕ) : ℝ :=
  (α + 2 * β / (Real.exp (N * σ * β) * (Real.exp (σ * β) - 1))) *
    (Real.exp (-(N * σ * β)) / (1 - Real.exp (-(σ * β))) ^ 2) *
    (1 + N - Real.exp (-(σ * β)) * N)

/-- Feasibility of `(B, M)` for (Sampling-LP) (p. 12), variables `B_0, …, B_N` and `M_{i,j}`
for `0 ≤ i ≤ j ≤ N`; one conjunct per constraint (13), (14), (15), (16), (17). -/
def SamplingLPFeasible (α σ β : ℝ) (N : ℕ) (B : ℕ → ℝ) (M : ℕ → ℕ → ℝ) : Prop :=
  -- (13)
  1 / σ ^ 2 ≤ (α + delta1 β σ N) *
      ∑ k ∈ Finset.range (N + 1), Real.exp (-(((k : ℝ) - 1) * σ * β)) * B k +
    delta2 α β σ N * B 1 +
    4 * β * ∑ j ∈ Finset.range (N + 1), ∑ i ∈ Finset.range (j + 1),
      Real.exp (-(((i : ℝ) + j - 1) * σ * β)) * M i j ∧
  -- (14)
  (∀ i j, 1 ≤ i → i ≤ j → i + j ≤ N → B (i + j) ≤ B i + B j) ∧
  -- (15)
  (∀ i j, i ≤ j → j ≤ N → M i j ≤ B i) ∧
  -- (16)
  (∀ i j, i ≤ j → j ≤ N → M i j ≤ B j) ∧
  -- (17)
  (∀ i, i ≤ N → 0 ≤ B i) ∧
  (∀ i j, i ≤ j → j ≤ N → 0 ≤ M i j)

/-- The objective `Σ_{i=0}^N e^{−(i+1/2)β} B_i` of (Sampling-LP), p. 12. -/
noncomputable def samplingLPObj (β : ℝ) (N : ℕ) (B : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N + 1), Real.exp (-(((i : ℝ) + 1 / 2) * β)) * B i

/-- Feasibility of `(x, y, v, w)` for (Dual-Sampling-LP) (p. 13): constraints (18), (19), (20).
`x i j` is the dual of (14) for `1 ≤ i ≤ j`, `i + j ≤ N`; `v i j`, `w i j` are the duals of (15),
(16) for `0 ≤ i ≤ j ≤ N`; `y` is the dual of (13). -/
def DualSamplingLPFeasible (α σ β : ℝ) (N : ℕ) (x : ℕ → ℕ → ℝ) (y : ℝ)
    (v w : ℕ → ℕ → ℝ) : Prop :=
  -- (18)
  (∀ i j, i ≤ j → j ≤ N →
    4 * β * Real.exp (-(((i : ℝ) + j - 1) * σ * β)) * y ≤ v i j + w i j) ∧
  -- (19)
  (∀ k, k ≤ N →
    (α + delta1 β σ N) * Real.exp (-(((k : ℝ) - 1) * σ * β)) * y +
      ∑ j ∈ Finset.Icc k N, v k j + ∑ j ∈ Finset.range (k + 1), w j k +
      (if k = 1 then delta2 α β σ N * y else 0) +
      (if 0 < k then
        (∑ i ∈ Finset.Icc 1 (min k (N - k)), x i k + ∑ i ∈ Finset.Icc k (N - k), x k i -
          ∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc i N, if i + j = k then x i j else 0)
      else 0) ≤
      Real.exp (-(((k : ℝ) + 1 / 2) * β))) ∧
  -- (20)
  0 ≤ y ∧
  (∀ i j, 1 ≤ i → i ≤ j → i + j ≤ N → 0 ≤ x i j) ∧
  (∀ i j, i ≤ j → j ≤ N → 0 ≤ v i j) ∧
  (∀ i j, i ≤ j → j ≤ N → 0 ≤ w i j)

end APrioriTSP.Sampling


