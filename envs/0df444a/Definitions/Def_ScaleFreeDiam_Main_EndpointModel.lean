-- Prove2me | Definitions.Def_ScaleFreeDiam_Main_EndpointModel
-- name    : ScaleFreeDiam_Main_EndpointModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:11:09.503586+00:00
-- url     : https://prove2.me/theorems/1bbda90c-fa6d-4748-9085-562b82f8200e
-- title:
--   §6–§7, pp. 16–23 — M₂(0,1), the sorted right endpoints W_i, the events E₁–E₅, useful vertices, and the random graph G(W₁,…,W_n)
-- statement:
--   This file fixes the objects of §§6–8 of Bollobás and Riordan (2004), used for the upper bound.
--
--   **The endpoint model.** An $M_2(0,1)$ random variable has density $2x$ on $0<x<1$. Let $r_1,\dots,r_{mn}$ be independent $M_2(0,1)$ variables and $R_1\le\dots\le R_{mn}$ their sorted values; $R_k$ is the $k$-th order statistic $\inf\{x:\ \#\{j: r_j\le x\}\ge k\}$. For $1\le i\le n$ put $W_i=R_{mi}$, $W_0=0$, and $w_i=W_i-W_{i-1}$.
--
--   **The parameters.** $s=2^a$ is the smallest power of $2$ larger than $(\log n)^7$, $2^b$ is the largest power of $2$ smaller than $2n/3$, and $I_t=[2^t+1,2^{t+1}]$.
--
--   **The events.**
--   1. $E_1$: $\big|W_i-\sqrt{i/n}\big|\le\frac1{10}\sqrt{i/n}$ for $s\le i\le n$.
--   2. $E_2$: for $a\le t<b$, $I_t$ contains at least $2^{t-1}$ vertices $i$ with $w_i\ge 1/(10\sqrt{in})$ (such $i$ are called **good**).
--   3. $E_3$: $w_1\ge 4/(\log n\,\sqrt n)$.
--   4. $E_4$: $w_i\ge(\log n)^2/n$ for $1\le i<n^{1/5}$.
--   5. $E_5$: $w_i\le n^{-4/5}$ for $n/(\log n)^5<i\le n$.
--
--   A vertex $i\ge1$ is **useful** if $i\le n/(\log n)^5$ and $w_i\ge(\log n)^2/n$.
--
--   **The random graph $G(W_1,\dots,W_n)$.** For $0=W_0<W_1<\dots<W_n<1$ (**admissible** $W$), each vertex $i$ sends two edges, to $l_{i,1}$ and $l_{i,2}$, where all $l_{i,j}$ are independent with
--   $$
--   \mathbb P_L(l_{i,j}=k)=\frac{w_k}{W_i},\qquad 1\le k\le i .
--   $$
--   A **descending path** of length $k$ from $v$ is $v=u_0>u_1>\dots>u_k$ with $u_{t+1}\in\{l_{u_t,1},l_{u_t,2}\}$.
--
--   These objects carry the upper-bound half of the mission (Lemmas 7, 8, 10, 11, 12, the coupling of §6 and the final display of p. 29).
--
--   **Formalization Note** $W$ is a function $\mathbb N\to\mathbb R$ read at $0,\dots,n$; `Admissible n W` is the page's $0<W_1<\dots<W_n<1$ with $W_0=0$, and is a hypothesis of every statement about $G(W)$. Outcomes `l i j` are stored 0-based and read 1-based through `lab`. The graph `GW` is the simple-graph shadow (loops dropped). The order statistic is written as an infimum, which avoids sorting; $a$, $b$ are defined for every $n$ (via `Nat.find` / `Nat.findGreatest`), their values for small $n$ being irrelevant to the asymptotic statements. In $E_2$, $2^{t-1}$ is a real power, so it equals $1/2$ at $t=0$.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), p. 16 (M₂(0,1), W_i, w_i, s, a, b, I_t), pp. 16–17 Lemma 7 (E₁–E₅), p. 20 (G(W₁,…,W_n)), p. 21 (useful, descending paths), p. 23 (good)

import Mathlib
import Definitions.Def_ScaleFreeDiam_Main_Process

namespace ScaleFreeDiam.Main

open MeasureTheory
open scoped Classical

/-- The law `M₂(0,1)` on `ℝ`: density `2x` on `0 < x < 1`. -/
noncomputable def M2 : Measure ℝ :=
  (volume.restrict (Set.Ioo (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (2 * x))

/-- The `k`-th order statistic (1-based) of the finite family `r`:
`inf {x : k ≤ #{j : r j ≤ x}}`. For `1 ≤ k ≤ #ι` this is the `k`-th smallest value. -/
noncomputable def orderStat {ι : Type*} [Fintype ι] (r : ι → ℝ) (k : ℕ) : ℝ :=
  sInf {x : ℝ | k ≤ (Finset.univ.filter (fun j => r j ≤ x)).card}

/-- `W_i = R_{mi}` for `1 ≤ i ≤ n`, with `W_0 = 0`, where `R_1 ≤ ⋯ ≤ R_{mn}` are the sorted
values of `r_1, …, r_{mn}` (1-based indices `i`). -/
noncomputable def Wof (m n : ℕ) (r : Fin (m * n) → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else orderStat r (m * i)

/-- The spacing `w_i = W_i − W_{i−1}` (1-based; `w_0 = 0`). -/
noncomputable def w (W : ℕ → ℝ) (i : ℕ) : ℝ := W i - W (i - 1)

/-- `a`: the least `t` with `2^t > (log n)^7`, so that `s = 2^a` is the smallest power of 2
larger than `(log n)^7` (p. 16). -/
noncomputable def aE (n : ℕ) : ℕ :=
  Nat.find (pow_unbounded_of_one_lt ((Real.log n) ^ 7) (one_lt_two : (1 : ℝ) < 2))

/-- `s = 2^a`. -/
noncomputable def sA (n : ℕ) : ℕ := 2 ^ aE n

/-- `b`: the largest `t` with `2^t < 2n/3` (p. 16); every such `t` is `< n`. It is `0` if no
power of 2 is smaller than `2n/3` (only for `n ≤ 1`). -/
noncomputable def bE (n : ℕ) : ℕ :=
  Nat.findGreatest (fun t => (2 : ℝ) ^ t < 2 * (n : ℝ) / 3) n

/-- The interval `I_t = [2^t + 1, 2^{t+1}]` of (1-based) vertices. -/
def It (t : ℕ) : Finset ℕ := Finset.Icc (2 ^ t + 1) (2 ^ (t + 1))

/-- The sequences the model `G(W_1, …, W_n)` is defined for: `0 = W_0 < W_1 < ⋯ < W_n < 1`. -/
def Admissible (n : ℕ) (W : ℕ → ℝ) : Prop :=
  W 0 = 0 ∧ (∀ i < n, W i < W (i + 1)) ∧ W n < 1

/-- `E_1`: `|W_i − √(i/n)| ≤ (1/10)√(i/n)` for `s ≤ i ≤ n`. -/
def E1 (n : ℕ) (W : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, sA n ≤ i → i ≤ n →
    |W i - Real.sqrt ((i : ℝ) / n)| ≤ (1 / 10) * Real.sqrt ((i : ℝ) / n)

/-- A vertex `i` is good if `w_i ≥ 1/(10√(in))` (p. 23). -/
def good (n : ℕ) (W : ℕ → ℝ) (i : ℕ) : Prop :=
  1 / (10 * Real.sqrt ((i : ℝ) * n)) ≤ w W i

/-- `E_2`: for `a ≤ t < b`, `I_t` contains at least `2^{t−1}` vertices `i` with
`w_i ≥ 1/(10√(in))`. -/
def E2 (n : ℕ) (W : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, aE n ≤ t → t < bE n →
    (2 : ℝ) ^ ((t : ℤ) - 1) ≤ (((It t).filter (fun i => good n W i)).card : ℝ)

/-- `E_3`: `w_1 ≥ 4/(log n · √n)`. -/
def E3 (n : ℕ) (W : ℕ → ℝ) : Prop :=
  4 / (Real.log n * Real.sqrt n) ≤ w W 1

/-- `E_4`: `w_i ≥ (log n)²/n` for (1-based) `i < n^{1/5}`. -/
def E4 (n : ℕ) (W : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → (i : ℝ) < (n : ℝ) ^ ((1 : ℝ) / 5) → (Real.log n) ^ 2 / n ≤ w W i

/-- `E_5`: `w_i ≤ n^{−4/5}` for `n/(log n)^5 < i ≤ n`. -/
def E5 (n : ℕ) (W : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, (n : ℝ) / (Real.log n) ^ 5 < i → i ≤ n → w W i ≤ (n : ℝ) ^ (-(4 : ℝ) / 5)

/-- A vertex `i` (`1 ≤ i`) is useful if `i ≤ n/(log n)^5` and `w_i ≥ (log n)²/n` (p. 21). -/
def useful (n : ℕ) (W : ℕ → ℝ) (i : ℕ) : Prop :=
  1 ≤ i ∧ (i : ℝ) ≤ n / (Real.log n) ^ 5 ∧ (Real.log n) ^ 2 / n ≤ w W i

/-- An outcome of `G(W_1, …, W_n)`: `l i j` (0-based `i`, `j ∈ {0,1}`) is the paper's
`l_{i+1, j+1} − 1 ∈ {0, …, i}`. -/
abbrev LSeq (n : ℕ) : Type := (i : Fin n) → Fin 2 → Fin (i.val + 1)

/-- The probability of an outcome: the `l_{i,j}` are independent with
`ℙ(l_{i,j} = k) = w_k / W_i` for `1 ≤ k ≤ i` (1-based). -/
noncomputable def weightL (n : ℕ) (W : ℕ → ℝ) (l : LSeq n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin 2, w W ((l i j).val + 1) / W (i.val + 1)

/-- `ℙ_L(P)` in the random graph `G(W_1, …, W_n)`. -/
noncomputable def probGW (n : ℕ) (W : ℕ → ℝ) (P : LSeq n → Prop) : ℝ :=
  ∑ l : LSeq n, if P l then weightL n W l else 0

/-- The (simple-graph shadow of the) graph `G(W_1, …, W_n)` on `Fin n`: `i` is joined to
`l i 0` and `l i 1`; loops are dropped. -/
def GW {n : ℕ} (l : LSeq n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ (i : Fin n) (j : Fin 2), e = s(i, Fin.castLE i.isLt (l i j))}

/-- 1-based accessor: `lab l i j` is the paper's `l_{i, j+1}` for `1 ≤ i ≤ n`, and `0` (junk)
otherwise. -/
def lab {n : ℕ} (l : LSeq n) (i : ℕ) (j : Fin 2) : ℕ :=
  if h : 1 ≤ i ∧ i ≤ n then (l ⟨i - 1, by omega⟩ j).val + 1 else 0

/-- There is a descending path `v = u_0 > u_1 > ⋯ > u_k` in `G(W)` of length `k ≤ x`, with
`u_{t+1} ∈ {l_{u_t,1}, l_{u_t,2}}`, ending at a vertex satisfying `U` (1-based labels;
`k = 0` is allowed). -/
def DescPathTo {n : ℕ} (l : LSeq n) (v : ℕ) (x : ℝ) (U : ℕ → Prop) : Prop :=
  ∃ k : ℕ, (k : ℝ) ≤ x ∧ ∃ u : ℕ → ℕ, u 0 = v ∧
    (∀ t < k, u (t + 1) < u t ∧ (u (t + 1) = lab l (u t) 0 ∨ u (t + 1) = lab l (u t) 1)) ∧
    U (u k)

end ScaleFreeDiam.Main


