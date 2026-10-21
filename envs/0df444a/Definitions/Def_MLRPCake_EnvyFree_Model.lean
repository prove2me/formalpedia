-- Prove2me | Definitions.Def_MLRPCake_EnvyFree_Model
-- name    : MLRPCake_EnvyFree_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:22:35.536373+00:00
-- url     : https://prove2.me/theorems/d93898eb-1c5a-42aa-bd65-5cf6acc5bce4
-- title:
--   §2, §5, pp. 5–13 — contiguous cake division under MLRP: instance, Eval/Cut queries, λ-Lipschitz, ripple map RD, δ-ripple divisions, BinSearch
-- statement:
--   This file fixes the model of Barman and Rathi's cake-division paper, with $n$ agents dividing the cake $[0,1]$ into contiguous pieces.
--
--   1. **Instance** (§2, p. 5). Each agent $i$ has a *value density* $f_i:[0,1]\to\mathbb R_+$. It is nonnegative and bounded on $[0,1]$, integrable, and normalized so that $\int_0^1 f_i = 1$. Agent $i$'s value of an interval $[a,b]\subseteq[0,1]$ is $v_i(a,b)=\int_a^b f_i(x)\,dx$.
--   2. **MLRP** (p. 7). The densities are strictly positive on $[0,1]$, and the agents are indexed in the MLRP order: for every $i\in[n-1]$ the likelihood ratio $f_{i+1}(x)/f_i(x)$ is nondecreasing in $x\in[0,1]$.
--   3. **Robertson–Webb queries** (p. 6). $\mathrm{Eval}_i(\ell,r)=v_i(\ell,r)$ is the value of $[\ell,r]$. $\mathrm{Cut}_i(\ell,\tau)$ is the leftmost $y\in[\ell,1]$ with $v_i(\ell,y)=\tau$; by convention $\mathrm{Cut}_i(\ell,\tau)=1$ when no such $y$ exists.
--   4. **λ-Lipschitz queries** (p. 8). For every agent $i$,
--   $$|\mathrm{Eval}_i(\ell',r')-\mathrm{Eval}_i(\ell,r)|\le\lambda\,\|(\ell',r')-(\ell,r)\|_\infty,\qquad |\mathrm{Cut}_i(\ell',\tau')-\mathrm{Cut}_i(\ell,\tau)|\le\lambda\,\|(\ell',\tau')-(\ell,\tau)\|_\infty,$$
--   for all $\ell,r,\ell',r'\in[0,1]$ and all $\tau,\tau'\ge 0$.
--   5. **Ripple map**, recursion (1), p. 11. $\mathrm{RD}_2(x)=\mathrm{Cut}_1(x,\mathrm{Eval}_1(0,x))$ and $\mathrm{RD}_i(x)=\mathrm{Cut}_{i-1}\big(\mathrm{RD}_{i-1}(x),\mathrm{Eval}_{i-1}(\mathrm{RD}_{i-2}(x),\mathrm{RD}_{i-1}(x))\big)$. Starting from the first cut point $x_1=x$, $\mathrm{RD}_i(x)$ is the cut point $x_i$ forced by the equalities $v_{i-1}(x_{i-2},x_{i-1})=v_{i-1}(x_{i-1},x_i)$.
--   6. **δ-ripple division** (Definition 2, p. 10). Points $x_0=0\le x_1\le\dots\le x_n\le 1$ with $x_n\ge 1-\delta$ and $v_i(x_{i-1},x_i)=v_i(x_i,x_{i+1})>0$ for all $i\in[n-1]$. Agent $i$ receives $I_i=[x_{i-1},x_i]$.
--   7. **Allocations and envy-freeness up to η** (pp. 6, 8). Cut points $0=x_0\le\dots\le x_n=1$ form a contiguous allocation. It is envy-free up to $\eta$ when $v_i(I_i)\ge v_i(I_j)-\eta$ for all agents $i,j$.
--   8. **BinSearch** (Algorithm 1, p. 13). Start from $\ell=0$, $r=1$. In each iteration, put $m=(\ell+r)/2$. If $\mathrm{RD}_n(m)<1-\delta$, set $\ell\leftarrow m$. If $\mathrm{RD}_n(m)=1$, set $r\leftarrow m$. If $\mathrm{RD}_n(m)\in[1-\delta,1)$, return $x_0=0$, $x_1=m$, $x_i=\mathrm{RD}_i(m)$.
--   9. **Coalescing** (proof of Theorem 1, p. 15). The last agent's interval is extended to $[x_{n-1},1]$.
--
--   These are the objects of the paper's envy-freeness result (Theorem 1) and of every milestone of this mission.
--
--   **Formalization Note** Agents are 0-based: `i : Fin n` is the paper's agent $i+1$. Cut points are a sequence `x : ℕ → ℝ`, of which only `x 0, …, x n` matter, and agent `i` receives `[x i, x (i+1)]`. Riemann integrability is encoded as boundedness plus `IntervalIntegrable` on $[0,1]$, which is weaker than Riemann integrability, so every statement over this model is at least as strong as the paper's. `val f k a b` is the interval integral $v_k(a,b)$ and is used only with $a\le b$. `eval` integrates over `Set.Icc ℓ r`, so it is $0$ when $\ell>r$, matching Eval's codomain $\mathbb R_+$. `cut` returns `sInf` of the solution set and `1` when that set is empty (the paper's truncation), never Lean's `sInf ∅ = 0`. The ripple map `rd` uses $\mathrm{RD}_0=0$ and $\mathrm{RD}_1=\mathrm{id}$, so its general line also covers $\mathrm{RD}_2$; agent densities at indices $k\ge n$ are a junk $0$ and are never queried by `rd f n`. `λ` is written `lam`. BinSearch is modeled by its iterates `bsIter`: `bsMid k` is the midpoint queried in iteration `k`, `bsStops k` says that iteration returns (line 7), and `bsOutput k` is the returned division (line 8). Its running time is counted in iterations; each iteration evaluates $\mathrm{RD}_n$ once, at a cost of $2(n-1)$ Robertson–Webb queries by (1).
-- source:
--   Barman & Rathi, Fair Cake Division Under Monotone Likelihood Ratios, arXiv:2006.00481v3, pp. 5–8, 10–13, 15: §2 (model, Eval/Cut queries, MLRP, λ-Lipschitz), Definition 2, equation (1), Algorithm 1, proof of Theorem 1 (coalescing)

import Mathlib

namespace MLRPCake.EnvyFree
open MeasureTheory

/-- §2, p. 5: a value density on the cake `[0,1]`: nonnegative, bounded (Riemann integrable
functions are bounded, footnote 7), integrable on `[0,1]`, and normalized to total value 1. -/
def IsDensity (g : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ g x) ∧ (∃ U : ℝ, ∀ x ∈ Set.Icc (0:ℝ) 1, g x ≤ U) ∧
  IntervalIntegrable g volume 0 1 ∧ ∫ x in (0:ℝ)..1, g x = 1

variable {n : ℕ}

/-- §2, p. 5: a cake-division instance `⟨[n], {f_i}_i⟩`; agent `i : Fin n` is the paper's agent
`i + 1`. -/
def IsInstance (f : Fin n → ℝ → ℝ) : Prop := ∀ i, IsDensity (f i)

/-- p. 7, MLRP in the paper's w.l.o.g. order (the agents are indexed so that the MLRP order is the
identity): the densities are strictly positive on `[0,1]` and each consecutive likelihood ratio
`f_{i+1}/f_i` is nondecreasing on `[0,1]`. -/
def IsMLRP (f : Fin n → ℝ → ℝ) : Prop :=
  (∀ i, ∀ x ∈ Set.Icc (0:ℝ) 1, 0 < f i x) ∧
  ∀ i j : Fin n, j.val = i.val + 1 → ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 →
    f j x / f i x ≤ f j y / f i y

/-- The density of agent `k` as a total function of `k : ℕ`. For `k ≥ n` it is the junk value `0`;
it is never used there (the ripple map `rd f n` only queries agents `k ≤ n - 2`). -/
noncomputable def dens (f : Fin n → ℝ → ℝ) (k : ℕ) : ℝ → ℝ :=
  if h : k < n then f ⟨k, h⟩ else fun _ => 0

/-- `v_k(a, b) = ∫_a^b f_k`, agent `k`'s value of `[a, b]`; used only with `a ≤ b`. -/
noncomputable def val (f : Fin n → ℝ → ℝ) (k : ℕ) (a b : ℝ) : ℝ := ∫ t in a..b, dens f k t

/-- Eval query (p. 6): the value of the interval `[ℓ, r]` (the integral over `Set.Icc ℓ r`,
so `0` when `ℓ > r`). -/
noncomputable def eval (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ r : ℝ) : ℝ := ∫ t in Set.Icc ℓ r, dens f k t

open Classical in
/-- Cut query (p. 6): the leftmost `y ∈ [ℓ, 1]` with `v_k(ℓ, y) = τ`, and `1` by convention when
no such `y` exists. -/
noncomputable def cut (f : Fin n → ℝ → ℝ) (k : ℕ) (ℓ τ : ℝ) : ℝ :=
  if ∃ y ∈ Set.Icc ℓ 1, val f k ℓ y = τ then sInf {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ} else 1

/-- p. 8: the cut and eval queries are `λ`-Lipschitz in the `∞`-norm (`lam` stands for `λ`). -/
def QueriesLipschitz (f : Fin n → ℝ → ℝ) (lam : ℝ) : Prop :=
  ∀ i : Fin n,
    (∀ ℓ r ℓ' r', ℓ ∈ Set.Icc (0:ℝ) 1 → r ∈ Set.Icc (0:ℝ) 1 → ℓ' ∈ Set.Icc (0:ℝ) 1 →
      r' ∈ Set.Icc (0:ℝ) 1 →
      |eval f i ℓ' r' - eval f i ℓ r| ≤ lam * max |ℓ' - ℓ| |r' - r|) ∧
    (∀ ℓ τ ℓ' τ', ℓ ∈ Set.Icc (0:ℝ) 1 → ℓ' ∈ Set.Icc (0:ℝ) 1 → 0 ≤ τ → 0 ≤ τ' →
      |cut f i ℓ' τ' - cut f i ℓ τ| ≤ lam * max |ℓ' - ℓ| |τ' - τ|)

/-- Recursion (1), p. 11, with `RD_0 = 0` and `RD_1 = id`: `rd f (k+2) x` is the paper's
`RD_{k+2}(x) = Cut_{k+1}(RD_{k+1}(x), Eval_{k+1}(RD_k(x), RD_{k+1}(x)))` (agent `k` 0-based). -/
noncomputable def rd (f : Fin n → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, x => x
  | k + 2, x => cut f k (rd f (k + 1) x) (eval f k (rd f k x) (rd f (k + 1) x))

/-- Definition 2 (δ-ripple division), p. 10. Agent `i` with `i + 1 < n` is the paper's agent
`i + 1 ∈ [n - 1]`; agent `i` (0-based) owns `[x i, x (i+1)]`. -/
def IsRipple (f : Fin n → ℝ → ℝ) (δ : ℝ) (x : ℕ → ℝ) : Prop :=
  x 0 = 0 ∧ (∀ k < n, x k ≤ x (k + 1)) ∧ x n ≤ 1 ∧ 1 - δ ≤ x n ∧
  ∀ i : ℕ, i + 1 < n → val f i (x i) (x (i + 1)) = val f i (x (i + 1)) (x (i + 2)) ∧
    0 < val f i (x i) (x (i + 1))

/-- p. 6: a contiguous allocation given by cut points `0 = x_0 ≤ … ≤ x_n = 1`; agent `i`
(0-based) receives `[x i, x (i+1)]`. -/
def IsAllocation (x : ℕ → ℝ) : Prop := x 0 = 0 ∧ (∀ k < n, x k ≤ x (k + 1)) ∧ x n = 1

/-- p. 8: envy-freeness up to precision `η`: `v_i(I_i) ≥ v_i(I_j) - η` for all agents `i, j`. -/
def EnvyFreeUpTo (f : Fin n → ℝ → ℝ) (η : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i j : ℕ, i < n → j < n → val f i (x j) (x (j + 1)) - η ≤ val f i (x i) (x (i + 1))

/-- Algorithm 1 (BinSearch), p. 13: the pair `(ℓ, r)` held before iteration `k`. Once the
stopping branch (line 7) fires the pair stays put (the algorithm has returned). -/
noncomputable def bsIter (f : Fin n → ℝ → ℝ) (δ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | k + 1 =>
    let p := bsIter f δ k
    let m := (p.1 + p.2) / 2
    if rd f n m < 1 - δ then (m, p.2) else if rd f n m = 1 then (p.1, m) else p

/-- The midpoint `(ℓ + r)/2` queried in iteration `k` of BinSearch. -/
noncomputable def bsMid (f : Fin n → ℝ → ℝ) (δ : ℝ) (k : ℕ) : ℝ :=
  ((bsIter f δ k).1 + (bsIter f δ k).2) / 2

/-- BinSearch returns in iteration `k` (line 7): `RD_n((ℓ + r)/2) ∈ [1 - δ, 1)`. -/
def bsStops (f : Fin n → ℝ → ℝ) (δ : ℝ) (k : ℕ) : Prop := rd f n (bsMid f δ k) ∈ Set.Ico (1 - δ) 1

/-- Line 8 of BinSearch, returning in iteration `k`: `x_0 = 0`, `x_1 = (ℓ+r)/2`,
`x_i = RD_i(x_1)`. -/
noncomputable def bsOutput (f : Fin n → ℝ → ℝ) (δ : ℝ) (k : ℕ) : ℕ → ℝ :=
  fun i => rd f i (bsMid f δ k)

/-- Proof of Theorem 1, p. 15: coalesce the unallocated piece `[x_n, 1]` into the last agent's
interval, i.e. replace the last cut point by `1`. -/
noncomputable def coalesce (n : ℕ) (x : ℕ → ℝ) : ℕ → ℝ := fun k => if k = n then 1 else x k

end MLRPCake.EnvyFree


