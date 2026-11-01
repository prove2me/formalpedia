-- Prove2me | Definitions.Def_ActiveCtxSearch_MarginAL
-- name    : ActiveCtxSearch_MarginAL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:41:44.326376+00:00
-- url     : https://prove2.me/theorems/af07f086-79b4-41b6-a05d-ac87884b8645
-- title:
--   Algorithm 3: margin-based active learning with intercept
-- statement:
--   **Algorithm 3** ($\mathrm{MarginBasedActiveLearning}(b,\varepsilon_a,\delta_a,\kappa_m,\kappa_n,\epsilon_0,\beta_0)$) at a fixed action $b$:
--
--   1. Query the next $n_0=\lceil\kappa_n/\epsilon_0^2\rceil$ items at $b$, giving the data $D_0$, and let $(\hat w_0,\hat\beta_0)\in\arg\min_{\|w\|_2=1,\,|\beta|\le\beta_0}\sum_{(x,y)\in D_0}\mathbf 1\{y\neq\operatorname{sgn}(\langle x,w\rangle-\beta)\}$.
--   2. Let $k_0=\min\{k\in\mathbb N:2^{-k}\epsilon_0\le\varepsilon_a\}$.
--   3. For $k=1,\dots,k_0$: set $\epsilon_k=2^{-k}\epsilon_0$, $m_k=\kappa_m\sqrt{\epsilon_k}$, $n_k=\lceil\kappa_nd/\epsilon_k\rceil$, $D_k=\emptyset$. While $|D_k|<n_k$: read the next context $x$; if $|\langle x,\hat w_{k-1}\rangle-\hat\beta_{k-1}|\le m_k$, query it at $b$ and append $(x,y)$ to $D_k$, otherwise let it pass. Then let $(\hat w_k,\hat\beta_k)$ be a minimizer of the same constrained empirical loss on $D_k$.
--   4. Return $(\hat w_{k_0},\hat\beta_{k_0})$.
--
--   A **tie-breaking rule** is any map choosing, for each data list, one of the constrained minimizers; every statement is made for every such rule. The run on a stream records the returned classifier, the number of queries $n_0+\sum_k n_k$ and the position after the last item read (queried or passed); it has no result if some inner loop never stops.
--
--   **Formalization Note** $\delta_a$ does not occur in the pseudocode (it enters only through $\kappa_n$), and $\beta_0$ enters only through the constraint of the arg min, i.e. through the tie-breaking rule. The source's "$\{x,y\}$" in line 11 is the pair $(x,y)$.
-- source:
--   Chen, Liu & Wang, Active Learning for Contextual Search with Binary Feedback, arXiv:2110.01072v2, Algorithm 3, p.13

import Mathlib
import Definitions.Def_ActiveCtxSearch_Errors
import Definitions.Def_ActiveCtxSearch_WhileLoop

open MeasureTheory
open scoped RealInnerProductSpace

namespace ActiveCtxSearch

variable {d : ℕ}

/-- A tie-breaking rule for the constrained empirical risk minimization of Algorithm 3, lines 3 and
14 (arXiv:2110.01072v2, p.13): `sel D` is one of the minimizers
`arg min_{‖w‖₂ = 1, |β| ≤ β₀} Σ_{(x,y)∈D} 1{y ≠ sgn(⟨x, w⟩ − β)}`.

**Formalization Note** The arg min need not be unique; the source does not say which minimizer is
returned, so every statement about Algorithm 3 is made for every such rule. The rule is a function
of the data list. -/
def IsERMSelection (β₀ : ℝ) (sel : List (E d × ℤ) → E d × ℝ) : Prop :=
  ∀ D, ‖(sel D).1‖ = 1 ∧ |(sel D).2| ≤ β₀ ∧
    ∀ c : E d × ℝ, ‖c.1‖ = 1 → |c.2| ≤ β₀ → empLoss D (sel D) ≤ empLoss D c

/-- The state of Algorithm 3 between epochs: the current classifier `(ŵ_k, β̂_k)`, the number of
queries so far and the position of the next unread item. -/
structure MBState (d : ℕ) where
  c : E d × ℝ
  queries : ℕ
  pos : ℕ

/-- The state of the inner `while` loop of Algorithm 3: the collected data `D_k` and the position of
the next unread item. -/
structure MBInner (d : ℕ) where
  D : List (E d × ℤ)
  pos : ℕ

/-- The output of Algorithm 3: the returned classifier `(ŵ_{k₀}, β̂_{k₀})`, the number of queries and
the position after the last item read. -/
structure MBResult (d : ℕ) where
  c : E d × ℝ
  queries : ℕ
  endPos : ℕ

/-- The warm-up size `n₀ = ⌈κ_n / ϵ₀²⌉` (Algorithm 3, line 2). -/
noncomputable def mbN0 (κn ϵ0 : ℝ) : ℕ := ⌈κn / ϵ0 ^ 2⌉₊

/-- The number of epochs `k₀ = min{k ∈ ℕ : 2^{−k} ϵ₀ ≤ ε_a}` (Algorithm 3, line 4).

**Formalization Note** The minimum exists whenever `ε_a > 0`; the value `0` is a placeholder for
`ε_a ≤ 0`, which no statement uses. -/
noncomputable def mbK0 (εa ϵ0 : ℝ) : ℕ :=
  open Classical in
  if h : ∃ k : ℕ, ϵ0 / 2 ^ k ≤ εa then Nat.find h else 0

/-- The epoch parameters of Algorithm 3, line 6: `ϵ_k = 2^{−k} ϵ₀`. -/
noncomputable def mbEps (ϵ0 : ℝ) (k : ℕ) : ℝ := ϵ0 / 2 ^ k

/-- The margin `m_k = κ_m √ϵ_k` (Algorithm 3, line 6). -/
noncomputable def mbMargin (κm ϵ0 : ℝ) (k : ℕ) : ℝ := κm * Real.sqrt (mbEps ϵ0 k)

/-- The epoch sample size `n_k = ⌈κ_n d / ϵ_k⌉` (Algorithm 3, line 6). -/
noncomputable def mbNk (d : ℕ) (κn ϵ0 : ℝ) (k : ℕ) : ℕ := ⌈κn * d / mbEps ϵ0 k⌉₊

namespace Problem

/-- The warm-up of Algorithm 3, lines 2–3: query the `n₀` items `start, …, start + n₀ − 1` at the action
`b`, giving `D₀`, and let `(ŵ₀, β̂₀) = sel D₀`. -/
noncomputable def mbWarmup (I : Problem d) (b κn ϵ0 : ℝ) (sel : List (E d × ℤ) → E d × ℝ)
    (ω : ℕ → E d × ℝ) (start : ℕ) : MBState d :=
  let n0 := mbN0 κn ϵ0
  let D0 : List (E d × ℤ) :=
    List.ofFn fun i : Fin n0 => ((ω (start + i)).1, I.response (ω (start + i)) b)
  { c := sel D0, queries := n0, pos := start + n0 }

/-- One pass of the inner loop of Algorithm 3, lines 8–12 (arXiv:2110.01072v2, p.13): read the next
context `x`; if `|⟨x, ŵ_{k−1}⟩ − β̂_{k−1}| ≤ m_k`, query it at the action `b` and append `(x, y)` to `D_k`;
otherwise let it pass. -/
noncomputable def mbInnerStep (I : Problem d) (b m : ℝ) (c : E d × ℝ) (ω : ℕ → E d × ℝ)
    (s : MBInner d) : MBInner d :=
  let x := (ω s.pos).1
  if |⟪x, c.1⟫ - c.2| ≤ m then
    { D := s.D ++ [(x, I.response (ω s.pos) b)], pos := s.pos + 1 }
  else
    { D := s.D, pos := s.pos + 1 }

/-- Epoch `k ≥ 1` of Algorithm 3, lines 6–14: with `ϵ_k, m_k, n_k` of line 6 and `D_k = ∅`, run
`while |D_k| < n_k` the inner step, then `(ŵ_k, β̂_k) = sel D_k`. Returns `none` if the inner loop does
not halt. -/
noncomputable def mbEpoch (I : Problem d) (b κm κn ϵ0 : ℝ) (sel : List (E d × ℤ) → E d × ℝ)
    (ω : ℕ → E d × ℝ) (k : ℕ) (s : MBState d) : Option (MBState d) :=
  let m := mbMargin κm ϵ0 k
  let nk := mbNk d κn ϵ0 k
  (whileRun (fun t : MBInner d => t.D.length < nk) (fun t => some (I.mbInnerStep b m s.c ω t))
      { D := [], pos := s.pos }).map fun t =>
    { c := sel t.D, queries := s.queries + t.D.length, pos := t.pos }

/-- The state after the warm-up and the epochs `1, …, k` of Algorithm 3. -/
noncomputable def mbAfter (I : Problem d) (b κm κn ϵ0 : ℝ) (sel : List (E d × ℤ) → E d × ℝ)
    (ω : ℕ → E d × ℝ) (start : ℕ) : ℕ → Option (MBState d)
  | 0 => some (I.mbWarmup b κn ϵ0 sel ω start)
  | k + 1 => (I.mbAfter b κm κn ϵ0 sel ω start k).bind (I.mbEpoch b κm κn ϵ0 sel ω (k + 1))

/-- **Algorithm 3** (`MarginBasedActiveLearning(b, ε_a, δ_a, κ_m, κ_n, ϵ₀, β₀)`), arXiv:2110.01072v2,
p.13, run on the stream `ω` from item `start`, with the tie-breaking rule `sel` for the arg min of
lines 3 and 14: the warm-up, then epochs `k = 1, …, k₀`, returning `(ŵ_{k₀}, β̂_{k₀})`, the number of
queries `n₀ + Σ_k |D_k|` and the position after the last item read (queried or passed). It is `none`
if some inner loop does not halt on `ω`.

**Formalization Note** `δ_a` does not occur in the pseudocode (it enters only through the choice of
`κ_n`), and `β₀` enters only through the constraint `|β| ≤ β₀` of the arg min, i.e. through the
hypothesis `IsERMSelection β₀ sel`; neither is an argument here. -/
noncomputable def marginAL (I : Problem d) (b εa κm κn ϵ0 : ℝ) (sel : List (E d × ℤ) → E d × ℝ)
    (ω : ℕ → E d × ℝ) (start : ℕ) : Option (MBResult d) :=
  (I.mbAfter b κm κn ϵ0 sel ω start (mbK0 εa ϵ0)).map fun s =>
    { c := s.c, queries := s.queries, endPos := s.pos }

end Problem

end ActiveCtxSearch


