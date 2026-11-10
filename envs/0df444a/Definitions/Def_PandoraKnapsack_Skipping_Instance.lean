-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_Instance
-- name    : PandoraKnapsack_Skipping_Instance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:22:50.349192+00:00
-- url     : https://prove2.me/theorems/3b2a50f4-8109-423d-95b8-3a3603fd373f
-- title:
--   MPK instances on the rational size grid, effective values and truncated sizes
-- statement:
--   An instance of **multi-choice Pandora's Knapsack (MPK)** on the grid of Section 5 has $n$ items, $m$ choices per item and a capacity $T$. Item $i$ has a value $v_i$; its choice $j$ has a cost $p_i^j$ and a size law $F_i^j$, an arbitrary probability law on $\{0,1,\dots,T+1\}$, where $T+1$ stands for every size larger than the knapsack.
--
--   For a real $r$, $\Pr[s_i^j\le r]$ is the CDF of $F_i^j$ (zero for $r<0$) and $E[\min\{s_i^j,r\}]$ its truncated mean. The **effective value** is $w_{i,j,t}=v_i\Pr[s_i^j\le T-t]-p_i^j$ with $T-t$ a real subtraction (so $w_{i,j,t}=-p_i^j$ for $t>T$), and the **truncated expected size** is $\mu_{i,j,t}=E[\min\{s_i^j,t\}]$.
--
--   `IsValid` collects the standing assumptions: $T\ge1$, $p_i^j\ge0$, and every pair is profitable in an empty knapsack, $w_{i,j}=w_{i,j,0}=v_i\Pr[s_i^j\le T]-p_i^j>0$. Zero sizes and zero costs are allowed.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), Pandora's Knapsack via Simple Policies, supplied PDF (STOC 2027 submission), SHA256 45e5830b173d687c08d5175988af81bf660c693ff805b1d2e7bc213140d27a2d, §2, printed pp. 8–9 (PDF 10–11); §5 preamble and §5.1, printed p. 21 (PDF 23)

import Mathlib

namespace PandoraKnapsack.Skipping

/-- **Multi-choice Pandora's Knapsack (MPK) instance on the Section 5 grid.**

Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen (2026), *Pandora's Knapsack via Simple
Policies*, supplied PDF (SHA256 45e5830b…7a2d): model, §2, printed pp. 8–9 (PDF 10–11), and the
standing assumption of §5, printed p. 21 (PDF 23): "all item sizes (or times) are in
{0, 1, …, T + 1} and … the knapsack size is T … size T + 1 represents any size larger than the
knapsack".

There are `n` items and `m` choices per item. Item `i` has value `value i`; its choice `j` has
cost `cost i j` and size law `sizeLaw i j`, an arbitrary probability law on `{0, …, T + 1}`.

**Formalization Note.** Items and choices are indexed by `Fin n` and `Fin m` (the source's
`[n]`, `[m]`, shifted to start at `0`). The capacity `T` is a type parameter so that sizes live in
`Fin (T + 2)`; it is arbitrary, not fixed. The standing assumptions are collected in `IsValid`. -/
structure Instance (n m T : ℕ) where
  /-- The deterministic value `v_i` of item `i`. -/
  value : Fin n → ℝ
  /-- The deterministic cost `p_i^j` of choice `j` of item `i`, paid before the size is seen. -/
  cost : Fin n → Fin m → ℝ
  /-- The size law `F_i^j` of choice `j` of item `i`, on `{0, …, T + 1}`. -/
  sizeLaw : Fin n → Fin m → PMF (Fin (T + 2))

variable {n m T : ℕ}

/-- `Pr_{s ∼ F_i^j}[s ≤ r]` for a real threshold `r` (so it is `0` when `r < 0`). -/
noncomputable def cdf (I : Instance n m T) (i : Fin n) (j : Fin m) (r : ℝ) : ℝ :=
  ∑ s : Fin (T + 2), if ((s : ℕ) : ℝ) ≤ r then (I.sizeLaw i j s).toReal else 0

/-- The `r`-truncated expected size `E_{s ∼ F_i^j}[min{s, r}]`. -/
noncomputable def truncMean (I : Instance n m T) (i : Fin n) (j : Fin m) (r : ℝ) : ℝ :=
  ∑ s : Fin (T + 2), (I.sizeLaw i j s).toReal * min ((s : ℕ) : ℝ) r

/-- The effective value `w_{i,j,t} = v_i · Pr[s_i^j ≤ T − t] − p_i^j` of §5.1 (printed p. 21,
PDF 23). **Formalization Note.** `T − t` is a real subtraction, so for `t > T` the fitting
probability is `0` and `w_{i,j,t} = −p_i^j` (Appendix B.1 evaluates the same formula at `2τ > b`). -/
noncomputable def effWeight (I : Instance n m T) (i : Fin n) (j : Fin m) (t : ℕ) : ℝ :=
  I.value i * cdf I i j ((T : ℝ) - (t : ℝ)) - I.cost i j

/-- The truncated expected size `μ_{i,j,t} = E[min{s_i^j, t}]` of §5.1 (printed p. 21, PDF 23). -/
noncomputable def mu (I : Instance n m T) (i : Fin n) (j : Fin m) (t : ℕ) : ℝ :=
  truncMean I i j (t : ℝ)

/-- **Standing assumptions.** The capacity is a positive integer `T` (§5 rescales capacity `1`
to `T`); costs are nonnegative (they are costs paid up front, §2); and every item-choice pair is
profitable in the empty knapsack, `w_{i,j} = v_i · Pr[s_i^j ≤ T] − p_i^j > 0` (§2, printed p. 9,
PDF 11: "we assume w_{i,j} > 0 for every item-choice pair"). Zero sizes and zero costs are
allowed; no lower bound on the return on investment is assumed. -/
def IsValid (I : Instance n m T) : Prop :=
  0 < T ∧ (∀ i j, 0 ≤ I.cost i j) ∧ (∀ i j, 0 < effWeight I i j 0)

end PandoraKnapsack.Skipping


