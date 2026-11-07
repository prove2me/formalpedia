-- Prove2me | Definitions.Def_RGMISFast_rankCharge
-- name    : RGMISFast_rankCharge
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:27:00.048655+00:00
-- url     : https://prove2.me/theorems/cd0ec80e-08a0-4895-9586-c76e55941f10
-- title:
--   Intervals $a_m=e^2c^{-m}$, $M$, capped ranks and rank charges $S(A,a)$
-- statement:
--   The analysis splits time at
--   $$
--   a_0=e^2,\qquad c=1+\frac1{2e^2},\qquad a_m=a_0c^{-m},\qquad M=\min\Big\{m\ge0: a_m\le\frac1{16\Delta}\Big\},
--   $$
--   where $\Delta$ bounds the degrees. The **capped rank** is $\bar r(v)=\min\{r(v),a_0\}$, and for $0<a\le a_0$ and $A\subseteq V(G)$ the **rank charge** is
--   $$
--   S(A,a)=\frac1a\sum_{v\in A}\bar r(v),\qquad S_m(A)=S(A,a_m)\quad(0\le m\le M).
--   $$
--   The rank cutoffs are $b_0=\infty$ and $b_i=a_{i-1}=ca_i$ for $i\ge1$.
--
--   The charges $S_m$ of the tree prefixes are the potential of the deterministic size bound (Proposition 4.1).
--
--   **Formalization Note** $M$ is the least element of a set of natural numbers, nonempty for $\Delta\ge1$ because $c>1$; the statements that use $M$ assume $\Delta\ge2$. $b_i$ lives in $\mathbb R\cup\{+\infty\}$.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), eq. (6), p.11 (PDF p.13); eq. (7) and r̄, p.12 (PDF p.14); b_i, p.14 (PDF p.16)

import Mathlib

set_option autoImplicit false

namespace RGMISFast

/-- `a₀ = e²` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast
at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), eq. (6), p.11). -/
noncomputable def a0 : ℝ := Real.exp 2

/-- `c = 1 + 1/(2e²)` (eq. (6), p.11). -/
noncomputable def c : ℝ := 1 + 1 / (2 * Real.exp 2)

/-- The interval ends `a_m = a₀ c^{−m}` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), eq. (6), p.11): `e² = a₀ > a₁ > a₂ > ⋯`. -/
noncomputable def am (m : ℕ) : ℝ := a0 * (c ^ m)⁻¹

/-- `M = min{m ≥ 0 : a_m ≤ 1/(16∆)}` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), eq. (6), p.11).

**Formalization Note** The minimum is `sInf` of a set of natural numbers. For `∆ ≥ 1` the set is
nonempty because `c > 1` and `a_m → 0`, so `sInf` is its least element; every statement using
`M` assumes `∆ ≥ 2`. (For `∆ = 0` the threshold `1/(16·0)` is `0` in Lean, the set is empty and
`sInf` returns `0`; that case is never used.) -/
noncomputable def Mof (Δ : ℕ) : ℕ := sInf {m : ℕ | am m ≤ 1 / (16 * (Δ : ℝ))}

/-- The capped rank `r̄(v) = min{r(v), a₀}` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran,
*Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256
e93cdfec…), §2.1, p.12). -/
noncomputable def rbar {V : Type*} (r : V → ℝ) (v : V) : ℝ := min (r v) a0

/-- The rank charge `S(A, a) = (1/a) Σ_{v∈A} r̄(v)` for `0 < a ≤ a₀` (Dalirrooyfard, Makarychev,
Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*, STOC 2027 submission
(manuscript sha256 e93cdfec…), eq. (7), p.12).

**Formalization Note** Defined for every real `a` by the same formula; every statement uses it
with `a = a_m ∈ (0, a₀]`. -/
noncomputable def S {V : Type*} (r : V → ℝ) (A : Finset V) (a : ℝ) : ℝ :=
  (1 / a) * ∑ v ∈ A, rbar r v

/-- `S_m(A) = S(A, a_m)` for `0 ≤ m ≤ M` (eq. (7), p.12). -/
noncomputable def Sm {V : Type*} (r : V → ℝ) (A : Finset V) (m : ℕ) : ℝ := S r A (am m)

/-- The rank cutoff `b_i` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy
MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §3, p.14):
`b_i = ∞` for `i = 0`, and `b_i = a_{i−1} = c·a_i` for `i ≥ 1`.

**Formalization Note** The value lies in `WithTop ℝ`, with `b₀ = ⊤ = ∞`. -/
noncomputable def b (i : ℕ) : WithTop ℝ := if i = 0 then ⊤ else ((am (i - 1) : ℝ) : WithTop ℝ)

end RGMISFast


