-- Prove2me | Definitions.Def_ChoresEFX_BrbiRun
-- name    : ChoresEFX_BrbiRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:06:08.911917+00:00
-- url     : https://prove2.me/theorems/2a37ba1d-64f4-4e36-b337-de2dab3dd759
-- title:
--   Balanced Reservation and Block Insertion: the factor $\alpha_B$ and the run relation of Algorithm 5
-- statement:
--   The factor of Theorem 4.1 is
--
--   $$\alpha_B(m,n,k)=\max\left\{1,\frac{\lceil(m-kn)/n\rceil}{k}\right\}.$$
--
--   A **run of BRBI** with $m\le kn$ returns any complete allocation with $|X_i|\le k$. With $m>kn$ it does the following:
--
--   1. It chooses balanced integers $r_i\ge0$ with $\sum_ir_i=m-kn$ and $|r_i-r_j|\le1$.
--   2. In the order $i=n,\dots,1$, agent $i$ reserves a set $E_i$ of $r_i$ cheapest chores among those remaining, according to $c_i$.
--   3. It partitions what is left into $n$ base bundles of size $k$, assigned bijectively to the agents.
--   4. For $i=1,\dots,n$, with $j\in\arg\min_h c_i(X_h)$: if $j=i$ then $X_i\leftarrow X_i\cup E_i$, and otherwise $(X_i,X_j)\leftarrow(X_j\cup E_i,X_i)$.
--
--   This is the procedure used for instances with few chores.
--
--   **Formalization Note** The set remaining when $i$ reserves is written as all chores minus $E_h$ for later agents $h$. Every choice is free, so a statement about every run is the strongest reading.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Theorem 4.1, p.13; Algorithm 5, p.14

import Mathlib
import Definitions.Def_ChoresEFX_IsAlphaEFX

namespace ChoresEFX

open Finset

/-- **The factor of Theorem 4.1**, `α_B(m, n, k) = max{1, ⌈(m − kn)/n⌉ / k}`, p.13.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…). The ceiling is the integer ceiling of a real number. -/
noncomputable def alphaB (m n k : ℕ) : ℝ :=
  max 1 ((⌈((m : ℝ) - (k : ℝ) * (n : ℝ)) / (n : ℝ)⌉ : ℤ) / (k : ℝ))

/-- **The reservations of BRBI**, Algorithm 5, lines 4–9, p.14 (Qin et al., STOC 2027 submission).
Balanced integers `r_i` with `∑ r_i = m − kn` and `|r_i − r_j| ≤ 1`; in the order `i = n, …, 1`, `E_i` is
a set of the `r_i` cheapest chores according to `c_i` among those not reserved by later agents.

**Formalization Note.** The remaining set `R` when agent `i` reserves is written directly as all chores
minus `E_h` for `h > i`. Ties are free (paper.md decision 8). -/
def IsReservation {n m : ℕ} (c : Fin n → Fin m → ℝ) (k : ℕ) (r : Fin n → ℕ)
    (E : Fin n → Finset (Fin m)) : Prop :=
  (∑ i, r i : ℕ) + k * n = m ∧ (∀ i j, r i ≤ r j + 1) ∧
    ∀ i, E i ⊆ univ \ (univ.filter (fun h => i < h)).biUnion E ∧ (E i).card = r i ∧
      ∀ e ∈ E i, ∀ g ∈ (univ \ (univ.filter (fun h => i < h)).biUnion E) \ E i, c i e ≤ c i g

/-- **One insertion of BRBI**, Algorithm 5, lines 13–18, p.14 (Qin et al., STOC 2027 submission):
`j ∈ argmin_h c_i(X_h)` over all `h`, including `i`; if `j = i` then `X_i ← X_i ∪ E_i`, otherwise
`(X_i, X_j) ← (X_j ∪ E_i, X_i)`. -/
def InsertStep {n m : ℕ} (c : Fin n → Fin m → ℝ) (E : Fin n → Finset (Fin m)) (i : Fin n)
    (X Y : Fin n → Finset (Fin m)) : Prop :=
  ∃ j, (∀ h, cost c i (X j) ≤ cost c i (X h)) ∧
    ((j = i ∧ Y = Function.update X i (X i ∪ E i)) ∨
      (j ≠ i ∧ Y = Function.update (Function.update X i (X j ∪ E i)) j (X i)))

/-- **A run of BRBI**, Algorithm 5, p.14 (Qin et al., STOC 2027 submission), with output `X`.

If `m ≤ kn`, any complete allocation with `|X_i| ≤ k`. Otherwise reservations, any partition of what
remains into `n` base bundles of size `k`, assigned bijectively to the agents, and the insertions for
`i = 1, …, n` (here `0, …, n − 1`).

**Formalization Note.** A family `X₀ : Fin n → Finset (Fin m)` with these properties is a partition and
a bijection at once. `Xs t` is the allocation after the first `t` insertions. Every choice is free, so a
statement about every run is the strongest reading (paper.md decision 8). -/
def BrbiRun {n m : ℕ} (c : Fin n → Fin m → ℝ) (k : ℕ) (X : Fin n → Finset (Fin m)) : Prop :=
  if m ≤ k * n then
    (∀ g, ∃! i, g ∈ X i) ∧ ∀ i, (X i).card ≤ k
  else
    ∃ (r : Fin n → ℕ) (E : Fin n → Finset (Fin m)) (Xs : ℕ → Fin n → Finset (Fin m)),
      IsReservation c k r E ∧
      (∀ i, (Xs 0 i).card = k) ∧
      (∀ i j, i ≠ j → Disjoint (Xs 0 i) (Xs 0 j)) ∧
      univ.biUnion (Xs 0) = univ \ univ.biUnion E ∧
      (∀ i : Fin n, InsertStep c E i (Xs i.val) (Xs (i.val + 1))) ∧
      X = Xs n

end ChoresEFX


