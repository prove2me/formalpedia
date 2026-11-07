-- Prove2me | Definitions.Def_AlmostMMS_IsPartialSelection
-- name    : AlmostMMS_IsPartialSelection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:25.273046+00:00
-- url     : https://prove2.me/theorems/4b8c7705-01b3-425b-9b92-1cf21bc7b85d
-- title:
--   Theorem 4.1, p.28 — the output of partial selection
-- statement:
--   For a partition $M=E+S$ and a set $V$ of agents, a set $A$ with choices $j_i\in[d]$ is an **output of partial selection** if $A\subseteq V$ and, writing $\pi_i=\pi_{i,j_i}$:
--
--   1. each $\pi_i$ has $\Delta(\pi_i)=0$ and $\pi^S_{i,j_i}=\emptyset$;
--   2. the $\pi_i$, $i\in A$, are simultaneously satisfied by distinct items of $E$, and for every $0\le\ell\le m$,
--   $$
--   \sum_{i\in A}P_i(\pi_i,\ell)\le\frac1{|V|}\sum_{i\in V}\sum_{j=1}^dP_i(\pi^E_{i,j},\ell);
--   $$
--   3. with $\rho_A=8+16q\log n$,
--   $$
--   |A|\ge d-|S|-\frac{q(q-1)}{|V|}\sum_{i\in V}T_i-\rho_A.
--   $$
--   These are the three bullets of Theorem 4.1. They are named because Corollaries 4.1 and 5.1 start from such an output.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Theorem 4.1, p.28

import Mathlib
import Definitions.Def_AlmostMMS_load
import Definitions.Def_AlmostMMS_headCount
import Definitions.Def_AlmostMMS_deficit
import Definitions.Def_AlmostMMS_mmsProfileIn
import Definitions.Def_AlmostMMS_SimulSatisfied

namespace AlmostMMS

open Finset

/-- **The output of partial selection** (the three bullets of Theorem 4.1, p.28), for the partition
`M = E + S` with `E = Sᶜ` and agents `V`: `A ⊆ V`, and the profile `π_i = π_{i,j_i}` of each `i ∈ A` has
zero deficit and no `S`-demand; the profiles are simultaneously satisfied by distinct items of `E`; each
prefix load is at most `(1/|V|) ∑_{i ∈ V} ∑_{j ∈ [d]} P_i(π^E_{i,j}, ℓ)`; and
`|A| ≥ d - |S| - (q(q-1)/|V|) ∑_{i ∈ V} T_i - ρ_A` with `ρ_A = 8 + 16q log n`, `log` base `2`.
Feige, Grinberg, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…).

**Formalization Note.** The choice `j : Fin n → Fin d` is read on `A` only. -/
def IsPartialSelection {n m d : ℕ} (J : OrderedInstance n m d) (q : ℕ) (S : Finset (Fin m))
    (V A : Finset (Fin n)) (j : Fin n → Fin d) : Prop :=
  A ⊆ V ∧
  (∀ i ∈ A, deficit q (mmsProfile J q i (j i)) = 0 ∧ mmsProfileIn J q i (j i) S = 0) ∧
  SimulSatisfied J.v A (fun i => mmsProfile J q i (j i)) Sᶜ ∧
  (∀ ℓ ≤ m, ((∑ i ∈ A, load J.v i (mmsProfile J q i (j i)) ℓ : ℕ) : ℝ) ≤
    (1 / (V.card : ℝ)) * ∑ i ∈ V, ∑ j' : Fin d, (load J.v i (mmsProfileIn J q i j' Sᶜ) ℓ : ℝ)) ∧
  (d : ℝ) - (S.card : ℝ) - ((q : ℝ) * ((q : ℝ) - 1) / (V.card : ℝ)) * ∑ i ∈ V, tailVal J.v q i
    - (8 + 16 * (q : ℝ) * Real.logb 2 (n : ℝ)) ≤ (A.card : ℝ)

end AlmostMMS


