-- Prove2me | Definitions.Def_MPBSelect_Problem_W
-- name    : MPBSelect_Problem_W
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:26:28.009651+00:00
-- url     : https://prove2.me/theorems/189e7e9e-014d-4284-a0ec-2b7fd1612bd9
-- title:
--   The gaps $d_j$ (9) and the balance weights $W_i(\theta_b)$ (17)
-- statement:
--   The **preference-probability gap** of solution $j$ is
--   $$
--   d_j=\sum_{b=1}^B p_b\,\mathbf 1\{i^*=i^b\}-\sum_{b=1}^B p_b\,\mathbf 1\{j=i^b\},
--   $$
--   which is positive for $j\ne i^*$. The **balance weight** of a pair $(i,\theta_b)\in\Xi$ is
--   $$
--   W_i(\theta_b)=\begin{cases}\max\Big\{\min\big(\min_{j\ne i^*}d_j,\ \tfrac{d_i}{2}\big)\big/p_b,\ 1\Big\}, & \theta_b\in\Theta_{i^*},\\[4pt] \max\{d_i/p_b,\ 1\}, & \theta_b\notin\Theta_{i^*},\end{cases}
--   $$
--   where $\theta_b\in\Theta_{i^*}$ means $i^b=i^*$. The division by $p_b$ applies to the whole inner minimum. $W_i(\theta_b)$ measures how critical it is, for the outer-level selection of $i^*$, to misidentify $i$ as the conditional optimum at $\theta_b$; it is at least $1$.
--
--   **Formalization Note** The page also sets $W_i(\theta_b)=\infty$ off $\Xi$; problem (20) and Theorem 3 use $W$ only on $\Xi$, so $W$ is the real formula (17) at every pair and is only evaluated on $\Xi$. $\min_{j\ne i^*}d_j$ is `Finset.inf'` over the nonempty set $\{j\ne i^*\}$ (nonempty because $k\ge2$, proved in the file).
-- source:
--   Kim, Kim, Song, Selection of the Most Probable Best, arXiv:2207.07533v2, §4.1, p.11, (9); Theorem 2, p.15, (17)

import Mathlib
import Definitions.Def_MPBSelect_Problem

namespace MPBSelect

open Finset

/-- **Preference-probability gap `d_j` (9).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, §4.1, (9), p.11:
"dj := Σ_{b=1}^B pb 1{i∗ = i^b} − Σ_{b=1}^B pb 1{j = i^b}". -/
noncomputable def Problem.d {k B : ℕ} (P : Problem k B) (j : Fin k) : ℝ :=
  prefProb P.p P.ib P.istar - prefProb P.p P.ib j

/-- The set `{j : j ≠ i*}` is nonempty because `k ≥ 2`. -/
theorem Problem.ne_istar_nonempty {k B : ℕ} (P : Problem k B) :
    (univ.filter (fun j : Fin k => j ≠ P.istar)).Nonempty := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr P.two_le_k
  obtain ⟨j, hj⟩ := exists_ne P.istar
  exact ⟨j, by simp [hj]⟩

/-- `min_{j ≠ i*} d_j`, the smallest preference-probability gap (used in (17)). -/
noncomputable def Problem.minD {k B : ℕ} (P : Problem k B) : ℝ :=
  (univ.filter (fun j : Fin k => j ≠ P.istar)).inf' P.ne_istar_nonempty P.d

/-- **Balance weight `W_i(θ_b)` (17).**
Kim, Kim, Song, *Selection of the Most Probable Best*, arXiv:2207.07533v2, Theorem 2, (17),
p.15: for each `(i, θ_b) ∈ Ξ`,
`W_i(θb) := max{ min( min_{j≠i∗} dj , di/2 ) / pb , 1 }` if `θb ∈ Θ_{i∗}`, and
`W_i(θb) := max{ di/pb , 1 }` if `θb ∉ Θ_{i∗}`.

`θ_b ∈ Θ_{i*}` (the favorable set (3), p.7) means `i* = i^b`.

**Formalization Note** The page also sets `W_i(θ_b) := ∞` for `(i, θ_b) ∉ Ξ`; problem (20) and
Theorem 3 only use `W` on `Ξ`, so `W` is the real-valued formula (17) at every pair and is only
ever evaluated on `Ξ`. The division by `p_b` applies to the whole inner `min`. -/
noncomputable def Problem.W {k B : ℕ} (P : Problem k B) (i : Fin k) (b : Fin B) : ℝ :=
  if P.ib b = P.istar then max (min P.minD (P.d i / 2) / P.p b) 1
  else max (P.d i / P.p b) 1

end MPBSelect


