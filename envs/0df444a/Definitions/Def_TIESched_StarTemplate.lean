-- Prove2me | Definitions.Def_TIESched_StarTemplate
-- name    : TIESched_StarTemplate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:45:49.848678+00:00
-- url     : https://prove2.me/theorems/53d4402a-67d6-49b9-bdec-b5b14a607957
-- title:
--   Star template, expected center load $F(\rho)$ and expected optimum $\mathrm{OPT}(\rho)$
-- statement:
--   A **star template** consists of a star with center $v_0$ and leaves $v_1,\dots,v_{m-1}$, an integer $L\ge1$, a finite $H>1$ and pairwise disjoint sets $J_0,\dots,J_{m-1}$ of $L$ jobs each; $J_r$ ($r\ge1$) belongs to the edge $\{v_0,v_r\}$ and $J_0$ to the center, and $J=\bigcup_r J_r$. For a bijection $\sigma$ from vertices to machines, the processing times are
--   $$p^\sigma_{ij}=\begin{cases}1/L,& i\in\{\sigma(v_0),\sigma(v_r)\}\\ H/L,&\text{otherwise}\end{cases}\ (j\in J_r,\ r\ge1),\qquad p^\sigma_{ij}=\begin{cases}1/L,& i=\sigma(v_0)\\ H/L,&\text{otherwise}\end{cases}\ (j\in J_0).$$
--   With $\sigma$ uniform and $S_\rho\subseteq J$ containing each job independently with probability $\rho$, the **expected center load** of an allocation family $x$ and the **expected optimum** are
--   $$F(\rho)=\mathbb E_{\sigma,S_\rho}\Big[\frac1L\sum_{j\in S_\rho}x^{S_\rho}_{\sigma(v_0),j}(p^\sigma_{S_\rho})\Big],\qquad \mathrm{OPT}(\rho)=\mathbb E_{\sigma,S_\rho}\big[\mathrm{OPT}(p^\sigma_{S_\rho})\big].$$
--
--   These are the random hard instances of §4.
--
--   **Formalization Note.** Vertices are `Fin m` with center `0`; the job labels are arbitrary. Both expectations are written as explicit finite sums $\frac1{m!}\sum_\sigma\sum_{S\subseteq J}\rho^{|S|}(1-\rho)^{|J|-|S|}(\cdots)$, polynomials defined for every real $\rho$; $F'(0)$ is the derivative of this polynomial at $0$.
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), §4, pp.11–12; §4.1, p.12; f_σ p.14

import Mathlib
import Definitions.Def_TIESched_FracMech

set_option autoImplicit false

namespace TIESched

/-- **Star template** of §4 (arXiv:2611.05142, §4, pp.11–12): a star with center `v_0` and leaves
`v_1, …, v_{m−1}`, an integer `L ≥ 1`, a finite parameter `H > 1`, and pairwise disjoint sets
`J_0, …, J_{m−1}` of `L` distinct jobs each: `J_r` is attached to the edge `{v_0, v_r}` for
`r ∈ [m−1]` and `J_0` to the center.

**Formalization Note.** The vertices are `Fin m`, with `v_r = r` and center `0`; `group r` is
`J_r`. Job labels are arbitrary natural numbers (any pairwise disjoint sets of `L` labels). -/
structure StarTemplate (m : ℕ) where
  /-- the group size `L` -/
  L : ℕ
  one_le_L : 1 ≤ L
  /-- the large processing-time parameter `H` -/
  H : ℝ
  one_lt_H : 1 < H
  /-- the job groups `J_0, …, J_{m−1}` -/
  group : Fin m → Finset ℕ
  card_group : ∀ r, (group r).card = L
  disjoint_group : Pairwise (fun r s => Disjoint (group r) (group s))

namespace StarTemplate

variable {m : ℕ} [NeZero m]

/-- The set `J = ⋃_{r=0}^{m−1} J_r` of all `mL` candidate jobs (p.12). -/
def jobs (T : StarTemplate m) : Finset ℕ :=
  Finset.univ.biUnion T.group

open Classical in
/-- Processing times `p^σ_ij` of the star instance for a bijection `σ` from vertices to machines
(arXiv:2611.05142, p.12): for an edge job `j ∈ J_r`, `p^σ_ij = 1/L` if `i ∈ {σ(v_0), σ(v_r)}` and
`H/L` otherwise; for `j ∈ J_0`, `p^σ_ij = 1/L` if `i = σ(v_0)` and `H/L` otherwise.

**Formalization Note.** Both cases are the single rule "`1/L` if `i = σ(v_0)` or `i = σ(v_r)` for the
group `J_r` containing `j`" (for `j ∈ J_0` the two conditions coincide). The value at a label
outside `J` is irrelevant. -/
noncomputable def times (T : StarTemplate m) (σ : Equiv.Perm (Fin m)) (j : ℕ) (i : Fin m) : ℝ :=
  if i = σ 0 ∨ ∃ r, j ∈ T.group r ∧ i = σ r then 1 / (T.L : ℝ) else T.H / T.L

/-- The star report `p^σ_S` on a job set `S` (p.12: the instance `(S, p^σ_S)`). -/
noncomputable def report (T : StarTemplate m) (σ : Equiv.Perm (Fin m)) (S : Finset ℕ) :
    Fin m → S → ℝ :=
  fun i j => T.times σ j i

/-- Normalized center load `f_σ(S) = (1/L) Σ_{j ∈ S} x^S_{σ(v_0), j}(p^σ_S)` (p.14). -/
noncomputable def centerLoad (T : StarTemplate m) (x : AllocFamily m) (σ : Equiv.Perm (Fin m))
    (S : Finset ℕ) : ℝ :=
  (1 / (T.L : ℝ)) * ∑ j : S, x S (T.report σ S) (σ 0) j

/-- **Expected center load** `F(ρ) = E_{σ, S_ρ}[(1/L) Σ_{j ∈ S_ρ} x^{S_ρ}_{σ(v_0), j}(p^σ_{S_ρ})]`
(arXiv:2611.05142, §4.1, p.12), where `σ` is a uniformly random bijection and `S_ρ ⊆ J` contains
each job independently with probability `ρ`.

**Formalization Note.** The expectation is written as the explicit finite sum
`(1/m!) Σ_σ Σ_{S ⊆ J} ρ^{|S|} (1−ρ)^{|J|−|S|} f_σ(S)`, which is a polynomial in `ρ` and is defined
for every real `ρ`; it is the expectation for `ρ ∈ [0,1]`. `F′(0)` is `deriv F 0`. -/
noncomputable def F (T : StarTemplate m) (x : AllocFamily m) (ρ : ℝ) : ℝ :=
  (Nat.factorial m : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin m), ∑ S ∈ T.jobs.powerset,
    ρ ^ S.card * (1 - ρ) ^ (T.jobs.card - S.card) * T.centerLoad x σ S

/-- **Expected integral optimum** `OPT(ρ) = E_{σ, S_ρ}[OPT(I_ρ)]` (arXiv:2611.05142, §4.1, p.12), as
the same explicit finite sum as `F`. -/
noncomputable def optRho (T : StarTemplate m) (ρ : ℝ) : ℝ :=
  (Nat.factorial m : ℝ)⁻¹ * ∑ σ : Equiv.Perm (Fin m), ∑ S ∈ T.jobs.powerset,
    ρ ^ S.card * (1 - ρ) ^ (T.jobs.card - S.card) * OPT (T.report σ S)

end StarTemplate

end TIESched


