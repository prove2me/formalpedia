-- Prove2me | Definitions.Def_CFLOutliers_Phi
-- name    : CFLOutliers_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:55.316759+00:00
-- url     : https://prove2.me/theorems/0a27cb82-6a16-497a-8451-7d182b906d9c
-- title:
--   Penalty potential $\Phi_\lambda$, optimal penalty assignments and the potential $\Phi^*_\lambda(F')$ of an open set
-- statement:
--   For a common rejection penalty $\lambda\ge 0$ the **penalty potential** of a solution is
--
--   $$\Phi_\lambda(S)=c(S)+\lambda\,r(S)=c(S)+\lambda\,(n-|C_S|).$$
--
--   For a fixed open set the algorithm always uses an **optimal penalty assignment**: a capacity-feasible assignment into $F_S$ minimizing $c_s+\lambda r$ among all capacity-feasible assignments into $F_S$ under the original capacities. For an open set $F'$,
--
--   $$\Phi^*_\lambda(F')=f(F')+\min\{c_s(\sigma)+\lambda r(\sigma):\ \sigma\text{ a capacity-feasible assignment into }F'\}$$
--
--   is the potential of the solution the algorithm computes for $F'$ (the open set determines the value). Rejecting every client is always admissible, so the minimum exists.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §1.2, p.3; §2, p.4; §3, p.7

import Mathlib
import Definitions.Def_CFLOutliers_Sol

namespace CFLOutliers

open Finset

/-- **Penalty potential** `Φ_λ(S) = c(S) + λ r(S)`, `r(S) = n − |C_S|`.
Dabas, arXiv:2611.04094, §1.2, p.3 and §2, p.4. -/
def Phi {I : Inst} (lam : ℝ) (S : Sol I) : ℝ := cost S + lam * rej S

/-- Penalized service cost `c_s + λ r` of an assignment (§3, p.7). -/
def penCost (I : Inst) (lam : ℝ) (σ : Fin I.n → Option (Fin I.m)) : ℝ :=
  acs I σ + lam * arej I σ

/-- **Optimal penalty assignment** (§3, p.7): `S` is capacity-feasible and its assignment
minimizes `c_s + λ r` among all capacity-feasible assignments into the same open set `F_S`
("For a current open set F_S, we always compute an assignment minimizing c_s(S) + λ r(S) under
the original capacities"). -/
def PenaltyOptimal {I : Inst} (lam : ℝ) (S : Sol I) : Prop :=
  S.CapFeasible ∧ ∀ σ' : Fin I.n → Option (Fin I.m),
    AssignInto S.openSet σ' → CapOK I σ' → penCost I lam S.σ ≤ penCost I lam σ'

open Classical in
/-- The capacity-feasible assignments into an open set `F'`. -/
noncomputable def feasAssign (I : Inst) (F' : Finset (Fin I.m)) :
    Finset (Fin I.n → Option (Fin I.m)) :=
  univ.filter (fun σ => AssignInto F' σ ∧ CapOK I σ)

/-- Rejecting every client is a capacity-feasible assignment into any open set. -/
theorem reject_all_mem_feasAssign (I : Inst) (F' : Finset (Fin I.m)) :
    (fun _ => none) ∈ feasAssign I F' := by
  classical
  unfold feasAssign
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j i h => ?_, fun i => ?_⟩
  · simp at h
  · simp [aload]

/-- **Potential of an open set** `Φ*_λ(F') = f(F') + min_σ (c_s + λ r)(σ)`, the minimum over
capacity-feasible assignments into `F'` under the original capacities: the potential of the
solution that the algorithm computes for the open set `F'` (§3, p.7: "the open set determines the
value of the current solution"). -/
noncomputable def PhiStar (I : Inst) (lam : ℝ) (F' : Finset (Fin I.m)) : ℝ :=
  ∑ i ∈ F', I.f i +
    (feasAssign I F').inf' ⟨_, reject_all_mem_feasAssign I F'⟩ (penCost I lam)

end CFLOutliers


