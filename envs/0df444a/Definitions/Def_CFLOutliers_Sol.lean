-- Prove2me | Definitions.Def_CFLOutliers_Sol
-- name    : CFLOutliers_Sol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:36:12.401647+00:00
-- url     : https://prove2.me/theorems/2ca6a537-eebf-48eb-9e8e-da018113029d
-- title:
--   Solutions, loads, capacity feasibility and the costs $c_f$, $c_s$, $c$, $r$
-- statement:
--   A **solution** $S$ consists of a set $F_S$ of open facilities and an assignment that sends each client $j$ either to a facility $\sigma_S(j)$ or to "rejected". The served clients form $C_S$. The **load** of facility $i$ is $w_i=|\sigma_S^{-1}(i)|$.
--
--   $S$ is **capacity-feasible** if every served client is assigned to an open facility and $|\sigma_S^{-1}(i)|\le u_i$ for every facility $i$ (hard capacities: each facility is opened at most once). The costs are
--
--   $$c_f(S)=\sum_{i\in F_S}f_i,\qquad c_s(S)=\sum_{j\in C_S}c_{j,\sigma_S(j)},\qquad c(S)=c_f(S)+c_s(S),\qquad r(S)=n-|C_S|.$$
--
--   An open facility serving no client is allowed and pays its opening cost. The **empty solution** opens nothing and rejects every client.
--
--   **Formalization Note** The assignment is a function `Fin n → Option (Fin m)` (`none` = rejected); the same quantities are also defined for a bare assignment (`aload`, `aserved`, `acs`, `arej`), which the penalty search minimizes over. $r(S)$ is a real number.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §1 "Problem and result", p.2

import Mathlib
import Definitions.Def_CFLOutliers_Inst

namespace CFLOutliers

open Finset

/-- **A solution** (p.2): a set `openSet = F_S` of open facilities and an assignment
`σ j = some i` (client `j` served by `i`) or `σ j = none` (client `j` rejected, an outlier).
Dabas, arXiv:2611.04094, §1 "Problem and result", p.2.

**Formalization Note.** The served set `C_S` is the set of clients with `σ j ≠ none`. Whether
`σ` maps into `openSet` and respects capacities is the predicate `Sol.CapFeasible`; an open
facility serving nobody is allowed and pays its opening cost. -/
@[ext] structure Sol (I : Inst) where
  /-- the open facilities `F_S` -/
  openSet : Finset (Fin I.m)
  /-- the assignment; `none` means rejected -/
  σ : Fin I.n → Option (Fin I.m)

/-- `Sol I` is the product of the open sets and the assignments. -/
def Sol.equiv (I : Inst) : Sol I ≃ Finset (Fin I.m) × (Fin I.n → Option (Fin I.m)) where
  toFun S := (S.openSet, S.σ)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (I : Inst) : Fintype (Sol I) := Fintype.ofEquiv _ (Sol.equiv I).symm

/-- Load `|σ⁻¹(i)|` of an assignment at facility `i`. -/
def aload {I : Inst} (σ : Fin I.n → Option (Fin I.m)) (i : Fin I.m) : ℕ :=
  (univ.filter (fun j => σ j = some i)).card

/-- Clients served by an assignment. -/
def aserved {I : Inst} (σ : Fin I.n → Option (Fin I.m)) : Finset (Fin I.n) :=
  univ.filter (fun j => (σ j).isSome)

/-- Service cost `Σ_{j served} c_{σ(j) j}` of an assignment. -/
def acs (I : Inst) (σ : Fin I.n → Option (Fin I.m)) : ℝ :=
  ∑ j, (σ j).elim 0 (fun i => I.cFC i j)

/-- Number of rejected clients `n − |C|` of an assignment, as a real number. -/
def arej (I : Inst) (σ : Fin I.n → Option (Fin I.m)) : ℝ :=
  (I.n : ℝ) - ((aserved σ).card : ℝ)

/-- The assignment uses only facilities of `F'`. -/
def AssignInto {I : Inst} (F' : Finset (Fin I.m)) (σ : Fin I.n → Option (Fin I.m)) : Prop :=
  ∀ j i, σ j = some i → i ∈ F'

/-- The assignment respects every hard capacity: `|σ⁻¹(i)| ≤ u_i`. -/
def CapOK (I : Inst) (σ : Fin I.n → Option (Fin I.m)) : Prop :=
  ∀ i, aload σ i ≤ I.u i

/-- The load `w_i` of a solution at facility `i`. -/
def load {I : Inst} (S : Sol I) (i : Fin I.m) : ℕ := aload S.σ i

/-- The served clients `C_S`. -/
def served {I : Inst} (S : Sol I) : Finset (Fin I.n) := aserved S.σ

/-- **Capacity feasibility** (p.2): every served client is assigned to an open facility and
`|σ_S⁻¹(i)| ≤ u_i` for every facility. -/
def Sol.CapFeasible {I : Inst} (S : Sol I) : Prop := AssignInto S.openSet S.σ ∧ CapOK I S.σ

/-- Opening cost `c_f(S) = Σ_{i ∈ F_S} f_i`. -/
def cf {I : Inst} (S : Sol I) : ℝ := ∑ i ∈ S.openSet, I.f i

/-- Service cost `c_s(S) = Σ_{j ∈ C_S} c_{j, σ_S(j)}`. -/
def cs {I : Inst} (S : Sol I) : ℝ := acs I S.σ

/-- Cost `c(S) = c_f(S) + c_s(S)`. -/
def cost {I : Inst} (S : Sol I) : ℝ := cf S + cs S

/-- Rejection count `r(S) = n − |C_S|`, as a real number. -/
def rej {I : Inst} (S : Sol I) : ℝ := arej I S.σ

/-- The empty solution: no open facility, every client rejected. -/
def Sol.empty (I : Inst) : Sol I := ⟨∅, fun _ => none⟩

end CFLOutliers


