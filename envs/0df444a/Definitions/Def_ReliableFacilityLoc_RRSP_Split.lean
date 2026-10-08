-- Prove2me | Definitions.Def_ReliableFacilityLoc_RRSP_Split
-- name    : ReliableFacilityLoc_RRSP_Split
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:17:14.025274+00:00
-- url     : https://prove2.me/theorems/d7d054de-e695-4d46-8c4f-b74060f8b707
-- title:
--   The split formulation (19a)–(19l) of (RSP$_i$): separate distance and probability assignments
-- statement:
--   In the proof of Proposition 4 the decision of (RSP$_i$) is split in two. For one customer $i$ with the data of (RSP$_i$):
--
--   1. $Y_{jr} = 1$ means that the facility serving at level $r$ has the transportation cost of facility $j$, and $Z_{jr} = 1$ means that it has the failure probability of facility $j$.
--   2. $(Y, Z, P, W)$ is **feasible** for the split formulation if $Y$ and $Z$ are both level assignments ((19b) = (4b)–(4d), (19c)–(19e), (19l)), $P$ and $W$ are the transitional probabilities and linearization variables computed from $Z$ by (19f)–(19k), and $Y$ and $Z$ put the emergency facility at the same level.
--   3. Writing $y(r)$ and $z(r)$ for the level-$r$ facilities of $Y$ and $Z$, the cost is
--
--   $$
--   G(Y,Z,P) = \sum_{r=0}^{R} \lambda_i\, d_{i,y(r)}\, P_{z(r),r} + \sum_{j=0}^{J-1}\sum_{r=0}^{R-1} \mu_{ij} Y_{jr},
--   $$
--
--   which in the array variables is $\sum_r \big(\sum_j \lambda_i d_{ij} Y_{jr}\big)\big(\sum_k W_{kr}\big) + \sum_{j<J}\sum_{r<R} \mu_{ij} Y_{jr}$.
--   4. A feasible point is **optimal** if its cost is at most the cost of every feasible point.
--
--   Adding the constraint (19m) $Y = Z$ gives back (RSP$_i$) with the same cost; without it the customer may combine the transportation cost of one facility with the failure probability of another. This is the relaxation through which the paper compares (RSP$_i$) and (RRSP$_i$).
--
--   **Formalization Note** The objective (19a) is printed as $\sum_j\sum_r \lambda_i d_{ij} W_{jr} + \sum \mu_{ij} Y_{jr}$ with $W$ tied to $Z$; read literally it charges the distance of the $Z$-facility and makes $Y$ irrelevant to the transportation cost. The cost formalized here is the one used in the proof of Lemma 1 (p. 39), where the distances $d_{iu}$, $d_{iv}$ belong to the $Y$-facilities $u$, $v$. The requirement that $Y$ and $Z$ put the emergency facility at the same level is not printed; it makes the levels of $Y$ and $Z$ pair up, as that proof does, and holds trivially under (19m). The printed (19g) has a stray index in $W_{i,k,r-1}$, read as $W_{k,r-1}$; (19c) is corrected like (4b).
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), pp. 37–38 (PDF 39–40), Appendix A.4, (19a)–(19m); cost G as used on p. 39 (PDF 41)

import Mathlib
import Definitions.Def_ReliableFacilityLoc_RRSP_RSP

open Finset

namespace ReliableFacilityLoc.RRSP

/-- Feasibility for the "split" formulation (19a)–(19l) of (RSP_i) (UCTC-FR-2010-02, Appendix A.4,
pp. 37–38, PDF 39–40). `Y j r = 1` means that the level-`r` facility has the transportation cost of
facility `j`; `Z j r = 1` means that it has the failure probability of facility `j`. Both are level
assignments ((19b) = (4b)–(4d), (19c)–(19e), (19l)); `P`, `W` are computed from `Z` by
(19f)–(19k); and `Y`, `Z` put the emergency facility at the same level.

Formalization Note: the last requirement is not printed. The proof of Lemma 1 (p. 39) pairs the
level-`r` facility `u` of `Y` with the level-`r` facility `j` of `Z`, which needs the two
assignments to occupy the same levels; for level assignments this is exactly "the emergency
facility is at the same level". With (19m) `Y = Z` it holds trivially. (19c) is corrected to sum
over all `j = 0, …, J`, as (4b) is. -/
def IsSplitFeasible {J R : ℕ} (q : Fin J → ℝ) (Y Z P W : Fin (J + 1) → Fin (R + 1) → ℝ) : Prop :=
  IsLevelAssignment Y ∧ IsLevelAssignment Z ∧ IsProbLinearization q Z P W ∧
    ∀ r, Y (Fin.last J) r = Z (Fin.last J) r

/-- The cost `G(Y, Z, P)` of the split formulation, as used in the proof of Lemma 1
(UCTC-FR-2010-02, Appendix A.4, p. 39, PDF 41):
`G = Σ_{r=0}^{R} λ_i d_{i,y(r)} P_{z(r),r} + Σ_{j=0}^{J-1} Σ_{r=0}^{R-1} µ_ij Y_jr`,
where `y(r)` and `z(r)` are the level-`r` facilities of `Y` and `Z`. In matrix form the level-`r`
transport term is `(Σ_j λ_i d_ij Y_jr) · (Σ_k W_kr)`, since `W_kr = P_kr Z_kr` and at most one `Z_kr`
is `1`.

Formalization Note: the objective (19a) is printed as `Σ_j Σ_r λ_i d_ij W_jr + Σ µ_ij Y_jr` with
`W` tied to `Z` by (19i), (19k); read literally it charges the distance of the `Z`-facility and
makes `Y` irrelevant to the transportation cost, contradicting the definition of `Y` ("the level r
facility … has the same transportation distance as facility j") and the cost difference computed in
the proof of Lemma 1 (`λ_i(P'_kr d_iu + P'_{j,r+1} d_iv − P_jr d_iu − P_{k,r+1} d_iv)`, with `u, v`
the `Y`-facilities). The objective formalized here is the one the proof uses. Under (19m) `Y = Z`
it coincides with (4a). -/
def splitObjective {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (mu : Fin J → ℝ)
    (Y W : Fin (J + 1) → Fin (R + 1) → ℝ) : ℝ :=
  ∑ r, (∑ j, lam * ReliableFacilityLoc.Supermod.dExt d phi j * Y j r) * (∑ k, W k r)
    + ∑ j : Fin J, ∑ r : Fin R, mu j * Y j.castSucc r.castSucc

/-- An optimal solution `(Y, Z, P, W)` of the split formulation (19a)–(19l)
(UCTC-FR-2010-02, Appendix A.4, p. 38, PDF 40): it is feasible and its cost `G` is at most the cost
of every feasible solution. -/
def IsSplitOptimal {J R : ℕ} (lam : ℝ) (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ)
    (mu : Fin J → ℝ) (Y Z P W : Fin (J + 1) → Fin (R + 1) → ℝ) : Prop :=
  IsSplitFeasible q Y Z P W ∧
    ∀ Y' Z' P' W' : Fin (J + 1) → Fin (R + 1) → ℝ, IsSplitFeasible q Y' Z' P' W' →
      splitObjective lam d phi mu Y W ≤ splitObjective lam d phi mu Y' W'

end ReliableFacilityLoc.RRSP


