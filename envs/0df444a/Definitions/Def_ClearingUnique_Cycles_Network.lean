-- Prove2me | Definitions.Def_ClearingUnique_Cycles_Network
-- name    : ClearingUnique_Cycles_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:27.362232+00:00
-- url     : https://prove2.me/theorems/f07b8fa7-d8a3-4d78-a2b9-f8f24f0909ee
-- title:
--   §2, pp. 5–6 — financial network and standing division-rule assumptions
-- statement:
--   A **financial network** $N=(I,z,L,d)$ has a finite set $I$ of agents, nonnegative endowments $z_i$, nonnegative liabilities $L_{ij}$ with $L_{ii}=0$, and a division rule $d^i$ for each agent. The total liability is $\bar L_i=\sum_jL_{ij}$. For an estate $E\ge0$, rule $d^i$ assigns nonnegative payments no larger than the claims and satisfies
--
--   $$
--   \sum_jd^i_j(E)=\min\{E,\bar L_i\}.
--   $$
--
--   The standing assumption is that each coordinate $d^i_j(E)$ is nondecreasing in $E\ge0$. These conditions define the networks to which the paper's clearing and uniqueness results apply. Values of $d^i$ at negative estates are outside the model and carry no condition.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), pp. 5–6 (PDF 7–8), §2

import Mathlib

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Section 2: agents' endowments, bilateral liabilities, and estate-dependent division rules. -/
structure FinNetwork (I : Type*) where
  z : I → ℝ
  L : I → I → ℝ
  d : I → ℝ → I → ℝ

/-- Total liabilities of agent `i`, denoted L̄ᵢ in the paper. -/
def FinNetwork.Lbar (N : FinNetwork I) (i : I) : ℝ := ∑ j, N.L i j

/-- A division rule is constrained only on nonnegative estates. -/
def FinNetwork.IsDivisionRule (N : FinNetwork I) (i : I) : Prop :=
  ∀ E : ℝ, 0 ≤ E →
    (∀ j, 0 ≤ N.d i E j ∧ N.d i E j ≤ N.L i j) ∧
    (∑ j, N.d i E j) = min E (N.Lbar i)

/-- Section 2's standing assumptions on every financial network. -/
def FinNetwork.Standing (N : FinNetwork I) : Prop :=
  (∀ i, 0 ≤ N.z i) ∧
  (∀ i j, 0 ≤ N.L i j) ∧
  (∀ i, N.L i i = 0) ∧
  (∀ i, N.IsDivisionRule i) ∧
  (∀ (i j : I) (E E' : ℝ), 0 ≤ E → E ≤ E' → N.d i E j ≤ N.d i E' j)

end ClearingUnique.Cycles


