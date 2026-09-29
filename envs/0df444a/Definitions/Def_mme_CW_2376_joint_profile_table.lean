-- Prove2me | Definitions.Def_mme_CW_2376_joint_profile_table
-- name    : mme_CW_2376_joint_profile_table
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T20:37:22.531883+00:00
-- url     : https://prove2.me/theorems/a603745e-345f-4ef8-bea1-093a9bd446c3
-- title:
--   Supported joint-profile tables and their three marginals
-- statement:
--   The five-grading of the squared Coppersmith--Winograd tensor has fifteen supported joint types $(i,j,k)$ with $i+j+k=4$. A joint-profile table assigns a nonnegative integral multiplicity to each of these fifteen types. The distinguished table is the optimized equation-(13) profile at scale $m$.
--
--   Two joint tables have the same marginals when, for every tensor mode $p$ among $0,1,2$ and grade $r$ among $0,1,2,3,4$, the sums of their cell multiplicities over all joint types whose $p$-th coordinate is $r$ agree. This is the finite contingency-table state space needed to compare all full marginal-supported CW profiles, rather than pruning only the distinguished exact profile.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) on journal pp. 267--268; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_dominance_weights

open BigOperators

namespace MME

abbrev CW2376SupportedJointType :=
  {sigma : Fin 3 → Fin 5 // sigma ∈ cw2376TargetJointTypes}

abbrev CW2376JointMultiplicityTable := CW2376SupportedJointType → ℕ

def cw2376TargetJointTable (m : ℕ) : CW2376JointMultiplicityTable :=
  fun sigma => cw2376ProfileMultiplicity m sigma.1

def CW2376SameJointMarginals
    (a b : CW2376JointMultiplicityTable) : Prop :=
  ∀ i : Fin 3, ∀ r : Fin 5,
    (∑ sigma, if sigma.1 i = r then a sigma else 0) =
      ∑ sigma, if sigma.1 i = r then b sigma else 0

end MME


