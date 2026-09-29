-- Prove2me | Definitions.Def_mme_CW_2376_marginal_joint_tables
-- name    : mme_CW_2376_marginal_joint_tables
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T22:44:02.290049+00:00
-- url     : https://prove2.me/theorems/de8b3a5f-b779-45d0-9c42-aa1e2f32c836
-- title:
--   Joint tables and target completion degree for the full marginal CW hypergraph
-- statement:
--   Every coordinate of a full marginal-supported Coppersmith--Winograd address determines one of the fifteen supported grade triples. Its joint table records the multiplicity of each of those triples. The distinguished target completion degree is the conditional multinomial coefficient
--
--   $$
--   D_*(m)=
--   rac{∏_{r=0}^4 A_r!}{∏_{σ∈Σ}β_σ!},
--   $$
--
--   where $A_r$ are the five prescribed mode marginals and $β_σ$ are the fifteen equation-(13) target multiplicities. It is the number of exact-target completions over one fixed mode word.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) and the completion counts on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_hash_incidence_universes
import Definitions.Def_mme_CW_2376_joint_profile_table
import Theorems.Thm_mme_CW_2376_target_joint_types_iff_sum_four

open BigOperators

namespace MME

def cw2376MarginalSupportedJointTypeAt {m : ℕ}
    (a : CW2376MarginalSupportedAddress m)
    (j : Fin (cw2376ProfileLength m)) : CW2376SupportedJointType :=
  ⟨cw2376AddressType a.1 j,
    mme_CW_2376_target_joint_types_iff_sum_four _ |>.2 (by
      simpa only [cw2376AddressType] using a.2.1 j)⟩

def cw2376MarginalJointTable {m : ℕ}
    (a : CW2376MarginalSupportedAddress m) :
    CW2376JointMultiplicityTable :=
  fun sigma => Fintype.card
    {j : Fin (cw2376ProfileLength m) //
      cw2376MarginalSupportedJointTypeAt a j = sigma}

def cw2376TargetStarDegree (m : ℕ) : ℕ :=
  (∏ r : Fin 5, (cw2376MarginalMultiplicity m r).factorial) /
    ∏ sigma : CW2376SupportedJointType,
      (cw2376TargetJointTable m sigma).factorial

end MME


