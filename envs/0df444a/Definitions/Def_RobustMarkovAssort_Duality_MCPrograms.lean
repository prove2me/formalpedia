-- Prove2me | Definitions.Def_RobustMarkovAssort_Duality_MCPrograms
-- name    : RobustMarkovAssort_Duality_MCPrograms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:17:44.857214+00:00
-- url     : https://prove2.me/theorems/e992188e-90ba-479d-84fd-0cfa8787ac53
-- title:
--   Row continuation minima for the Markov model
-- statement:
--   MCRowMin M v i z means z is the attained minimum of the outgoing row dot product sum_j q_j v_j over exactly M.rows i. The vector v ranges over all real vectors. This relation is false for every z if the row objective has no minimum; no infimum or default choice is used.
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact p. 9, equation (2)

import Definitions.Def_RobustMarkovAssort_Duality_MCModel
import Definitions.Def_RobustMarkovAssort_Duality_GeneralPrograms

namespace RobustMarkovAssort.Duality

def MCRowMin {n : ℕ} (M : MCUncertainty n) (v : Vec n) (i : Fin n) (z : ℝ) : Prop :=
  MinValue (M.rows i) (fun q => ∑ j, q j * v j) z

end RobustMarkovAssort.Duality


