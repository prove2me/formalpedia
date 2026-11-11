-- Prove2me | Definitions.Def_SybilClinch_domYProfile
-- name    : SybilClinch_domYProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:29.435772+00:00
-- url     : https://prove2.me/theorems/f33ecff4-8cd6-44f1-9cad-09b132ff5dd9
-- title:
--   Profile of the dominant sell-$Y$ auction
-- statement:
--   When sell-$Y$ is dominant, the one-sided auction runs on the eligible sell-$Y$ reports $(v_i,q_i)_{i\in E_Y}$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, rule 2, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_SybilClinch_eligY
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, rule 2 (sell-`Y` dominant), printed p.26 (PDF p.28): the one-sided profile on which
the dominant sell-`Y` auction runs, the reports `(vᵢ, qᵢ)_{i ∈ E_Y}`. -/
noncomputable def domYProfile (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) :
    OneSidedProfile where
  ids := eligY A ids rep
  v := fun i => (((rep i).val : ℝ) : WithTop ℝ)
  q := fun i => (rep i).bud

end SybilClinch


