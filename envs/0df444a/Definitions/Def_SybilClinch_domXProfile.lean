-- Prove2me | Definitions.Def_SybilClinch_domXProfile
-- name    : SybilClinch_domXProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:41:48.558103+00:00
-- url     : https://prove2.me/theorems/81cfbb66-04d6-40d6-a9a0-52afb2865ecf
-- title:
--   Profile of the reverse auction
-- statement:
--   When sell-$X$ is dominant, the reverse auction runs on the eligible sell-$X$ identities with clock values $1/u_i$ (with $1/0=+\infty$: such an identity never exits because of its value) and budgets $r_i$.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2, p.27 (PDF p.29), footnote 2

import Mathlib
import Definitions.Def_SybilClinch_eligX
import Definitions.Def_SybilClinch_OneSidedProfile

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §5.2 (sell-`X` dominant), printed p.27 (PDF p.29), and footnote 2: the one-sided profile of
the reverse auction, the dominant sell-`X` identities with clock values `1/uᵢ` (`+∞` for `uᵢ = 0`)
and budgets `rᵢ`. -/
noncomputable def domXProfile (A : AdmissibleAMM) (ids : Finset ℕ) (rep : ℕ → Report) :
    OneSidedProfile where
  ids := eligX A ids rep
  v := fun i => if (rep i).val = 0 then ⊤ else ((((rep i).val)⁻¹ : ℝ) : WithTop ℝ)
  q := fun i => (rep i).bud

end SybilClinch


