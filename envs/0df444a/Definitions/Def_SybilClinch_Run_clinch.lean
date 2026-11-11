-- Prove2me | Definitions.Def_SybilClinch_Run_clinch
-- name    : SybilClinch_Run_clinch
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:42:47.581711+00:00
-- url     : https://prove2.me/theorems/cb6bd529-927b-452e-8bf2-3d7535338cdd
-- title:
--   Clinching identities
-- statement:
--   The clinching identities are the active identities whose budget equals the water level,
--   $$\mathrm{Clinch}=\{i\in\mathrm{Active}:b_i=h\},$$
--   which by $pD_{-i}=B-b_i$ is the set $\{i\in\mathrm{Active}:S=D_{-i}\}$ of (14): the residual demand of the others no longer covers the residual supply.
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (14)–(15), p.10 (PDF p.12)

import Mathlib
import Definitions.Def_SybilClinch_Run_active
import Definitions.Def_SybilClinch_Run_waterLevel

set_option autoImplicit false

open Filter Topology Set

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §3.2, (14)–(15), printed p.10 (PDF p.12): the clinching identities
`Clinch = {i ∈ Active : S = D₋ᵢ} = {i ∈ Active : bᵢ = h}` at clock price `p`.

**Formalization Note.** Defined through the water-level form (15); its equivalence with (14) is
item 1 of Lemma 4.8. -/
noncomputable def Run.clinch (M : TargetMech) (P : OneSidedProfile) (R : Run) (p : ℝ) :
    Finset ℕ :=
  (R.active M P p).filter (fun i => R.bud M P i p = R.waterLevel M P p)

end SybilClinch


