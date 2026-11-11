-- Prove2me | Definitions.Def_RandPurIso_Completion_idealOracle
-- name    : RandPurIso_Completion_idealOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:29:31.882415+00:00
-- url     : https://prove2.me/theorems/0192c32f-031d-4a8d-b278-6e21f1bfe414
-- title:
--   The ideal oracle $\Phi^{D^V_U}$
-- statement:
--   The oracle answering forward queries with the random completion: $\rho\mapsto D^V_U\rho(D^V_U)^\dagger$ on $\mathcal H([M])$, as the channel $\Phi$ of Definition 3.4 (its $\perp$ weight vanishes because $D^V_U$ is unitary), with no private register.
-- source:
--   Goldin, On Random Purifications of Isometries and Channels, arXiv:2611.04573, Theorem 5.4, p. 29

import Mathlib
import Definitions.Def_RandPurIso_Completion_contractionOracle
import Definitions.Def_RandPurIso_Completion_randomCompletion
open Matrix

namespace RandPurIso.Completion

/-- **The oracle `Φ^{D^V_U}`** (Goldin, *On Random Purifications of Isometries and Channels*, arXiv:2611.04573, Theorem 5.4, p. 29): forward queries to the unitary
`D^V_{U_{M1}}`, i.e. `ρ ↦ D^V_U ρ (D^V_U)†` on `H([M])`, as the `Φ` of Definition 3.4 (its `⊥` weight
is zero for a unitary), with no private register. -/
noncomputable def idealOracle {N M : ℕ} (D : Matrix.unitaryGroup (Fin M) ℂ)
    (U : Matrix.unitaryGroup (Fin (M - N)) ℂ) : Oracle (Fin M) (Option (Fin M)) Unit :=
  contractionOracle (liftUnit (randomCompletion (N := N) D U)) unitInit

end RandPurIso.Completion


