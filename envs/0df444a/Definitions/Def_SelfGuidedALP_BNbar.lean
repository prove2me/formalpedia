-- Prove2me | Definitions.Def_SelfGuidedALP_BNbar
-- name    : SelfGuidedALP_BNbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:26:58.886546+00:00
-- url     : https://prove2.me/theorems/b05881fe-504f-4c22-88a8-92a9cb4aa2a0
-- title:
--   The closure $\bar{\mathcal B}_N$
-- statement:
--   $\bar{\mathcal B}_N$ is the closure of $\mathcal B_N$ in $\mathcal B$, and $\bar{\mathcal B}_N^\perp$ is its perpendicular complement.
--
--   The goal's constant measures the component of $B^*$ in $\bar{\mathcal B}_N^\perp$.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8

import Mathlib
import Definitions.Def_SelfGuidedALP_BN

namespace SelfGuidedALP

/-- `ℬ̄_N`, the closure of `ℬ_N` in `ℬ` (Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, Definition EC.2, p.ec8). Its
perpendicular complement `ℬ̄_N^⊥` is `(BNbar R θs)ᗮ`. -/
noncomputable def BNbar {d N : ℕ} (R : RBClass d) (θs : Fin N → EuclideanSpace ℝ (Fin (d + 1))) :
    Submodule ℝ (Bspace R) :=
  (BN R θs).topologicalClosure

end SelfGuidedALP


