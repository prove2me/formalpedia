-- Prove2me | Definitions.Def_SelfGuidedALP_Ds
-- name    : SelfGuidedALP_Ds
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:23:21.11798+00:00
-- url     : https://prove2.me/theorems/753a0954-0d8c-42e4-a00e-70b286fc61d6
-- title:
--   The state-space radius $D_s$
-- statement:
--   The state-space radius is $D_s:=\max_{s\in\mathcal S}\|s\|_2$. The maximum is attained because $\mathcal S$ is compact and nonempty.
-- source:
--   Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.11

import Mathlib
import Definitions.Def_SelfGuidedALP_MDP

namespace SelfGuidedALP

/-- `D_s := max_{s∈𝒮} ‖s‖₂` (Pakiman, Nadarajah, Soheili, Lin, Self-guided Approximate Linear Programs, arXiv:2001.02798v2, p.11).

**Formalization Note.** `𝒮` is compact and nonempty, so the `sSup` is an attained maximum. -/
noncomputable def Ds {d m : ℕ} (M : MDP d m) : ℝ :=
  sSup ((fun s => ‖s‖) '' M.S)

end SelfGuidedALP


