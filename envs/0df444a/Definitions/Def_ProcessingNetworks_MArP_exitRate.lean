-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_exitRate
-- name    : ProcessingNetworks_MArP_exitRate
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:25.635689+00:00
-- url     : https://prove2.me/theorems/b44055bb-b9c4-47d9-b0f5-9155b45d5cf6
-- title:
--   The exit rate $\lambda(i)=-\Lambda_{ii}$
-- statement:
--   The **exit rate** of state $i$ under a generator $\Lambda$ is $\lambda(i)=-\Lambda_{ii}$. The chain holds in $i$ for an exponentially distributed time with mean $1/\lambda(i)$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section D.1, p.287 (PDF p.303)

import Mathlib

namespace ProcessingNetworks.MArP

/-- The exit rate `λ(i) = -Λ_ii` of state `i` (Dai & Harrison, Processing Networks, pre-publication
draft 2020-4-2, p.287, PDF p.303). -/
def exitRate {S : Type*} (Λ : S → S → ℝ) (i : S) : ℝ :=
  -Λ i i

end ProcessingNetworks.MArP


