-- Prove2me | Definitions.Def_AllPhotonicRepeater_zSuccess
-- name    : AllPhotonicRepeater_zSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:18.117386+00:00
-- url     : https://prove2.me/theorems/9b686fbd-6e68-4b9d-ad11-b58bd4e79238
-- title:
--   Loss-tolerant $Z$-measurement success probability $P_Z$
-- statement:
--   For a qubit encoded in a tree cluster state with branching parameters $b_0,\dots,b_l$ and per-photon loss probability $\epsilon_0$, the loss-tolerant $Z$-basis measurement succeeds when a direct or indirect $Z$ measurement succeeds on every one of the $b_0$ 1st-level qubits. Its success probability is
--   $$
--   P_Z=(1-\epsilon_0+\epsilon_0R_1)^{b_0},
--   $$
--   where $R_1$ is the indirect $Z$-measurement success probability of the 1st level (A3).
--
--   In the repeater, $2(m-1)$ of the $2m$ 1st-leaf qubits at each source node are measured in this way, which gives the factor $P_Z^{2(m-1)n}$ of (C1).
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A2, Eq. (A13), p. 9

import Mathlib
import Definitions.Def_AllPhotonicRepeater_indirectZSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The success probability `P_Z` of the loss-tolerant `Z`-basis measurement on a qubit encoded
in a tree cluster state with branching parameters `b 0, …, b l`, per-photon loss probability
`ε0` (Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. A2,
Eq. (A13), p. 9):

`P_Z = (1 − ε0 + ε0 R_1)^{b_0}`,

with `R_1 = indirectZSuccess ε0 l b 1` from (A3). -/
noncomputable def zSuccess (ε0 : ℝ) (l : ℕ) (b : ℕ → ℕ) : ℝ :=
  (1 - ε0 + ε0 * indirectZSuccess ε0 l b 1) ^ b 0

end AllPhotonicRepeater


