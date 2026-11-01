-- Prove2me | Definitions.Def_AllPhotonicRepeater_xSuccess
-- name    : AllPhotonicRepeater_xSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:21:25.377008+00:00
-- url     : https://prove2.me/theorems/9e4edd9a-f149-4ee7-a72d-45d9b0fa75eb
-- title:
--   Loss-tolerant $X$-measurement success probability $P_X$
-- statement:
--   For a qubit encoded in a tree cluster state with branching parameters $b_0,\dots,b_l$ and per-photon loss probability $\epsilon_0$, the loss-tolerant $X$-basis measurement succeeds when, for some 1st-level qubit, a direct $X$ measurement on it and direct or indirect $Z$ measurements on all its children succeed. Its success probability is
--   $$
--   P_X=R_0 ,
--   $$
--   the level-$0$ value of the indirect $Z$-measurement recursion (A3).
--
--   In the repeater, the two 1st-leaf qubits of the successful Bell measurement at each source node are measured in this way, which gives the factor $P_X^{2n}$ of (C1).
--
--   **Formalization Note** $R_0$ is (A3) evaluated at $k=0$ (see the definition of $R_k$).
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A2, Eq. (A16), p. 9

import Mathlib
import Definitions.Def_AllPhotonicRepeater_indirectZSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The success probability `P_X` of the loss-tolerant `X`-basis measurement on a qubit encoded
in a tree cluster state with branching parameters `b 0, …, b l`, per-photon loss probability
`ε0` (Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. A2,
Eq. (A16), p. 9):

`P_X = R_0`.

**Formalization Note** `R_0` is (A3) at `k = 0` (see `indirectZSuccess`). -/
noncomputable def xSuccess (ε0 : ℝ) (l : ℕ) (b : ℕ → ℕ) : ℝ :=
  indirectZSuccess ε0 l b 0

end AllPhotonicRepeater


