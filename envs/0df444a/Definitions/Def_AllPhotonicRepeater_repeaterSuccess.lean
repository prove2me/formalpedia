-- Prove2me | Definitions.Def_AllPhotonicRepeater_repeaterSuccess
-- name    : AllPhotonicRepeater_repeaterSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:13.984538+00:00
-- url     : https://prove2.me/theorems/e18a7d1a-c489-4ac0-adf0-532cd3c9ad19
-- title:
--   Success probability $P$ of one trial of the all photonic repeater
-- statement:
--   Alice and Bob are joined by $n$ source nodes and $n+1$ receiver nodes. Each source node emits a cluster state with $2m$ arms whose 1st-leaf qubits are encoded in tree cluster states with branching $b_0,\dots,b_l$; each receiver node attempts $m$ Bell measurements on arriving photons. A trial succeeds when every receiver node has at least one successful Bell measurement and all the loss-tolerant measurements on the 1st-leaf qubits succeed. With per-photon loss probability $\epsilon_0$ its success probability is
--   $$
--   P=P_Z^{\,2(m-1)n}\,P_X^{\,2n}\,\big[1-(1-P_B)^m\big]^{n+1},
--   $$
--   with $P_Z$ from (A13), $P_X$ from (A16) and $P_B=(1-\epsilon_0)^2/2$ from (C2).
--
--   $P$ is the denominator of the photon count (C4).
--
--   **Formalization Note** The exponent $2(m-1)n$ is a natural number computed with truncated subtraction, which differs from the formula only at $m=0$; no statement of the mission uses $m=0$.
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. C1, Eq. (C1), p. 11

import Mathlib
import Definitions.Def_AllPhotonicRepeater_zSuccess
import Definitions.Def_AllPhotonicRepeater_xSuccess
import Definitions.Def_AllPhotonicRepeater_bellSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The success probability `P` of one trial of the all photonic repeater protocol (Fig. 3) with
`n` source nodes, `n + 1` receiver nodes, `2m`-arm cluster states whose 1st-leaf qubits are
encoded in tree cluster states with branching `b 0, …, b l`, and per-photon loss probability
`ε0` (Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. C1,
Eq. (C1), p. 11):

`P = P_Z^{2(m−1)n} · P_X^{2n} · [1 − (1 − P_B)^m]^{n+1}`.

**Formalization Note** The exponent `2(m − 1)n` is the natural number `2 * (m - 1) * n`; its
truncated subtraction only matters at `m = 0`, which no statement of the mission uses. -/
noncomputable def repeaterSuccess (ε0 : ℝ) (n m l : ℕ) (b : ℕ → ℕ) : ℝ :=
  zSuccess ε0 l b ^ (2 * (m - 1) * n) * xSuccess ε0 l b ^ (2 * n) *
    (1 - (1 - bellSuccess ε0) ^ m) ^ (n + 1)

end AllPhotonicRepeater


