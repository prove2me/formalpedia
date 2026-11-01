-- Prove2me | Definitions.Def_AllPhotonicRepeater_expectedPhotons
-- name    : AllPhotonicRepeater_expectedPhotons
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:22:53.282002+00:00
-- url     : https://prove2.me/theorems/cf8f2243-a557-4d41-a069-ba595b3f0424
-- title:
--   Average photon number $\bar Q$ per entangled pair
-- statement:
--   The average number of single photons the all photonic repeater consumes to produce one entangled pair between Alice and Bob is
--   $$
--   \bar Q=\frac{2mn(Q_L+1)+2m}{P},
--   $$
--   where $n$ is the number of source nodes, $m$ the number of arms per side of each cluster state, $Q_L$ the size (A1) of the tree that encodes each 1st-leaf qubit, and $P$ the success probability (C1) of one trial.
--
--   The mission's goal bounds $\bar Q$ polynomially in the distance.
--
--   **Formalization Note** The quotient is real division, which Lean evaluates to $0$ when $P=0$. Every statement about $\bar Q$ in the mission therefore also asserts $P>0$.
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. C1, Eq. (C4), p. 11

import Mathlib
import Definitions.Def_AllPhotonicRepeater_treeSize
import Definitions.Def_AllPhotonicRepeater_repeaterSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- The average number `Q̄` of single photons consumed by the all photonic repeater protocol to
produce one entangled pair between Alice and Bob (Azuma, Tamaki, Lo, *All photonic quantum
repeaters*, arXiv:1309.7207v1, App. C1, Eq. (C4), p. 11):

`Q̄ = (2mn(Q_L + 1) + 2m) / P`,

with `Q_L = treeSize l b` (A1) and `P = repeaterSuccess ε0 n m l b` (C1).

**Formalization Note** This is real division, so Lean returns `0` when `P = 0`; every statement
about `Q̄` in this mission also asserts `0 < P`. -/
noncomputable def expectedPhotons (ε0 : ℝ) (n m l : ℕ) (b : ℕ → ℕ) : ℝ :=
  (2 * (m : ℝ) * n * ((treeSize l b : ℝ) + 1) + 2 * m) / repeaterSuccess ε0 n m l b

end AllPhotonicRepeater


