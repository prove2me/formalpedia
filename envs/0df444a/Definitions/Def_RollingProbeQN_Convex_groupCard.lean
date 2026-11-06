-- Prove2me | Definitions.Def_RollingProbeQN_Convex_groupCard
-- name    : RollingProbeQN_Convex_groupCard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:18:58.199609+00:00
-- url     : https://prove2.me/theorems/ac9bd848-db39-4b0a-a83b-7e04bf1982c3
-- title:
--   Group size $|g|$
-- statement:
--   For a group $g$ of the partition, $|g|$ is its number of columns. It enters the probe radius $\tau_k$ of (4).
--
--   **Formalization Note** As for $v_g$, the group with label $c$ is $\{j:\mathrm{grp}(j)=c\}$ (0-based).
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Definition 2.2, p. 7

import Mathlib

namespace RollingProbeQN.Convex

/-- **The group size `|g|`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Definition 2.2, p. 7: "For a group `g` we write `|g|` for its size".

**Formalization Note.** As for `groupVec`, the group with label `c` is `{j | (grp j : ℕ) = c}`
(0-based, reading R5). -/
def groupCard {d χ : ℕ} (grp : Fin d → Fin χ) (c : ℕ) : ℕ :=
  (Finset.univ.filter (fun j => (grp j : ℕ) = c)).card

end RollingProbeQN.Convex


