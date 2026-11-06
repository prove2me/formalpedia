-- Prove2me | Definitions.Def_RollingProbeQN_Convex_groupVec
-- name    : RollingProbeQN_Convex_groupVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:19:03.361659+00:00
-- url     : https://prove2.me/theorems/0a2eadff-efbb-48fc-a54c-7646d28a9dba
-- title:
--   Group indicator vector $v_g=\sum_{j\in g}e_j$
-- statement:
--   For a group $g$ of the partition, $v_g=\sum_{j\in g}e_j$ is its indicator vector. Algorithm 1 probes the gradient along $v_g$.
--
--   **Formalization Note** Groups are labelled by natural numbers: the group with label $c$ is $\{j:\mathrm{grp}(j)=c\}$, the paper's $g_{c+1}$ for $c<\chi$ (0-based), and is empty for $c\ge\chi$.
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Definition 2.2, p. 7

import Mathlib

namespace RollingProbeQN.Convex

/-- **The group indicator vector `v_g = ∑_{j ∈ g} e_j`.**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Definition 2.2, p. 7: "For a group `g` we write `|g|` for its size and
`v_g = ∑_{j∈g} e_j` for its indicator vector".

**Formalization Note.** Groups are labelled by natural numbers `c`: the group with label `c` is
`{j | (grp j : ℕ) = c}`, which is the paper's `g_{c+1}` for `c < χ` (0-based, reading R5) and is
empty for `c ≥ χ`. Algorithm 1 refreshes the group with label `k % χ`. -/
noncomputable def groupVec {d χ : ℕ} (grp : Fin d → Fin χ) (c : ℕ) : EuclideanSpace ℝ (Fin d) :=
  ∑ j ∈ Finset.univ.filter (fun j => (grp j : ℕ) = c), EuclideanSpace.single j (1 : ℝ)

end RollingProbeQN.Convex


