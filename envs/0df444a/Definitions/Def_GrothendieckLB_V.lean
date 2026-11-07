-- Prove2me | Definitions.Def_GrothendieckLB_V
-- name    : GrothendieckLB_V
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:47:36.604175+00:00
-- url     : https://prove2.me/theorems/8df60b3d-17e3-45cb-bab4-458485cecb0a
-- title:
--   $V(u)$
-- statement:
--   For a one-dimensional function $u$,
--   $$
--   V(u):=\sum_{j=0}^3\big(\mathbb E[u(Z)\mathrm{He}_j(Z)]\big)^2,\qquad Z\sim N(0,1).
--   $$
--   It is the squared mass of $u$ on the Hermites of degree at most three, and it controls the disagreement term through its fibers.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.4, p.36

import Mathlib
import Definitions.Def_GrothendieckLB_stdExp
import Definitions.Def_GrothendieckLB_he

namespace GrothendieckLB

/-- `V(u) := ∑_{j=0}^3 (E[u(Z) He_j(Z)])²`, the mass of a one-dimensional function on the Hermites of
degree at most three (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 8.4, p.36). -/
noncomputable def V (u : ℝ → ℝ) : ℝ :=
  ∑ j : Fin 4, (stdExp fun z => u z * he j z) ^ 2

end GrothendieckLB


