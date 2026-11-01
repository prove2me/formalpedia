-- Prove2me | Definitions.Def_RedundancyHT_ValidDescr
-- name    : RedundancyHT_ValidDescr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:24:50.259734+00:00
-- url     : https://prove2.me/theorems/5b96be59-9111-4737-870e-8b930de0f40f
-- title:
--   Valid descriptors $(c;u)$
-- statement:
--   A pair $(c;u)$ is valid if $u$ is a sequence of distinct useful servers and no job type occurring in $c$ is compatible with a server in $u$.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.3.2, p.8

import Definitions.Def_RedundancyHT_useful

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The pairs `(c;u)` carrying mass in (5)** (arXiv:2005.14566v5, p.8): `u` lists distinct useful
servers, and "none of the waiting jobs can be compatible with one of the idle servers". -/
def ValidDescr {n m : ℕ} (D : Model n m) (c : List (Fin n)) (u : List (Fin m)) : Prop :=
  u.Nodup ∧ (∀ j ∈ u, useful D j) ∧ ∀ i ∈ c, ∀ j ∈ u, D.compatible i j = false

end RedundancyHT


