-- Prove2me | Definitions.Def_IntADSat_degreeSet
-- name    : IntADSat_degreeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:20.251488+00:00
-- url     : https://prove2.me/theorems/8e48b722-e52e-46cb-83a0-a2a9487ad5c5
-- title:
--   Set of distinct degrees $\mathcal D_G$
-- statement:
--   For a simple graph $G$ on $[n]$, $\mathcal D_G=\{\deg_G(v): v\in[n]\}$ is the set of distinct degrees, and $q=|\mathcal D_G|$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix B, p.14 (PDF 15)

import Mathlib
import Definitions.Def_IntADSat_deg

set_option autoImplicit false

namespace IntADSat

/-- The set `𝒟_G` of distinct degrees of `G` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Appendix B, p.14 (PDF 15)); `q = |𝒟_G|`. -/
noncomputable def degreeSet {n : ℕ} (G : SimpleGraph (Fin n)) : Finset ℕ :=
  Finset.univ.image (deg G)

end IntADSat


