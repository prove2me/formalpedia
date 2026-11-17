-- Prove2me | Definitions.Def_NoPerfectRandComp_Supplement_Fm
-- name    : NoPerfectRandComp_Supplement_Fm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:11:56.849235+00:00
-- url     : https://prove2.me/theorems/4fad8787-86f9-4a77-829a-953cffb4dcc7
-- title:
--   AND of ORs $F_m = \mathrm{AND}_m\circ\mathrm{OR}_m$
-- statement:
--   The function
--   $$
--   F_m = \mathrm{AND}_m\circ\mathrm{OR}_m,\qquad F_m(x) = \bigwedge_{i=1}^m\bigvee_{j=1}^m x_{ij},
--   $$
--   on $N = m^2$ bits. The OR blocks $\{x_{i1},\dots,x_{im}\}$ are its **rows**.
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), §9, p.37

import Mathlib
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition
import Definitions.Def_NoPerfectRandComp_Supplement_andF
import Definitions.Def_NoPerfectRandComp_Supplement_orF

namespace NoPerfectRandComp

namespace Supplement

/-- AND of ORs, `F_m = AND_m ∘ OR_m`, `F_m(x) = ⋀_{i=1}^m ⋁_{j=1}^m x_{ij}` (Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), §9, p.37),
on `N = m²` bits; the OR blocks `{i} × [m]` are the rows.

**Formalization Note** The composition is the published `OAI.Paper320.compose`. -/
def Fm (m : ℕ) : (Fin m × Fin m → Bool) → Bool :=
  OAI.Paper320.compose (andF m) (orF m)

end Supplement

end NoPerfectRandComp


