-- Prove2me | Definitions.Def_AbelianCayleyHDX_Omega
-- name    : AbelianCayleyHDX_Omega
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:14.487441+00:00
-- url     : https://prove2.me/theorems/ad8e45c9-ee95-4dbb-aa55-479825938e93
-- title:
--   The column set $\Omega = F^\times \times V_0$
-- statement:
--   The columns of $H_D$ are indexed by $\Omega = F^\times \times V_0$, $V_0 = F^t$; for $|F| = q^2$ there are $M = (q^2 - 1)q^{2t}$ of them.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12

import Mathlib

namespace AbelianCayleyHDX

/-- **The column index set `Ω = F^× × V₀`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12), `V₀ = F^t`; it has
`M = (q² − 1) q^{2t}` elements when `|F| = q²`. -/
abbrev Omega (F : Type*) [Field F] (t : ℕ) : Type _ := Fˣ × (Fin t → F)

end AbelianCayleyHDX


