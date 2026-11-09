-- Prove2me | Definitions.Def_AbelianCayleyHDX_PG
-- name    : AbelianCayleyHDX_PG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:08.999458+00:00
-- url     : https://prove2.me/theorems/867df3e1-62a2-40ee-8ff7-95796dbb2d92
-- title:
--   Projective space $\mathrm{PG}(t-1, F)$
-- statement:
--   For a field $F$ and $t \ge 1$, $\mathrm{PG}(t-1, F) = (F^t \setminus \{0\})/F^\times$; the class of $a \ne 0$ is $[a] = F^\times a$, which records only the direction of $a$.
--
--   **Formalization Note** Mathlib's `Projectivization F (Fin t → F)`.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11

import Mathlib

namespace AbelianCayleyHDX

/-- **The projective space `PG(t − 1, F)`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.1, p.11): "we identify
`PG(t − 1, F) = (F^t ∖ {0})/F^×` and write `[a] = F^× a`".

**Formalization Note** Mathlib's `Projectivization F (Fin t → F)`: points are lines through the
origin of `F^t`; `Projectivization.mk F a ha` is `[a]` and `Projectivization.rep` a chosen nonzero
representative. -/
abbrev PG (t : ℕ) (F : Type*) [Field F] : Type _ := Projectivization F (Fin t → F)

end AbelianCayleyHDX


