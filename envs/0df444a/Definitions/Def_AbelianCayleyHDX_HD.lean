-- Prove2me | Definitions.Def_AbelianCayleyHDX_HD
-- name    : AbelianCayleyHDX_HD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:36:51.25829+00:00
-- url     : https://prove2.me/theorems/49ba593e-4760-4288-994e-7ab755f450f9
-- title:
--   The relation matrix $H_D$
-- statement:
--   For a spanning $D \subseteq \mathrm{PG}(t-1, F)$, $H_D$ is the binary matrix with columns $\Omega = F^\times \times V_0$ whose row $(b, x, \ell)$ has support
--   $$T(b, x, \ell) = \{(p,\ x + pb) : p \in \ell\}.$$
--   Each row records three points on the line $x + Fb$ together with the scalars locating them.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12

import Mathlib
import Definitions.Def_AbelianCayleyHDX_RowIdx
import Definitions.Def_AbelianCayleyHDX_Omega

namespace AbelianCayleyHDX

/-- **The relation matrix `H_D`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12): the binary matrix with columns
`Ω = F^× × V₀` whose row `(b, x, ℓ)` has support `T(b, x, ℓ) = {(p, x + pb) : p ∈ ℓ}`. -/
def HD {t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] (D : Finset (PG t F)) :
    Matrix (RowIdx D) (Omega F t) (ZMod 2) :=
  fun r c => if (c.1 : F) ∈ r.2.2.1 ∧ c.2 = r.2.1 + (c.1 : F) • r.1.1 then 1 else 0

end AbelianCayleyHDX


