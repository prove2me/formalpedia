-- Prove2me | Definitions.Def_AbelianCayleyHDX_LF
-- name    : AbelianCayleyHDX_LF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:31:19.33398+00:00
-- url     : https://prove2.me/theorems/52037992-4e67-49db-851b-7937c97f5594
-- title:
--   The triples $L_F$
-- statement:
--   For a finite field $F$, $L_F = \big\{\{p, r, p + r\} : p, r \in F^\times,\ p \ne r\big\}$. In characteristic two every member has three elements and satisfies $\sum_{s \in \ell} s = \sum_{s \in \ell} s^2 = 0$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12

import Mathlib

namespace AbelianCayleyHDX

/-- **The triples `L_F`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12): `L_F = {{p, r, p + r} : p, r ∈ F^×, p ≠ r}`. -/
def LF (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (Finset F) :=
  ((Finset.univ ×ˢ Finset.univ : Finset (F × F)).filter fun x => x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.1 ≠ x.2).image
    fun x => ({x.1, x.2, x.1 + x.2} : Finset F)

end AbelianCayleyHDX


