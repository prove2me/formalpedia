-- Prove2me | Definitions.Def_AbelianCayleyHDX_Dhat
-- name    : AbelianCayleyHDX_Dhat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:49.460897+00:00
-- url     : https://prove2.me/theorems/49933e65-1bd3-49aa-88c6-93d05f725d3b
-- title:
--   All nonzero representatives $\hat D$
-- statement:
--   For $D \subseteq \mathrm{PG}(t-1, F)$, $\hat D = \{b \in V_0 \setminus \{0\} : [b] \in D\}$ is the set of all nonzero representatives of the points of $D$; $\hat\nu = |\hat D| = (|F| - 1)|D|$. It is closed under multiplication by $F^\times$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12

import Mathlib
import Definitions.Def_AbelianCayleyHDX_PG

namespace AbelianCayleyHDX

/-- **`D̂`, all nonzero representatives of the points of `D`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 3.2, p.12):
`D̂ = {b ∈ V₀ ∖ {0} : [b] ∈ D}`. -/
noncomputable def Dhat {t : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F] (D : Finset (PG t F)) :
    Finset (Fin t → F) := by
  classical
  exact Finset.univ.filter fun b => ∃ hb : b ≠ 0, Projectivization.mk F b hb ∈ D

end AbelianCayleyHDX


