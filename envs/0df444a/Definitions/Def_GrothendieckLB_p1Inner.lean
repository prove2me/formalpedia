-- Prove2me | Definitions.Def_GrothendieckLB_p1Inner
-- name    : GrothendieckLB_p1Inner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:48:19.079131+00:00
-- url     : https://prove2.me/theorems/827b43e9-9d06-460b-a240-1222f62659c9
-- title:
--   $\langle P_1F,P_1G\rangle$
-- statement:
--   The inner product of the degree-one Hermite parts of $F,G:\mathbb R^d\to\mathbb R$:
--   $$
--   \langle P_1F,P_1G\rangle=\langle c_F,c_G\rangle=\sum_{i=1}^d\mathbb E[F(X)X_i]\,\mathbb E[G(X)X_i].
--   $$
--
--   **Formalization Note** The moment sum is the definition, since the $\mathbb E[FX_i]$ are the coordinates of $P_1F$ in the orthonormal basis $X_1,\dots,X_d$. No $L^2$ projection is constructed.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_linearMoment

namespace GrothendieckLB

/-- `⟨P₁F, P₁G⟩ = ⟨c_F, c_G⟩`, the inner product of the degree-one Hermite parts
(Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31).

**Formalization Note** The moment sum is the definition: the `E[F X_i]` are the coordinates of
`P₁F` in the orthonormal basis `X₁, …, X_d`. No `L²` projection is constructed. -/
noncomputable def p1Inner {d : ℕ} (F G : (Fin d → ℝ) → ℝ) : ℝ :=
  ∑ i, linearMoment F i * linearMoment G i

end GrothendieckLB


