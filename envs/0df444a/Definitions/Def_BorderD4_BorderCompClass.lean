-- Prove2me | Definitions.Def_BorderD4_BorderCompClass
-- name    : BorderD4_BorderCompClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:03.052182+00:00
-- url     : https://prove2.me/theorems/9ef76808-e5e1-4084-b561-1181f69bc33d
-- title:
--   The border class $\overline{C}_d(m,r)$
-- statement:
--   $\overline{C}_d(m,r)$ is the set of $G\in F[u]$ for which some $G_\varepsilon\in C_d(m,r;F((\varepsilon)))$ lies in $F[[\varepsilon]][u]$ and satisfies $G_\varepsilon(0,u)=G$. So $G$ is the limit, as $\varepsilon\to 0$, of a sum of $m$ compositions of arity $r$ over $F((\varepsilon))$.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 6.4, p.50

import Mathlib
import Definitions.Def_BorderD4_CompClass
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The border class `C̄_d(m, r)`: the polynomials `G ∈ F[u]` for which some `G_ε ∈ C_d(m, r; F((ε)))` lies in
`F[[ε]][u]` and satisfies `G_ε(0, u) = G`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 6.4, p.50. -/
def BorderCompClass (F τ : Type*) [Field F] (d m r : ℕ) : Set (MvPolynomial τ F) :=
  {G | ∃ Gε : MvPolynomial τ F⟦X⟧,
    map (algebraMap F⟦X⟧ (LaurentSeries F)) Gε ∈ CompClass (LaurentSeries F) τ d m r ∧
      map PowerSeries.constantCoeff Gε = G}

end BorderD4


