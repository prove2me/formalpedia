-- Prove2me | Definitions.Def_GomoryGroup_Rel_Supplement_Presentation
-- name    : GomoryGroup_Rel_Supplement_Presentation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:19:23.17233+00:00
-- url     : https://prove2.me/theorems/49cea839-d995-438e-ad65-1d6d35780491
-- title:
--   p. 262 — supplied cyclic standard form and the lattice quotient map
-- statement:
--   Let $B$ be an integer $m\times m$ basis matrix. A **lattice presentation** supplies the finite abelian group $G=M(I)/M(B)$ in standard form, a direct sum of cyclic groups of known positive orders, together with the quotient homomorphism $f:\mathbb Z^m\to G$. The map is onto and satisfies
--   $$f(v)=0\quad\Longleftrightarrow\quad v\in B\mathbb Z^m.$$
--
--   A list enumerates every group element exactly once. Thus $f(N_j)$ is the actual image of nonbasic column $j$, and $f(b-Ny)=0$ is precisely the feasibility predicate of the already-published group problem (4). The presentation contains neither costs nor optimal values or witnesses. It supplies the representation assumed given by THEOREM 3, rather than redoing the standard-form computation.
--
--   **Formalization Note** Finite abelian groups, homomorphisms, cyclic groups and their products use Mathlib. The new record specifies only the paper-specific lattice representation. The original real and integer programs, relative costs, group objective and optimality predicates are imported from the published Setting.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), pp. 261–262, M(I)/M(B), standard form preceding THEOREM 3, and (4)

import Mathlib

set_option autoImplicit false

namespace GomoryGroup.Rel.Supplement

open Matrix

/-- The supplied standard form of M(I)/M(B), with its actual quotient map.
The finite abelian group and cyclic factors are Mathlib objects. No cost or
optimal solution is a field. All hypotheses here specify input representation. -/
structure LatticePresentation {m : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (G : Type) [AddCommGroup G] where
  rank : ℕ
  orders : Fin rank → ℕ
  positive : ∀ i, 0 < orders i
  standard : G ≃+ ((i : Fin rank) → ZMod (orders i))
  quotientMap : (Fin m → ℤ) →+ G
  onto : Function.Surjective quotientMap
  kernel : ∀ v, quotientMap v = 0 ↔ ∃ k : Fin m → ℤ, v = B *ᵥ k
  enumeration : List G
  nodup : enumeration.Nodup
  complete : ∀ g, g ∈ enumeration

end GomoryGroup.Rel.Supplement


