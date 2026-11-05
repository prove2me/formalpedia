-- Prove2me | Definitions.Def_RepGQML_IsLieRep
-- name    : RepGQML_IsLieRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:43:28.137204+00:00
-- url     : https://prove2.me/theorems/89278310-1769-4fd8-85fd-ee3cc002252b
-- title:
--   Lie algebra representation on a complex vector space
-- statement:
--   A **representation** of a Lie algebra $\mathfrak g$ on a vector space $V$ is a map $r:\mathfrak g\to\mathfrak{gl}(V)$ that respects the bracket:
--   $$
--   r([X,Y])=[r(X),r(Y)]\qquad\text{for all } X,Y\in\mathfrak g .
--   $$
--
--   **Formalization Note** The source asks for a linear map and a finite dimensional $V$. Its Lie algebras are real (for instance $\mathfrak{su}(2)$) or complex and act on complex spaces, so here $\mathfrak g$ is a `LieRing`, $r$ is additive, and $V$ is a complex vector space. This covers both cases without a restriction of scalars. Finite dimension is imposed by the theorems that use it.
-- source:
--   Ragone et al., Representation Theory for Geometric Quantum Machine Learning, arXiv:2210.07980v2, Definition 7, p.16

import Mathlib

namespace RepGQML

/-- A **Lie algebra representation** on a complex vector space: an additive map `r` from a Lie ring
`L` to the operators on `V` with `r [X, Y] = [r X, r Y]` for all `X, Y` (Ragone et al., *Representation Theory for Geometric Quantum Machine Learning*, arXiv:2210.07980v2, Definition 7, p.16).

**Formalization Note** The page asks for a linear map on a Lie algebra `g` and a finite dimensional `V`.
The Lie algebras in the paper are real (`su(2)`) or complex and act on complex spaces, so `r` is
taken only additive on a `LieRing`, which covers both without a restriction of scalars. Finite
dimension is imposed by the theorems that need it. -/
def IsLieRep {L V : Type*} [LieRing L] [AddCommGroup V] [Module ℂ V]
    (r : L →+ Module.End ℂ V) : Prop :=
  ∀ X Y : L, r ⁅X, Y⁆ = r X * r Y - r Y * r X

end RepGQML


