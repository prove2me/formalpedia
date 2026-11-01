-- Prove2me | Definitions.Def_NeebLieExt_IsCentral
-- name    : NeebLieExt_IsCentral
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:17:19.780969+00:00
-- url     : https://prove2.me/theorems/50846be2-b06f-4f66-985e-5de5569cca12
-- title:
--   The centre $\mathfrak z(\mathfrak n)$
-- statement:
--   An element $z$ of a Lie algebra $\mathfrak n$ is **central**, written $z\in\mathfrak z(\mathfrak n)$, if
--   $$
--   [z,m]=0\qquad\text{for all } m\in\mathfrak n .
--   $$
--
--   The centre $\mathfrak z(\mathfrak n)$ is the coefficient module of the cohomology groups $H^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$ that classify extensions with a fixed outer action.
--
--   **Formalization Note** This is membership in Mathlib's `LieAlgebra.center K n`, written as a predicate on elements. A $\mathfrak z(\mathfrak n)$-valued cochain is an $\mathfrak n$-valued cochain all of whose values are central.
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Definition II.2, p. 11 (the centre z(n) with x.z := S(x).z)

import Mathlib

namespace NeebLieExt

/-- **Central elements** `z(n)`. Neeb, arXiv:math/0411256v1, §II (Definition II.2, p. 11, "the
center z(n)").

`IsCentral z` says that `⁅z, m⁆ = 0` for every `m ∈ n`, i.e. `z` lies in the centre `z(n)`.

**Formalization Note** This is membership in Mathlib's `LieAlgebra.center K n` written out as a
predicate on elements; `z(n)`-valued cochains are `n`-valued cochains all of whose values satisfy
`IsCentral`. -/
def IsCentral {n : Type*} [LieRing n] (z : n) : Prop :=
  ∀ m : n, ⁅z, m⁆ = 0

end NeebLieExt


