-- Prove2me | Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
-- name    : DiscreteConvex_MixedMatrices_IsMixedMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T06:36:52.415742+00:00
-- url     : https://prove2.me/theorems/5f7cadce-ab6b-445b-8147-60d063afb567
-- title:
--   Mixed matrix (Eq. 12.7)
-- statement:
--   $A = Q + T$ (Eq. (12.7)) is a **mixed matrix** with respect to $(K,F)$ ($K$ a subfield of $F$, realized as an `Algebra K F` instance): $Q$ is a matrix over $K$ (axiom (M-Q)) embedded into $F$ via the structure map, $T$ is a matrix over $F$ (axiom (M-T)), and the family of $T$'s nonzero entries is algebraically independent over $K$ (Mathlib's `AlgebraicIndependent`, indexed by the subtype of nonzero-entry positions).
--
--   **Formalization Note.** The book's further "usually assume $T_{ij}\ne 0 \Rightarrow Q_{ij}=0$" normalization (stated immediately after Eq. (12.7), for uniqueness of the decomposition) is *not* part of this predicate: it is a convention for representing a given mixed matrix, not a hypothesis Theorems 12.6-12.9 need for their own truth.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.353-354, Eq. (12.7).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.353-354, Eq. (12.7)

import Mathlib

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.353-354, Eq. (12.7), axioms (M-Q), (M-T): the
definition of a mixed matrix, in `DiscreteConvex.MixedMatrices`.
-/

namespace DiscreteConvex.MixedMatrices

/-- `A = Q + T` (Eq. (12.7)) is a **mixed matrix** with respect to `(K, F)` (`K` a subfield of
`F`, realized as `Algebra K F`): `Q` is a matrix over `K` (axiom (M-Q)) embedded into `F` via the
structure map, `T` is a matrix over `F` (axiom (M-T)), and the family of `T`'s nonzero entries is
algebraically independent over `K`. The "usually assume `Tᵢⱼ ≠ 0 ⟹ Qᵢⱼ = 0`" normalization the
book adds immediately after Eq. (12.7) (for uniqueness of the decomposition `Q + T`) is not part
of this predicate: it is a convention for representing a given mixed matrix, not a hypothesis any
of this chapter's theorems (12.6-12.9) need. -/
def IsMixedMatrix {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F] [Algebra K F]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) : Prop :=
  (∀ i j, A i j = algebraMap K F (Q i j) + T i j) ∧
  AlgebraicIndependent K (fun e : {p : R × C // T p.1 p.2 ≠ 0} => T e.1.1 e.1.2)

end DiscreteConvex.MixedMatrices


