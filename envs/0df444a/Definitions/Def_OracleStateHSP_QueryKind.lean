-- Prove2me | Definitions.Def_OracleStateHSP_QueryKind
-- name    : OracleStateHSP_QueryKind
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:19.928676+00:00
-- url     : https://prove2.me/theorems/d17e9659-a8a7-4d20-ba7c-4c66f2a16ac1
-- title:
--   Query kinds: forward $O$, inverse $O^\dagger$, conjugate $O^*$, transpose $O^T$
-- statement:
--   An oracle $O$ on the query register $\mathcal H_S$ can be called in four ways:
--
--   1. the **forward query** $O$;
--   2. the **inverse query** $O^{-1} = O^\dagger$ (conjugate transpose);
--   3. the **conjugate query** $O^*$ (entrywise complex conjugate);
--   4. the **transpose query** $O^T$.
--
--   Definition 4.1 allows the first two; Theorem 4.10 and Definition 1.3 add the last two. A query of kind $k$ applies the matrix $k(O) \in \{O, O^\dagger, O^*, O^T\}$ to the query register. A kind is *forward-or-inverse* if it is one of the first two.
--
--   **Formalization Note** The conjugate is entrywise, so $O^\dagger = (O^*)^T$; it is never identified with the adjoint.
-- source:
--   Liu–Carrasco–Eisert–Bellante, The power of oracle access, arXiv:2609.35656, Definition 4.1, p.35; Theorem 4.10, p.40; Definition 1.3, p.6

import Mathlib

namespace OracleStateHSP

/-- The four kinds of oracle call of Liu–Carrasco–Eisert–Bellante, *The power of oracle access*, arXiv:2609.35656: the forward query `O` and the inverse query
`O⁻¹ = O†` of Definition 4.1 (p.35), and the complex conjugate `O^*` and the transpose `O^T` that
Theorem 4.10 (p.40) and Definition 1.3 (p.6) add.

**Formalization Note.** `conj` is the entrywise complex conjugate (`O.map star`) and `transp` the
transpose, so that `O† = (O^*)^T`; the conjugate is never identified with the adjoint. -/
inductive QueryKind : Type
  /-- The forward query `O`. -/
  | fwd
  /-- The inverse query `O⁻¹ = O†` (conjugate transpose). -/
  | inv
  /-- The complex-conjugate query `O^*` (entrywise conjugate). -/
  | conj
  /-- The transpose query `O^T`. -/
  | transp
  deriving DecidableEq

namespace QueryKind

/-- The matrix that a query of kind `k` applies to the query register for the oracle `O`
(arXiv:2609.35656, Definition 4.1, p.35, and Theorem 4.10, p.40): `O`, `O†`, `O^*` or `O^T`. -/
def apply {Q : Type*} (k : QueryKind) (O : Matrix Q Q ℂ) : Matrix Q Q ℂ :=
  match k with
  | fwd => O
  | inv => O.conjTranspose
  | conj => O.map star
  | transp => O.transpose

/-- A kind allowed by Definition 4.1 (arXiv:2609.35656, p.35): a forward or an inverse query. -/
def IsForwardOrInverse (k : QueryKind) : Prop :=
  k = fwd ∨ k = inv

end QueryKind

end OracleStateHSP


