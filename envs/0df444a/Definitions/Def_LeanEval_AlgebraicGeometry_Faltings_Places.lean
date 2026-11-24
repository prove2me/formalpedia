-- Prove2me | Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Places
-- name    : LeanEval_AlgebraicGeometry_Faltings_Places
-- status  : Definition
-- author  : @LG
-- created : 2026-11-24T01:23:35.296796+00:00
-- url     : https://prove2.me/theorems/61d3be03-6024-4ec0-877c-f827c0fe48b2
-- title:
--   LeanEval function fields: valuation subalgebras, bundled function fields and places
-- statement:
--   This file fixes the vocabulary of algebraic function fields of one variable used by the LeanEval problem `faltings`, following Stichtenoth, *Algebraic Function Fields and Codes*, Definitions 1.1.4 and 1.1.8.
--
--   Let $R$ be a commutative semiring and $F$ a field carrying an $R$-algebra structure. A **valuation subalgebra** of $F$ over $R$ is a subset that is simultaneously an $R$-subalgebra of $F$ and a valuation subring of $F$: it is closed under the algebra operations, and for every $x \in F$ it contains $x$ or $x^{-1}$. The two structures share one carrier, so a valuation subalgebra is a single object, not a pair of unrelated subobjects.
--
--   Now let $K$ and $F$ be fields with $F$ a $K$-algebra, and write $K(X)$ for the rational function field over $K$. The class `BundledFunctionField K F` records that $F$ is an **algebraic function field of one variable** over $K$ with a chosen structure map: $F$ is a $K(X)$-algebra, the tower $K \to K(X) \to F$ is a scalar tower, and $F$ is finite-dimensional over $K(X)$.
--
--   A **place** of $F/K$ is a valuation subalgebra $\mathcal O_v$ of $F$ over $K$ that is proper:
--
--   $$\mathcal O_v \subseteq F \text{ is a } K\text{-subalgebra},\qquad \forall x \in F,\; x \in \mathcal O_v \ \lor\ x^{-1} \in \mathcal O_v,\qquad \mathcal O_v \neq F.$$
--
--   The condition $\mathcal O_v \neq \{0\}$ is automatic for a valuation subring of a field and is deliberately not imposed. Places are the algebraic form of the closed points of the smooth projective curve with function field $F$; the ring $\mathcal O_v$ is the local ring at that point.
--
--   The file also supplies the instances that make a place behave like the subring it is: membership and set coercion, closure under $K$-scalars and under the ring operations, the valuation property $x \in v \lor x^{-1} \in v$, and the structure of a $K$-algebra, a scalar tower $K \to \mathcal O_v \to F$, a fraction ring of $F$, and a valuation ring. These instances are what later statements about residue fields, adeles and degrees rely on.
--
--   **Formalization Note.** The declarations are the LeanEval benchmark's own, in the namespace `LeanEval.AlgebraicGeometry.Faltings`, with the benchmark's instance names. Only the benchmark marker attribute and its import are omitted. This layer is sorry-free and compiles in the platform's default environment (Mathlib `0df444a`, Lean v4.33.1).
-- source:
--   LeanEval benchmark problem `faltings`, definition layer (lines 18–59), https://github.com/leanprover/lean-eval/blob/bcc142463a0530038f12e8f1c1e9cce78e129f0a/LeanEval/AlgebraicGeometry/Faltings.lean#L18-L59 ; mirrored verbatim in AxiomMath/Mordell, `Mordell/LeanEval/Faltings.lean` (lines 50–92), https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/LeanEval/Faltings.lean#L50-L92 . Mathematical source: H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Springer GTM 254, 2009, Definitions 1.1.4 and 1.1.8, https://doi.org/10.1007/978-3-540-77086-4 .

import Mathlib

namespace LeanEval
namespace AlgebraicGeometry
namespace Faltings

section ValuationSubalgebra

variable (R F : Type*) [CommSemiring R] [Field F] [Algebra R F]

/-- A valuation subalgebra of `F` over `R`: an `R`-subalgebra which is also a valuation subring. -/
@[ext] structure ValuationSubalgebra extends Subalgebra R F, ValuationSubring F

end ValuationSubalgebra

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- `F` is an algebraic function field of one variable over `K`, with the structure map
`K(X) → F` bundled. -/
class BundledFunctionField extends
  Algebra (RatFunc K) F, IsScalarTower K (RatFunc K) F, FunctionField K F

/-- The type of places of a 1-dimensional function field. See [Stichtenoth,
Definition 1.1.4 and 1.1.8]. We omit the condition `toSubalgebra ≠ ⊥` since it is automatic. -/
@[ext] structure Place extends ValuationSubalgebra K F where
  ne_top : toSubalgebra ≠ ⊤

instance Place.instSetLike : SetLike (Place K F) F where
  coe v := v.carrier
  coe_injective _ _ := Place.ext

instance Place.instSMulMemClass : SMulMemClass (Place K F) K F where
  smul_mem {v} r _ h := v.smul_mem h r

instance Place.instSubringClass : SubringClass (Place K F) F where
  mul_mem {v} := v.mul_mem
  one_mem {v} := v.one_mem
  add_mem {v} := v.add_mem
  zero_mem {v} := v.zero_mem
  neg_mem {v} := v.toValuationSubring.neg_mem _

variable (v : Place K F)

instance Place.instHasMemOrInvMem : HasMemOrInvMem v where
  mem_or_inv_mem := v.mem_or_inv_mem'

instance Place.instAlgebra : Algebra v F := inferInstanceAs (Algebra v.toSubalgebra F)
instance Place.instIsScalarTower : IsScalarTower K v F :=
  inferInstanceAs (IsScalarTower K v.toSubalgebra F)
instance Place.instIsFractionRing : IsFractionRing v F :=
  inferInstanceAs (IsFractionRing v.toValuationSubring F)
instance Place.instValuationRing : ValuationRing v :=
  inferInstanceAs (ValuationRing v.toValuationSubring)

end Faltings
end AlgebraicGeometry
end LeanEval


