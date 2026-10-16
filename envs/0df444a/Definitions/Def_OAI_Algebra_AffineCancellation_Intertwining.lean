-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining
-- name    : OAI_Algebra_AffineCancellation_Intertwining
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:41:45.318761+00:00
-- url     : https://prove2.me/theorems/565a21d3-8ccb-4648-bb1e-51a0e8b476b7
-- title:
--   The subalgebra on which an algebra homomorphism intertwines two derivations
-- statement:
--   Let $k$ be a commutative ring, $R$ and $S$ commutative $k$-algebras, $f:R\to S$ a $k$-algebra homomorphism, $D$ a $k$-derivation of $R$ and $E$ a $k$-derivation of $S$. The file defines the set of elements on which $f$ carries $D$ to $E$,
--   $$\mathrm{Int}(f;D,E)=\bigl\{\,r\in R:\ E\bigl(f(r)\bigr)=f\bigl(D(r)\bigr)\,\bigr\},$$
--   as a $k$-subalgebra of $R$: it contains the image of $k$ in $R$ (both derivations vanish on scalars) and it is closed under addition and multiplication (the latter by the Leibniz rule for $D$ and $E$).
--
--   Because it is a subalgebra, the identity $E\circ f=f\circ D$ holds on all of $R$ as soon as it holds on a set of $k$-algebra generators of $R$. This is the device used to verify that explicit algebra homomorphisms, for instance maps out of quotients of polynomial rings, are compatible with given derivations by checking finitely many generators.
--
--   **Formalization Note** The definition is `DerivationIntertwining.subalgebra f D E : Subalgebra k R`, with carrier `{r | E (f r) = f (D r)}`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/Intertwining.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Intertwining.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ComplexCancellation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler

namespace OAI

noncomputable section

namespace ComplexCancellation.DerivationIntertwining
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
def subalgebra (f : R →ₐ[k] S) (D : Derivation k R R) (E : Derivation k S S) : Subalgebra k R where
  carrier := {r | E (f r)=f (D r)}
  algebraMap_mem' a := by
    change E (f (algebraMap k R a))=f (D (algebraMap k R a))
    rw [f.commutes,E.map_algebraMap,D.map_algebraMap,map_zero]
  add_mem' := by
    intro r s hr hs
    change E (f r)=f (D r) at hr
    change E (f s)=f (D s) at hs
    change E (f (r+s))=f (D (r+s))
    rw [map_add,map_add,hr,hs,map_add,map_add]
  mul_mem' := by
    intro r s hr hs
    change E (f r)=f (D r) at hr
    change E (f s)=f (D s) at hs
    change E (f (r*s))=f (D (r*s))
    rw [map_mul,Derivation.leibniz,Derivation.leibniz,hr,hs,smul_eq_mul,smul_eq_mul,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul]
end ComplexCancellation.DerivationIntertwining

end

end OAI


