-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
-- name    : OAI_Algebra_AffineCancellation_RelativeClearing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:35:47.990581+00:00
-- url     : https://prove2.me/theorems/604a80c8-0218-419f-86d1-3a1c99624aa9
-- title:
--   Subalgebras of elements cleared by nonzero constants and of elements with stable derivative
-- statement:
--   Let $k$ be a commutative ring.
--
--   1. **Elements cleared by nonzero constants.** Let $A$ be a commutative $k$-algebra that is an integral domain, let $B$ and $R$ be commutative $k$-algebras, let $h:A\to B$ and $f:B\to R$ be $k$-algebra homomorphisms, and let $D$ be a $k$-derivation of $A$. The relative clearing subalgebra is
--   $$\mathcal{C}(h,f,D)=\bigl\{\,r\in R:\ \text{there are } c\in A \text{ and } b\in B \text{ with } D(c)=0,\ c\ne0,\ f(h(c))\,r=f(b)\,\bigr\}.$$
--   It is a $k$-subalgebra of $R$: it contains the image of $k$ (take $c=1$), and it is closed under sums and products because the product of two nonzero elements of $\ker D$ is again a nonzero element of $\ker D$ (here one uses that $A$ is a domain). In words, $\mathcal{C}(h,f,D)$ consists of the elements of $R$ whose denominator relative to $f(B)$ can be cleared by a nonzero $D$-constant.
--
--   2. **Elements with stable derivative.** Let $B$ and $R$ be commutative $k$-algebras, $f:B\to R$ a $k$-algebra homomorphism and $E$ a $k$-derivation of $R$. Then
--   $$\mathcal{S}(f,E)=\bigl\{\,b\in B:\ E(f(b))=f(t)\ \text{for some } t\in B\,\bigr\}$$
--   is a $k$-subalgebra of $B$; closure under products follows from the Leibniz rule $E(f(b)f(b'))=f(b)E(f(b'))+f(b')E(f(b))$.
--
--   These subalgebras organize a clearing-of-denominators argument for derivations. If all values $E(f(b))$ lie in $\mathcal{C}(h,f,D)$, a single nonzero constant $c$ clears $E$ on any finite set of elements at once; after multiplying $E$ by $f(h(c))$, the generators of $B$ lie in the stable subalgebra $\mathcal{S}$, hence all of $B$ does, and the rescaled derivation restricts from $R$ to the image of $B$.
--
--   **Formalization Note** The two definitions are `RelativeClearing.subalgebra h f D : Subalgebra k R` (with the hypothesis `IsDomain A`) and `DerivationRange.stable f E : Subalgebra k B`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/RelativeClearing.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/RelativeClearing.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.RelativeClearing
variable {k A B R : Type*} [CommRing k] [CommRing A] [IsDomain A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]
variable (h : A →ₐ[k] B) (f : B →ₐ[k] R) (D : Derivation k A A)
def subalgebra : Subalgebra k R where
  carrier := {r | ∃ c : A, ∃ b : B, D c=0 ∧ c≠0 ∧ f (h c)*r=f b}
  algebraMap_mem' a := ⟨1,algebraMap k B a,D.map_one_eq_zero,one_ne_zero,by simp⟩
  add_mem' := by
    rintro r s ⟨c,b,hc,hcn,hcb⟩ ⟨d,e,hd,hdn,hde⟩
    refine ⟨c*d,h d*b+h c*e,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · simp only [map_mul,map_add]
      calc f (h c)*f (h d)*(r+s)=f (h d)*(f (h c)*r)+f (h c)*(f (h d)*s) := by ring
        _ = _ := by rw [hcb,hde]
  mul_mem' := by
    rintro r s ⟨c,b,hc,hcn,hcb⟩ ⟨d,e,hd,hdn,hde⟩
    refine ⟨c*d,b*e,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · simp only [map_mul]
      calc f (h c)*f (h d)*(r*s)=(f (h c)*r)*(f (h d)*s) := by ring
        _ = _ := by rw [hcb,hde]
end ComplexCancellation.RelativeClearing

namespace ComplexCancellation.DerivationRange
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R] [Algebra k B] [Algebra k R]
def stable (f : B →ₐ[k] R) (E : Derivation k R R) : Subalgebra k B where
  carrier := {b | ∃ t : B, E (f b)=f t}
  algebraMap_mem' a := ⟨0,by rw [f.commutes,E.map_algebraMap,map_zero]⟩
  add_mem' := by
    rintro r s ⟨t,ht⟩ ⟨u,hu⟩
    exact ⟨t+u,by rw [map_add,map_add,ht,hu,map_add]⟩
  mul_mem' := by
    rintro r s ⟨t,ht⟩ ⟨u,hu⟩
    exact ⟨r*u+s*t,by rw [map_mul,Derivation.leibniz,ht,hu,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul]⟩
end ComplexCancellation.DerivationRange

end

end OAI


