-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
-- name    : OAI_Algebra_AffineCancellation_PolynomialDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T19:02:43.025093+00:00
-- url     : https://prove2.me/theorems/c8082cbc-b542-4547-b818-d6c7fffa507d
-- title:
--   Derivations as homomorphisms into dual numbers, and extending a derivation to a polynomial ring
-- statement:
--   Let $k$ be a commutative ring and $R$ a commutative $k$-algebra. For a commutative ring $S$, let $S[\varepsilon]=S\oplus S\varepsilon$ with $\varepsilon^2=0$ be the ring of dual numbers over $S$, with multiplication $(s_0+s_1\varepsilon)(s_0'+s_1'\varepsilon)=s_0s_0'+(s_0s_1'+s_0's_1)\varepsilon$; call $s_0$ and $s_1$ the first and second components.
--
--   1. **From derivations to homomorphisms.** For a $k$-derivation $D$ of $R$, the map
--   $$R\to R[\varepsilon],\qquad r\mapsto r+D(r)\,\varepsilon,$$
--   is a $k$-algebra homomorphism.
--   2. **From homomorphisms to derivations.** Conversely, if $g\colon R\to R[\varepsilon]$ is a $k$-algebra homomorphism whose first component is the identity, i.e. $g(r)=r+g_1(r)\,\varepsilon$ for all $r\in R$, then $g_1$ is a $k$-derivation of $R$.
--   3. **Along a homomorphism.** For a commutative $k$-algebra $S$, a $k$-algebra homomorphism $f\colon R\to S$ and a $k$-derivation $D$ of $R$, the map $r\mapsto f(r)+f(D(r))\,\varepsilon$ is a $k$-algebra homomorphism $R\to S[\varepsilon]$.
--   4. **Extending a derivation to polynomials.** Let $I$ be any index set and $R[X_i: i\in I]$ the polynomial ring. Given a $k$-derivation $D$ of $R$ and polynomials $d_i\in R[X_i: i\in I]$, the $k$-algebra homomorphism $R[X_i:i\in I]\to R[X_i: i\in I][\varepsilon]$ that is the map of item 3 on coefficients and sends $X_i\mapsto X_i+d_i\,\varepsilon$ has first component the identity, so item 2 yields a $k$-derivation $D_d$ of $R[X_i:i\in I]$ with
--   $$D_d(c)=D(c)\quad(c\in R),\qquad D_d(X_i)=d_i\quad(i\in I).$$
--
--   Item 4 is a convenient way to write down a derivation of a polynomial ring with prescribed action on the coefficients and on each variable; explicitly $D_d(q)=q^{D}+\sum_{i}d_i\,\partial q/\partial X_i$, where $q^D$ is obtained by applying $D$ to the coefficients of $q$. Once such a derivation is checked to preserve an ideal, it descends to the quotient ring; this is how Euler-type derivations on rings of the form $R[X_0,X_1]/(X_0^2X_1-v)$ are built.
--
--   **Formalization Note** The dual numbers are `TrivSqZeroExt S S`, with components `fst` and `snd`. Items 1 to 3 are `dual` (with `dual_fst`, `dual_snd`), `fromDual` and `along` (with `along_fst`, `along_snd`). In item 4 the homomorphism is `mvDual D d` (with `mvDual_C`, `mvDual_X`, `mvDual_fst`) and the derivation is `mv D d`, defined as `fromDual (mvDual D d) _`, with computation rules `mv_C` and `mv_X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/PolynomialDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/PolynomialDerivation.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.PolynomialDerivation
open TrivSqZeroExt
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
def dual (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt R R where
  toFun r := inl r + inr (D r)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext <;>
      simp [Derivation.leibniz,smul_eq_mul,mul_comm]
  commutes' r := by apply TrivSqZeroExt.ext <;> simp [algebraMap_eq_inl']
@[simp] lemma dual_fst (D : Derivation k R R) (r : R) : fst (dual D r)=r := by simp [dual]
@[simp] lemma dual_snd (D : Derivation k R R) (r : R) : snd (dual D r)=D r := by simp [dual]
def fromDual (g : R →ₐ[k] TrivSqZeroExt R R)
    (hg : ∀ r, fst (g r)=r) : Derivation k R R :=
  Derivation.mk' (((sndHom R R).restrictScalars k).comp g.toLinearMap) (by
    intro r s
    change snd (g (r*s)) = r * snd (g s)+s * snd (g r)
    rw [map_mul,snd_mul,hg,hg]
    simp only [smul_eq_mul,op_smul_eq_mul,mul_comm])
variable {S : Type*} [CommRing S] [Algebra k S]
def along (f : R →ₐ[k] S) (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt S S where
  toFun r := inl (f r)+inr (f (D r))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' r s := by apply TrivSqZeroExt.ext <;> simp
  map_mul' r s := by
    apply TrivSqZeroExt.ext <;>
      simp [Derivation.leibniz,smul_eq_mul,mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext <;> simp [algebraMap_eq_inl']
@[simp] lemma along_fst (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) :
    fst (along f D r)=f r := by simp [along]
@[simp] lemma along_snd (f : R →ₐ[k] S) (D : Derivation k R R) (r : R) :
    snd (along f D r)=f (D r) := by simp [along]

variable {ι : Type*}
def mvDual (D : Derivation k R R) (d : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[k] TrivSqZeroExt (MvPolynomial ι R) (MvPolynomial ι R) where
  __ := MvPolynomial.eval₂Hom (along (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) D).toRingHom
    (fun i => inl (MvPolynomial.X i)+inr (d i))
  commutes' a := by
    change MvPolynomial.eval₂ _ _ (MvPolynomial.C (algebraMap k R a)) = _
    rw [MvPolynomial.eval₂_C]
    exact (along (IsScalarTower.toAlgHom k R (MvPolynomial ι R)) D).commutes a
lemma mvDual_C (D : Derivation k R R) (d : ι → MvPolynomial ι R) (r : R) :
    mvDual D d (MvPolynomial.C r)=inl (MvPolynomial.C r)+inr (MvPolynomial.C (D r)) :=
  MvPolynomial.eval₂_C _ _ _
lemma mvDual_X (D : Derivation k R R) (d : ι → MvPolynomial ι R) (i : ι) :
    mvDual D d (MvPolynomial.X i)=inl (MvPolynomial.X i)+inr (d i) :=
  MvPolynomial.eval₂_X _ _ _
lemma mvDual_fst (D : Derivation k R R) (d : ι → MvPolynomial ι R) (p : MvPolynomial ι R) :
    fst (mvDual D d p)=p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [mvDual_C]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp => simp [mvDual_X,hp]
def mv (D : Derivation k R R) (d : ι → MvPolynomial ι R) :
    Derivation k (MvPolynomial ι R) (MvPolynomial ι R) := fromDual (mvDual D d) (mvDual_fst D d)
@[simp] lemma mv_C (D : Derivation k R R) (d : ι → MvPolynomial ι R) (r : R) :
    mv D d (MvPolynomial.C r)=MvPolynomial.C (D r) := by
  change snd (mvDual D d (MvPolynomial.C r))=_
  simp [mvDual_C]
@[simp] lemma mv_X (D : Derivation k R R) (d : ι → MvPolynomial ι R) (i : ι) :
    mv D d (MvPolynomial.X i)=d i := by
  change snd (mvDual D d (MvPolynomial.X i))=_
  simp [mvDual_X]
end ComplexCancellation.PolynomialDerivation

end

end OAI


