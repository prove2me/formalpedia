-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
-- name    : OAI_Algebra_AffineCancellation_PolynomialSlice
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:46:11.944974+00:00
-- url     : https://prove2.me/theorems/391c51d0-4624-49cc-837f-6276e480158e
-- title:
--   Polynomial model of a domain via a rational slice, and clearing denominators by invariants
-- statement:
--   This file provides three constructions around derivations and their fields of constants. For a field $K$ and a derivation $D$ of $K$ write $K^D=\{r\in K: D(r)=0\}$ for its field of constants.
--
--   1. **The constants as a $k$-algebra.** Let $k$ be a commutative ring, $K$ a field that is a $k$-algebra, and $D$ a $k$-linear derivation of $K$. Since $D$ vanishes on the image of $k$, the structure map $k\to K$ takes values in $K^D$; the resulting ring homomorphism $k\to K^D$ makes $K^D$ a $k$-algebra, and the composite $k\to K^D\subseteq K$ is the structure map of $K$.
--   2. **Clearing denominators by invariants.** Let $k$ be a commutative ring, $R$ an integral domain and $S$ a commutative ring, both $k$-algebras, let $f\colon R\to S$ be a $k$-algebra homomorphism and $D$ a $k$-derivation of $R$. Then
--   $$S_{f,D}=\{\,s\in S:\ f(c)\,s=f(r)\ \text{for some } c,r\in R \text{ with } D(c)=0,\ c\neq0\,\}$$
--   is a $k$-subalgebra of $S$: the elements of $S$ that land in $f(R)$ after multiplication by the image of a nonzero $D$-constant.
--   3. **The polynomial model.** Let $k$ be a field and $R$ an integral domain of characteristic zero that is a $k$-algebra, with fraction field $K$ and canonical embedding $\iota\colon R\to K$. Let $D$ be a locally nilpotent $k$-derivation of $R$ (every $r\in R$ satisfies $D^n(r)=0$ for some $n\ge0$), let $\tilde D$ be its extension to a derivation of $K$ by the quotient rule, and put $F=K^{\tilde D}$. Fix $t\in K$ with $\tilde D(t)=1$ and let $\mathrm{ev}_t\colon F[X]\to K$, $p\mapsto p(t)$, regarded as a $k$-algebra homomorphism. Then $\mathrm{ev}_t$ is injective, and for every $r\in R$ there is $p\in F[X]$ with $p(t)=\iota(r)$. Consequently there is a $k$-algebra homomorphism $\mu\colon R\to F[X]$, the *polynomial model*, determined by
--   $$\mu(r)(t)=\iota(r)\qquad(r\in R),$$
--   that is, $\mathrm{ev}_t\circ\mu=\iota$; here $\mu(r)$ is the unique polynomial over $F$ whose value at $t$ is $r$.
--
--   Since $\iota$ is injective, so is $\mu$: the polynomial model realizes $R$ as a subring of the polynomial ring $F[X]$ in one variable over the field of constants, with the rational slice $t$ playing the role of the variable. This turns questions about a locally nilpotent derivation of an abstract domain into questions about polynomials in one variable, and the subalgebra $S_{f,D}$ of item 2 records which elements of a larger ring are fractions with invariant denominators.
--
--   **Formalization Note** Item 1 consists of `constantMap`, the instance `constantAlgebra` and the scalar-tower instance `constantTower`. Item 2 is `InvariantClearing.subalgebra f D`. In item 3, `PolynomialModel.K` is `FractionRing R`, `F D` is `constants (extend D)`, `ι` is the canonical map, `evaluation` is `Polynomial.aeval t` with scalars restricted to `k`, and `evaluation_injective` and `exists_model` are the two facts used to define `model` by choice; the algebra-homomorphism axioms of `model` follow from the injectivity of `evaluation`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/PolynomialSlice.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/PolynomialSlice.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.DifferentialSlice
variable {k K : Type*} [CommRing k] [Field K] [CharZero K] [Algebra k K]
def constantMap (D : Derivation k K K) : k →+* constants D where
  toFun a := ⟨algebraMap k K a,Derivation.map_algebraMap D a⟩
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_one' := by apply Subtype.ext; exact map_one _
  map_add' a b := by apply Subtype.ext; exact map_add _ a b
  map_mul' a b := by apply Subtype.ext; exact map_mul _ a b
instance constantAlgebra (D : Derivation k K K) : Algebra k (constants D) := (constantMap D).toAlgebra
instance constantTower (D : Derivation k K K) : IsScalarTower k (constants D) K :=
  IsScalarTower.of_algebraMap_eq' rfl
end ComplexCancellation.DifferentialSlice

namespace ComplexCancellation.InvariantClearing
variable {k R S : Type*} [CommRing k] [CommRing R] [IsDomain R] [CommRing S]
  [Algebra k R] [Algebra k S]
def subalgebra (f : R →ₐ[k] S) (D : Derivation k R R) : Subalgebra k S where
  carrier := {s | ∃ c r : R, D c=0 ∧ c ≠ 0 ∧ f c*s=f r}
  algebraMap_mem' a := ⟨1,algebraMap k R a,D.map_one_eq_zero,one_ne_zero,by rw [map_one,one_mul,f.commutes]⟩
  add_mem' := by
    rintro s t ⟨c,r,hc,hcn,hcr⟩ ⟨d,u,hd,hdn,hdu⟩
    refine ⟨c*d,d*r+c*u,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · rw [map_mul,mul_add,map_add,map_mul,map_mul]
      calc f c*f d*s+f c*f d*t = f d*(f c*s)+f c*(f d*t) := by ring
        _ = _ := by rw [hcr,hdu]
  mul_mem' := by
    rintro s t ⟨c,r,hc,hcn,hcr⟩ ⟨d,u,hd,hdn,hdu⟩
    refine ⟨c*d,r*u,?_,mul_ne_zero hcn hdn,?_⟩
    · rw [Derivation.leibniz,hc,hd,smul_zero,smul_zero,add_zero]
    · rw [map_mul,map_mul,show f c*f d*(s*t)=(f c*s)*(f d*t) by ring,hcr,hdu]
end ComplexCancellation.InvariantClearing

namespace ComplexCancellation.PolynomialModel
open Polynomial DifferentialSlice FractionDerivation
variable {k R : Type*} [Field k] [CommRing R] [IsDomain R] [CharZero R] [Algebra k R]
abbrev K := FractionRing R
variable (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
abbrev F := constants (extend (K := K (R := R)) D)
def ι : R →ₐ[k] K (R := R) := IsScalarTower.toAlgHom k R (K (R := R))
variable {t : K (R := R)} (ht : extend D t=1)
def evaluation : Polynomial (F D) →ₐ[k] K (R := R) := (aeval t).restrictScalars k
include ht in
lemma evaluation_injective : Function.Injective (evaluation (D := D) (t := t)) := eval_injective _ ht
include hD ht in
lemma exists_model (r : R) : ∃ p : Polynomial (F D), evaluation (D := D) (t := t) p=ι (k := k) r :=
  RationalSlice.image_is_polynomial D hD ht r

def model : R →ₐ[k] Polynomial (F D) where
  toFun r := Classical.choose (exists_model D hD ht r)
  map_zero' := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht 0),map_zero,map_zero]
  map_one' := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht 1),map_one,map_one]
  map_add' r s := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht (r+s)),map_add,map_add,
      Classical.choose_spec (exists_model D hD ht r),Classical.choose_spec (exists_model D hD ht s)]
  map_mul' r s := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht (r*s)),map_mul,map_mul,
      Classical.choose_spec (exists_model D hD ht r),Classical.choose_spec (exists_model D hD ht s)]
  commutes' a := by
    apply evaluation_injective D ht
    rw [Classical.choose_spec (exists_model D hD ht (algebraMap k R a)),AlgHom.commutes,AlgHom.commutes]
end ComplexCancellation.PolynomialModel

end

end OAI


