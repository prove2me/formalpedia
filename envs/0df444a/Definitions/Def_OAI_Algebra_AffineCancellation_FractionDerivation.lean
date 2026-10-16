-- Prove2me | Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
-- name    : OAI_Algebra_AffineCancellation_FractionDerivation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T18:39:56.565981+00:00
-- url     : https://prove2.me/theorems/4580e601-8391-4353-961d-89c74995793e
-- title:
--   Extending a derivation of a domain to its fraction field via dual numbers
-- statement:
--   Let $k$ be a commutative ring, let $R$ be a commutative $k$-algebra which is an integral domain with fraction field $K$ (compatibly a $k$-algebra), and let $D$ be a $k$-derivation of $R$. Write $K[\varepsilon]=K\oplus K\varepsilon$ with $\varepsilon^2=0$ for the ring of dual numbers over $K$ (the trivial square-zero extension of $K$ by itself), and identify $R$ with its image in $K$.
--
--   1. **The dual-number homomorphism.** The map
--   $$R\to K[\varepsilon],\qquad r\mapsto r+D(r)\,\varepsilon,$$
--   is a $k$-algebra homomorphism; multiplicativity is exactly the Leibniz rule for $D$.
--
--   2. **Its extension to $K$.** Every nonzero $r\in R$ is sent to an element with invertible first component, hence to a unit of $K[\varepsilon]$. By the universal property of the fraction field the homomorphism therefore extends uniquely to a $k$-algebra homomorphism $\Phi_D:K\to K[\varepsilon]$, and the first component of $\Phi_D(z)$ is $z$ for every $z\in K$.
--
--   3. **The extended derivation.** Define $\widetilde D:K\to K$ by $\Phi_D(z)=z+\widetilde D(z)\,\varepsilon$. Then $\widetilde D$ is a $k$-derivation of $K$ extending $D$, and the same holds for all iterates:
--   $$\widetilde D(r)=D(r),\qquad \widetilde D^{\,n}(r)=D^{n}(r)\qquad(r\in R,\ n\ge0).$$
--   Being a derivation, $\widetilde D$ obeys the quotient rule $\widetilde D(r/s)=\bigl(s\,D(r)-r\,D(s)\bigr)/s^2$ for $r,s\in R$, $s\ne0$.
--
--   This extension lets one apply a derivation of a domain to fractions, for instance to form a quotient $t=s/D(s)$ with $\widetilde D(t)=1$ when $D^2(s)=0$ and $D(s)\ne0$; the compatibility of iterates shows that local nilpotence on $R$ is visible on the image of $R$ in $K$.
--
--   **Formalization Note** The dual numbers are `TrivSqZeroExt K K`. The homomorphism of item 1 is `dualMap D`, its extension `dualLift D` (via `IsLocalization.liftAlgHom` over the non-zero-divisors of `R`, with `dualLift_fst`), and the derivation is `extend D`; the stated properties are `extend_algebraMap` and `iterate_algebraMap`, where `R` is identified with its image under `algebraMap R K`. The hypothesis is `IsFractionRing R K` with `K` a field, which makes `R` a domain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/FractionDerivation.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/FractionDerivation.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ComplexCancellation.FractionDerivation
variable {k R K : Type*} [CommRing k] [CommRing R] [Field K]
  [Algebra k R] [Algebra R K] [IsFractionRing R K] [Algebra k K] [IsScalarTower k R K]

open TrivSqZeroExt

def dualMap (D : Derivation k R R) : R →ₐ[k] TrivSqZeroExt K K where
  toFun r := inl (algebraMap R K r) + inr (algebraMap R K (D r))
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' := by
    intro r s
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
        map_add, add_zero, zero_add]
  map_mul' := by
    intro r s
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
        fst_mul, snd_mul, add_zero, zero_add, Derivation.leibniz,
        smul_eq_mul, map_add, map_mul, op_smul_eq_mul, mul_comm]
  commutes' r := by
    apply TrivSqZeroExt.ext <;>
      simp only [fst_add, fst_inl, fst_inr, snd_add, snd_inl, snd_inr,
        algebraMap_eq_inl', Derivation.map_algebraMap, map_zero, add_zero,
        ← IsScalarTower.algebraMap_apply k R K]

omit [IsFractionRing R K] in
@[simp] lemma dualMap_fst (D : Derivation k R R) (r : R) :
    fst (dualMap D r : TrivSqZeroExt K K) = algebraMap R K r := by
  simp only [dualMap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, fst_add, fst_inl, fst_inr, add_zero]

omit [IsFractionRing R K] in
@[simp] lemma dualMap_snd (D : Derivation k R R) (r : R) :
    snd (dualMap D r : TrivSqZeroExt K K) = algebraMap R K (D r) := by
  simp only [dualMap, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, snd_add, snd_inl, snd_inr, zero_add]

def dualLift (D : Derivation k R R) : K →ₐ[k] TrivSqZeroExt K K :=
  IsLocalization.liftAlgHom (M := nonZeroDivisors R) (S := K) (f := dualMap D) (by
    intro y
    apply isUnit_iff_isUnit_fst.mpr
    rw [dualMap_fst]
    exact IsLocalization.map_units K y)

lemma dualLift_algebraMap (D : Derivation k R R) (r : R) :
    dualLift D (algebraMap R K r) = dualMap D r :=
  IsLocalization.lift_eq _ r

lemma dualLift_fst (D : Derivation k R R) (z : K) : fst (dualLift D z) = z := by
  have h : (fstHom k K K).comp (dualLift D) = AlgHom.id k K := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (nonZeroDivisors R)
    ext r
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom,
      AlgHom.comp_apply, dualLift_algebraMap, AlgHom.id_apply]
    exact dualMap_fst D r
  exact DFunLike.congr_fun h z

def extend (D : Derivation k R R) : Derivation k K K :=
  Derivation.mk' (((sndHom K K).restrictScalars k).comp (dualLift D).toLinearMap) (by
    intro x y
    change snd (dualLift D (x*y)) = x * snd (dualLift D y) + y * snd (dualLift D x)
    rw [map_mul, snd_mul, dualLift_fst, dualLift_fst]
    simp only [smul_eq_mul, op_smul_eq_mul, mul_comm])

@[simp] lemma extend_algebraMap (D : Derivation k R R) (r : R) :
    extend D (algebraMap R K r) = algebraMap R K (D r) := by
  change snd (dualLift D (algebraMap R K r)) = _
  rw [dualLift_algebraMap]
  exact dualMap_snd D r

lemma iterate_algebraMap (D : Derivation k R R) (r : R) (n : ℕ) :
    (extend D : K → K)^[n] (algebraMap R K r) = algebraMap R K ((D : R → R)^[n] r) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, extend_algebraMap,
      Function.iterate_succ_apply']

end ComplexCancellation.FractionDerivation

end

end OAI


