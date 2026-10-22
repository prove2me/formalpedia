-- Prove2me | Definitions.Def_MazurTransfer_OriginalCyclicNineteenGroupAlgebraPointsData20261020
-- name    : MazurTransfer_OriginalCyclicNineteenGroupAlgebraPointsData20261020
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-21T21:52:28.969646+00:00
-- url     : https://prove2.me/theorems/4f7dec37-a220-42b5-823a-71a7dbc9ab00
-- title:
--   Original literal nineteenth-root points of the cyclic nineteen group algebra
-- statement:
--   Retain the original cyclic group, generator, literal-root characters, inverse point maps, point equivalence, convolution generator representation and multiplicative point equivalence. All eleven complete original types and whole nonproof values and every original private proof helper type are independently checked. No characteristic, field or invertibility hypothesis is added. Named downstream consumer: same-model selected pi quotient normalization and pushforward of its norm Kummer classes.
-- source:
--   MazurTheorem CyclicNineteenGroupAlgebraPoints by Vas and contributors; original all-algebra literal-root point equivalence, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the group algebra of Z/19 represents LITERAL mu19 over
EVERY coefficient algebra; retain multiplication and every coefficient map.
Named downstream consumer: normalization of the SAME selected integral
pi quotient and pushforward of its actual norm Kummer classes.
-/
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.Convolution
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.RootsOfUnity.Basic

noncomputable section
namespace MazurTransfer.CyclicNineteenGroupAlgebraPoints
open scoped TensorProduct
abbrev Cyclic := Multiplicative (ZMod 19)
def generator : Cyclic := Multiplicative.ofAdd 1

private theorem generator_pow_nineteen : generator ^ 19 = 1 := by
  apply Multiplicative.toAdd.injective
  change 19 • (1 : ZMod 19) = 0
  simpa only [nsmul_eq_mul, mul_one] using (ZMod.natCast_self 19)

private theorem generator_pow_val (m : Cyclic) : generator ^ m.toAdd.val = m := by
  apply Multiplicative.toAdd.injective
  change m.toAdd.val • (1 : ZMod 19) = m.toAdd
  simpa only [nsmul_eq_mul, mul_one] using ZMod.natCast_zmod_val m.toAdd

private theorem character_ext {T : Type} [Monoid T] {f g : Cyclic →* T}
    (h : f generator = g generator) : f = g := by
  apply MonoidHom.ext
  intro m
  rw [← generator_pow_val m, map_pow, map_pow, h]

variable {T : Type} [CommRing T]

private theorem root_nsmul (ζ : rootsOfUnity 19 T) : (19 : ℕ) • Additive.ofMul ζ.val = 0 := by
  change Additive.ofMul (ζ.val ^ 19) = Additive.ofMul (1 : Tˣ)
  exact congrArg Additive.ofMul ((mem_rootsOfUnity 19 ζ.val).mp ζ.property)

def rootLiftData (ζ : rootsOfUnity 19 T) :
    { f : ℤ →+ Additive Tˣ // f 19 = 0 } :=
  ⟨zmultiplesHom (Additive Tˣ) (Additive.ofMul ζ.val), by
    change ((19 : ℕ) : ℤ) • Additive.ofMul ζ.val = 0
    rw [natCast_zsmul]
    exact root_nsmul ζ⟩

def rootCharacter (ζ : rootsOfUnity 19 T) : Cyclic →* Tˣ :=
  (ZMod.lift 19 (rootLiftData ζ)).toMultiplicative

private theorem rootCharacter_generator (ζ : rootsOfUnity 19 T) : rootCharacter ζ generator = ζ.val := by
  have h := ZMod.lift_coe 19 (rootLiftData ζ) 1
  have h' : (ZMod.lift 19 (rootLiftData ζ)) (1 : ZMod 19) = Additive.ofMul ζ.val := by
    simpa [rootLiftData] using h
  exact congrArg Additive.toMul h'

variable (R : Type) [CommRing R] [Algebra R T]

def pointCharacter (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) : Cyclic →* Tˣ :=
  ((MonoidAlgebra.lift R T Cyclic).symm f.ofConv).toHomUnits

def rootOfPoint (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) : rootsOfUnity 19 T :=
  ⟨pointCharacter R f generator, (mem_rootsOfUnity 19 _).mpr (by
    rw [← map_pow, generator_pow_nineteen, map_one])⟩

private theorem rootOfPoint_val (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    ((rootOfPoint R f : Tˣ) : T) = f (MonoidAlgebra.single generator 1) := rfl

def pointOfRoot (ζ : rootsOfUnity 19 T) : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T) :=
  .toConv (MonoidAlgebra.lift R T Cyclic ((Units.coeHom T).comp (rootCharacter ζ)))

private theorem rootOfPoint_pointOfRoot (ζ : rootsOfUnity 19 T) : rootOfPoint R (pointOfRoot R ζ) = ζ := by
  apply Subtype.ext
  apply Units.ext
  rw [rootOfPoint_val]
  change MonoidAlgebra.lift R T Cyclic _ (MonoidAlgebra.single generator 1) = _
  rw [MonoidAlgebra.lift_single, one_smul]
  exact congrArg (fun u : Tˣ => (u : T)) (rootCharacter_generator ζ)

private theorem pointOfRoot_rootOfPoint (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    pointOfRoot R (rootOfPoint R f) = f := by
  apply WithConv.ext
  apply (MonoidAlgebra.lift R T Cyclic).symm.injective
  apply character_ext
  rw [pointOfRoot, WithConv.ofConv_toConv, Equiv.symm_apply_apply]
  change ((rootCharacter (rootOfPoint R f) generator : Tˣ) : T) = _
  rw [rootCharacter_generator]
  rfl

def pointEquiv : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T) ≃ rootsOfUnity 19 T where
  toFun := rootOfPoint R
  invFun := pointOfRoot R
  left_inv := pointOfRoot_rootOfPoint R
  right_inv := rootOfPoint_pointOfRoot R

def generatorRepr : Coalgebra.Repr R (MonoidAlgebra.single generator (1 : R)) Unit where
  index := {()}
  left _ := MonoidAlgebra.single generator 1
  right _ := MonoidAlgebra.single generator 1
  eq := by simp [MonoidAlgebra.comul_single]

private theorem rootOfPoint_mul (f g : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    rootOfPoint R (f * g) = rootOfPoint R f * rootOfPoint R g := by
  apply Subtype.ext
  apply Units.ext
  change (f * g).ofConv (MonoidAlgebra.single generator 1) =
    f.ofConv (MonoidAlgebra.single generator 1) * g.ofConv (MonoidAlgebra.single generator 1)
  have hc : Coalgebra.comul (R := R) (MonoidAlgebra.single generator (1 : R)) =
      MonoidAlgebra.single generator 1 ⊗ₜ[R] MonoidAlgebra.single generator 1 := by
    simp [MonoidAlgebra.comul_single]
  rw [AlgHom.convMul_apply, hc, Algebra.TensorProduct.lift_tmul]

private theorem rootOfPoint_one : rootOfPoint R (1 : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  change algebraMap R T (Coalgebra.counit (R := R) (MonoidAlgebra.single generator (1 : R))) = 1
  simp [MonoidAlgebra.counit_single]

private theorem rootOfPoint_natural {T' : Type} [CommRing T'] [Algebra R T']
    (a : T →ₐ[R] T') (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    rootOfPoint R (.toConv (a.comp f.ofConv)) =
      restrictRootsOfUnity a.toRingHom 19 (rootOfPoint R f) := by
  apply Subtype.ext
  apply Units.ext
  rfl

private theorem cyclic_pow_nineteen (m : Cyclic) : m ^ 19 = 1 := by
  rw [← generator_pow_val m, ← pow_mul, Nat.mul_comm, pow_mul, generator_pow_nineteen, one_pow]

def pointRootsCharacter (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    Cyclic →* rootsOfUnity 19 T where
  toFun m := ⟨pointCharacter R f m, (mem_rootsOfUnity 19 _).mpr (by
    rw [← map_pow, cyclic_pow_nineteen, map_one])⟩
  map_one' := Subtype.ext (map_one (pointCharacter R f))
  map_mul' m n := Subtype.ext (map_mul (pointCharacter R f) m n)

private theorem pointRootsCharacter_generator (f : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T)) :
    pointRootsCharacter R f generator = rootOfPoint R f := rfl

def pointMulEquiv : WithConv (MonoidAlgebra R Cyclic →ₐ[R] T) ≃* rootsOfUnity 19 T where
  __ := pointEquiv R
  map_mul' := rootOfPoint_mul R

end MazurTransfer.CyclicNineteenGroupAlgebraPoints


#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.Cyclic
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.generator
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootLiftData
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootCharacter
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointCharacter
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.rootOfPoint
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointOfRoot
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointEquiv
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.generatorRepr
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointRootsCharacter
#print axioms MazurTransfer.CyclicNineteenGroupAlgebraPoints.pointMulEquiv


