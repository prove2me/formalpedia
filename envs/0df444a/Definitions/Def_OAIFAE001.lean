-- Prove2me | Definitions.Def_OAIFAE001
-- name    : OAIFAE001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-24T19:22:08.769178+00:00
-- url     : https://prove2.me/theorems/e18d989c-4cf7-4fbf-9290-8446b798f2bf
-- title:
--   Definitions bundle OAIFAE001 of the split of OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteAlgebraicEnvelopes.main`, carved from OpenAI's openai/math development (OpenAI, *Finite algebraic envelopes and the Boone–Higman conjecture*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 658 declarations of OpenAI's Lean: 255 definitions, 14 inductive types or structures, 13 instances and 376 theorems. The definitions and types are `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.Data`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.Hom`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.Hom.comp`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.Hom.id`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.Object`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.Object.tensor`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.SymmetryData`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.associator`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.associatorVal`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.braiding`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.braidingVal`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.combHead`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.combSwap`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.exchangeEquiv`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.firstSwap`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.iso`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.left`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.leftUnitor`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.middleSwap`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.monoidal`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.monoidalStruct`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.right`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.rightPower`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.rightUnitor`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.secondSwap`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.sumEquiv`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.sumIndex`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.sumPermutation`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.symmetric`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.tensorHom`, `OAI.FiniteAlgebraicEnvelopes.BinaryGroupCategory.tensorVal`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Irreducible`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.Mon`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.Rel`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Quotient.present`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.RulesEq`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.lexBool`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.lexFinish`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Search.lexFoldStep`, `OAI.FiniteAlgebraicEnvelopes.Bootstrap.Selectors.BoundedEq` and 229 more.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler, in whole or in part: `ActionEnvelope`, `AffineModules`, `AlgebraPresentations`, `Basic`, `BinaryCategory`, `BinaryCoherence`, `CantorBricks`, `Contracted`, `Corners`, `DecoratedPresentation`, `Effectivity`, `EndpointCoherence`, `Enveloping`, `FinitePresentation`, `Generators`, `GroupInput`, `MappingTori`, `MonoidAlgebras`, `Normalization`, `PartialAffine`, `Quotients`, `Rewriting`, `Selectors`, `SelfReference`, `Simulator`, `Steinberg`, `SteinbergLimits`, `SteinbergPresentation`, `TapeFolding`, `Transition`, `TreeRefinement`, `Trees`, `UniformPaths`, `Validator`, `WordProblem`.
--
--   **Imports.** It imports the published bundle `Def_BooneHigman`.
--
--   **Imported by** (directly, in this split): the bundles `OAIFAE002` and `OAIFAE003`; the statement `OAI.FiniteAlgebraicEnvelopes.envelope`.
-- source:
--   OpenAI, Finite algebraic envelopes and the Boone–Higman conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Finite-algebraic-envelopes-and-the-Boone-Higman-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/GroupTheory/BooneHigman, lean/OAI/Computability/FiniteCompiler at commit adc7f12

import Mathlib
import Definitions.Def_BooneHigman

section
-- module Solutions.OAIFAE.Steinberg
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Nonunital correction, Steinberg groups, corners, and kernel annihilation.
-/


namespace FiniteAlgebraicEnvelopes

universe u


/-! The correction for a nonunital coefficient map in the affine transition and product identities.
The proof works over a noncommutative ring. -/


section NonunitalCorrection
variable {R S : Type*} [Ring R] [Ring S]

/-- Adjoining the unchanged complementary identity to a nonunital map. -/
def correctedMap (ψ : R →ₙ+* S) : R →* S where
  toFun x := 1 + ψ (x - 1)
  map_one' := by simp
  map_mul' x y := by
    have h : x * y - 1 = (x - 1) + (y - 1) + (x - 1) * (y - 1) := by
      noncomm_ring
    rw [h, map_add, map_add, map_mul]
    noncomm_ring

@[simp] theorem correctedMap_apply (ψ : R →ₙ+* S) (x : R) :
    correctedMap ψ x = 1 + ψ (x - 1) := rfl

/-- Entrywise extension before adjoining the unchanged identity. -/
def matrixNonunitalMap {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : R →ₙ+* S) :
    Matrix ι ι R →ₙ+* Matrix ι ι S where
  toFun A := A.map ψ
  map_zero' := by ext; simp
  map_add' A B := by ext; simp
  map_mul' A B := Matrix.map_mul

@[simp] theorem matrixNonunitalMap_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : R →ₙ+* S) (A : Matrix ι ι R) : matrixNonunitalMap ψ A = A.map ψ := rfl

end NonunitalCorrection


/-! The Steinberg presentation in the Steinberg kernel argument.  No stability or centrality
 theorem is assumed.  Root indices are restricted to the off-diagonal. -/
namespace Steinberg
open scoped commutatorElement

variable {ι R S : Type*} [Ring R] [Ring S]

section MatrixRepresentation
variable [Fintype ι] [DecidableEq ι]

/-- Left multiplication of columns, viewed purely additively. -/
def mulVecAddHom (A : Matrix ι ι R) : (ι → R) →+ (ι → R) where
  toFun v := Matrix.mulVec A v
  map_zero' := Matrix.mulVec_zero A
  map_add' := Matrix.mulVec_add A

omit [DecidableEq ι] in
@[simp] theorem mulVecAddHom_apply (A : Matrix ι ι R) (v : ι → R) :
    mulVecAddHom A v = Matrix.mulVec A v := rfl

def vecMulAddHom (A : Matrix ι ι R) : (ι → R) →+ (ι → R) where
  toFun v := Matrix.vecMul v A
  map_zero' := Matrix.zero_vecMul A
  map_add' := Matrix.add_vecMul A

omit [DecidableEq ι] in
@[simp] theorem vecMulAddHom_apply (A : Matrix ι ι R) (v : ι → R) :
    vecMulAddHom A v = Matrix.vecMul v A := rfl

theorem vecMul_single_matrix (i j : ι) (a : R) (v : ι → R) :
    Matrix.vecMul v (Matrix.single i j a) = Pi.single j (v i * a) := by
  ext l
  by_cases h : j = l
  · subst l; simp [Matrix.vecMul, dotProduct, Matrix.single]
  · simp [Matrix.vecMul, dotProduct, Matrix.single, h]

omit [Ring R] [Ring S] [Fintype ι] [DecidableEq ι] in
theorem commute_commutator {T : Type*} [_root_.Group T] {a b c : T}
    (hb : Commute a b) (hc : Commute a c) : Commute a ⁅b, c⁆ := by
  rw [commutatorElement_def]
  exact ((hb.mul_right hc).mul_right hb.inv_right).mul_right hc.inv_right

end MatrixRepresentation


/-! Orthogonal equivalent corners, as specified by (corner-equivalence)
in the Steinberg kernel argument. The symbol `e` below is the specified d*, not an involution. -/
structure CornerPair (R : Type*) [Ring R] where
  E : R
  F : R
  d : R
  e : R
  E_idem : E * E = E
  F_idem : F * F = F
  EF : E * F = 0
  FE : F * E = 0
  d_support : F * d * E = d
  e_support : E * e * F = e
  ed : e * d = E
  de : d * e = F

namespace CornerPair

variable (c : CornerPair R)

def swap : CornerPair R where
  E := c.F
  F := c.E
  d := c.e
  e := c.d
  E_idem := c.F_idem
  F_idem := c.E_idem
  EF := c.FE
  FE := c.EF
  d_support := c.e_support
  e_support := c.d_support
  ed := c.de
  de := c.ed

theorem d_left : c.F * c.d = c.d := by
  calc
    c.F * c.d = c.F * (c.F * c.d * c.E) := by rw [c.d_support]
    _ = c.F * c.d * c.E := by simp only [← mul_assoc, c.F_idem]
    _ = c.d := c.d_support

theorem d_right : c.d * c.E = c.d := by
  calc
    c.d * c.E = (c.F * c.d * c.E) * c.E := by rw [c.d_support]
    _ = c.F * c.d * c.E := by rw [mul_assoc, c.E_idem]
    _ = c.d := c.d_support

theorem d_left_zero : c.E * c.d = 0 := by
  rw [← c.d_left, ← mul_assoc, c.EF, zero_mul]

theorem d_right_zero : c.d * c.F = 0 := by
  rw [← c.d_right, mul_assoc, c.EF, mul_zero]

theorem e_left : c.E * c.e = c.e := c.swap.d_left

theorem e_right : c.e * c.F = c.e := c.swap.d_right

theorem e_left_zero : c.F * c.e = 0 := c.swap.d_left_zero

theorem e_right_zero : c.e * c.E = 0 := c.swap.d_right_zero

theorem left_of_corner {y : R} (hy : c.E * y * c.E = y) : c.E * y = y := by
  calc
    c.E * y = c.E * (c.E * y * c.E) := by rw [hy]
    _ = c.E * y * c.E := by simp only [← mul_assoc, c.E_idem]
    _ = y := hy

theorem right_of_corner {y : R} (hy : c.E * y * c.E = y) : y * c.E = y := by
  calc
    y * c.E = (c.E * y * c.E) * c.E := by rw [hy]
    _ = c.E * y * c.E := by rw [mul_assoc, c.E_idem]
    _ = y := hy

theorem e_mul_corner {y : R} (hy : c.E * y * c.E = y) : c.e * y = 0 := by
  rw [← c.left_of_corner hy, ← mul_assoc, c.e_right_zero, zero_mul]

theorem corner_mul_d {y : R} (hy : c.E * y * c.E = y) : y * c.d = 0 := by
  rw [← c.right_of_corner hy, mul_assoc, c.d_left_zero, mul_zero]

end CornerPair

section Compression
variable [Fintype ι] [DecidableEq ι]

omit [Ring R] [Ring S] [Fintype ι] [DecidableEq ι] in
theorem conjugate_mul {T : Type*} [_root_.Group T] (a b z : T) :
    (a * b) * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group

end Compression

section OrthogonalCorners
variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem corner_product_zero {E F a b : R} (hEF : E * F = 0)
    (ha : E * a * E = a) (hb : F * b * F = b) : a * b = 0 := by
  calc
    a * b = (E * a * E) * (F * b * F) := by rw [ha, hb]
    _ = E * a * (E * F) * b * F := by noncomm_ring
    _ = 0 := by rw [hEF]; simp

end OrthogonalCorners

section BalancedDiagonal
variable [Fintype ι] [DecidableEq ι]

def pairScalar (b : R) (p q i : ι) : R := if i = p ∨ i = q then b else 1

end BalancedDiagonal

namespace CornerPair
variable (c : CornerPair R)

theorem dd : c.d * c.d = 0 := by
  calc
    c.d * c.d = (c.d * c.E) * c.d := by rw [c.d_right]
    _ = 0 := by rw [mul_assoc, c.d_left_zero, mul_zero]

theorem ee : c.e * c.e = 0 := c.swap.dd

/-- The involutive scalar interchanging the two corners. -/
def swapScalar : R := c.d + c.e + 1 - c.E - c.F

theorem swapScalar_square : c.swapScalar * c.swapScalar = 1 := by
  simp only [swapScalar, add_mul, mul_add, sub_mul, mul_sub, one_mul, mul_one,
    c.dd, c.ee, c.ed, c.de, c.E_idem, c.F_idem, c.EF, c.FE, c.d_left,
    c.d_right, c.d_left_zero, c.d_right_zero, c.e_left, c.e_right,
    c.e_left_zero, c.e_right_zero]
  abel

theorem swapScalar_E : c.swapScalar * c.E = c.d := by
  simp only [swapScalar, add_mul, sub_mul, one_mul, c.d_right, c.e_right_zero,
    c.E_idem, c.FE]
  abel

theorem d_swapScalar : c.d * c.swapScalar = c.F := by
  simp only [swapScalar, mul_add, mul_sub, mul_one, c.dd, c.de,
    c.d_right, c.d_right_zero]
  abel

theorem swapScalar_E_swapScalar : c.swapScalar * c.E * c.swapScalar = c.F := by
  rw [c.swapScalar_E, c.d_swapScalar]

theorem swapScalar_commute {a : R} (hE : Commute c.E a) (hF : Commute c.F a)
    (hd : Commute c.d a) (he : Commute c.e a) : Commute c.swapScalar a :=
  (((hd.add_left he).add_left (Commute.one_left a)).sub_left hE).sub_left hF

end CornerPair

/-- Cutting down a nonunital coefficient map by a commuting idempotent. -/
def cornerMap (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) : R →ₙ+* S where
  toFun a := ψ a * E
  map_zero' := by simp
  map_add' a b := by simp [add_mul]
  map_mul' a b := by
    rw [map_mul]
    calc
      ψ a * ψ b * E = ψ a * ψ b * (E * E) := by rw [hE]
      _ = ψ a * (ψ b * E) * E := by simp only [mul_assoc]
      _ = ψ a * (E * ψ b) * E := by rw [(hc b).eq]
      _ = ψ a * E * (ψ b * E) := by simp only [mul_assoc]

@[simp] theorem cornerMap_apply (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) (a : R) : cornerMap ψ E hE hc a = ψ a * E := rfl

theorem cornerMap_corner (ψ : R →ₙ+* S) (E : S) (hE : E * E = E)
    (hc : ∀ a, Commute E (ψ a)) (a : R) :
    E * cornerMap ψ E hE hc a * E = cornerMap ψ E hE hc a := by
  simp only [cornerMap_apply]
  rw [← mul_assoc E, (hc a).eq]
  simp only [mul_assoc, hE]

theorem orthogonal_sum_idem {E F : S} (hE : E * E = E) (hF : F * F = F)
    (hEF : E * F = 0) (hFE : F * E = 0) : (E + F) * (E + F) = E + F := by
  simp only [add_mul, mul_add, hE, hF, hEF, hFE, zero_add, add_zero]

/-- A pair of supported one-sided inverse elements, with the prescribed
commutation with the nonunital coefficient image. -/
structure SupportedPair (ψ : R →ₙ+* S) where
  U : S
  V : S
  VU : V * U = ψ 1
  PU : ψ 1 * U = U
  UP : U * ψ 1 = U
  PV : ψ 1 * V = V
  VP : V * ψ 1 = V
  commU : ∀ a, Commute U (ψ a)
  commV : ∀ a, Commute V (ψ a)

namespace SupportedPair
variable {ψ : R →ₙ+* S} (p q : SupportedPair ψ)

def E : S := p.U * p.V

theorem E_idem : p.E * p.E = p.E := by
  change (p.U * p.V) * (p.U * p.V) = p.U * p.V
  calc
    _ = p.U * (p.V * p.U) * p.V := by simp only [mul_assoc]
    _ = p.U * p.V := by rw [p.VU, p.UP]

theorem commE (a : R) : Commute p.E (ψ a) := (p.commU a).mul_left (p.commV a)

/-- Composition gives the descendants 00 and 01 of the zero corner. -/
def comp : SupportedPair ψ where
  U := p.U * q.U
  V := q.V * p.V
  VU := by
    calc
      q.V * p.V * (p.U * q.U) = q.V * (p.V * p.U) * q.U := by simp only [mul_assoc]
      _ = ψ 1 := by rw [p.VU, q.VP, q.VU]
  PU := by rw [← mul_assoc, p.PU]
  UP := by rw [mul_assoc, q.UP]
  PV := by rw [← mul_assoc, q.PV]
  VP := by rw [mul_assoc, p.VP]
  commU a := (p.commU a).mul_left (q.commU a)
  commV a := (q.commV a).mul_left (p.commV a)

theorem E_mul_E (hpq : p.V * q.U = 0) : p.E * q.E = 0 := by
  change (p.U * p.V) * (q.U * q.V) = 0
  calc
    _ = p.U * (p.V * q.U) * q.V := by simp only [mul_assoc]
    _ = 0 := by rw [hpq]; simp

/-- Explicit equivalence data between two orthogonal supported corners. -/
def corners (hpq : p.V * q.U = 0) (hqp : q.V * p.U = 0) : CornerPair S where
  E := p.E
  F := q.E
  d := q.U * p.V
  e := p.U * q.V
  E_idem := p.E_idem
  F_idem := q.E_idem
  EF := p.E_mul_E q hpq
  FE := q.E_mul_E p hqp
  d_support := by
    change (q.U * q.V) * (q.U * p.V) * (p.U * p.V) = q.U * p.V
    calc
      _ = q.U * (q.V * q.U) * (p.V * p.U) * p.V := by simp only [mul_assoc]
      _ = q.U * p.V := by rw [q.VU, p.VU, q.UP, q.UP]
  e_support := by
    change (p.U * p.V) * (p.U * q.V) * (q.U * q.V) = p.U * q.V
    calc
      _ = p.U * (p.V * p.U) * (q.V * q.U) * q.V := by simp only [mul_assoc]
      _ = p.U * q.V := by rw [p.VU, q.VU, p.UP, p.UP]
  ed := by
    change (p.U * q.V) * (q.U * p.V) = p.U * p.V
    calc
      _ = p.U * (q.V * q.U) * p.V := by simp only [mul_assoc]
      _ = p.U * p.V := by rw [q.VU, p.UP]
  de := by
    change (q.U * p.V) * (p.U * q.V) = q.U * q.V
    calc
      _ = q.U * (p.V * p.U) * q.V := by simp only [mul_assoc]
      _ = q.U * q.V := by rw [p.VU, q.UP]

theorem comp_cross (r : SupportedPair ψ) : (p.comp q).V * (p.comp r).U = q.V * r.U := by
  change (q.V * p.V) * (p.U * r.U) = q.V * r.U
  calc
    _ = q.V * (p.V * p.U) * r.U := by simp only [mul_assoc]
    _ = q.V * r.U := by rw [p.VU, q.VP]

theorem comp_cross_right (r : SupportedPair ψ) (hpq : p.V * q.U = 0) :
    (p.comp r).V * q.U = 0 := by
  change (r.V * p.V) * q.U = 0
  rw [mul_assoc, hpq, mul_zero]

theorem comp_cross_left (r : SupportedPair ψ) (hqp : q.V * p.U = 0) :
    q.V * (p.comp r).U = 0 := by
  change q.V * (p.U * r.U) = 0
  rw [← mul_assoc, hqp, zero_mul]

theorem comp_split (hsum : p.E + q.E = ψ 1) :
    (p.comp p).E + (p.comp q).E = p.E := by
  calc
    (p.comp p).E + (p.comp q).E = p.U * (p.E + q.E) * p.V := by
      dsimp [comp, E]
      noncomm_ring
    _ = p.E := by rw [hsum, p.UP]; rfl

end SupportedPair

end Steinberg

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Enveloping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Tensor-enveloping algebra actions, simplicity, and elementary row control.
-/


namespace FiniteAlgebraicEnvelopes.Enveloping
open scoped TensorProduct
variable (k B : Type*) [CommRing k] [Ring B] [Algebra k B]
abbrev Coeff := B ⊗[k] Bᵐᵒᵖ

/-- Right multiplication, with its order correctly reversed. -/
def right : Bᵐᵒᵖ →ₐ[k] Module.End k B where
  toFun b := LinearMap.mulRight k b.unop
  map_one' := by ext a; simp
  map_mul' b c := by ext a; simp [mul_assoc]
  map_zero' := by ext a; simp
  map_add' b c := by ext a; simp [mul_add]
  commutes' r := by ext a; simp [Algebra.smul_def,Algebra.commutes]

/-- The true enveloping-ring action on the algebra. -/
def representation : Coeff k B →ₐ[k] Module.End k B :=
  Algebra.TensorProduct.lift (Algebra.lmul k B) (right k B) (by
    intro a b
    ext x
    exact (mul_assoc a x b.unop).symm)

instance module : Module (Coeff k B) B := Module.compHom B (representation k B).toRingHom

@[simp] theorem tmul_smul (a b m : B) :
    (a ⊗ₜ[k] MulOpposite.op b : Coeff k B) • m = a*m*b := by
  change representation k B (a ⊗ₜ[k] MulOpposite.op b) m = _
  simp [representation,right,mul_assoc]

def eval : Coeff k B →ₗ[Coeff k B] B := LinearMap.toSpanSingleton (Coeff k B) B 1
theorem eval_apply (r : Coeff k B) : eval k B r = r • (1:B) := rfl
@[simp] theorem eval_tmul (a b : B) : eval k B (a ⊗ₜ[k] MulOpposite.op b) = a*b := by simp [eval_apply]

def difference (b : B) : Coeff k B := b ⊗ₜ[k] (1:Bᵐᵒᵖ) - (1:B) ⊗ₜ[k] MulOpposite.op b

@[simp] theorem difference_zero : difference k B 0 = 0 := by simp [difference]
@[simp] theorem difference_one : difference k B 1 = 0 := by simp [difference]
theorem difference_add (b c : B) : difference k B (b+c) = difference k B b + difference k B c := by
  simp only [difference,TensorProduct.add_tmul,MulOpposite.op_add,TensorProduct.tmul_add]
  abel
theorem difference_mul (b c : B) : difference k B (b*c) =
    (b ⊗ₜ[k] (1:Bᵐᵒᵖ)) * difference k B c +
    ((1:B) ⊗ₜ[k] MulOpposite.op c) * difference k B b := by
  simp only [difference,mul_sub,Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,
    ← MulOpposite.op_mul]
  abel
@[simp] theorem difference_algebraMap (r : k) : difference k B (algebraMap k B r) = 0 := by
  simp [difference,Algebra.algebraMap_eq_smul_one,TensorProduct.smul_tmul,TensorProduct.tmul_smul]

variable {k B}
/-- The generators of the kernel, exactly d_y=y⊗1−1⊗yᵒᵖ. -/
def relations (Y : Set B) : Submodule (Coeff k B) (Coeff k B) :=
  Submodule.span (Coeff k B) (difference k B '' Y)

/-- The product identity propagates the kernel generators through the whole algebra. -/
theorem difference_mem (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) (b : B) :
    difference k B b ∈ relations (k:=k) Y := by
  have hb : b ∈ Algebra.adjoin k Y := by rw [hgen]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem b hb => exact Submodule.subset_span ⟨b,hb,rfl⟩
  | algebraMap r => simp
  | add b c _ _ hb hc => rw [difference_add]; exact Submodule.add_mem _ hb hc
  | mul b c _ _ hb hc =>
    rw [difference_mul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hc) (Submodule.smul_mem _ _ hb)

theorem relations_le_kernel (Y : Set B) : relations (k:=k) Y ≤ (eval k B).ker := by
  apply Submodule.span_le.mpr
  rintro _ ⟨b,hb,rfl⟩
  change eval k B (difference k B b) = 0
  simp only [difference,map_sub]
  simp only [← MulOpposite.op_one,eval_tmul,mul_one,one_mul,sub_self]

/-- Every tensor is congruent to its value tensored with one. -/
theorem reduce_tensor (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) (r : Coeff k B) :
    r - (eval k B r ⊗ₜ[k] (1:Bᵐᵒᵖ)) ∈ relations (k:=k) Y := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have hb := difference_mem Y hgen b.unop
    have h := Submodule.smul_mem (relations (k:=k) Y) (a ⊗ₜ[k] (1:Bᵐᵒᵖ)) hb
    have hev : eval k B (a ⊗ₜ[k] b) = a*b.unop := by
      simpa only [MulOpposite.op_unop] using eval_tmul k B a b.unop
    have he : a ⊗ₜ[k] b - (eval k B (a ⊗ₜ[k] b) ⊗ₜ[k] (1:Bᵐᵒᵖ)) =
        -((a ⊗ₜ[k] (1:Bᵐᵒᵖ)) * difference k B b.unop) := by
      simp only [difference,mul_sub,Algebra.TensorProduct.tmul_mul_tmul,one_mul,mul_one,
        MulOpposite.op_unop,neg_sub,hev]
    rw [he]
    exact Submodule.neg_mem _ h
  | add r s hr hs =>
    simpa only [map_add,TensorProduct.add_tmul,add_sub_add_comm] using Submodule.add_mem _ hr hs

theorem kernel_eq (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) :
    (eval k B).ker = relations (k:=k) Y := by
  apply le_antisymm
  · intro r hr
    have h := reduce_tensor Y hgen r
    have hz : eval k B r = 0 := hr
    simpa [hz] using h
  · exact relations_le_kernel Y

theorem eval_surjective : Function.Surjective (eval k B) := by
  intro b
  exact ⟨b ⊗ₜ[k] (1:Bᵐᵒᵖ),by simpa using eval_tmul k B b 1⟩

/-- The cyclic-module lemma, with no assumed tensor action identities. -/
noncomputable def quotientEquiv (Y : Set B) (hgen : Algebra.adjoin k Y = ⊤) :
    (Coeff k B ⧸ relations (k:=k) Y) ≃ₗ[Coeff k B] B := by
  let f := (relations (k:=k) Y).liftQ (eval k B) (relations_le_kernel Y)
  apply LinearEquiv.ofBijective f
  constructor
  · intro x y hxy
    obtain ⟨r,rfl⟩ := Submodule.Quotient.mk_surjective (relations (k:=k) Y) x
    obtain ⟨s,rfl⟩ := Submodule.Quotient.mk_surjective (relations (k:=k) Y) y
    apply (Submodule.Quotient.eq _).mpr
    rw [← kernel_eq Y hgen]
    change eval k B (r-s) = 0
    change eval k B r = eval k B s at hxy
    rw [map_sub,hxy,sub_self]
  · intro b
    obtain ⟨r,hr⟩ := eval_surjective (k:=k) (B:=B) b
    exact ⟨Submodule.Quotient.mk r,hr⟩

section Simple
variable {A : Type*} [Ring A] [Algebra k A] [IsSimpleRing A]

/-- The coefficients that can be reached from one input form a two-sided ideal;
    unitality of the inclusion into B is deliberately not required. -/
def reachable (i : A →ₙₐ[k] B) (u : A) : TwoSidedIdeal A :=
  TwoSidedIdeal.mk' {d | ∃ r : Coeff k B, r • i u = i d}
    (by exact ⟨(0 : Coeff k B), by simpa only [map_zero] using (zero_smul (Coeff k B) (i u))⟩)
    (by
      rintro x y ⟨r,hr⟩ ⟨s,hs⟩
      exact ⟨r+s,by rw [add_smul,hr,hs,map_add]⟩)
    (by
      rintro x ⟨r,hr⟩
      exact ⟨-r,by rw [neg_smul,hr,map_neg]⟩)
    (by
      rintro x y ⟨r,hr⟩
      refine ⟨(i x ⊗ₜ[k] (1:Bᵐᵒᵖ))*r,?_⟩
      rw [mul_smul,hr]
      simp only [← MulOpposite.op_one,tmul_smul,mul_one,map_mul])
    (by
      rintro x y ⟨r,hr⟩
      refine ⟨((1:B) ⊗ₜ[k] MulOpposite.op (i y))*r,?_⟩
      rw [mul_smul,hr,tmul_smul,one_mul,map_mul])

end Simple

end FiniteAlgebraicEnvelopes.Enveloping


end OAI
end

section
-- module Solutions.OAIFAE.Contracted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Contracted monoid algebras, selectors, and the simplicity criterion.
-/


namespace FiniteAlgebraicEnvelopes.Contracted
open MonoidAlgebra
open scoped Classical
noncomputable section
variable (k H : Type*) [CommRing k] [MonoidWithZero H]

/-- The one-dimensional ideal spanned by the absorbing monoid zero. -/
def zeroSupported (f : MonoidAlgebra k H) : Prop := ∀ h : H, h ≠ 0 → f.coeff h = 0

theorem zeroSupported_iff (f : MonoidAlgebra k H) :
    zeroSupported k H f ↔ f = single 0 (f.coeff 0) := by
  classical
  constructor
  · intro h
    ext a
    by_cases ha : a=0
    · subst a; simp
    · simp [h a ha,ha]
  · intro h a ha
    rw [h]
    simp [ha]

def zeroIdeal : TwoSidedIdeal (MonoidAlgebra k H) :=
  TwoSidedIdeal.mk' {f | zeroSupported k H f}
    (by intro h hh; simp)
    (by intro f g hf hg h hh; simp [hf h hh,hg h hh])
    (by intro f hf h hh; simp [hf h hh])
    (by
      intro f g hg h hh
      rw [(zeroSupported_iff k H g).mp hg]
      exact coeff_mul_single_of_forall_mul_ne _ _ (by simpa using fun _ : H => Ne.symm hh))
    (by
      intro f g hf h hh
      rw [(zeroSupported_iff k H f).mp hf]
      exact coeff_single_mul_of_forall_mul_ne _ _ (by simpa using fun _ : H => Ne.symm hh))

abbrev Algebra := (zeroIdeal k H).ringCon.Quotient

def quotient : MonoidAlgebra k H →ₐ[k] Algebra k H := (zeroIdeal k H).ringCon.mkₐ k

theorem quotient_eq (f g : MonoidAlgebra k H) :
    quotient k H f = quotient k H g ↔ ∀ h : H, h ≠ 0 → f.coeff h = g.coeff h := by
  change (zeroIdeal k H).ringCon.toQuotient f = (zeroIdeal k H).ringCon.toQuotient g ↔ _
  rw [RingCon.eq]
  change zeroSupported k H (f-g) ↔ _
  simp only [zeroSupported,
    MonoidAlgebra.coeff_sub,Finsupp.sub_apply,sub_eq_zero]

def basis (h : H) (c : k) : Algebra k H := quotient k H (single h c)
@[simp] theorem basis_mul (h g : H) (c d : k) :
    basis k H h c * basis k H g d = basis k H (h*g) (c*d) := by
  simp [basis,← map_mul]
@[simp] theorem basis_zero (c : k) : basis k H 0 c = 0 := by
  change quotient k H (single 0 c) = quotient k H 0
  rw [quotient_eq]
  intro h hh
  simp [hh]
@[simp] theorem basis_coeff_zero (h : H) : basis k H h 0 = 0 := by simp [basis]
@[simp] theorem basis_one (c : k) : basis k H 1 c = algebraMap k (Algebra k H) c := rfl
@[simp] theorem basis_identity : basis k H 1 1 = 1 := by simp

instance instNontrivialAlgebra [Nontrivial k] [Nontrivial H] : Nontrivial (Algebra k H) := by
  apply nontrivial_of_ne (1 : Algebra k H) 0
  intro h
  have h' : quotient k H 1 = quotient k H 0 := h
  have hh := (quotient_eq k H 1 0).mp h' 1 one_ne_zero
  simp at hh

variable {k H}

/-- Ordered finite selectors, expressed by a finite support and distinguished entry. -/
def Selectors (H : Type*) [MonoidWithZero H] : Prop :=
  ∀ (S : Finset H), (0:H) ∉ S → ∀ h ∈ S, ∃ L R : H,
    L*h*R=1 ∧ ∀ g ∈ S, g ≠ h → L*g*R=0

/-- Coefficients at nonzero monoid elements descend unchanged to the quotient. -/
def coefficient (h : H) (hh : h ≠ 0) : Algebra k H →ₗ[k] k where
  toFun := Quotient.lift (fun f : MonoidAlgebra k H => f.coeff h) (by
    intro f g hfg
    exact (quotient_eq k H f g).mp ((zeroIdeal k H).ringCon.eq.mpr hfg) h hh)
  map_add' x y := Quotient.inductionOn₂ x y (fun f g => by
    change (f+g).coeff h = f.coeff h + g.coeff h
    simp)
  map_smul' c x := Quotient.inductionOn x (fun f => by
    change (c • f).coeff h = c • f.coeff h
    simp)

@[simp] theorem coefficient_quotient (h : H) (hh : h ≠ 0) (f : MonoidAlgebra k H) :
    coefficient h hh (quotient k H f) = f.coeff h := rfl
@[simp] theorem coefficient_basis (h : H) (hh : h ≠ 0) (g : H) (c : k) :
    coefficient h hh (basis k H g c) = if h=g then c else 0 := by
  classical
  simp [basis,Finsupp.single_apply,eq_comm]

/-- The actual basis consists precisely of the nonzero monoid elements. -/
theorem basis_linearIndependent :
    LinearIndependent k (fun h : {h : H // h ≠ 0} => basis k H h 1) := by
  classical
  rw [linearIndependent_iff']
  intro S a ha h hh
  have he := congrArg (coefficient (k:=k) h.val h.property) ha
  have eqv (g : {h : H // h ≠ 0}) : h.val=g.val ↔ h=g := Subtype.ext_iff.symm
  simpa [map_sum,coefficient_basis,eqv,hh] using he

theorem basis_spans :
    (⊤ : Submodule k (Algebra k H)) ≤
      Submodule.span k (Set.range (fun h : {h : H // h ≠ 0} => basis k H h 1)) := by
  intro x hx
  clear hx
  obtain ⟨f,rfl⟩ := (zeroIdeal k H).ringCon.mkₐ_surjective (α:=k) x
  change quotient k H f ∈ _
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | single h r =>
    by_cases hh : h=0
    · subst h; change basis k H 0 r ∈ _; simp
    · have he : quotient k H (single h r) = r • basis k H h 1 := by
        change quotient k H (single h r) = r • quotient k H (single h 1)
        rw [← map_smul]
        congr 1
        simp
      rw [he]
      apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨h,hh⟩,rfl⟩

def monoidBasis : Module.Basis {h : H // h ≠ 0} k (Algebra k H) :=
  Module.Basis.mk basis_linearIndependent basis_spans

@[simp] theorem monoidBasis_apply (h : {h : H // h ≠ 0}) :
    monoidBasis (k:=k) h = basis k H h 1 := Module.Basis.mk_apply _ _ h

section Lift
variable {C : Type*} [Ring C] [_root_.Algebra k C]
variable (f : MonoidAlgebra k H →ₙₐ[k] C) (hz : f (single (0:H) 1)=0)

include hz in
theorem kill_zeroSupported (x : MonoidAlgebra k H) (hx : zeroSupported k H x) : f x=0 := by
  rw [(zeroSupported_iff k H x).mp hx]
  have he : single (0:H) (x.coeff 0) = x.coeff 0 • single (0:H) (1:k) := by simp
  rw [he,map_smul,hz,smul_zero]

def lift : Algebra k H →ₙₐ[k] C where
  toFun := Quotient.lift f (by
    intro x y hxy
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply kill_zeroSupported f hz
    exact hxy)
  map_zero' := map_zero f
  map_add' x y := Quotient.inductionOn₂ x y (fun a b => map_add f a b)
  map_mul' x y := Quotient.inductionOn₂ x y (fun a b => map_mul f a b)
  map_smul' c x := Quotient.inductionOn x (fun a => map_smul f c a)

@[simp] theorem lift_quotient (x : MonoidAlgebra k H) :
    lift f hz (quotient k H x) = f x := rfl
end Lift

section Embedded
variable {J : Type*} [MonoidWithZero J]
variable (c : H →ₙ* J)

/-- The shift by c(0), essential because c need not preserve either 0 or 1. -/
def shifted : H →ₙ* Algebra k J where
  toFun h := basis k J (c h) 1 - basis k J (c 0) 1
  map_mul' h g := by
    simp only [sub_mul,mul_sub,basis_mul,one_mul,← map_mul,mul_zero,zero_mul]
    abel

def shiftedLift : MonoidAlgebra k H →ₙₐ[k] Algebra k J := MonoidAlgebra.liftMagma k (shifted (k:=k) c)

@[simp] theorem shiftedLift_single (h : H) (r : k) :
    shiftedLift (k:=k) c (single h r) = r • (basis k J (c h) 1 - basis k J (c 0) 1) := by
  simp [shiftedLift,MonoidAlgebra.liftMagma,shifted,smul_sub]

def embedding : Algebra k H →ₙₐ[k] Algebra k J :=
  lift (shiftedLift (k:=k) c) (by simp)

@[simp] theorem embedding_basis (h : H) (r : k) :
    embedding (k:=k) c (basis k H h r) = r • (basis k J (c h) 1 - basis k J (c 0) 1) := by
  simp [embedding,basis]

end Embedded

/-- Zero-preserving unital monoid maps induce unital maps of contracted algebras. -/
def map {J : Type*} [MonoidWithZero J] (c : H →*₀ J) : Algebra k H →ₐ[k] Algebra k J :=
  { embedding (k:=k) c.toMulHom with
    map_one' := by
      change embedding (k:=k) c.toMulHom 1 = 1
      rw [← basis_identity k H,embedding_basis]
      simp
    commutes' r := by
      change embedding (k:=k) c.toMulHom (algebraMap k (Algebra k H) r) = _
      rw [← basis_one k H r,embedding_basis]
      simp [Algebra.algebraMap_eq_smul_one] }

@[simp] theorem map_basis {J : Type*} [MonoidWithZero J] (c : H →*₀ J) (h : H) (r : k) :
    map (k:=k) c (basis k H h r) = basis k J (c h) r := by
  change embedding c.toMulHom (basis k H h r) = _
  rw [embedding_basis]
  change r • (basis k J (c h) 1 - basis k J (c 0) 1) = _
  rw [c.map_zero, basis_zero, sub_zero]
  change r • quotient k J (single (c h) 1) = quotient k J (single (c h) r)
  rw [← map_smul]
  congr 1
  simp


end
end FiniteAlgebraicEnvelopes.Contracted


/- Finite weak components and bounded normalization for the finite compiler. -/

end OAI
end

section
-- module Solutions.OAIFAE.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite signed words, computable word problem, simple embeddings, and action-envelope predicates.
-/

namespace FiniteAlgebraicEnvelopes

universe u

/-- Action-envelope hypotheses. -/
def HasActionEnvelope (G : Type u) [Group G] : Prop :=
  ∃ (Γ : Type u) (_ : Group Γ) (X : Type u) (_ : MulAction Γ X),
    Group.IsFinitelyPresented Γ ∧ Countable X ∧ Infinite X ∧
    FaithfulSMul Γ X ∧
    (∀ x₁ x₂ y₁ y₂ : X, x₁ ≠ x₂ → y₁ ≠ y₂ →
      ∃ g : Γ, g • x₁ = y₁ ∧ g • x₂ = y₂) ∧
    (∀ x : X, Group.FG (MulAction.stabilizer Γ x)) ∧
    ∃ f : G →* Γ, Function.Injective f

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Transition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite weak transition components and finite-scan instruction semantics.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation

variable {α : Type*} {r : α → α → Prop}

/-- An internal terminal configuration has no forward transition. -/
def Terminal (r : α → α → Prop) (a : α) : Prop := ∀ b, ¬ r a b

/-- Determinism makes forward-reachability joins an equivalence relation. -/
theorem deterministic_join (hr : Relator.RightUnique r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply equivalence_join_reflTransGen
  intro a b c hab hac
  have hbc := hr hab hac
  subst c
  exact ⟨b, .refl, .refl⟩

/-- Undirected internal connectivity may be converted to a common forward
    descendant; no reversibility of the simulated machine is required. -/
theorem weak_component_joins (hr : Relator.RightUnique r) {a b : α}
    (h : EqvGen r a b) : Join (ReflTransGen r) a b := by
  let : IsEquiv α (Join (ReflTransGen r)) := (deterministic_join hr).isEquiv
  exact EqvGen.eqvGen_le (fun _ y hxy => ⟨y, .single hxy, .refl⟩) _ _ h

theorem terminal_eq_of_reaches {a b : α} (ha : Terminal r a)
    (hab : ReflTransGen r a b) : a=b := by
  rcases hab.cases_head with h | ⟨c, hac, _⟩
  · exact h
  · exact False.elim (ha c hac)

/-- Every configuration in a terminal's weak component reaches that terminal.
    This is the graph-theoretic core of source Lemma compiler-components,
    and holds even without the finite-component assumption. -/
theorem reaches_terminal (hr : Relator.RightUnique r) {a b : α}
    (hb : Terminal r b) (hab : EqvGen r a b) : ReflTransGen r a b := by
  obtain ⟨c, hac, hbc⟩ := weak_component_joins hr hab
  have h := terminal_eq_of_reaches hb hbc
  exact h ▸ hac

/-- In particular there cannot be two successful terminal sectors in the same
    weak component, even with arbitrary reverse branching on dirty data. -/
theorem terminal_unique (hr : Relator.RightUnique r) {a b : α}
    (ha : Terminal r a) (hb : Terminal r b) (hab : EqvGen r a b) : a=b :=
  terminal_eq_of_reaches ha (reaches_terminal hr hb hab)

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIFAE.Validator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite tape validation, scan reversal, and bounded cleanup.
-/

namespace FiniteAlgebraicEnvelopes.Compiler
open Relation
variable {α : Type*} {r : α → α → Prop}

/-- A source vertex cannot be reached from a different vertex. -/
theorem source_eq_of_reaches {a b : α} (hb : ∀ c, ¬ r c b)
    (hab : ReflTransGen r a b) : a = b := by
  rcases hab.cases_tail with h | ⟨c, _, hcb⟩
  · exact h.symm
  · exact False.elim (hb c hcb)

/-- In a reverse-deterministic graph, two sources reaching the same vertex agree. -/
theorem sources_unique_of_join (hr : Relator.LeftUnique r) {a b c : α}
    (ha : ∀ x, ¬ r x a) (hb : ∀ x, ¬ r x b)
    (hac : ReflTransGen r a c) (hbc : ReflTransGen r b c) : a = b := by
  induction hac with
  | refl => exact (source_eq_of_reaches ha hbc).symm
  | @tail c d hac hcd ih =>
      rcases hbc.cases_tail with h | ⟨x, hbx, hxd⟩
      · subst d
        exact False.elim (hb c hcd)
      · have hxc : c = x := hr hcd hxd
        subst x
        exact ih hbx

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIFAE.Simulator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

section
open Relation
variable {S Γ Q : Type*}

/-- Locate a specified item of a projected list without discarding the cells
    skipped by the projection. This handles interleaved anchors and workspace. -/
theorem split_filterMap {α β : Type*} (f : α → Option β) (l : List α)
    (p : List β) (b : β) (r : List β) (h : l.filterMap f = p ++ b::r) :
    ∃ l₁ a l₂, l = l₁ ++ a::l₂ ∧ l₁.filterMap f = p ∧
      f a = some b ∧ l₂.filterMap f = r := by
  induction l generalizing p with
  | nil => simp at h
  | cons a l ih =>
      cases hf : f a with
      | none =>
          simp only [List.filterMap_cons, hf] at h
          obtain ⟨l₁,c,l₂,hl,hp,hc,hr⟩ := ih p h
          exact ⟨a::l₁,c,l₂,by simp [hl],by simp [hf,hp],hc,hr⟩
      | some v =>
          simp only [List.filterMap_cons, hf] at h
          cases p with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at h
              exact ⟨[],a,l,by simp, rfl,by simpa [h.1] using hf,h.2⟩
          | cons v' p =>
              simp only [List.cons_append, List.cons.injEq] at h
              obtain ⟨l₁,c,l₂,hl,hp,hc,hr⟩ := ih p h.2
              exact ⟨a::l₁,c,l₂,by simp [hl],by simp [hf,hp,h.1],hc,hr⟩

end

open Relation

end FiniteAlgebraicEnvelopes.Compiler.Simulator

end OAI
end

section
-- module Solutions.OAIFAE.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Raw-run folds, full word compilation, partial budgets, and bounded normalization.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.RawRuns
variable {C S : Type*}

/-- Budget laws are used only where the *unreduced* concatenation has bounded
    length. They are exactly the totality/length/context interface of the source. -/
structure Budget (f : List S → List S) (m : ℕ) : Prop where
  length : ∀ w, w.length ≤ m → (f w).length ≤ w.length
  context : ∀ x w y, (x++w++y).length ≤ m → f (x++f w++y) = f (x++w++y)

variable {f : List S → List S} {m : ℕ}

/-- The two bracketings of three adjacent raw inputs agree inside the same
    budget. No idempotence assumption on raw singleton sectors is made. -/
theorem triple (h : Budget f m) (x y z : List S)
    (hm : (x++y++z).length ≤ m) : f (x++f (y++z)) = f (f (x++y)++z) := by
  have h₁ := h.context x (y++z) [] (by simpa [List.append_assoc] using hm)
  have h₂ := h.context [] (x++y) z (by simpa using hm)
  simp only [List.append_nil,List.nil_append,List.append_assoc] at h₁ h₂ ⊢
  exact h₁.trans h₂.symm

end FiniteAlgebraicEnvelopes.Compiler.RawRuns

namespace FiniteAlgebraicEnvelopes.Compiler

/-- Literal domain/length/context premises of the finite compiler's bounded theorem.
    These are conditions on the given partial program, not a total replacement. -/
structure PartialBudget {S : Type*} (f : List S → Part (List S)) (m : ℕ) : Prop where
  total : ∀ w, w.length ≤ m → (f w).Dom
  length : ∀ w, w.length ≤ m → ∀ out ∈ f w, out.length ≤ w.length
  context : ∀ x w y, (x++w++y).length ≤ m →
    ∀ out ∈ f w, f (x++out++y) = f (x++w++y)

/-- Used only to state the bounded correctness proof of the partial algorithm.
    It has no place in its definition or in its claimed effective implementation. -/
noncomputable def partValue {S : Type*} (p : Part (List S)) : List S := by
  classical
  exact if h : p.Dom then p.get h else []

end FiniteAlgebraicEnvelopes.Compiler

end OAI
end

section
-- module Solutions.OAIFAE.Effectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive encodings and effective finite compiler data.
-/

/- Effectivity dependencies for the source compiler and its bounded recursive
   evaluator. No partial function is completed by classical choice. -/
namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

def traverseStep (f : α →. β) : List α × List β →. List β ⊕ (List α × List β)
  | ([],acc) => Part.some (.inl acc)
  | (a::l,acc) => (f a).map fun b => .inr (l,acc++[b])

end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect.Graph
open Relation
variable {α : Type*} [DecidableEq α]

variable [Primcodable α]

omit [DecidableEq α] in
 theorem primrec_listAny {β : Type*} [Primcodable β]
    {f : β → List α} {p : β → α → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun b => (f b).any (p b)) := by
  exact (Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun b => by
    induction f b <;> simp_all

omit [DecidableEq α] in
 theorem primrec_listFilter {β : Type*} [Primcodable β]
    {f : β → List α} {p : β → α → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun b => (f b).filter (p b)) := by
  exact (Primrec.listFilterMap hf
    (Primrec.cond hp (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).of_eq
    fun b => by
      simp only [Bool.cond_eq_ite]
      induction f b with
      | nil => rfl
      | cons a l ih => cases h : p b a <;> simp [h,ih]

end FiniteAlgebraicEnvelopes.Effect.Graph

namespace FiniteAlgebraicEnvelopes.Effect
open FiniteAlgebraicEnvelopes.Effect.Graph
variable {α : Type*} [Primcodable α] [DecidableEq α]

 theorem primrec_listIsEmpty : Primrec (List.isEmpty (α := α)) :=
  (Primrec.eq.decide.comp Primrec.id (Primrec.const [])).of_eq fun l => by
    cases l <;> simp

variable [LinearOrder α]

omit [DecidableEq α] in
 theorem primrec_listMin (hle : PrimrecRel (fun a b : α => a ≤ b)) :
    Primrec (List.min? (α := α)) := by
  have hmin : Primrec₂ (min : α → α → α) := by
    exact (Primrec.ite hle Primrec.fst Primrec.snd).of_eq fun p => by
      simp only [min_def]
  have hfold : Primrec₂ (fun (_ : List α) (p : α × List α) => some (p.2.foldl min p.1)) := by
    exact (Primrec.option_some.comp (Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd) (hmin.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd)).to₂)).to₂
  exact (Primrec.list_casesOn Primrec.id (Primrec.const none) hfold).of_eq fun l =>
    by cases l <;> rfl

omit [Primcodable α] in
 theorem minList_eq (s : List α) (t : Finset α) (h : t.Nonempty)
    (he : s.toFinset = t) (a : α) : s.min?.getD a = t.min' h := by
  have hm : s.min? = some (t.min' h) := by
    rw [List.min?_eq_some_iff]
    constructor
    · rw [← List.mem_toFinset,he]; exact Finset.min'_mem _ _
    · intro b hb
      exact Finset.min'_le _ _ (he ▸ List.mem_toFinset.mpr hb)
  rw [hm]; rfl

end FiniteAlgebraicEnvelopes.Effect

end OAI
end

section
-- module Solutions.OAIFAE.Rewriting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Newman normalization, block coding, canonical representatives, and static tests.
-/

/- Rewriting layer for the self-reference construction.  No assumptions on
   either main theorem are introduced here. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
open Relation

section Newman
variable {α : Type*} (R : α → α → Prop)

def Irreducible (a : α) : Prop := ∀ b, ¬ R a b

theorem exists_irreducible (wf : WellFounded (flip R)) (a : α) :
    ∃ b, ReflTransGen R a b ∧ Irreducible R b := by
  classical
  induction a using wf.induction with
  | h a ih =>
    by_cases ha : Irreducible R a
    · exact ⟨a, .refl, ha⟩
    · obtain ⟨b, hab⟩ := not_forall.mp ha
      have hab : R a b := Classical.not_not.mp hab
      obtain ⟨c, hbc, hc⟩ := ih b hab
      exact ⟨c, (ReflTransGen.single hab).trans hbc, hc⟩

theorem irreducible_reaches {a b : α} (ha : Irreducible R a)
    (hab : ReflTransGen R a b) : a = b := by
  rcases hab.cases_head with hab | ⟨c,hac,_⟩
  · exact hab
  · exact False.elim (ha c hac)

end Newman

variable {S : Type*}

theorem lex_append_suffix {r : S → S → Prop} {u v : List S}
    (h : List.Lex r u v) (hlen : u.length = v.length) (y : List S) :
    List.Lex r (u++y) (v++y) := by
  induction h with
  | nil => simp at hlen
  | rel h => exact .rel h
  | cons h ih => exact .cons (ih (by simpa using hlen))

theorem shortlex_context {r : S → S → Prop} {u v : List S}
    (h : List.Shortlex r u v) (x y : List S) :
    List.Shortlex r (x++u++y) (x++v++y) := by
  simp only [List.append_assoc]
  apply List.Shortlex.append_left (s := x)
  rcases List.shortlex_def.mp h with h | ⟨hl,h⟩
  · apply List.Shortlex.of_length_lt
    simpa using h
  · exact List.Shortlex.of_lex (by simp [hl]) (lex_append_suffix h hl y)

end

/- The marker/constant-width code used in the self-reference construction.
   A block has its marker only at the start, not at the end. -/

namespace BlockCode
variable {A S : Type*}

theorem lex_append_two {r : S → S → Prop} {u v : List S}
    (h : List.Lex r u v) (hlen : u.length=v.length) (x y : List S) :
    List.Lex r (u++x) (v++y) := by
  induction h with
  | nil => simp at hlen
  | rel hh => exact .rel hh
  | cons h ih => exact .cons (ih (by simpa using hlen))

end BlockCode

open Relation
end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.Selectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Literal selector envelopes, rewrite saturation, and zero recognition.
-/

/- Literal selector envelopes from the self-reference construction. -/
namespace FiniteAlgebraicEnvelopes.Bootstrap

section
namespace Envelopes
variable {S : Type*}

theorem infix_strip_cons {a d : S} {v w : List S} (hd : d≠a)
    (h : d::v <:+: a::w) : d::v <:+: w := by
  obtain ⟨x,y,he⟩ := h
  cases x with
  | nil => exact False.elim (hd (List.cons.inj he).1)
  | cons b x =>
    have hh : x++(d::v)++y=w := (List.cons.inj he).2
    exact ⟨x,y,hh⟩

theorem infix_strip_prefix {d : S} {v p w : List S} (hd : d∉p)
    (h : d::v <:+: p++w) : d::v <:+: w := by
  induction p with
  | nil => exact h
  | cons a p ih =>
    exact ih (fun hh => hd (List.mem_cons_of_mem _ hh))
      (infix_strip_cons (fun he => hd (by simp [he])) h)

theorem infix_strip_suffix {h : S} {v p w : List S} (hh : h∉p)
    (hi : v++[h] <:+: w++p) : v++[h] <:+: w := by
  have hr : h :: v.reverse <:+: p.reverse ++ w.reverse := by
    simpa using hi.reverse
  have hs := infix_strip_prefix (by simpa using hh) hr
  simpa using hs.reverse

theorem prefix_mem_initial {v p q : List S} (hv : v <+: p++q)
    (hlen : v.length ≤ p.length) : v ⊆ p := by
  have ht : (p++q).take v.length = v := by
    obtain ⟨t,he⟩ := hv
    rw [← he]
    simp
  have htake : (p++q).take v.length = p.take v.length := List.take_append_of_le_length hlen
  rw [htake] at ht
  intro a ha
  apply (List.take_sublist v.length p).subset
  rw [ht]
  exact ha

theorem infix_strip_outer {v w : List S} {a : S}
    (hi : v <:+: a::w) (hn : ¬ v <+: a::w) : v <:+: w := by
  obtain ⟨x,y,he⟩ := hi
  cases x with
  | nil => exact False.elim (hn ⟨y,he⟩)
  | cons b x => exact ⟨x,y,(List.cons.inj he).2⟩

/-- A short older selector cannot start in, or straddle, the new left guard. -/
theorem bounded_strip_left {d l h : S} {v w : List S} {N : ℕ}
    (hdl : d≠l) (hhd : h≠d) (hhl : h≠l) (hend : h∈d::v)
    (hlen : (d::v).length ≤ N) (hi : d::v <:+: d::(List.replicate N l++w)) :
    d::v <:+: w := by
  have hn : ¬ d::v <+: d::(List.replicate N l++w) := by
    intro hp
    have hm : h ∈ d :: List.replicate N l :=
      prefix_mem_initial (p := d::List.replicate N l) hp
        (by simp only [List.length_cons,List.length_replicate] at hlen ⊢; omega) hend
    simp only [List.mem_cons,List.mem_replicate] at hm
    rcases hm with ha | ⟨_,hl⟩
    · exact hhd ha
    · exact hhl hl
  have hs := infix_strip_outer hi hn
  exact infix_strip_prefix (by simp [hdl]) hs

end Envelopes

open Relation

end

section
open Relation
namespace Selectors
variable {S : Type*}
  [DecidableEq S]

variable {a}

def BoundedEq (rs rt : List (List S × List S)) (k : ℕ) : Prop :=
  ∀ p, p.1.length ≤ k → (p ∈ rs ↔ p ∈ rt)

omit [DecidableEq S] in
theorem boundedEq_refl (rs : List (List S × List S)) (k : ℕ) : BoundedEq rs rs k :=
  fun _ _ => Iff.rfl

omit [DecidableEq S] in
theorem boundedEq_trans {rs rt ru : List (List S × List S)} {k : ℕ}
    (h : BoundedEq rs rt k) (g : BoundedEq rt ru k) : BoundedEq rs ru k :=
  fun p hp => (h p hp).trans (g p hp)

end Selectors
end

namespace Search

section
variable {A : Type*} [DecidableEq A]

def lexBool (r : A → A → Bool) : List A → List A → Bool
  | [],[] => false
  | [],_::_ => true
  | _::_,[] => false
  | a::u,b::v => if a=b then lexBool r u v else r a b

def lexFoldStep (r : A → A → Bool) (st : Bool ⊕ List A) (a : A) : Bool ⊕ List A :=
  match st with
  | .inl b => .inl b
  | .inr [] => .inl false
  | .inr (b::v) => if a=b then .inr v else .inl (r a b)

def lexFinish : Bool ⊕ List A → Bool := Sum.elim id (fun v => !v.isEmpty)

theorem lexFold (r : A → A → Bool) (u : List A) (st : Bool ⊕ List A) :
    lexFinish (u.foldl (lexFoldStep r) st)=st.elim id (lexBool r u) := by
  induction u generalizing st with
  | nil => cases st with
    | inl b => rfl
    | inr v => cases v <;> rfl
  | cons a u ih =>
    rw [List.foldl_cons,ih]
    cases st with
    | inl b => rfl
    | inr v =>
      cases v with
      | nil => cases u <;> rfl
      | cons b v =>
        simp only [lexFoldStep,lexBool,Sum.elim_inr]
        split <;> rfl

variable [Primcodable A]

theorem primrec_lexBool (r : A → A → Bool) (hr : Primrec₂ r) : Primrec₂ (lexBool r) := by
  have hinr : Primrec₂ (fun (p : (Bool ⊕ List A) × A) (v : List A) =>
      match v with
      | [] => (Sum.inl false : Bool ⊕ List A)
      | b::v => if p.2=b then .inr v else .inl (r p.2 b)) := by
    exact (Primrec.list_casesOn Primrec.snd (Primrec.const (.inl false))
      (Primrec.ite
        (Primrec.eq.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
        (Primrec.sumInr.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.sumInl.comp (hr.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.fst.comp Primrec.snd)))).to₂).to₂.of_eq (by intro p v; cases v <;> rfl)
  have hstep : Primrec₂ (lexFoldStep r) :=
    (Primrec.sumCasesOn Primrec.fst
      (Primrec.sumInl.comp Primrec.snd).to₂ hinr).to₂.of_eq (by
        intro st a
        cases st with
        | inl b => rfl
        | inr v => cases v <;> rfl)
  have hf : Primrec (lexFinish (A:=A)) :=
    (Primrec.sumCasesOn Primrec.id (Primrec.snd.to₂)
      ((Primrec.not.comp (Effect.primrec_listIsEmpty.comp Primrec.snd)).to₂)).of_eq (fun p => by cases p <;> rfl)
  exact ((hf.comp (Primrec.list_foldl Primrec.fst
    (Primrec.sumInr.comp Primrec.snd) (hstep.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq (fun p => lexFold r p.1 (.inr p.2))).to₂

end

end Search
end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap.Selectors

section
variable {S : Type*} [DecidableEq S] [Primcodable S]

 theorem primrec_mem {X : Type*} [Primcodable X] : PrimrecRel (fun (x : X) (l : List X) => x∈l) :=
  (PrimrecRel.of_eq Primrec.eq.exists_mem_list (by intro l x; simp)).swap

 theorem primrec_dedup {X : Type*} [Primcodable X] [DecidableEq X] : Primrec (@List.dedup X _) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite
      (primrec_mem.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂).of_eq
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [id_eq] at ih ⊢
    simp only [List.foldr_cons,ih,List.dedup_cons']

 theorem primrec_nodup {X : Type*} [Primcodable X] [DecidableEq X] : PrimrecPred (@List.Nodup X) :=
  (Primrec.eq.comp primrec_dedup Primrec.id).of_eq (fun _ => List.dedup_eq_self)

end

variable {S : Type*} [DecidableEq S] [Primcodable S]

omit [DecidableEq S] in
theorem primrec_replicate (b : S) : Primrec (fun n => List.replicate n b) :=
  (Primrec.nat_rec₁ [] (Primrec.list_cons.comp (Primrec.const b) Primrec.snd).to₂).of_eq
    (by intro n; induction n <;> simp_all [List.replicate_succ])

end FiniteAlgebraicEnvelopes.Bootstrap.Selectors

end OAI
end

section
-- module Solutions.OAIFAE.WordProblem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Effective finite presentations, decidable word problem in simple groups, and the reverse implication.
-/

namespace FiniteAlgebraicEnvelopes

universe u

namespace WordProblem

open Primrec

def reduceStep {n : ℕ} (p : (Fin n × Bool) × Word n) : Word n :=
  List.casesOn p.2 [p.1] fun hd tl =>
    if p.1.1 = hd.1 ∧ p.1.2 = !hd.2 then tl else p.1 :: hd :: tl

/-- A finite product of signed conjugates is a certificate for normal closure. -/
abbrev Factor (n m : ℕ) := Word n × Fin m × Bool
abbrev Certificate (n m : ℕ) := List (Factor n m)

def factorWord {n m : ℕ} (r : Fin m → Word n) (c : Factor n m) : Word n :=
  c.1 ++ (if c.2.2 then r c.2.1 else FreeGroup.invRev (r c.2.1)) ++
    FreeGroup.invRev c.1

def certificateWord {n m : ℕ} (r : Fin m → Word n) (cs : Certificate n m) : Word n :=
  (cs.map (factorWord r)).flatten

def factorValue {n m : ℕ} (r : Fin m → Word n) (c : Factor n m) : FreeGroup (Fin n) :=
  FreeGroup.mk c.1 * (if c.2.2 then FreeGroup.mk (r c.2.1) else
    (FreeGroup.mk (r c.2.1))⁻¹) * (FreeGroup.mk c.1)⁻¹

def certificateValue {n m : ℕ} (r : Fin m → Word n) (cs : Certificate n m) :
    FreeGroup (Fin n) := (cs.map (factorValue r)).prod

def flipFactor {n m} (c : Factor n m) : Factor n m := (c.1, c.2.1, !c.2.2)

theorem invRev_primrec (n : ℕ) : Primrec (@FreeGroup.invRev (Fin n)) := by
  unfold FreeGroup.invRev
  apply Primrec.list_reverse.comp
  apply Primrec.list_map Primrec.id
  exact Primrec.pair (Primrec.fst.comp Primrec.snd)
    (Primrec.not.comp <| Primrec.snd.comp Primrec.snd)

theorem evalWord_eq_lift {H : Type*} [Group H] {n} (s : Fin n → H) (w : Word n) :
    evalWord s w = FreeGroup.lift s (FreeGroup.mk w) := by
  simp only [evalWord, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro a _
  cases a.2 <;> rfl

/-- Effective replacement of each generator by a fixed finite word. -/
def substitute {n m} (r : Fin n → Word m) (w : Word n) : Word m :=
  (w.map fun a => if a.2 then r a.1 else FreeGroup.invRev (r a.1)).flatten

theorem evalWord_append {H : Type*} [Group H] {n} (s : Fin n → H) (v w : Word n) :
    evalWord s (v ++ w) = evalWord s v * evalWord s w := by
  simp only [evalWord, List.map_append, List.prod_append]

theorem evalWord_invRev {H : Type*} [Group H] {n} (s : Fin n → H) (w : Word n) :
    evalWord s (FreeGroup.invRev w) = (evalWord s w)⁻¹ := by
  simp only [evalWord_eq_lift, ← FreeGroup.inv_mk, map_inv]

end WordProblem

end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.Quotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical compiler quotients and effective tested classes for word problems.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap

section

namespace Quotient
open Relation
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))

/-- Literal equations of the stabilized infinite table. Restricting a stage to
its own budget removes only premature copies of the fixed absorption rules. -/
def Rel (u v : FreeMonoid S) : Prop :=
  ∃ n rs, rs ∈ T n ∧ (u.toList,v.toList) ∈ rs ∧ u.toList.length ≤ n

abbrev Mon := PresentedMonoid (Rel T)
def present (w : List S) : Mon T := PresentedMonoid.mk (Rel T) (FreeMonoid.ofList w)

omit [DecidableEq S] in
@[simp] theorem present_nil : present T []=1 := rfl
omit [DecidableEq S] in
@[simp] theorem present_append (u v : List S) : present T (u++v)=present T u * present T v := rfl

end Quotient

open Relation

namespace Quotient
variable {S : Type*} [DecidableEq S]
variable (T : ℕ → Part (List (List S × List S)))
variable {r : S → S → Prop}
  (wf : WellFounded r)
  (stable : ∀ k n,k ≤ n → ∀ rk∈T k,∀ rn∈T n,Selectors.BoundedEq rk rn k)
include wf stable

omit [DecidableEq S] wf stable in
 theorem present_surjective : Function.Surjective (present T) := by
  intro x
  obtain ⟨w,rfl⟩ := PresentedMonoid.surjective_mk x
  exact ⟨w.toList,rfl⟩

end Quotient
end

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes.Bootstrap

variable {S : Type*}

namespace Separator

theorem prefix_before {z : S} {p u v : List S} (hz : z∉p)
    (h : p <+: u++z::v) : p <+: u := by
  induction u generalizing p with
  | nil =>
    have hnil : p=[] := by
      cases p with
      | nil => rfl
      | cons a p =>
        have ha := (List.cons_prefix_cons.mp h).1
        exact False.elim (hz (by simp [ha]))
    simp [hnil]
  | cons a u ih =>
    cases p with
    | nil => simp
    | cons b p =>
      obtain ⟨rfl,hp⟩ := List.cons_prefix_cons.mp h
      exact List.cons_prefix_cons.mpr ⟨rfl,ih (fun hh => hz (List.mem_cons_of_mem _ hh)) hp⟩

theorem infix_split {z : S} {p u v : List S} (hz : z∉p)
    (h : p <:+: u++z::v) : p <:+: u ∨ p <:+: v := by
  induction u with
  | nil =>
    rcases List.infix_cons_iff.mp h with hp | hp
    · have he := List.prefix_nil.mp (prefix_before (u:=[]) hz hp)
      exact Or.inl (by simp [he])
    · exact Or.inr hp
  | cons a u ih =>
    rcases List.infix_cons_iff.mp h with hp | hp
    · exact Or.inl (prefix_before hz hp).isInfix
    · rcases ih hp with hu | hv
      · exact Or.inl (List.infix_cons_iff.mpr (Or.inr hu))
      · exact Or.inr hv

end Separator

end FiniteAlgebraicEnvelopes.Bootstrap

namespace FiniteAlgebraicEnvelopes

namespace WordProblem
variable {G : Type*} [Group G] {n : ℕ} (s : Fin n → G)

/-- The original word-problem algorithm gives a genuine two-word comparison. -/
theorem computable_word_equiv (h : ComputablePred (fun w : Word n => evalWord s w=1)) :
    ComputablePred (fun p : Word n × Word n => evalWord s p.1=evalWord s p.2) := by
  classical
  have hc : ComputablePred (fun p : Word n × Word n =>
      evalWord s (p.1 ++ FreeGroup.invRev p.2)=1) :=
    ⟨inferInstance,h.decide.comp (Primrec.list_append.comp Primrec.fst
      ((invRev_primrec n).comp Primrec.snd)).to_comp⟩
  exact hc.of_eq (fun p => by rw [evalWord_append,evalWord_invRev,mul_inv_eq_one])

end WordProblem
end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.PartialAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Primitive recursive dyadic partial affine monoid and its six-letter presentation.
-/

namespace FiniteAlgebraicEnvelopes.PartialAffine
namespace Dyad

theorem primrec_pow2 : Primrec (fun n : ℕ => 2^n) :=
  (Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂).of_eq
    (by intro n; induction n <;> simp_all [pow_succ])

end Dyad

/-- Partial identities on rational tails, in the ambient partial-map monoid. -/
def tail (r : ℚ) : Function.End (Option ℚ) :=
  fun o => o.bind (fun x => if r≤x then some x else none)

 theorem tail_mul (r s : ℚ) : tail r*tail s=tail (max r s) := by
  funext o
  cases o with
  | none => rfl
  | some x =>
    change ((if s≤x then some x else none).bind
      (fun y => if r≤y then some y else none)) = if max r s≤x then some x else none
    by_cases hr : r ≤ x <;> by_cases hs : s ≤ x <;> simp [hr,hs]

end FiniteAlgebraicEnvelopes.PartialAffine

end OAI
end

section
-- module Solutions.OAIFAE.TapeFolding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.UniformCode
open Turing.ToPartrec

theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

open Encodable

end FiniteAlgebraicEnvelopes.MachineRealization.UniformCode

end OAI
end

section
-- module Solutions.OAIFAE.UniformPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Uniform surface and path normalization with recursive compiler interfaces.
-/

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]
theorem primrec_sumElim {f : α → γ} {g : β → γ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (Sum.elim f g) := by
  exact (Primrec.sumCasesOn Primrec.id (hf.comp Primrec.snd).to₂
    (hg.comp Primrec.snd).to₂).of_eq fun x => by cases x <;> rfl
end FiniteAlgebraicEnvelopes.Effect

namespace FiniteAlgebraicEnvelopes.Effect
variable {α β : Type*}

variable [LinearOrder α] [LinearOrder β]

theorem minList_map (i : α → β) (hi : Monotone i) (s : List α) :
    (s.map i).min?=s.min?.map i := by
  cases h : s.min? with
  | none =>
    have hs := List.min?_eq_none_iff.mp h
    subst s; rfl
  | some a =>
    simp only [Option.map_some]
    obtain ⟨ha,hm⟩ := List.min?_eq_some_iff.mp h
    apply List.min?_eq_some_iff.mpr
    refine ⟨List.mem_map.mpr ⟨a,ha,rfl⟩,?_⟩
    rintro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact hi (hm c hc)

theorem minList_ext [DecidableEq α] {s t : List α} (he : s.toFinset=t.toFinset) :
    s.min?=t.min? := by
  have hm : ∀ a,a∈s ↔ a∈t := fun a => by simpa using Finset.ext_iff.mp he a
  apply Option.ext
  intro a
  simp only [List.min?_eq_some_iff,hm]

end FiniteAlgebraicEnvelopes.Effect

end OAI
end

section
-- module Solutions.OAIFAE.SelfReference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Controlled shorter-input evaluator calls, fixed points, totality, and tested-class realization.
-/

namespace FiniteAlgebraicEnvelopes.Bootstrap
variable {S : Type*}
def RulesEq (rs rt : List (List S × List S)) : Prop := ∀ p,p∈rs ↔ p∈rt

end FiniteAlgebraicEnvelopes.Bootstrap

end OAI
end

section
-- module Solutions.OAIFAE.MonoidAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite compiler monoids, zero products, both F₂ algebras, and selector constructions.
-/

namespace FiniteAlgebraicEnvelopes

namespace Bootstrap

namespace ZeroProduct
variable {A C D : Type*} [DecidableEq C]
def test (z : C) (f : List A → C) (g : List A → D) (w : List A) : Option (C×D) :=
  if f w=z then none else some (f w,g w)

end ZeroProduct
end Bootstrap

end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.ContractedPresentation

section
variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

def word : FreeMonoid S →* FreeAlgebra k S := FreeMonoid.lift (FreeAlgebra.ι k)

def Rel (a b : FreeAlgebra k S) : Prop :=
  (∃ u v, rel u v ∧ a=word k S u ∧ b=word k S v) ∨ (a=word k S z ∧ b=0)

abbrev Presentation := RingQuot (Rel k S rel z)

def generator (x : S) : Presentation k S rel z :=
  RingQuot.mkAlgHom k (Rel k S rel z) (FreeAlgebra.ι k x)

theorem word_generator (u : FreeMonoid S) :
    FreeMonoid.lift (generator k S rel z) u=RingQuot.mkAlgHom k (Rel k S rel z) (word k S u) := by
  have hh : FreeMonoid.lift (generator k S rel z)=
      (RingQuot.mkAlgHom k (Rel k S rel z)).toMonoidHom.comp (word k S) := by
    apply FreeMonoid.hom_eq
    intro x
    rfl
  exact DFunLike.congr_fun hh u

def monoidEval : M →* Presentation k S rel z :=
  (PresentedMonoid.lift (generator k S rel z) (by
    intro a b hab
    rw [word_generator,word_generator]
    exact RingQuot.mkAlgHom_rel k (Or.inl ⟨a,b,hab,rfl,rfl⟩))).comp e.symm.toMonoidHom

theorem monoidEval_mk (u : FreeMonoid S) :
    monoidEval k S rel e z (e (PresentedMonoid.mk rel u))=
      RingQuot.mkAlgHom k (Rel k S rel z) (word k S u) := by
  unfold monoidEval
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply]
  exact word_generator k S rel z u

include hz in
theorem monoidEval_zero : monoidEval k S rel e z 0=0 := by
  rw [←hz,monoidEval_mk]
  have he := RingQuot.mkAlgHom_rel k (s:=Rel k S rel z) (Or.inr ⟨rfl,rfl⟩)
  simpa only [map_zero] using he

def toPresentation : Contracted.Algebra k M →ₐ[k] Presentation k S rel z :=
  let f := MonoidAlgebra.lift k (Presentation k S rel z) M (monoidEval k S rel e z)
  let hf : f (MonoidAlgebra.single (0:M) 1)=0 := by
    rw [MonoidAlgebra.lift_single,one_smul,monoidEval_zero k S rel e z hz]
  let g := Contracted.lift f.toNonUnitalAlgHom hf
  { g with
    map_one' := by
      change g (Contracted.quotient k M 1)=1
      exact (Contracted.lift_quotient f.toNonUnitalAlgHom hf 1).trans (map_one f)
    commutes' := by
      intro r
      change g (algebraMap k (Contracted.Algebra k M) r)=_
      rw [Algebra.algebraMap_eq_smul_one,map_smul]
      have he : g 1=1 := by
        change g (Contracted.quotient k M 1)=1
        exact (Contracted.lift_quotient f.toNonUnitalAlgHom hf 1).trans (map_one f)
      rw [he,Algebra.algebraMap_eq_smul_one] }

@[simp] theorem toPresentation_basis (m : M) (r : k) :
    toPresentation k S rel e z hz (Contracted.basis k M m r)=r • monoidEval k S rel e z m := by
  exact MonoidAlgebra.lift_single _ _ _

def monoidBasis : M →* Contracted.Algebra k M where
  toFun m := Contracted.basis k M m 1
  map_one' := Contracted.basis_identity k M
  map_mul' a b := by rw [Contracted.basis_mul,one_mul]

def freeEval : FreeAlgebra k S →ₐ[k] Contracted.Algebra k M :=
  FreeAlgebra.lift k (fun x => monoidBasis k (e (PresentedMonoid.of rel x)))

theorem freeEval_word (u : FreeMonoid S) :
    freeEval k S rel e (word k S u)=Contracted.basis k M (e (PresentedMonoid.mk rel u)) 1 := by
  have hh : (freeEval k S rel e).toMonoidHom.comp (word k S)=
      (monoidBasis k).comp (e.toMonoidHom.comp (PresentedMonoid.mk rel)) := by
    apply FreeMonoid.hom_eq
    intro x
    simp [word,freeEval]
    rfl
  exact DFunLike.congr_fun hh u

include hz in
theorem freeEval_respects : ∀ ⦃a b⦄, Rel k S rel z a b → freeEval k S rel e a=freeEval k S rel e b := by
  intro a b hab
  rcases hab with ⟨u,v,hu,rfl,rfl⟩|⟨rfl,rfl⟩
  · rw [freeEval_word,freeEval_word,PresentedMonoid.mk_eq_mk_of_rel hu]
  · rw [freeEval_word,hz,Contracted.basis_zero,map_zero]

def fromPresentation : Presentation k S rel z →ₐ[k] Contracted.Algebra k M :=
  RingQuot.liftAlgHom k ⟨freeEval k S rel e,freeEval_respects k S rel e z hz⟩

@[simp] theorem fromPresentation_mk (a : FreeAlgebra k S) :
    fromPresentation k S rel e z hz (RingQuot.mkAlgHom k (Rel k S rel z) a)=freeEval k S rel e a := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

end

variable (k S : Type*) [CommRing k]
variable (rel : FreeMonoid S → FreeMonoid S → Prop)
variable {M : Type*} [MonoidWithZero M] (e : PresentedMonoid rel ≃* M)
variable (z : FreeMonoid S) (hz : e (PresentedMonoid.mk rel z)=0)

theorem from_to_basis (m : M) (r : k) :
    fromPresentation k S rel e z hz (toPresentation k S rel e z hz (Contracted.basis k M m r))=
      Contracted.basis k M m r := by
  obtain ⟨u,hu⟩ := PresentedMonoid.surjective_mk (e.symm m)
  have hm : m=e (PresentedMonoid.mk rel u) := by rw [hu,e.apply_symm_apply]
  rw [hm,toPresentation_basis,map_smul,monoidEval_mk,fromPresentation_mk,freeEval_word]
  simp [Contracted.basis,←map_smul]

theorem from_to : (fromPresentation k S rel e z hz).comp (toPresentation k S rel e z hz)=AlgHom.id k _ := by
  apply DFunLike.ext
  intro a
  obtain ⟨a,rfl⟩ := (Contracted.zeroIdeal k M).ringCon.mkₐ_surjective (α:=k) a
  change fromPresentation k S rel e z hz (toPresentation k S rel e z hz (Contracted.quotient k M a))=Contracted.quotient k M a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | single m r => exact from_to_basis k S rel e z hz m r

theorem to_from : (toPresentation k S rel e z hz).comp (fromPresentation k S rel e z hz)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext x
  change toPresentation k S rel e z hz
    (fromPresentation k S rel e z hz (RingQuot.mkAlgHom k (Rel k S rel z) (FreeAlgebra.ι k x)))=_
  rw [fromPresentation_mk]
  change toPresentation k S rel e z hz
    (FreeAlgebra.lift k _ (FreeAlgebra.ι k x))=_
  rw [FreeAlgebra.lift_ι_apply]
  change toPresentation k S rel e z hz
    (Contracted.basis k M (e (PresentedMonoid.mk rel (FreeMonoid.of x))) 1)=_
  rw [toPresentation_basis,one_smul,monoidEval_mk]
  rfl

/-- Exact finite algebra presentation: replace the monoid equations by the same
    free-algebra equations and set a representative of monoid zero equal to zero. -/
def equivalence : Presentation k S rel z ≃ₐ[k] Contracted.Algebra k M :=
  AlgEquiv.ofAlgHom (fromPresentation k S rel e z hz) (toPresentation k S rel e z hz)
    (from_to k S rel e z hz) (to_from k S rel e z hz)

end FiniteAlgebraicEnvelopes.ContractedPresentation

section
namespace FiniteAlgebraicEnvelopes.ContractedPresentation
variable (k S : Type*) [CommRing k] (rel : FreeAlgebra k S → FreeAlgebra k S → Prop)

def quotientGenerators (x : S) : RingQuot rel := RingQuot.mkAlgHom k rel (FreeAlgebra.ι k x)

end FiniteAlgebraicEnvelopes.ContractedPresentation

end

namespace FiniteAlgebraicEnvelopes.ZeroProduct
variable (K P : Type*) [MonoidWithZero K] [Monoid P]

/-- Collapse precisely the pairs whose first coordinate is zero. This quotient
    is the zero product `(K \ {0}) × P ⊔ {0}` from the algebra construction. -/
def cong : Con (K × P) where
  r a b := a=b ∨ a.1=0 ∧ b.1=0
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := by intro a b h; rcases h with h | h; exact Or.inl h.symm; exact Or.inr h.symm
    trans := by
      intro a b c hab hbc
      rcases hab with rfl | hab
      · exact hbc
      rcases hbc with rfl | hbc
      · exact Or.inr hab
      exact Or.inr ⟨hab.1,hbc.2⟩ }
  mul' := by
    intro a b c d hab hcd
    rcases hab with rfl | hab
    · rcases hcd with rfl | hcd
      · exact Or.inl rfl
      · exact Or.inr ⟨by simp [hcd.1],by simp [hcd.2]⟩
    · exact Or.inr ⟨by simp [hab.1],by simp [hab.2]⟩

abbrev Mon := (cong K P).Quotient

def pair : K × P →* Mon K P := (cong K P).mk'

instance instZeroMon : Zero (Mon K P) := ⟨pair K P (0,1)⟩

 theorem pair_eq_iff (a b : K × P) : pair K P a=pair K P b ↔ a=b ∨ a.1=0 ∧ b.1=0 :=
  (cong K P).eq

 theorem pair_zero (p : P) : pair K P (0,p)=0 :=
  (pair_eq_iff K P _ _).mpr (Or.inr ⟨rfl,rfl⟩)

 theorem pair_eq_zero (a : K × P) : pair K P a=0 ↔ a.1=0 := by
  rw [show (0 : Mon K P)=pair K P (0,1) from rfl,pair_eq_iff]
  constructor
  · rintro (h | h)
    · exact congrArg Prod.fst h
    · exact h.1
  · exact fun h => Or.inr ⟨h,rfl⟩

 theorem pair_surjective : Function.Surjective (pair K P) := by
  intro a
  induction a using Con.induction_on
  exact ⟨_,rfl⟩

instance instMonoidWithZeroMon : MonoidWithZero (Mon K P) where
  __ := (inferInstance : Monoid (Mon K P))
  zero := pair K P (0,1)
  zero_mul a := by
    obtain ⟨a,rfl⟩ := pair_surjective K P a
    change pair K P (0,1)*pair K P a=0
    rw [←map_mul]
    exact (pair_eq_zero K P _).mpr (zero_mul _)
  mul_zero a := by
    obtain ⟨a,rfl⟩ := pair_surjective K P a
    change pair K P a*pair K P (0,1)=0
    rw [←map_mul]
    exact (pair_eq_zero K P _).mpr (mul_zero _)

end FiniteAlgebraicEnvelopes.ZeroProduct

namespace FiniteAlgebraicEnvelopes.ZeroProduct
open scoped TensorProduct
open Contracted
variable (k K P : Type*) [CommRing k] [MonoidWithZero K] [Monoid P]

def left₀ : K →*₀ Mon K P where
  toFun a := pair K P (a,1)
  map_one' := map_one (pair K P)
  map_mul' a b := by simpa using (pair K P).map_mul (a,1) (b,1)
  map_zero' := pair_zero K P 1

def rightBasis : P →* Contracted.Algebra k (Mon K P) where
  toFun p := basis k (Mon K P) (pair K P (1,p)) 1
  map_one' := by
    rw [show pair K P (1,1)=1 from map_one (pair K P)]
    exact basis_identity k (Mon K P)
  map_mul' a b := by
    rw [basis_mul,one_mul,←map_mul]
    simp only [Prod.mk_mul_mk,one_mul]

def leftAlgebra : Contracted.Algebra k K →ₐ[k] Contracted.Algebra k (Mon K P) := Contracted.map (left₀ K P)
def rightAlgebra : MonoidAlgebra k P →ₐ[k] Contracted.Algebra k (Mon K P) :=
  MonoidAlgebra.lift k _ P (rightBasis k K P)

@[simp] theorem leftAlgebra_basis (a : K) (r : k) :
    leftAlgebra k K P (basis k K a r)=basis k (Mon K P) (pair K P (a,1)) r :=
  Contracted.map_basis (left₀ K P) a r

@[simp] theorem rightAlgebra_single (p : P) (r : k) :
    rightAlgebra k K P (MonoidAlgebra.single p r)=basis k (Mon K P) (pair K P (1,p)) r := by
  rw [rightAlgebra,MonoidAlgebra.lift_single]
  change r • quotient k (Mon K P) (MonoidAlgebra.single (pair K P (1,p)) 1)=_
  rw [←map_smul]
  simp [basis]

theorem left_right_commute (x : Contracted.Algebra k K) (y : MonoidAlgebra k P) :
    Commute (leftAlgebra k K P x) (rightAlgebra k K P y) := by
  obtain ⟨f,rfl⟩ := (zeroIdeal k K).ringCon.mkₐ_surjective (α:=k) x
  change leftAlgebra k K P (quotient k K f)*rightAlgebra k K P y=
    rightAlgebra k K P y*leftAlgebra k K P (quotient k K f)
  induction f using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,add_mul,mul_add,hf,hg]
  | single a r =>
    change leftAlgebra k K P (basis k K a r)*rightAlgebra k K P y=
      rightAlgebra k K P y*leftAlgebra k K P (basis k K a r)
    rw [leftAlgebra_basis]
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,add_mul,mul_add,hf,hg]
    | single p t =>
      simp only [rightAlgebra_single,basis_mul,←map_mul,Prod.mk_mul_mk,one_mul,mul_one]
      rw [mul_comm r t]

def tensorMap : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P →ₐ[k] Contracted.Algebra k (Mon K P) :=
  Algebra.TensorProduct.lift (leftAlgebra k K P) (rightAlgebra k K P) (left_right_commute k K P)

@[simp] theorem tensorMap_basis (a : K) (p : P) (r t : k) :
    tensorMap k K P (basis k K a r ⊗ₜ[k] MonoidAlgebra.single p t)=
      basis k (Mon K P) (pair K P (a,p)) (r*t) := by
  rw [tensorMap,Algebra.TensorProduct.lift_tmul,leftAlgebra_basis,rightAlgebra_single,basis_mul,←map_mul]
  simp

def nonzeroPair (a : {a : K // a≠0} × P) : {t : Mon K P // t≠0} :=
  ⟨pair K P (a.1,a.2),fun he => a.1.property ((pair_eq_zero K P _).mp he)⟩

theorem nonzeroPair_bijective : Function.Bijective (nonzeroPair K P) := by
  constructor
  · rintro ⟨⟨a,ha⟩,p⟩ ⟨⟨b,hb⟩,q⟩ he
    have hh := (pair_eq_iff K P _ _).mp (congrArg Subtype.val he)
    rcases hh with hh | hh
    · exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (congrArg (fun t : K×P => t.2) hh)
    · exact (ha hh.1).elim
  · rintro ⟨t,ht⟩
    obtain ⟨⟨a,p⟩,rfl⟩ := pair_surjective K P t
    have ha : a≠0 := fun he => ht ((pair_eq_zero K P _).mpr he)
    exact ⟨(⟨a,ha⟩,p),rfl⟩

def nonzeroEquiv : ({a : K // a≠0} × P) ≃ {t : Mon K P // t≠0} :=
  Equiv.ofBijective (nonzeroPair K P) (nonzeroPair_bijective K P)

def tensorBasis := (monoidBasis (k:=k) (H:=K)).tensorProduct (MonoidAlgebra.basis P k)

def tensorLinearEquiv : Contracted.Algebra k K ⊗[k] MonoidAlgebra k P ≃ₗ[k] Contracted.Algebra k (Mon K P) :=
  (tensorBasis k K P).equiv (monoidBasis (k:=k) (H:=Mon K P)) (nonzeroEquiv K P)

end FiniteAlgebraicEnvelopes.ZeroProduct

end

end OAI
end

section
-- module Solutions.OAIFAE.Corners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tensor embeddings and the nonunital corner maps between the two algebras.
-/

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open scoped TensorProduct
variable {k A B C D : Type*} [CommRing k] [Ring A] [Ring B] [Ring C] [Ring D]
  [Algebra k A] [Algebra k B] [Algebra k C] [Algebra k D]

def map (f : A →ₙₐ[k] B) (g : C →ₙₐ[k] D) : A⊗[k] C →ₙₐ[k] B⊗[k] D where
  toFun := TensorProduct.map (f : A →ₗ[k] B) (g : C →ₗ[k] D)
  map_zero' := map_zero _
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x z hx hz => simp only [add_mul,map_add,hx,hz]
    | tmul a c =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [mul_add,map_add,hx,hy]
      | tmul b d => simp only [Algebra.TensorProduct.tmul_mul_tmul,TensorProduct.map_tmul,LinearMap.coe_coe,map_mul]

@[simp] theorem map_tmul (f : A →ₙₐ[k] B) (g : C →ₙₐ[k] D) (a : A) (c : C) :
    map f g (a⊗ₜ[k] c)=f a⊗ₜ[k] g c := TensorProduct.map_tmul _ _ _ _

def op (f : A →ₙₐ[k] B) : Aᵐᵒᵖ →ₙₐ[k] Bᵐᵒᵖ where
  toFun x := MulOpposite.op (f x.unop)
  map_zero' := by simp
  map_add' x y := by simp
  map_mul' x y := by simp
  map_smul' r x := by simp

@[simp] theorem op_apply (f : A →ₙₐ[k] B) (x : Aᵐᵒᵖ) : op f x=MulOpposite.op (f x.unop) := rfl

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
variable {k A B : Type*} [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
def linear (f : A →ₙₐ[k] B) : A →ₗ[k] B := f
@[simp] theorem linear_apply (f : A →ₙₐ[k] B) (a : A) : linear f a=f a := rfl
end

end FiniteAlgebraicEnvelopes.NonunitalTensor

namespace FiniteAlgebraicEnvelopes.NonunitalTensor

section
open scoped TensorProduct
variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable (f : A →ₙₐ[k] A)

 theorem image_left (a : A) : f 1*f a=f a := by rw [←map_mul,one_mul]
 theorem image_right (a : A) : f a*f 1=f a := by rw [←map_mul,mul_one]

end

end FiniteAlgebraicEnvelopes.NonunitalTensor

end

end OAI
end

section
-- module Solutions.OAIFAE.MappingTori
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Sequential limits, injective induced maps, and finite presentation of mapping tori.
-/


namespace FiniteAlgebraicEnvelopes.SequentialLimit

variable {Q : Type*} [Group Q] (f : Monoid.End Q)

def transition (i j : ℕ) (_ : i ≤ j) : Q →* Q := f ^ (j - i)

instance instDirectedSystemNatCoeMonoidHomTransition : DirectedSystem (fun _ : ℕ => Q) (transition f · · ·) where
  map_self {i} x := by
    change (f ^ (i-i)) x = x
    rw [Nat.sub_self, pow_zero]
    rfl
  map_map {k j i} hij hjk x := by
    change ((f ^ (k-j)) * (f ^ (j-i))) x = (f ^ (k-i)) x
    rw [← pow_add]
    congr 2
    omega

abbrev Limit := DirectLimit (fun _ : ℕ => Q) (transition f)

noncomputable def of (i : ℕ) : Q →* Limit f where
  toFun x := ⟦⟨i,x⟩⟧
  map_one' := (DirectLimit.one_def i).symm
  map_mul' _ _ := (DirectLimit.mul_def _ _ _).symm

theorem of_transition (i j : ℕ) (h : i ≤ j) (x : Q) :
    of f j (transition f i j h x) = of f i x := DirectLimit.mk_apply ..

@[simp] theorem of_succ (i : ℕ) (x : Q) : of f (i+1) (f x) = of f i x := by
  have he : transition f i (i+1) (Nat.le_succ i) = f := by
    change (f ^ (i+1-i) : Monoid.End Q) = f
    rw [show i+1-i = 1 by omega, pow_one]
  have hh := of_transition f i (i+1) (Nat.le_succ i) x
  rw [he] at hh
  exact hh

noncomputable def lift {H : Type*} [Group H] (g : ℕ → Q →* H)
    (h : ∀ i j hij x, g i x = g j (transition f i j hij x)) : Limit f →* H where
  toFun := DirectLimit.lift (transition f) (g ·) h
  map_one' := DirectLimit.lift_one g h
  map_mul' := DirectLimit.lift_mul g h

@[simp] theorem lift_of {H : Type*} [Group H] (g : ℕ → Q →* H) (h) (i) (x) :
    lift f g h (of f i x) = g i x := rfl

theorem hom_ext {H : Type*} [Group H] {a b : Limit f →* H}
    (h : ∀ i x, a (of f i x) = b (of f i x)) : a = b := by
  ext z
  exact DirectLimit.induction (transition f) h z

noncomputable def shiftHom : Limit f →* Limit f :=
  lift f (fun i => of f (i+1)) (by
    intro i j hij x
    simpa [transition] using
      (of_transition f (i+1) (j+1) (Nat.add_le_add_right hij 1) x).symm)

noncomputable def forwardHom : Limit f →* Limit f :=
  lift f (fun i => (of f i).comp f) (by
    intro i j hij x
    change of f i (f x) = of f j (f ((f ^ (j-i)) x))
    have hc : f ((f ^ (j-i)) x) = (f ^ (j-i)) (f x) := by
      exact DFunLike.congr_fun (Commute.self_pow f (j-i)).eq x
    rw [hc]
    exact (of_transition f i j hij (f x)).symm)

@[simp] theorem shift_of (i) (x) : shiftHom f (of f i x) = of f (i+1) x := rfl
@[simp] theorem forward_of (i) (x) : forwardHom f (of f i x) = of f i (f x) := rfl

noncomputable def shift : MulAut (Limit f) where
  toFun := shiftHom f
  invFun := forwardHom f
  left_inv := by
    intro z
    induction z using DirectLimit.induction with | ih i x =>
      exact of_succ f i x
  right_inv := by
    intro z
    induction z using DirectLimit.induction with | ih i x =>
      exact of_succ f i x
  map_mul' := map_mul (shiftHom f)

@[simp] theorem shift_apply_of (i) (x) : shift f (of f i x) = of f (i+1) x := rfl
@[simp] theorem shift_symm_of (i) (x) : (shift f).symm (of f i x) = of f i (f x) := rfl

theorem compatible_of_succ {H : Type*} [Group H] (g : ℕ → Q →* H)
    (h : ∀ i x, g (i+1) (f x) = g i x) :
    ∀ i j hij x, g i x = g j (transition f i j hij x) := by
  intro i j hij x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  simp only [transition, Nat.add_sub_cancel_left]
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ']
    change g i x = g (i + (k+1)) (f ((f ^ k) x))
    rw [show i+(k+1) = (i+k)+1 by omega, h]
    exact ih x (Nat.le_add_right _ _)

noncomputable def action : Multiplicative ℤ →* MulAut (Limit f) :=
  zpowersHom _ (shift f)

abbrev Torus := (Limit f) ⋊[action f] Multiplicative ℤ

noncomputable def base : Q →* Torus f := SemidirectProduct.inl.comp (of f 0)
noncomputable def stable : Torus f := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[simp] theorem action_one : action f (Multiplicative.ofAdd 1) = shift f := by
  simp [action, zpowersHom]

@[simp] theorem action_neg_one : action f (Multiplicative.ofAdd (-1)) = (shift f).symm := by
  change (shift f) ^ (-1 : ℤ) = (shift f).symm
  rw [zpow_neg_one]
  rfl

theorem relation (x : Q) : (stable f)⁻¹ * base f x * stable f = base f (f x) := by
  change (SemidirectProduct.inr (Multiplicative.ofAdd 1))⁻¹ *
    SemidirectProduct.inl (of f 0 x) * SemidirectProduct.inr (Multiplicative.ofAdd 1) = _
  rw [← map_inv, ← SemidirectProduct.inl_aut_inv]
  change SemidirectProduct.inl ((shift f).symm (of f 0 x)) = _
  rfl

section Universal
variable {H : Type*} [Group H] (h : Q →* H) (t : H)
    (ht : ∀ x, t⁻¹ * h x * t = h (f x))

noncomputable def stageMap (i : ℕ) : Q →* H :=
  (MulAut.conj (t ^ i)).toMonoidHom.comp h

@[simp] theorem stageMap_apply (i) (x) : stageMap h t i x = t^i * h x * (t^i)⁻¹ := rfl

include ht in
theorem stageMap_succ (i : ℕ) (x : Q) : stageMap h t (i+1) (f x) = stageMap h t i x := by
  simp only [stageMap_apply, ← ht, pow_succ, mul_inv_rev]
  group

noncomputable def limitMap : Limit f →* H :=
  lift f (stageMap h t) (compatible_of_succ f (stageMap h t) (stageMap_succ f h t ht))

@[simp] theorem limitMap_of (i) (x) : limitMap f h t ht (of f i x) = t^i * h x * (t^i)⁻¹ := rfl

theorem limitMap_shift (x : Limit f) :
    limitMap f h t ht (shift f x) = t * limitMap f h t ht x * t⁻¹ := by
  induction x using DirectLimit.induction (transition f) with | ih i x =>
    change limitMap f h t ht (shift f (of f i x)) =
      t * limitMap f h t ht (of f i x) * t⁻¹
    simp only [shift_apply_of, limitMap_of, pow_succ', mul_inv_rev]
    group

theorem limitMap_shift_inv (x : Limit f) :
    limitMap f h t ht ((shift f)⁻¹ x) = t⁻¹ * limitMap f h t ht x * t := by
  have hh := limitMap_shift f h t ht ((shift f)⁻¹ x)
  simp only [MulAut.apply_inv_self] at hh
  rw [hh]
  group

theorem limitMap_shift_zpow (n : ℤ) (x : Limit f) :
    limitMap f h t ht (((shift f)^n) x) = t^n * limitMap f h t ht x * (t^n)⁻¹ := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    rw [zpow_add, zpow_add, zpow_one, zpow_one, mul_inv_rev]
    change limitMap f h t ht (((shift f)^(n:ℤ)) (shift f x)) = _
    rw [ih, limitMap_shift]
    group
  | pred n ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_add, zpow_neg_one, zpow_neg_one, mul_inv_rev]
    change limitMap f h t ht (((shift f)^(-(n:ℤ))) ((shift f)⁻¹ x)) = _
    rw [ih, limitMap_shift_inv]
    group

noncomputable def torusLift : Torus f →* H :=
  SemidirectProduct.lift (limitMap f h t ht) (zpowersHom H t) (by
    intro n
    ext x
    exact limitMap_shift_zpow f h t ht n.toAdd x)

@[simp] theorem torusLift_base (x : Q) : torusLift f h t ht (base f x) = h x := by
  simp [base, torusLift]

@[simp] theorem torusLift_stable : torusLift f h t ht (stable f) = t := by
  simp [stable, torusLift, zpowersHom]

end Universal

theorem inl_of (i : ℕ) (x : Q) :
    (SemidirectProduct.inl (of f i x) : Torus f) =
      stable f ^ i * base f x * (stable f ^ i)⁻¹ := by
  induction i with
  | zero => simp [base]
  | succ i ih =>
    have hh := SemidirectProduct.inl_aut (φ := action f) (Multiplicative.ofAdd 1) (of f i x)
    rw [action_one, shift_apply_of, map_inv] at hh
    rw [hh, ih]
    change stable f * (stable f ^ i * base f x * (stable f ^ i)⁻¹) * (stable f)⁻¹ = _
    rw [pow_succ', mul_inv_rev]
    simp only [mul_assoc]

theorem torus_hom_ext {H : Type*} [Group H] {a b : Torus f →* H}
    (hq : a.comp (base f) = b.comp (base f)) (ht : a (stable f) = b (stable f)) : a = b := by
  apply SemidirectProduct.hom_ext
  · apply hom_ext f
    intro i x
    simp only [MonoidHom.comp_apply, inl_of, map_mul, map_inv, map_pow, ht]
    have hx : a (base f x) = b (base f x) := DFunLike.congr_fun hq x
    rw [hx]
  · apply MonoidHom.ext
    intro n
    have hn : n = (Multiplicative.ofAdd 1) ^ n.toAdd := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hn]
    simp only [MonoidHom.comp_apply, map_zpow]
    exact congrArg (fun z => z ^ n.toAdd) ht

end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.MappingTorus
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

abbrev Free := Monoid.Coprod Q (Multiplicative ℤ)
def letter : Free (Q := Q) := Monoid.Coprod.inr (Multiplicative.ofAdd 1)
def relator (x : Q) : Free (Q := Q) :=
  (letter (Q := Q))⁻¹ * Monoid.Coprod.inl x * letter * (Monoid.Coprod.inl (f x))⁻¹

def relations : Subgroup (Free (Q := Q)) := Subgroup.normalClosure (Set.range (relator f))
instance instNormalFreeRelations : (relations f).Normal := inferInstanceAs (Subgroup.normalClosure _).Normal
abbrev Presentation := Free (Q := Q) ⧸ relations f
noncomputable def base : Q →* Presentation f := (QuotientGroup.mk' (relations f)).comp Monoid.Coprod.inl
noncomputable def stable : Presentation f := QuotientGroup.mk' (relations f) letter

theorem relation (x : Q) : (stable f)⁻¹ * base f x * stable f = base f (f x) := by
  have h : QuotientGroup.mk' (relations f) (relator f x) = 1 := by
    change relator f x ∈ (QuotientGroup.mk' (relations f)).ker
    rw [QuotientGroup.ker_mk']
    exact Subgroup.subset_normalClosure (Set.mem_range_self x)
  apply mul_inv_eq_one.mp
  exact h

section Universal
variable {H : Type*} [Group H] (h : Q →* H) (t : H)
    (ht : ∀ x, t⁻¹ * h x * t = h (f x))

noncomputable def lift : Presentation f →* H :=
  QuotientGroup.lift (relations f) (Monoid.Coprod.lift h (zpowersHom H t)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, rfl⟩
    change Monoid.Coprod.lift h (zpowersHom H t) (relator f x) = 1
    simpa [relator, letter, zpowersHom] using mul_inv_eq_one.mpr (ht x))

@[simp] theorem lift_base (x : Q) : lift f h t ht (base f x) = h x := by
  change (Monoid.Coprod.lift h (zpowersHom H t)) (Monoid.Coprod.inl x) = h x
  simp
@[simp] theorem lift_stable : lift f h t ht (stable f) = t := by
  simp [lift, stable, letter, zpowersHom]
end Universal

theorem hom_ext {H : Type*} [Group H] {a b : Presentation f →* H}
    (hq : a.comp (base f) = b.comp (base f)) (ht : a (stable f) = b (stable f)) : a = b := by
  apply MonoidHom.cancel_right (QuotientGroup.mk'_surjective (relations f)) |>.mp
  apply Monoid.Coprod.hom_ext
  · exact hq
  · apply MonoidHom.ext
    intro n
    have hn : n = (Multiplicative.ofAdd 1) ^ n.toAdd := by
      apply Multiplicative.toAdd.injective
      simp
    rw [hn]
    simp only [MonoidHom.comp_apply, map_zpow]
    exact congrArg (fun z => z ^ n.toAdd) ht

noncomputable def equivalence : Presentation f ≃* SequentialLimit.Torus f := by
  let a := lift f (SequentialLimit.base f) (SequentialLimit.stable f) (SequentialLimit.relation f)
  let b := SequentialLimit.torusLift f (base f) (stable f) (relation f)
  have ha : b.comp a = MonoidHom.id _ := by
    apply hom_ext f
    · ext x : 1
      simp [a,b]
    · simp [a,b]
  have hb : a.comp b = MonoidHom.id _ := by
    apply SequentialLimit.torus_hom_ext f
    · ext x : 1
      simp [a,b]
    · simp [a,b]
  exact { a with
    invFun := b
    left_inv := DFunLike.congr_fun ha
    right_inv := DFunLike.congr_fun hb }

end FiniteAlgebraicEnvelopes.MappingTorus

namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q E : Type*} [Group Q] [Group E] (f : Monoid.End Q) (g : Monoid.End E)
    (q : Q →* E) (hq : ∀ x, q (f x) = g (q x))

include hq in
theorem transition_natural (i j : ℕ) (hij : i ≤ j) (x : Q) :
    q (transition f i j hij x) = transition g i j hij (q x) := by
  change q ((f ^ (j-i)) x) = (g ^ (j-i)) (q x)
  generalize j-i = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change q ((f * f^n) x) = (g * g^n) (q x)
    change q (f ((f^n) x)) = g ((g^n) (q x))
    rw [hq, ih]

noncomputable def map : Limit f →* Limit g :=
  lift f (fun i => (of g i).comp q) (by
    intro i j hij x
    change of g i (q x) = of g j (q (transition f i j hij x))
    rw [transition_natural f g q hq]
    exact (of_transition g i j hij (q x)).symm)

@[simp] theorem map_of (i) (x) : map f g q hq (of f i x) = of g i (q x) := rfl

theorem map_shift (x : Limit f) : map f g q hq (shift f x) = shift g (map f g q hq x) := by
  induction x using DirectLimit.induction (transition f) with | ih i x => rfl

theorem map_surjective (hs : Function.Surjective q) : Function.Surjective (map f g q hq) := by
  intro z
  induction z using DirectLimit.induction (transition g) with | ih i x =>
    obtain ⟨y, rfl⟩ := hs x
    exact ⟨of f i y, rfl⟩

/-- Killing the coefficient kernel in one step makes the induced map injective.
No injectivity assumption on either transition is needed. -/
theorem map_injective (hk : ∀ x, q x = 1 → f x = 1) : Function.Injective (map f g q hq) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro z hz
  change z = 1
  induction z using DirectLimit.induction (transition f) with | ih i x =>
    change of g i (q x) = 1 at hz
    obtain ⟨j, hij, he⟩ := (DirectLimit.exists_eq_one (G := fun _ : ℕ => E) (f := transition g) ⟨i, q x⟩).mp hz
    have he' : q (transition f i j hij x) = 1 := by
      rw [transition_natural f g q hq, he]
    have hf' := hk _ he'
    change of f i x = 1
    rw [← of_transition f i j hij x, ← of_succ f j (transition f i j hij x), hf', map_one]

noncomputable def equivalence (hs : Function.Surjective q)
    (hk : ∀ x, q x = 1 → f x = 1) : Limit f ≃* Limit g :=
  MulEquiv.ofBijective (map f g q hq) ⟨map_injective f g q hq hk, map_surjective f g q hq hs⟩

end FiniteAlgebraicEnvelopes.SequentialLimit

end OAI
end

section
-- module Solutions.OAIFAE.SteinbergLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Steinberg sequential limits, annihilated kernels, and injective torus maps.
-/

section

namespace FiniteAlgebraicEnvelopes.Steinberg
variable {R : Type*} [Ring R]

def correctedUnits (ψ : R →ₙ+* R) := Units.map (correctedMap (matrixNonunitalMap (ι:=Fin 6) ψ))

end FiniteAlgebraicEnvelopes.Steinberg
end

namespace FiniteAlgebraicEnvelopes.Steinberg

section
open scoped commutatorElement
variable {R : Type*} [Ring R]

theorem freshThird (i j : Fin 6) : ∃ k : Fin 6, k≠i ∧ k≠j := by
  have hh : ∃ k ∈ (Finset.univ : Finset (Fin 6)), k∉({i,j} : Finset (Fin 6)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have hc : ({i,j} : Finset (Fin 6)).card≤2 := by
      simpa using Finset.card_insert_le i {j}
    simpa using (show ({i,j} : Finset (Fin 6)).card<6 by omega)
  simpa using hh

abbrev RootIndex := {p : Fin 6 × Fin 6 // p.1≠p.2}

end

open scoped commutatorElement
variable {R : Type*} [Ring R]

theorem thirdIndex (i j : Fin 6) : ∃ k : Fin 6, k≠i ∧ k≠j := by
  have hh : ∃ k ∈ (Finset.univ : Finset (Fin 6)), k∉({i,j} : Finset (Fin 6)) := by
    apply Finset.exists_mem_notMem_of_card_lt_card
    have hc : ({i,j} : Finset (Fin 6)).card≤2 := by simpa using Finset.card_insert_le i {j}
    simpa using (show ({i,j} : Finset (Fin 6)).card<6 by omega)
  simpa using hh

end FiniteAlgebraicEnvelopes.Steinberg

end

end OAI
end

section
-- module Solutions.OAIFAE.AlgebraPresentations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentations of tensor, opposite, contracted, unitized, and coefficient algebras.
-/

namespace FiniteAlgebraicEnvelopes.TensorPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] (A C : Type*)

abbrev F := FreeAlgebra k (A⊕C)
def inLeft : FreeAlgebra k A →ₐ[k] F k A C := FreeAlgebra.lift k (fun a => FreeAlgebra.ι k (Sum.inl a))
def inRight : FreeAlgebra k C →ₐ[k] F k A C := FreeAlgebra.lift k (fun c => FreeAlgebra.ι k (Sum.inr c))

variable {A C}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop) (s : FreeAlgebra k C → FreeAlgebra k C → Prop)

inductive Rel : F k A C → F k A C → Prop
  | left {a b} : r a b → Rel (inLeft k A C a) (inLeft k A C b)
  | right {a b} : s a b → Rel (inRight k A C a) (inRight k A C b)
  | commute (a : A) (c : C) : Rel (FreeAlgebra.ι k (Sum.inl a)*FreeAlgebra.ι k (Sum.inr c))
      (FreeAlgebra.ι k (Sum.inr c)*FreeAlgebra.ι k (Sum.inl a))

abbrev P := RingQuot (Rel k r s)
def q : F k A C →ₐ[k] P k r s := RingQuot.mkAlgHom k (Rel k r s)

def leftFree : FreeAlgebra k A →ₐ[k] P k r s := (q k r s).comp (inLeft k A C)
def rightFree : FreeAlgebra k C →ₐ[k] P k r s := (q k r s).comp (inRight k A C)

def left : RingQuot r →ₐ[k] P k r s := RingQuot.liftAlgHom k ⟨leftFree k r s,by
  intro a b hab
  exact RingQuot.mkAlgHom_rel k (Rel.left hab)⟩
def right : RingQuot s →ₐ[k] P k r s := RingQuot.liftAlgHom k ⟨rightFree k r s,by
  intro a b hab
  exact RingQuot.mkAlgHom_rel k (Rel.right hab)⟩

@[simp] theorem left_mk (a : FreeAlgebra k A) : left k r s (RingQuot.mkAlgHom k r a)=leftFree k r s a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
@[simp] theorem right_mk (c : FreeAlgebra k C) : right k r s (RingQuot.mkAlgHom k s c)=rightFree k r s c :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem leftFree_ι (a : A) : leftFree k r s (FreeAlgebra.ι k a)=q k r s (FreeAlgebra.ι k (Sum.inl a)) := by
  simp [leftFree,inLeft]
@[simp] theorem rightFree_ι (c : C) : rightFree k r s (FreeAlgebra.ι k c)=q k r s (FreeAlgebra.ι k (Sum.inr c)) := by
  simp [rightFree,inRight]

theorem free_commute (a : FreeAlgebra k A) (c : FreeAlgebra k C) : Commute (leftFree k r s a) (rightFree k r s c) := by
  induction a using FreeAlgebra.induction with
  | grade0 z => rw [AlgHom.commutes]; exact Algebra.commutes _ _
  | grade1 a =>
    induction c using FreeAlgebra.induction with
    | grade0 z => rw [AlgHom.commutes]; exact (Algebra.commutes _ _).symm
    | grade1 c =>
      rw [leftFree_ι,rightFree_ι]
      change q k r s _ * q k r s _=q k r s _ * q k r s _
      rw [←map_mul,←map_mul]
      exact RingQuot.mkAlgHom_rel k (Rel.commute a c)
    | add a b ha hb => rw [map_add]; exact ha.add_right hb
    | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add]; exact ha.add_left hb
  | mul a b ha hb => rw [map_mul]; exact ha.mul_left hb

theorem quotient_commute (a : RingQuot r) (c : RingQuot s) : Commute (left k r s a) (right k r s c) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective k r a
  obtain ⟨c,rfl⟩ := RingQuot.mkAlgHom_surjective k s c
  rw [left_mk,right_mk]
  exact free_commute k r s a c

def fromTensor : (RingQuot r ⊗[k] RingQuot s) →ₐ[k] P k r s :=
  Algebra.TensorProduct.lift (left k r s) (right k r s) (quotient_commute k r s)

def toTensorFree : F k A C →ₐ[k] (RingQuot r ⊗[k] RingQuot s) :=
  FreeAlgebra.lift k (Sum.elim
    (fun a => RingQuot.mkAlgHom k r (FreeAlgebra.ι k a) ⊗ₜ[k] (1:RingQuot s))
    (fun c => (1:RingQuot r) ⊗ₜ[k] RingQuot.mkAlgHom k s (FreeAlgebra.ι k c)))

theorem toTensorFree_left : (toTensorFree k r s).comp (inLeft k A C)=
    Algebra.TensorProduct.includeLeft.comp (RingQuot.mkAlgHom k r) := by
  apply FreeAlgebra.hom_ext
  funext a
  simp [toTensorFree,inLeft]

theorem toTensorFree_right : (toTensorFree k r s).comp (inRight k A C)=
    Algebra.TensorProduct.includeRight.comp (RingQuot.mkAlgHom k s) := by
  apply FreeAlgebra.hom_ext
  funext c
  simp [toTensorFree,inRight]

def toTensor : P k r s →ₐ[k] (RingQuot r ⊗[k] RingQuot s) :=
  RingQuot.liftAlgHom k ⟨toTensorFree k r s,by
    intro a b hab
    cases hab with
    | left hab =>
      change ((toTensorFree k r s).comp (inLeft k A C)) _ = ((toTensorFree k r s).comp (inLeft k A C)) _
      rw [toTensorFree_left]
      exact congrArg (Algebra.TensorProduct.includeLeft : RingQuot r →ₐ[k] (RingQuot r ⊗[k] RingQuot s)) (RingQuot.mkAlgHom_rel k hab)
    | right hab =>
      change ((toTensorFree k r s).comp (inRight k A C)) _ = ((toTensorFree k r s).comp (inRight k A C)) _
      rw [toTensorFree_right]
      exact congrArg (Algebra.TensorProduct.includeRight : RingQuot s →ₐ[k] (RingQuot r ⊗[k] RingQuot s)) (RingQuot.mkAlgHom_rel k hab)
    | commute a c => simp [toTensorFree,Algebra.TensorProduct.tmul_mul_tmul]⟩

@[simp] theorem toTensor_q (a : F k A C) : toTensor k r s (q k r s a)=toTensorFree k r s a :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

@[simp] theorem toTensor_left (a : RingQuot r) : toTensor k r s (left k r s a)=a ⊗ₜ[k] (1:RingQuot s) := by
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective k r a
  rw [left_mk]
  change toTensor k r s (q k r s (inLeft k A C a))=_
  rw [toTensor_q]
  exact DFunLike.congr_fun (toTensorFree_left k r s) a

@[simp] theorem toTensor_right (c : RingQuot s) : toTensor k r s (right k r s c)=(1:RingQuot r) ⊗ₜ[k] c := by
  obtain ⟨c,rfl⟩ := RingQuot.mkAlgHom_surjective k s c
  rw [right_mk]
  change toTensor k r s (q k r s (inRight k A C c))=_
  rw [toTensor_q]
  exact DFunLike.congr_fun (toTensorFree_right k r s) c

theorem to_from : (toTensor k r s).comp (fromTensor k r s)=AlgHom.id k _ := by
  apply Algebra.TensorProduct.ext'
  intro a c
  simp [fromTensor]

theorem from_to : (fromTensor k r s).comp (toTensor k r s)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply FreeAlgebra.hom_ext
  funext a
  cases a with
  | inl a =>
    change fromTensor k r s (toTensor k r s (q k r s (FreeAlgebra.ι k (Sum.inl a))))=_
    rw [toTensor_q]
    simp [toTensorFree,fromTensor,q]
  | inr c =>
    change fromTensor k r s (toTensor k r s (q k r s (FreeAlgebra.ι k (Sum.inr c))))=_
    rw [toTensor_q]
    simp [toTensorFree,fromTensor,q]

def equivalence : P k r s ≃ₐ[k] (RingQuot r ⊗[k] RingQuot s) :=
  AlgEquiv.ofAlgHom (toTensor k r s) (fromTensor k r s) (to_from k r s) (from_to k r s)

end FiniteAlgebraicEnvelopes.TensorPresentation

namespace FiniteAlgebraicEnvelopes.OppositePresentation
open MulOpposite
variable (k : Type*) [CommRing k] (A : Type*)

def reverse : FreeAlgebra k A →ₐ[k] (FreeAlgebra k A)ᵐᵒᵖ :=
  FreeAlgebra.lift k (fun a => op (FreeAlgebra.ι k a))

def unreverse : (FreeAlgebra k A)ᵐᵒᵖ →ₐ[k] FreeAlgebra k A := AlgHom.opComm (reverse k A)

@[simp] theorem reverse_ι (a : A) : reverse k A (FreeAlgebra.ι k a)=op (FreeAlgebra.ι k a) := by
  simp [reverse]
@[simp] theorem unreverse_op (a : FreeAlgebra k A) : unreverse k A (op a)=(reverse k A a).unop := rfl

theorem unreverse_reverse : (unreverse k A).comp (reverse k A)=AlgHom.id k _ := by
  apply FreeAlgebra.hom_ext
  funext a
  simp

theorem reverse_unreverse : (reverse k A).comp (unreverse k A)=AlgHom.id k _ := by
  apply AlgHom.ext
  intro a
  obtain ⟨a,rfl⟩ := op_surjective a
  apply unop_injective
  exact DFunLike.congr_fun (unreverse_reverse k A) a

def freeEquivalence : FreeAlgebra k A ≃ₐ[k] (FreeAlgebra k A)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (reverse k A) (unreverse k A) (reverse_unreverse k A) (unreverse_reverse k A)

variable {A}
variable {R : Type*} [Ring R] [Algebra k R] (r : R → R → Prop)

def opRel (a b : Rᵐᵒᵖ) : Prop := r a.unop b.unop

def quotientToOp : RingQuot (opRel r) →ₐ[k] (RingQuot r)ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k r).op,by
    intro a b hab
    exact congrArg op (RingQuot.mkAlgHom_rel k hab)⟩

def quotientFromOpAux : RingQuot r →ₐ[k] (RingQuot (opRel r))ᵐᵒᵖ :=
  RingQuot.liftAlgHom k ⟨(RingQuot.mkAlgHom k (opRel r)).op.comp (AlgEquiv.opOp k R).toAlgHom,by
    intro a b hab
    exact congrArg op (RingQuot.mkAlgHom_rel k (show opRel r (op a) (op b) from hab))⟩

def quotientFromOp : (RingQuot r)ᵐᵒᵖ →ₐ[k] RingQuot (opRel r) :=
  AlgHom.opComm (quotientFromOpAux k r)

@[simp] theorem quotientToOp_mk (a : Rᵐᵒᵖ) :
    quotientToOp k r (RingQuot.mkAlgHom k (opRel r) a)=op (RingQuot.mkAlgHom k r a.unop) := by
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _
@[simp] theorem quotientFromOp_mk (a : R) :
    quotientFromOp k r (op (RingQuot.mkAlgHom k r a))=RingQuot.mkAlgHom k (opRel r) (op a) := by
  change (quotientFromOpAux k r (RingQuot.mkAlgHom k r a)).unop=_
  congr 1
  exact RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ _

theorem quotientToFrom : (quotientToOp k r).comp (quotientFromOp k r)=AlgHom.id k _ := by
  apply AlgHom.ext
  intro a
  obtain ⟨a,rfl⟩ := op_surjective a
  obtain ⟨a,rfl⟩ := RingQuot.mkAlgHom_surjective k r a
  simp

theorem quotientFromTo : (quotientFromOp k r).comp (quotientToOp k r)=AlgHom.id k _ := by
  apply RingQuot.ringQuot_ext'
  apply AlgHom.ext
  intro a
  simp

def quotientEquivalence : RingQuot (opRel r) ≃ₐ[k] (RingQuot r)ᵐᵒᵖ :=
  AlgEquiv.ofAlgHom (quotientToOp k r) (quotientFromOp k r) (quotientToFrom k r) (quotientFromTo k r)

variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

def freeRel (a b : FreeAlgebra k A) := opRel r ((freeEquivalence k A) a) ((freeEquivalence k A) b)

def presentation : RingQuot (freeRel k r) ≃ₐ[k] (RingQuot r)ᵐᵒᵖ :=
  (RingQuot.algEquivQuotAlgEquiv (freeEquivalence k A).symm (opRel r)).symm.trans (quotientEquivalence k r)

end FiniteAlgebraicEnvelopes.OppositePresentation

namespace FiniteAlgebraicEnvelopes.Unitize
variable {A B G : Type*} [Ring A] [Ring B] [Group G]
variable (i : A →ₙ+* B) (f : G →* A)

 theorem support_left (a : A) : i 1*i a=i a := by rw [←map_mul,one_mul]
 theorem support_right (a : A) : i a*i 1=i a := by rw [←map_mul,mul_one]

/-- Extend a group represented in a nonunital corner to units of the ambient ring. -/
def hom : G →* B where
  toFun g := 1-i 1+i (f g)
  map_one' := by rw [f.map_one,sub_add_cancel]
  map_mul' g h := by
    rw [map_mul,map_mul]
    have he : i 1*i 1=i 1 := support_left i 1
    have hg := support_right i (f g)
    have hh := support_left i (f h)
    noncomm_ring [he,hg,hh]

@[simp] theorem hom_apply (g : G) : hom i f g=1-i 1+i (f g) := rfl

def unitsHom : G →* Bˣ := (hom i f).toHomUnits

end FiniteAlgebraicEnvelopes.Unitize

namespace FiniteAlgebraicEnvelopes.EnvelopingPresentation
open scoped TensorProduct
variable (k : Type*) [CommRing k] {A : Type*}
variable (r : FreeAlgebra k A → FreeAlgebra k A → Prop)

abbrev Generators := A⊕A
def Rel : FreeAlgebra k (Generators (A:=A)) → FreeAlgebra k (Generators (A:=A)) → Prop :=
  TensorPresentation.Rel k r (OppositePresentation.freeRel k r)

def equivalence : RingQuot (Rel k r) ≃ₐ[k] (RingQuot r ⊗[k] (RingQuot r)ᵐᵒᵖ) :=
  (TensorPresentation.equivalence k r (OppositePresentation.freeRel k r)).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : RingQuot r ≃ₐ[k] RingQuot r)
      (OppositePresentation.presentation k r))

end FiniteAlgebraicEnvelopes.EnvelopingPresentation

end

end OAI
end

section
-- module Solutions.OAIFAE.AffineModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Affine module presentations, stabilized actions, and finite stabilizers.
-/

namespace FiniteAlgebraicEnvelopes.MatrixModule
open scoped BigOperators
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

def applyMatrix (A : Matrix ι ι R) (v : ι → V) : ι → V := fun i => ∑ j, A i j • v j

omit [DecidableEq ι] in
@[simp] theorem applyMatrix_zero (v : ι → V) : applyMatrix (0 : Matrix ι ι R) v=0 := by
  funext i
  simp [applyMatrix]

omit [DecidableEq ι] in
theorem applyMatrix_add (A B : Matrix ι ι R) (v : ι → V) :
    applyMatrix (A+B) v=applyMatrix A v+applyMatrix B v := by
  funext i
  simp [applyMatrix,add_smul,Finset.sum_add_distrib]

omit [DecidableEq ι] in
theorem applyMatrix_sub (A B : Matrix ι ι R) (v : ι → V) :
    applyMatrix (A-B) v=applyMatrix A v-applyMatrix B v := by
  funext i
  simp [applyMatrix,sub_smul,Finset.sum_sub_distrib]

@[simp] theorem applyMatrix_one (v : ι → V) : applyMatrix (1 : Matrix ι ι R) v=v := by
  funext i
  simp [applyMatrix,Matrix.one_apply,ite_smul]

omit [DecidableEq ι] in
theorem applyMatrix_mul (A B : Matrix ι ι R) (v : ι → V) :
    applyMatrix (A*B) v=applyMatrix A (applyMatrix B v) := by
  funext i
  simp only [applyMatrix,Matrix.mul_apply,Finset.sum_smul,Finset.smul_sum,mul_smul]
  exact Finset.sum_comm

omit [DecidableEq ι] in
theorem applyMatrix_vec_add (A : Matrix ι ι R) (v w : ι → V) :
    applyMatrix A (v+w)=applyMatrix A v+applyMatrix A w := by
  funext i
  simp [applyMatrix,smul_add,Finset.sum_add_distrib]

@[simp] theorem applyMatrix_singleVec (A : Matrix ι ι R) (j : ι) (v : V) (i : ι) :
    applyMatrix A (Pi.single j v) i=A i j • v := by
  simp [applyMatrix,Pi.single_apply,smul_ite]

@[simp] theorem applyMatrix_single (i j : ι) (r : R) (v : ι → V) :
    applyMatrix (Matrix.single i j r) v=Pi.single i (r • v j) := by
  funext c
  by_cases hc : c=i
  · subst c
    simp [applyMatrix,Matrix.single_apply]
  · simp [applyMatrix,hc,Ne.symm hc]

def unitsAddEquiv (g : (Matrix ι ι R)ˣ) : (ι → V) ≃+ (ι → V) where
  toFun := applyMatrix g.val
  invFun := applyMatrix g.inv
  left_inv v := by rw [←applyMatrix_mul,g.inv_val,applyMatrix_one]
  right_inv v := by rw [←applyMatrix_mul,g.val_inv,applyMatrix_one]
  map_add' := applyMatrix_vec_add g.val

def unitsAction : (Matrix ι ι R)ˣ →* MulAut (Multiplicative (ι → V)) where
  toFun g := AddEquiv.toMultiplicative (unitsAddEquiv g)
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact applyMatrix_one _
  map_mul' g h := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact applyMatrix_mul _ _ _

@[simp] theorem unitsAction_apply (g : (Matrix ι ι R)ˣ) (v : Multiplicative (ι → V)) :
    (unitsAction g v).toAdd=applyMatrix g.val v.toAdd := rfl

end FiniteAlgebraicEnvelopes.MatrixModule

section
namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V ι : Type*} [Ring R] [AddCommGroup V] [Module R V] [Fintype ι] [DecidableEq ι]

def columnMap (f : V →+ V) (v : ι → V) : ι → V := fun i => f (v i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem columnMap_add (f : V →+ V) (v w : ι → V) :
    columnMap f (v+w)=columnMap f v+columnMap f w := by funext i; exact map_add f _ _

theorem columnMap_matrix (f : V →+ V) (ψ : R →ₙ+* R)
    (hf : ∀ r v, f (r • v)=ψ r • f v) (A : Matrix ι ι R) (v : ι → V) :
    columnMap f (applyMatrix A v)=applyMatrix (matrixNonunitalMap ψ A) (columnMap f v) := by
  funext i
  simp only [columnMap,applyMatrix,map_sum,hf]
  rfl

theorem columnMap_corrected (f : V →+ V) (ψ : R →ₙ+* R)
    (hf : ∀ r v, f (r • v)=ψ r • f v) (A : Matrix ι ι R) (v : ι → V) :
    columnMap f (applyMatrix A v)=applyMatrix (correctedMap (matrixNonunitalMap ψ) A) (columnMap f v) := by
  change _=applyMatrix (1+matrixNonunitalMap ψ (A-1)) (columnMap f v)
  rw [applyMatrix_add,applyMatrix_one,←columnMap_matrix f ψ hf,←columnMap_add]
  rw [applyMatrix_sub,applyMatrix_one,add_sub_cancel]
end FiniteAlgebraicEnvelopes.MatrixModule

end

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {Q : Type*} [Group Q] (f : Monoid.End Q)

def stage (j : ℕ) : Set (Limit f) := Set.range (of f j)

instance countable_limit [Countable Q] : Countable (Limit f) := by
  unfold Limit DirectLimit
  infer_instance
end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.ColumnLimit
variable {B : Type*} [Ring B] (φ : B →ₙ+* B)

def transition : Monoid.End (Multiplicative (Fin 6 → B)) where
  toFun x := Multiplicative.ofAdd (fun i => φ (x.toAdd i))
  map_one' := by apply Multiplicative.toAdd.injective; funext i; exact map_zero φ
  map_mul' x y := by apply Multiplicative.toAdd.injective; funext i; exact map_add φ _ _

def marker : Multiplicative (Fin 6 → B) := Multiplicative.ofAdd (fun i => if i=0 then 1 else 0)

end FiniteAlgebraicEnvelopes.ColumnLimit
end

section
namespace FiniteAlgebraicEnvelopes.SequentialLimit
variable {A B C : Type*} [Group A] [Group B] [Group C]
variable (f : Monoid.End A) (g : Monoid.End B) (h : Monoid.End C)

theorem exists_common_stage₂ (x : Limit f) (y : Limit g) :
    ∃ i a b, x=of f i a ∧ y=of g i b := by
  obtain ⟨i,a,rfl⟩ := DirectLimit.exists_eq_mk (transition f) x
  obtain ⟨j,b,rfl⟩ := DirectLimit.exists_eq_mk (transition g) y
  exact ⟨max i j,transition f i (max i j) (le_max_left _ _) a,
    transition g j (max i j) (le_max_right _ _) b,
    (of_transition f _ _ _ _).symm,(of_transition g _ _ _ _).symm⟩

theorem exists_common_stage₃ (x : Limit f) (y : Limit g) (z : Limit h) :
    ∃ i a b c, x=of f i a ∧ y=of g i b ∧ z=of h i c := by
  obtain ⟨i,a,b,rfl,rfl⟩ := exists_common_stage₂ f g x y
  obtain ⟨j,c,rfl⟩ := DirectLimit.exists_eq_mk (transition h) z
  exact ⟨max i j,transition f i (max i j) (le_max_left _ _) a,
    transition g i (max i j) (le_max_left _ _) b,
    transition h j (max i j) (le_max_right _ _) c,
    (of_transition f _ _ _ _).symm,(of_transition g _ _ _ _).symm,(of_transition h _ _ _ _).symm⟩
end FiniteAlgebraicEnvelopes.SequentialLimit

namespace FiniteAlgebraicEnvelopes.LimitAction
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

include hc
theorem compatible_pow (n : ℕ) (x : Q) (v : V) :
    (g^n) (α x v)=α ((f^n) x) ((g^n) v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    exact (congrArg g ih).trans (hc _ _)

def applyLimit : Limit f → Limit g → Limit g :=
  DirectLimit.map₂ (transition f) (transition g) (transition g) (fun _ x v => α x v)
    (fun i j _ x v => compatible_pow α f g hc (j-i) x v)

@[simp] theorem applyLimit_of (i : ℕ) (x : Q) (v : V) :
    applyLimit α f g hc (of f i x) (of g i v)=of g i (α x v) := by
  change DirectLimit.map₂ (transition f) (transition g) (transition g) (fun _ x v => α x v) _ ⟦⟨i,x⟩⟧ ⟦⟨i,v⟩⟧=⟦⟨i,α x v⟩⟧
  exact DirectLimit.map₂_def (transition f) (transition g) (transition g)
    (fun _ x v => α x v) (fun i j _ x v => compatible_pow α f g hc (j-i) x v) i x v

@[simp] theorem applyLimit_one (v : Limit g) : applyLimit α f g hc 1 v=v := by
  obtain ⟨i,v,rfl⟩ := DirectLimit.exists_eq_mk (transition g) v
  change applyLimit α f g hc 1 (of g i v)=of g i v
  rw [←map_one (of f i),applyLimit_of,map_one]
  rfl

theorem applyLimit_mul (x y : Limit f) (v : Limit g) :
    applyLimit α f g hc (x*y) v=applyLimit α f g hc x (applyLimit α f g hc y v) := by
  obtain ⟨i,x,y,v,rfl,rfl,rfl⟩ := exists_common_stage₃ f f g x y v
  rw [←map_mul,applyLimit_of,applyLimit_of,applyLimit_of,map_mul]
  rfl

theorem applyLimit_mul_vec (x : Limit f) (v w : Limit g) :
    applyLimit α f g hc x (v*w)=applyLimit α f g hc x v*applyLimit α f g hc x w := by
  obtain ⟨i,x,v,w,rfl,rfl,rfl⟩ := exists_common_stage₃ f g g x v w
  rw [←map_mul,applyLimit_of,applyLimit_of,applyLimit_of,map_mul,map_mul]

def action : Limit f →* MulAut (Limit g) where
  toFun x := {
    toFun := applyLimit α f g hc x
    invFun := applyLimit α f g hc x⁻¹
    left_inv v := by rw [←applyLimit_mul,inv_mul_cancel,applyLimit_one]
    right_inv v := by rw [←applyLimit_mul,mul_inv_cancel,applyLimit_one]
    map_mul' := applyLimit_mul_vec α f g hc x }
  map_one' := by apply MulEquiv.ext; exact applyLimit_one α f g hc
  map_mul' x y := by apply MulEquiv.ext; exact applyLimit_mul α f g hc x y

@[simp] theorem action_of (i : ℕ) (x : Q) (v : V) :
    action α f g hc (of f i x) (of g i v)=of g i (α x v) := applyLimit_of α f g hc i x v

end FiniteAlgebraicEnvelopes.LimitAction
end

section

namespace FiniteAlgebraicEnvelopes.NonunitalTensor
open SequentialLimit
variable {k B : Type*} [CommRing k] [Ring B] [Algebra k B]
variable (φ : B →ₙₐ[k] B)

abbrev Columns := Multiplicative (Fin 6 → B)

def columnStep : Monoid.End (Columns (B:=B)) := ColumnLimit.transition (φ : B →ₙ+* B)

end FiniteAlgebraicEnvelopes.NonunitalTensor
end

namespace FiniteAlgebraicEnvelopes.MatrixModule
variable {R V W : Type*} [Ring R] [AddCommGroup V] [AddCommGroup W] [Module R V] [Module R W]

def columnEquiv (e : V ≃ₗ[R] W) : Multiplicative (Fin 6 → V) ≃* Multiplicative (Fin 6 → W) :=
  AddEquiv.toMultiplicative (LinearEquiv.piCongrRight (fun _ : Fin 6 => e)).toAddEquiv

end FiniteAlgebraicEnvelopes.MatrixModule

namespace FiniteAlgebraicEnvelopes.LimitAction
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

/-- The stage shift intertwines the actual linear limit actions. -/
theorem action_shift (x : Limit f) (v : Limit g) :
    action α f g hc (shift f x) (shift g v)=shift g (action α f g hc x v) := by
  obtain ⟨i,x,v,rfl,rfl⟩ := exists_common_stage₂ f g x v
  rw [shift_apply_of,shift_apply_of,action_of,action_of,shift_apply_of]

theorem action_shift_inv (x : Limit f) (v : Limit g) :
    action α f g hc ((shift f)⁻¹ x) ((shift g)⁻¹ v)=(shift g)⁻¹ (action α f g hc x v) := by
  apply (shift g).injective
  simpa using (action_shift α f g hc ((shift f)⁻¹ x) ((shift g)⁻¹ v)).symm

theorem action_shift_zpow (n : ℤ) (x : Limit f) (v : Limit g) :
    action α f g hc (((shift f)^n) x) (((shift g)^n) v)=((shift g)^n) (action α f g hc x v) := by
  induction n using Int.induction_on generalizing x v with
  | zero => simp
  | succ n ih =>
    rw [zpow_add,zpow_add,zpow_one,zpow_one]
    change action α f g hc (((shift f)^(n:ℤ)) (shift f x)) (((shift g)^(n:ℤ)) (shift g v)) = _
    rw [ih,action_shift]
    rfl
  | pred n ih =>
    rw [sub_eq_add_neg,zpow_add,zpow_add,zpow_neg_one,zpow_neg_one]
    change action α f g hc (((shift f)^(-(n:ℤ))) ((shift f)⁻¹ x)) (((shift g)^(-(n:ℤ))) ((shift g)⁻¹ v)) = _
    rw [ih,action_shift_inv]
    rfl

def torusAction : Torus f →* MulAut (Limit g) :=
  SemidirectProduct.lift (action α f g hc) (SequentialLimit.action g) (by
    intro n
    ext x v
    have he := action_shift_zpow α f g hc n.toAdd x (((shift g)^n.toAdd)⁻¹ v)
    change action α f g hc (((shift f)^n.toAdd) x) v=
      ((shift g)^n.toAdd) (action α f g hc x (((shift g)^n.toAdd)⁻¹ v))
    simpa only [MulAut.apply_inv_self] using he)

@[simp] theorem torusAction_apply (a : Torus f) (v : Limit g) :
    torusAction α f g hc a v=action α f g hc a.left (((shift g)^a.right.toAdd) v) := rfl

@[simp] theorem torusAction_inl (x : Limit f) :
    torusAction α f g hc (SemidirectProduct.inl x)=action α f g hc x := by
  simp [torusAction]

@[simp] theorem shift_pow_of (i n : ℕ) (v : V) :
    ((shift g)^n) (of g i v)=of g (i+n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change shift g (((shift g)^n) (of g i v))=of g (i+(n+1)) v
    rw [ih,shift_apply_of]
    rfl

def affineStep : Monoid.End (V ⋊[α] Q) :=
  SemidirectProduct.map g f (by intro x; ext v; exact hc x v)

@[simp] theorem affineStep_left (a : V ⋊[α] Q) : (affineStep α f g hc a).left=g a.left := rfl
@[simp] theorem affineStep_right (a : V ⋊[α] Q) : (affineStep α f g hc a).right=f a.right := rfl

@[simp] theorem affineStep_pow_left (n : ℕ) (a : V ⋊[α] Q) :
    (((affineStep α f g hc)^n) a).left=(g^n) a.left := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change g ((((affineStep α f g hc)^n) a).left)=g ((g^n) a.left)
    rw [ih]

@[simp] theorem affineStep_pow_right (n : ℕ) (a : V ⋊[α] Q) :
    (((affineStep α f g hc)^n) a).right=(f^n) a.right := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change f ((((affineStep α f g hc)^n) a).right)=f ((f^n) a.right)
    rw [ih]

abbrev AffineLimit := (Limit g) ⋊[action α f g hc] Limit f

def affineStage (i : ℕ) : (V ⋊[α] Q) →* AffineLimit α f g hc :=
  SemidirectProduct.map (of g i) (of f i) (by intro x; ext v; exact (action_of α f g hc i x v).symm)

def affineLimitMap : Limit (affineStep α f g hc) →* AffineLimit α f g hc :=
  lift (affineStep α f g hc) (affineStage α f g hc)
    (compatible_of_succ _ _ (by intro i a; ext <;> exact of_succ _ i _))

@[simp] theorem affineLimitMap_of (i : ℕ) (a : V ⋊[α] Q) :
    affineLimitMap α f g hc (of (affineStep α f g hc) i a)=affineStage α f g hc i a := rfl

theorem pow_map_one_later {W : Type*} [Group W] (p : Monoid.End W)
    (i j m : ℕ) (hij : i ≤ j) (hjm : j ≤ m) (x : W) (hx : (p^(j-i)) x=1) :
    (p^(m-i)) x=1 := by
  rw [show m-i=(m-j)+(j-i) by omega,pow_add]
  change (p^(m-j)) ((p^(j-i)) x)=1
  rw [hx,map_one]

theorem affineLimitMap_injective : Function.Injective (affineLimitMap α f g hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  obtain ⟨i,a,rfl⟩ := DirectLimit.exists_eq_mk (transition (affineStep α f g hc)) x
  change affineStage α f g hc i a=1 at hx
  have hv : of g i a.left=1 := congrArg SemidirectProduct.left hx
  have hq : of f i a.right=1 := congrArg SemidirectProduct.right hx
  obtain ⟨j,hij,hj⟩ := (DirectLimit.exists_eq_one (G:=fun _ : ℕ => V) (f:=transition g) ⟨i,a.left⟩).mp hv
  obtain ⟨k,hik,hk⟩ := (DirectLimit.exists_eq_one (G:=fun _ : ℕ => Q) (f:=transition f) ⟨i,a.right⟩).mp hq
  apply (DirectLimit.exists_eq_one (G:=fun _ : ℕ => V ⋊[α] Q) (f:=transition (affineStep α f g hc)) ⟨i,a⟩).mpr
  refine ⟨max j k,le_trans hij (le_max_left _ _),?_⟩
  apply SemidirectProduct.ext
  · exact (affineStep_pow_left α f g hc (max j k-i) a).trans
      (pow_map_one_later g i j (max j k) hij (le_max_left _ _) a.left hj)
  · exact (affineStep_pow_right α f g hc (max j k-i) a).trans
      (pow_map_one_later f i k (max j k) hik (le_max_right _ _) a.right hk)

theorem affineLimitMap_surjective : Function.Surjective (affineLimitMap α f g hc) := by
  intro a
  obtain ⟨i,v,q,hv,hq⟩ := exists_common_stage₂ g f a.left a.right
  refine ⟨of (affineStep α f g hc) i ⟨v,q⟩,?_⟩
  exact SemidirectProduct.ext hv.symm hq.symm

def affineLimitEquivalence : Limit (affineStep α f g hc) ≃* AffineLimit α f g hc :=
  MulEquiv.ofBijective (affineLimitMap α f g hc) ⟨affineLimitMap_injective α f g hc,affineLimitMap_surjective α f g hc⟩

end FiniteAlgebraicEnvelopes.LimitAction

end

end OAI
end

section
-- module Solutions.OAIFAE.GroupInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-!
Wreath-product reduction to countably infinite finitely generated decidable input groups.
-/


namespace FiniteAlgebraicEnvelopes
universe u
namespace GroupInput
variable (G : Type u) [Group G]

def shift (z : Multiplicative ℤ) : MulAut (ℤ → G) where
  toFun f i := f (i - z.toAdd)
  invFun f i := f (i + z.toAdd)
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
  map_mul' _ _ := rfl

def shifts : Multiplicative ℤ →* MulAut (ℤ → G) where
  toFun := shift G
  map_one' := by ext f i; simp [shift]
  map_mul' z w := by ext f i; simp [shift, sub_sub]

abbrev Ambient := SemidirectProduct (ℤ → G) (Multiplicative ℤ) (shifts G)

def base : G × G →* (ℤ → G) where
  toFun ab i := if i < 0 then 1 else if i = 0 then ab.1 else ab.2
  map_one' := by ext i; split <;> simp_all
  map_mul' a b := by ext i; split <;> simp_all

def embed : G × G →* Ambient G := SemidirectProduct.inl.comp (base G)
def stable : Ambient G := SemidirectProduct.inr (Multiplicative.ofAdd 1)

abbrev Letters (n : ℕ) := Option (Fin n × Bool)
abbrev InputWord (n : ℕ) := List (Letters n × Bool)

def generators {n} (s : Fin n → G) : Letters n → Ambient G
  | none => stable G
  | some (i, false) => embed G (s i,1)
  | some (i, true) => embed G (1,s i)

def heightLetter {n} : Letters n × Bool → ℤ
  | (none, true) => 1
  | (none, false) => -1
  | (some _, _) => 0

def atLetter {n} (a : Letters n × Bool) (i : ℤ) : Word n :=
  match a.1 with
  | none => []
  | some (j, b) => if (b = false ∧ i = 0) ∨ (b = true ∧ 0 < i) then [(j,a.2)] else []

def height {n} (w : InputWord n) : ℤ := (w.map heightLetter).sum

def sectionWord {n} (i : ℤ) : InputWord n → Word n
  | [] => []
  | a :: w => atLetter a i ++ sectionWord (i - heightLetter a) w

def value {n} (s : Fin n → G) (w : InputWord n) : Ambient G :=
  (w.map fun a => if a.2 then generators G s a.1 else (generators G s a.1)⁻¹).prod

@[simp] theorem height_nil {n} : height ([] : InputWord n) = 0 := rfl
@[simp] theorem height_cons {n} (a) (w : InputWord n) :
    height (a::w) = heightLetter a + height w := rfl

@[simp] theorem heightLetter_bounds {n} (a : Letters n × Bool) :
    -1 ≤ heightLetter a ∧ heightLetter a ≤ 1 := by
  rcases a with ⟨_ | ⟨j,b⟩, t⟩ <;> cases t <;> simp [heightLetter]

@[simp] theorem value_nil {n} (s : Fin n → G) : value G s [] = 1 := rfl
@[simp] theorem value_cons {n} (s : Fin n → G) (a : Letters n × Bool) (w) :
    value G s (a::w) = (if a.2 then generators G s a.1 else (generators G s a.1)⁻¹) *
      value G s w := rfl

/-- Unsimplified positive/negative counters avoid assuming a computation model on `G`. -/
def countsLetter {n} : Letters n × Bool → ℕ × ℕ
  | (none, true) => (1,0)
  | (none, false) => (0,1)
  | (some _, _) => (0,0)

def counts {n} (w : InputWord n) : ℕ × ℕ :=
  w.foldl (fun c a => (c.1 + (countsLetter a).1, c.2 + (countsLetter a).2)) (0,0)

def natAtLetter {n} (a : Letters n × Bool) (pq : ℕ × ℕ) : Word n :=
  match a.1 with
  | none => []
  | some (j,b) => if (b = false ∧ pq.1 = pq.2) ∨ (b = true ∧ pq.2 < pq.1)
      then [(j,a.2)] else []

def natStep {n} (v : (ℕ × ℕ) × Word n) (a : Letters n × Bool) : (ℕ × ℕ) × Word n :=
  ((v.1.1 + (countsLetter a).2, v.1.2 + (countsLetter a).1),
    v.2 ++ natAtLetter a v.1)

def natAt {n} (w : InputWord n) (pq : ℕ × ℕ) : Word n :=
  (w.foldl natStep (pq,[])).2

open Primrec

/-- The finitely generated subgroup, rather than the whole unrestricted wreath product. -/
def generated {n} (s : Fin n → G) : Subgroup (Ambient G) :=
  Subgroup.closure (Set.range (generators G s))

def subgroupGenerators {n} (s : Fin n → G) : Letters n → generated G s :=
  fun a => ⟨generators G s a, Subgroup.subset_closure ⟨a,rfl⟩⟩

end GroupInput


end FiniteAlgebraicEnvelopes

end OAI
end

section
-- module Solutions.OAIFAE.SteinbergPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite free-algebra Steinberg presentations and transport to finitely presented algebras.
-/

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree

section
open scoped commutatorElement
variable {Q : Type*} [Group Q]

theorem commute_commutator {a b c : Q} (hab : Commute a b) (hac : Commute a c) :
    Commute a ⁅b,c⁆ := by
  exact ((hab.mul_right hac).mul_right hab.inv_right).mul_right hac.inv_right

/-- The rank-four commutator calculus needed for the finite free-algebra presentation. -/
theorem associate_commutator (a b c : Q) (hac : Commute a c)
    (hde : Commute ⁅a,b⁆ ⁅b,c⁆) (hec : Commute ⁅b,c⁆ c) :
    ⁅⁅a,b⁆,c⁆=⁅a,⁅b,c⁆⁆ := by
  have h := commutatorElement_commutatorElement_conj_mul a b c
  have hca : c*a*c⁻¹=a := by rw [←hac.eq]; simp [mul_assoc]
  have hbc : b*c*b⁻¹=⁅b,c⁆*c := by simp [commutatorElement_def,mul_assoc]
  rw [hac.symm.commutator_eq,hca,hbc,commutatorElement_one_left,mul_one,
    commutatorElement_mul_right_eq_mul_conj,hde.commutator_eq,one_mul] at h
  have he : Commute ⁅b,c⁆ ⁅⁅a,b⁆,c⁆ := commute_commutator hde.symm hec
  rw [he.eq] at h
  simp only [mul_assoc,mul_inv_cancel,mul_one] at h
  have hh := mul_eq_one_iff_eq_inv.mp h
  simpa only [commutatorElement_inv] using hh

/-- A central commutator of an involution is itself an involution. -/
theorem commutator_square (a b : Q) (ha : a*a=1) (hc : Commute a ⁅a,b⁆) :
    ⁅a,b⁆*⁅a,b⁆=1 := by
  have h := commutatorElement_mul_left_eq_conj_mul a a b
  rw [ha,commutatorElement_one_left,hc.eq] at h
  simpa only [mul_assoc,mul_inv_cancel,one_mul,mul_one] using h.symm

end

open scoped commutatorElement
variable {A Q : Type*} [Group Q]

structure SmallSystem (A Q : Type*) [Group Q] where
  small : Fin 6 → Fin 6 → Option A → Q
  diagonal : ∀ i a, small i i a=1
  square : ∀ i j a, small i j a*small i j a=1
  distant : ∀ i j k l a b, i≠l → j≠k → Commute (small i j a) (small k l b)
  unit_left : ∀ i j k a, i≠j → j≠k → i≠k → ⁅small i j none,small j k a⁆=small i k a
  unit_right : ∀ i j k a, i≠j → j≠k → i≠k → ⁅small i j a,small j k none⁆=small i k a

lemma freshIndex (s : Finset (Fin 6)) (hs : s.card<6) : ∃ i : Fin 6, i∉s := by
  have h := Finset.exists_mem_notMem_of_card_lt_card (s:=s) (t:=Finset.univ)
    (by simpa using hs)
  simpa using h

lemma fresh5 (a b c d e : Fin 6) : ∃ i : Fin 6, i≠a ∧ i≠b ∧ i≠c ∧ i≠d ∧ i≠e := by
  have hc : ({a,b,c,d,e} : Finset (Fin 6)).card≤5 := by
    have h1 := Finset.card_insert_le a ({b,c,d,e} : Finset (Fin 6))
    have h2 := Finset.card_insert_le b ({c,d,e} : Finset (Fin 6))
    have h3 := Finset.card_insert_le c ({d,e} : Finset (Fin 6))
    have h4 := Finset.card_insert_le d ({e} : Finset (Fin 6))
    simp only [Finset.card_singleton] at h4
    omega
  simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using
    freshIndex {a,b,c,d,e} (by omega)

def middle (i j : Fin 6) : Fin 6 := (fresh5 i j j j j).choose
lemma middle_ne_left (i j : Fin 6) : middle i j≠i := (fresh5 i j j j j).choose_spec.1
lemma middle_ne_right (i j : Fin 6) : middle i j≠j := (fresh5 i j j j j).choose_spec.2.1

namespace SmallSystem
variable (S : SmallSystem A Q)

def word : List A → Fin 6 → Fin 6 → Q
  | [],i,j => S.small i j none
  | [a],i,j => S.small i j (some a)
  | a::b::w,i,j => if i=j then 1 else ⁅S.small i (middle i j) (some a),word (b::w) (middle i j) j⁆

@[simp] lemma word_nil (i j : Fin 6) : S.word [] i j=S.small i j none := rfl
@[simp] lemma word_singleton (a : A) (i j : Fin 6) : S.word [a] i j=S.small i j (some a) := rfl
@[simp] lemma word_diagonal (w : List A) (i : Fin 6) : S.word w i i=1 := by
  cases w with
  | nil => exact S.diagonal i none
  | cons a w => cases w <;> simp [word,S.diagonal]

lemma word_cons {w : List A} (hw : w≠[]) (a : A) (i j : Fin 6) (hij : i≠j) :
    S.word (a::w) i j=⁅S.small i (middle i j) (some a),S.word w (middle i j) j⁆ := by
  cases w with
  | nil => contradiction
  | cons b w => simp [word,hij]

/-- Finite-length invariants for the simultaneous noncommutative-root induction.
The distant invariant bounds the maximum, not the sum, of the two word lengths. -/
structure Valid (n : ℕ) : Prop where
  factor : ∀ (a : A) (w : List A), w≠[] → (a::w).length≤n →
    ∀ i k j : Fin 6, i≠k → k≠j → i≠j → S.word (a::w) i j=⁅S.small i k (some a),S.word w k j⁆
  distant : ∀ (w v : List A), w.length≤n → v.length≤n →
    ∀ i j k l : Fin 6, i≠l → j≠k → Commute (S.word w i j) (S.word v k l)
  chain : ∀ (w v : List A), w.length+v.length≤n →
    ∀ i j k : Fin 6, i≠j → j≠k → i≠k → ⁅S.word w i j,S.word v j k⁆=S.word (w++v) i k
  square : ∀ (w : List A), w.length≤n → ∀ i j : Fin 6, S.word w i j*S.word w i j=1

lemma valid_zero : S.Valid 0 := by
  constructor
  · intro a w hw hn; simp at hn
  · intro w v hw hv
    have : w=[] := List.length_eq_zero_iff.mp (by omega)
    have : v=[] := List.length_eq_zero_iff.mp (by omega)
    subst w; subst v
    exact fun i j k l h1 h2 => S.distant i j k l none none h1 h2
  · intro w v hw
    have : w=[] := List.length_eq_zero_iff.mp (by omega)
    have : v=[] := List.length_eq_zero_iff.mp (by omega)
    subst w; subst v
    exact fun i j k hij hjk hik => S.unit_left i j k none hij hjk hik
  · intro w hw
    have : w=[] := List.length_eq_zero_iff.mp (by omega)
    subst w
    exact fun i j => S.square i j none

lemma factor_step {n : ℕ} (H : S.Valid n) (a : A) (w : List A) (hw : w≠[])
    (hn : (a::w).length≤n+1) (i k j : Fin 6) (hik : i≠k) (hkj : k≠j) (hij : i≠j) :
    S.word (a::w) i j=⁅S.small i k (some a),S.word w k j⁆ := by
  have hwlen : w.length≤n := by simpa using hn
  have h1 : 1≤n := by have := List.length_pos_iff.mpr hw; omega
  let p := middle i j
  have hpi : p≠i := middle_ne_left i j
  have hpj : p≠j := middle_ne_right i j
  rw [S.word_cons hw a i j hij]
  by_cases hpk : p=k
  · subst k; rfl
  have hleft := S.unit_right i k p (some a) hik (Ne.symm hpk) hpi.symm
  have hright := H.chain [] w (by simpa using hwlen) k p j (Ne.symm hpk) hpj hkj
  simp only [word_nil,List.nil_append] at hright
  have hac : Commute (S.small i k (some a)) (S.word w p j) :=
    H.distant [a] w (by simpa using h1) hwlen i k p j hij (Ne.symm hpk)
  have hd : Commute (S.small i p (some a)) (S.word w k j) :=
    H.distant [a] w (by simpa using h1) hwlen i p k j hij hpk
  have hc : Commute (S.word w k j) (S.word w p j) :=
    H.distant w w hwlen hwlen k j p j hkj hpj.symm
  have hh := associate_commutator (S.small i k (some a)) (S.small k p none) (S.word w p j) hac
    (by rw [hleft,hright]; exact hd) (by rw [hright]; exact hc)
  rw [hleft,hright] at hh
  exact hh

end SmallSystem
end FiniteAlgebraicEnvelopes.SteinbergFiniteFree

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree.SmallSystem

section
open scoped commutatorElement
variable {A Q : Type*} [Group Q] (S : SmallSystem A Q)

lemma short_word (w : List A) (hw : w.length≤1) : ∃ a : Option A, w=a.toList := by
  cases w with
  | nil => exact ⟨none,rfl⟩
  | cons a w =>
    have : w=[] := List.length_eq_zero_iff.mp (by simpa using hw)
    subst w
    exact ⟨some a,rfl⟩

@[simp] lemma word_option (a : Option A) (i j : Fin 6) : S.word a.toList i j=S.small i j a := by
  cases a <;> rfl

lemma valid_one : S.Valid 1 := by
  constructor
  · intro a w hw hn
    have hp := List.length_pos_iff.mpr hw
    simp only [List.length_cons] at hn
    omega
  · intro w v hw hv
    obtain ⟨a,rfl⟩ := short_word w hw
    obtain ⟨b,rfl⟩ := short_word v hv
    simpa only [word_option] using fun i j k l h1 h2 => S.distant i j k l a b h1 h2
  · intro w v hw
    obtain ⟨a,rfl⟩ := short_word w (by omega)
    obtain ⟨b,rfl⟩ := short_word v (by omega)
    cases a with
    | none => simpa using S.unit_left (a:=b)
    | some a =>
      cases b with
      | none => simpa using S.unit_right (a:=some a)
      | some b => simp at hw
  · intro w hw
    obtain ⟨a,rfl⟩ := short_word w hw
    simpa using fun i j => S.square i j a

lemma distant_step_short {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w v : List A) (hw : w.length≤n+1) (hv : v.length≤n)
    (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.word w i j) (S.word v k l) := by
  by_cases hij : i=j
  · subst j; rw [word_diagonal]; exact Commute.one_left _
  cases w with
  | nil => exact H.distant [] v (by simp) hv i j k l hil hjk
  | cons a w =>
    cases w with
    | nil => exact H.distant [a] v (by simpa using hn) hv i j k l hil hjk
    | cons b w =>
      obtain ⟨p,hpi,hpj,hpk,hpl,_⟩ := fresh5 i j k l l
      rw [S.factor_step H a (b::w) (by simp) hw i p j hpi.symm hpj hij]
      exact (commute_commutator
        (H.distant [a] v (by simpa using hn) hv i p k l hil hpk).symm
        (H.distant (b::w) v (by simpa using hw) hv p j k l hpl hjk).symm).symm

lemma distant_step {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w v : List A) (hw : w.length≤n+1) (hv : v.length≤n+1)
    (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.word w i j) (S.word v k l) := by
  by_cases hvo : v.length≤n
  · exact S.distant_step_short hn H w v hw hvo i j k l hil hjk
  by_cases hwo : w.length≤n
  · exact (S.distant_step_short hn H v w hv hwo k l i j hjk.symm hil.symm).symm
  by_cases hij : i=j
  · subst j; rw [word_diagonal]; exact Commute.one_left _
  by_cases hkl : k=l
  · subst l; rw [word_diagonal]; exact Commute.one_right _
  cases w with
  | nil => simp at hwo
  | cons a w =>
    cases w with
    | nil => simp at hwo; omega
    | cons b w =>
      cases v with
      | nil => simp at hvo
      | cons c v =>
        cases v with
        | nil => simp at hvo; omega
        | cons d v =>
          obtain ⟨p,hpi,hpj,hpk,hpl,_⟩ := fresh5 i j k l l
          obtain ⟨q,hqi,hqj,hqk,hql,hqp⟩ := fresh5 i j k l p
          rw [S.factor_step H a (b::w) (by simp) hw i p j hpi.symm hpj hij,
            S.factor_step H c (d::v) (by simp) hv k q l hqk.symm hql hkl]
          have h1 := H.distant [a] [c] (by simpa using hn) (by simpa using hn) i p k q hqi.symm hpk
          have h2 := H.distant [a] (d::v) (by simpa using hn) (by simpa using hv) i p q l hil hqp.symm
          have h3 := H.distant (b::w) [c] (by simpa using hw) (by simpa using hn) p j k q hqp.symm hjk
          have h4 := H.distant (b::w) (d::v) (by simpa using hw) (by simpa using hv) p j q l hpl hqj.symm
          exact (commute_commutator (commute_commutator h1 h2).symm
            (commute_commutator h3 h4).symm).symm

lemma chain_step {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w v : List A) (hw : w.length+v.length≤n+1)
    (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅S.word w i j,S.word v j k⁆=S.word (w++v) i k := by
  have hw' : w.length≤n+1 := by omega
  have hv' : v.length≤n+1 := by omega
  cases w with
  | nil =>
    cases v with
    | nil => exact S.unit_left i j k none hij hjk hik
    | cons a v =>
      cases v with
      | nil => exact S.unit_left i j k (some a) hij hjk hik
      | cons b v =>
        obtain ⟨p,hpi,hpj,hpk,_,_⟩ := fresh5 i j k k k
        have hfac := S.factor_step H a (b::v) (by simp) hv' j p k hpj.symm hpk hjk
        have hleft := S.unit_left i j p (some a) hij hpj.symm hpi.symm
        have hfac' := S.factor_step H a (b::v) (by simp) hv' i p k hpi.symm hpk hik
        have hac : Commute (S.word [] i j) (S.word (b::v) p k) :=
          S.distant_step hn H [] (b::v) (by simp) (by simp only [List.length_cons, List.length_nil] at *; omega) i j p k hik hpj.symm
        have hd : Commute (S.word [a] i p) (S.word (a::b::v) j k) :=
          S.distant_step hn H [a] (a::b::v) (by simp only [List.length_cons, List.length_nil]; omega) hv' i p j k hik hpj
        have hc : Commute (S.word (a::b::v) j k) (S.word (b::v) p k) :=
          S.distant_step hn H (a::b::v) (b::v) hv' (by simp only [List.length_cons, List.length_nil] at *; omega) j k p k hjk hpk.symm
        have hh := associate_commutator (S.small i j none) (S.small j p (some a))
          (S.word (b::v) p k) hac (by rw [hleft,←hfac]; exact hd)
          (by rw [←hfac]; exact hc)
        rw [hleft,←hfac,←hfac'] at hh
        exact hh.symm
  | cons a w =>
    cases w with
    | nil =>
      cases v with
      | nil => exact S.unit_right i j k (some a) hij hjk hik
      | cons b v =>
        simpa using (S.factor_step H a (b::v) (by simp) (by simp only [List.length_cons, List.length_nil] at *; omega) i j k hij hjk hik).symm
    | cons b w =>
      obtain ⟨p,hpi,hpj,hpk,_,_⟩ := fresh5 i j k k k
      have hfac := S.factor_step H a (b::w) (by simp) hw' i p j hpi.symm hpj hij
      have hsum : (b::w).length+v.length≤n := by simp only [List.length_cons] at *; omega
      have hright := H.chain (b::w) v hsum p j k hpj hjk hpk
      have hfac' := S.factor_step H a ((b::w)++v) (by simp) (by simp only [List.length_cons, List.length_append] at *; omega) i p k hpi.symm hpk hik
      have hac : Commute (S.word [a] i p) (S.word v j k) :=
        S.distant_step hn H [a] v (by simp only [List.length_cons, List.length_nil]; omega) hv' i p j k hik hpj
      have hd : Commute (S.word (a::b::w) i j) (S.word ((b::w)++v) p k) :=
        S.distant_step hn H (a::b::w) ((b::w)++v) hw' (by simp only [List.length_cons, List.length_append] at *; omega) i j p k hik hpj.symm
      have hc : Commute (S.word ((b::w)++v) p k) (S.word v j k) :=
        S.distant_step hn H ((b::w)++v) v (by simp only [List.length_cons, List.length_append] at *; omega) hv' p k j k hpk hjk.symm
      have hh := associate_commutator (S.small i p (some a)) (S.word (b::w) p j) (S.word v j k)
        hac (by rw [←hfac,hright]; exact hd) (by rw [hright]; exact hc)
      rw [←hfac,hright,←hfac'] at hh
      exact hh

lemma square_step {n : ℕ} (hn : 1≤n) (H : S.Valid n)
    (w : List A) (hw : w.length≤n+1) (i j : Fin 6) : S.word w i j*S.word w i j=1 := by
  by_cases hij : i=j
  · subst j; simp
  cases w with
  | nil => exact S.square i j none
  | cons a w =>
    cases w with
    | nil => exact S.square i j (some a)
    | cons b w =>
      let p := middle i j
      have hpi : p≠i := middle_ne_left i j
      have hpj : p≠j := middle_ne_right i j
      have hf := S.factor_step H a (b::w) (by simp) hw i p j hpi.symm hpj hij
      rw [hf]
      exact commutator_square _ _ (S.square i p (some a)) (by
        rw [←hf]
        exact S.distant_step hn H [a] (a::b::w) (by simp only [List.length_cons, List.length_nil]; omega) hw i p i j hij hpi)

lemma valid_succ {n : ℕ} (hn : 1≤n) (H : S.Valid n) : S.Valid (n+1) where
  factor := S.factor_step H
  distant := S.distant_step hn H
  chain := S.chain_step hn H
  square := S.square_step hn H

lemma valid (n : ℕ) : S.Valid n := by
  induction n with
  | zero => exact S.valid_zero
  | succ n ih =>
    by_cases hn : n=0
    · subst n; exact S.valid_one
    · exact S.valid_succ (by omega) ih

lemma word_distant (w v : List A) (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.word w i j) (S.word v k l) :=
  (S.valid (w.length+v.length)).distant w v (by omega) (by omega) i j k l hil hjk

lemma word_chain (w v : List A) (i j k : Fin 6) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅S.word w i j,S.word v j k⁆=S.word (w++v) i k :=
  (S.valid (w.length+v.length)).chain w v (by omega) i j k hij hjk hik

lemma word_square (w : List A) (i j : Fin 6) : S.word w i j*S.word w i j=1 :=
  (S.valid w.length).square w (by omega) i j

end

open scoped commutatorElement IsMulCommutative
variable {A Q : Type*} [Group Q] (S : SmallSystem A Q)

abbrev Polynomial (A : Type*) := MonoidAlgebra (ZMod 2) (FreeMonoid A)

def rootSubgroup (i j : Fin 6) : Subgroup Q := Subgroup.closure (Set.range fun w => S.word w i j)
instance root_commutative (i j : Fin 6) : IsMulCommutative (S.rootSubgroup i j) := by
  apply Subgroup.isMulCommutative_closure
  rintro _ ⟨w,rfl⟩ _ ⟨v,rfl⟩
  by_cases hij : i=j
  · subst j; simp
  · exact (S.word_distant w v i j i j hij (Ne.symm hij)).eq

def wordInRoot (w : List A) (i j : Fin 6) : S.rootSubgroup i j :=
  ⟨S.word w i j,Subgroup.subset_closure ⟨w,rfl⟩⟩

lemma scalar_cases (c : ZMod 2) : c=0 ∨ c=1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

def wordScalar (w : List A) (i j : Fin 6) : ZMod 2 →+ Additive (S.rootSubgroup i j) where
  toFun c := if c=0 then 0 else Additive.ofMul (S.wordInRoot w i j)
  map_zero' := by simp
  map_add' c d := by
    rcases scalar_cases c with rfl|rfl <;> rcases scalar_cases d with rfl|rfl <;>
      simp only [zero_add,add_zero,ite_true,one_ne_zero,ite_false,show (1 : ZMod 2)+1=0 from by decide]
    change (1 : S.rootSubgroup i j)=S.wordInRoot w i j*S.wordInRoot w i j
    apply Subtype.ext
    exact (S.word_square w i j).symm

def polynomialAdd (i j : Fin 6) : Polynomial A →+ Additive (S.rootSubgroup i j) :=
  (Finsupp.liftAddHom fun w : FreeMonoid A => S.wordScalar w.toList i j).comp
    (MonoidAlgebra.coeffAddEquiv (R:=ZMod 2) (M:=FreeMonoid A)).toAddMonoidHom

def polynomial (p : Polynomial A) (i j : Fin 6) : Q :=
  (Additive.toMul (S.polynomialAdd i j p)).val

@[simp] lemma polynomial_zero (i j : Fin 6) : S.polynomial 0 i j=1 := by
  simp [polynomial]

lemma polynomial_add (p q : Polynomial A) (i j : Fin 6) :
    S.polynomial (p+q) i j=S.polynomial p i j*S.polynomial q i j := by
  simp [polynomial]

@[simp] lemma polynomial_single (w : FreeMonoid A) (i j : Fin 6) :
    S.polynomial (MonoidAlgebra.single w 1) i j=S.word w.toList i j := by
  simp [polynomial,polynomialAdd,Finsupp.liftAddHom,wordScalar,wordInRoot]

lemma polynomial_induction (P : Polynomial A → Prop) (h0 : P 0)
    (hword : ∀ w : FreeMonoid A, P (MonoidAlgebra.single w 1))
    (hadd : ∀ p q, P p → P q → P (p+q)) (p : Polynomial A) : P p := by
  apply MonoidAlgebra.induction_on p hword hadd
  intro c p hp
  rcases scalar_cases c with rfl|rfl
  · simpa using h0
  · simpa using hp

lemma polynomial_distant (p q : Polynomial A) (i j k l : Fin 6) (hil : i≠l) (hjk : j≠k) :
    Commute (S.polynomial p i j) (S.polynomial q k l) := by
  apply polynomial_induction (fun p => Commute (S.polynomial p i j) (S.polynomial q k l))
  · simp
  · intro w
    apply polynomial_induction (fun q => Commute (S.polynomial (MonoidAlgebra.single w 1) i j) (S.polynomial q k l))
    · simp
    · intro v; simp only [polynomial_single]; exact S.word_distant _ _ _ _ _ _ hil hjk
    · intro p q hp hq; rw [polynomial_add]; exact hp.mul_right hq
  · intro p q hp hq; rw [polynomial_add]; exact hp.mul_left hq

lemma polynomial_chain_add_left (p q r : Polynomial A) (i j k : Fin 6)
    (hij : i≠j) (hik : i≠k)
    (hp : ⁅S.polynomial p i j,S.polynomial r j k⁆=S.polynomial (p*r) i k)
    (hq : ⁅S.polynomial q i j,S.polynomial r j k⁆=S.polynomial (q*r) i k) :
    ⁅S.polynomial (p+q) i j,S.polynomial r j k⁆=S.polynomial ((p+q)*r) i k := by
  rw [polynomial_add,commutatorElement_mul_left_eq_conj_mul,hp,hq]
  rw [(S.polynomial_distant p (q*r) i j i k hik (Ne.symm hij)).eq]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  rw [add_mul,polynomial_add]
  exact (S.polynomial_distant (q*r) (p*r) i k i k hik (Ne.symm hik)).eq

lemma polynomial_chain_add_right (p q r : Polynomial A) (i j k : Fin 6)
    (hjk : j≠k) (hik : i≠k)
    (hq : ⁅S.polynomial p i j,S.polynomial q j k⁆=S.polynomial (p*q) i k)
    (hr : ⁅S.polynomial p i j,S.polynomial r j k⁆=S.polynomial (p*r) i k) :
    ⁅S.polynomial p i j,S.polynomial (q+r) j k⁆=S.polynomial (p*(q+r)) i k := by
  rw [polynomial_add,commutatorElement_mul_right_eq_mul_conj,hq,hr]
  rw [mul_assoc (S.polynomial (p*q) i k)]
  rw [(S.polynomial_distant q (p*r) j k i k hjk (Ne.symm hik)).eq]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  rw [mul_add,polynomial_add]

lemma polynomial_chain (p q : Polynomial A) (i j k : Fin 6)
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅S.polynomial p i j,S.polynomial q j k⁆=S.polynomial (p*q) i k := by
  apply polynomial_induction (fun p => ⁅S.polynomial p i j,S.polynomial q j k⁆=S.polynomial (p*q) i k)
  · simp
  · intro w
    apply polynomial_induction (fun q => ⁅S.polynomial (MonoidAlgebra.single w 1) i j,S.polynomial q j k⁆=
      S.polynomial (MonoidAlgebra.single w 1*q) i k)
    · simp
    · intro v
      simp only [MonoidAlgebra.single_mul_single,one_mul,polynomial_single,FreeMonoid.toList_mul]
      exact S.word_chain _ _ _ _ _ hij hjk hik
    · intro p q hp hq
      exact S.polynomial_chain_add_right _ _ _ i j k hjk hik hp hq
  · intro p q hp hq
    exact S.polynomial_chain_add_left _ _ _ i j k hij hik hp hq

end FiniteAlgebraicEnvelopes.SteinbergFiniteFree.SmallSystem

namespace FiniteAlgebraicEnvelopes.SteinbergFiniteFree

section
open scoped commutatorElement
variable (A : Type*)
abbrev SmallGenerator := (Fin 6 × Fin 6) × Option A

def freeSmall (i j : Fin 6) (a : Option A) : FreeGroup (SmallGenerator A) := FreeGroup.of ((i,j),a)

def smallRelator (d : Fin 5) (i j k l : Fin 6) (a b : Option A) : FreeGroup (SmallGenerator A) :=
  if d=0 then freeSmall A i i a else
  if d=1 then freeSmall A i j a*freeSmall A i j a else
  if d=2 then if i≠l ∧ j≠k then ⁅freeSmall A i j a,freeSmall A k l b⁆ else 1 else
  if d=3 then if i≠j ∧ j≠k ∧ i≠k then
    ⁅freeSmall A i j none,freeSmall A j k a⁆*(freeSmall A i k a)⁻¹ else 1 else
  if i≠j ∧ j≠k ∧ i≠k then
    ⁅freeSmall A i j a,freeSmall A j k none⁆*(freeSmall A i k a)⁻¹ else 1

def smallRelations : Set (FreeGroup (SmallGenerator A)) :=
  Set.range fun z : Fin 5 × Fin 6 × Fin 6 × Fin 6 × Fin 6 × Option A × Option A =>
    smallRelator A z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2.1 z.2.2.2.2.2.2

abbrev Presentation := PresentedGroup (smallRelations A)
instance instIsFinitelyPresentedPresentationOfFinite [Finite A] : Group.IsFinitelyPresented (Presentation A) := by
  have : Finite (smallRelations A) := (Set.finite_range _).to_subtype
  infer_instance

def presentSmall (i j : Fin 6) (a : Option A) : Presentation A := PresentedGroup.of ((i,j),a)
lemma present_relator (d : Fin 5) (i j k l : Fin 6) (a b : Option A) :
    PresentedGroup.mk (smallRelations A) (smallRelator A d i j k l a b)=1 :=
  PresentedGroup.one_of_mem (rels:=smallRelations A) ⟨(d,i,j,k,l,a,b),rfl⟩

lemma present_diagonal (i : Fin 6) (a : Option A) : presentSmall A i i a=1 := by
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of] using present_relator A 0 i i i i a a
lemma present_square (i j : Fin 6) (a : Option A) : presentSmall A i j a*presentSmall A i j a=1 := by
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of] using present_relator A 1 i j i j a a
lemma present_distant (i j k l : Fin 6) (a b : Option A) (hil : i≠l) (hjk : j≠k) :
    Commute (presentSmall A i j a) (presentSmall A k l b) := by
  apply commutatorElement_eq_one_iff_mul_comm.mp
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of,hil,hjk] using present_relator A 2 i j k l a b
lemma present_unit_left (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅presentSmall A i j none,presentSmall A j k a⁆=presentSmall A i k a := by
  apply mul_inv_eq_one.mp
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of,hij,hjk,hik] using present_relator A 3 i j k k a a
lemma present_unit_right (i j k : Fin 6) (a : Option A) (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ⁅presentSmall A i j a,presentSmall A j k none⁆=presentSmall A i k a := by
  apply mul_inv_eq_one.mp
  simpa [smallRelator,freeSmall,presentSmall,PresentedGroup.of,hij,hjk,hik] using present_relator A 4 i j k k a a

def presentSystem : SmallSystem A (Presentation A) where
  small := presentSmall A
  diagonal := present_diagonal A
  square := present_square A
  distant := present_distant A
  unit_left := present_unit_left A
  unit_right := present_unit_right A

variable {A} {Q : Type*} [Group Q] (S : SmallSystem A Q)
def SmallSystem.fromPresentation : Presentation A →* Q :=
  PresentedGroup.toGroup (f:=fun z : SmallGenerator A => S.small z.1.1 z.1.2 z.2) (by
    rintro _ ⟨⟨d,i,j,k,l,a,b⟩,rfl⟩
    simp only [smallRelator]
    split_ifs <;> simp_all only [map_mul,map_inv,map_commutatorElement,map_one,freeSmall,FreeGroup.lift_apply_of]
    all_goals first
      | exact S.diagonal _ _
      | exact S.square _ _ _
      | exact (S.distant _ _ _ _ _ _ (by tauto) (by tauto)).commutator_eq
      | rw [S.unit_left _ _ _ _ (by tauto) (by tauto) (by tauto),mul_inv_cancel]
      | rw [S.unit_right _ _ _ _ (by tauto) (by tauto) (by tauto),mul_inv_cancel])

@[simp] lemma SmallSystem.fromPresentation_small (i j : Fin 6) (a : Option A) :
    S.fromPresentation (presentSmall A i j a)=S.small i j a := PresentedGroup.toGroup.of _

end

section
open scoped commutatorElement
open SmallSystem
variable {A Q Q' : Type*} [Group Q] [Group Q']
variable (S : SmallSystem A Q) (T : SmallSystem A Q') (f : Q →* Q')
variable (hf : ∀ i j a, f (S.small i j a)=T.small i j a)

include hf in
lemma SmallSystem.map_word (w : List A) (i j : Fin 6) : f (S.word w i j)=T.word w i j := by
  induction w generalizing i j with
  | nil => exact hf i j none
  | cons a w ih =>
    cases w with
    | nil => exact hf i j (some a)
    | cons b w =>
      by_cases hij : i=j
      · subst j; simp
      · rw [S.word_cons (by simp) a i j hij,T.word_cons (by simp) a i j hij,map_commutatorElement,hf]
        exact congrArg (fun z => ⁅T.small i (middle i j) (some a),z⁆) (by
          exact ih (middle i j) j)

include hf in
lemma SmallSystem.map_polynomial (p : Polynomial A) (i j : Fin 6) :
    f (S.polynomial p i j)=T.polynomial p i j := by
  apply polynomial_induction (fun p => f (S.polynomial p i j)=T.polynomial p i j)
  · simp
  · intro w; simp only [polynomial_single]; exact S.map_word T f hf _ i j
  · intro p q hp hq; rw [S.polynomial_add,T.polynomial_add,map_mul,hp,hq]

end

open scoped commutatorElement
open SmallSystem

end FiniteAlgebraicEnvelopes.SteinbergFiniteFree

end

end OAI
end

section
-- module Solutions.OAIFAE.ActionEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Full finitely presented faithful two-transitive action envelope and type-(A) applications.
-/

namespace FiniteAlgebraicEnvelopes
variable {A B : Type*} [Group A] [Group B]

/-- Intertwining of bijections propagates to every integer iterate. -/
theorem intertwine_zpow (F : A → B) (s : MulAut A) (t : MulAut B)
    (h : ∀ x, F (s x)=t (F x)) (n : ℤ) (x : A) : F ((s^n) x)=(t^n) (F x) := by
  have hinv (x : A) : F (s⁻¹ x)=t⁻¹ (F x) := by
    apply t.injective
    simpa only [MulAut.apply_inv_self] using (h (s⁻¹ x)).symm
  induction n using Int.induction_on generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [zpow_add,zpow_add,zpow_one,zpow_one]
    change F ((s^(n:ℤ)) (s x))=(t^(n:ℤ)) (t (F x))
    rw [ih,h]
  | pred n ih =>
    rw [sub_eq_add_neg,zpow_add,zpow_add,zpow_neg_one,zpow_neg_one]
    change F ((s^(-(n:ℤ))) (s⁻¹ x))=(t^(-(n:ℤ))) (t⁻¹ (F x))
    rw [ih,hinv]

namespace SequentialLimit
variable (f : Monoid.End A) (g : Monoid.End B)

def torusCongr (e : Limit f ≃* Limit g) (he : ∀ x, e (shift f x)=shift g (e x)) :
    Torus f ≃* Torus g :=
  SemidirectProduct.congr e (MulEquiv.refl _) (by
    intro z
    ext x
    exact intertwine_zpow e (shift f) (shift g) he z.toAdd x)

def quotientTorusEquiv (q : A →* B) (hq : ∀ x, q (f x)=g (q x))
    (hs : Function.Surjective q) (hk : ∀ x, q x=1 → f x=1) : Torus f ≃* Torus g :=
  torusCongr f g (equivalence f g q hq hs hk) (map_shift f g q hq)

end SequentialLimit
end FiniteAlgebraicEnvelopes

namespace FiniteAlgebraicEnvelopes.LimitAction

section
open SequentialLimit
variable {Q V : Type*} [Group Q] [Group V]
variable (α : Q →* MulAut V) (f : Monoid.End Q) (g : Monoid.End V)
variable (hc : ∀ x v, g (α x v)=α (f x) (g v))

def affineShift : MulAut (AffineLimit α f g hc) :=
  SemidirectProduct.congr (shift g) (shift f) (by intro x; ext v; exact (action_shift α f g hc x v).symm)

@[simp] theorem affineShift_left (a : AffineLimit α f g hc) :
    (affineShift α f g hc a).left=shift g a.left := rfl
@[simp] theorem affineShift_right (a : AffineLimit α f g hc) :
    (affineShift α f g hc a).right=shift f a.right := rfl

@[simp] theorem affineShift_zpow_left (z : ℤ) (a : AffineLimit α f g hc) :
    (((affineShift α f g hc)^z) a).left=((shift g)^z) a.left :=
  intertwine_zpow SemidirectProduct.left (affineShift α f g hc) (shift g) (fun _ => rfl) z a
@[simp] theorem affineShift_zpow_right (z : ℤ) (a : AffineLimit α f g hc) :
    (((affineShift α f g hc)^z) a).right=((shift f)^z) a.right :=
  intertwine_zpow SemidirectProduct.right (affineShift α f g hc) (shift f) (fun _ => rfl) z a

abbrev AffineTorus := (AffineLimit α f g hc) ⋊[zpowersHom _ (affineShift α f g hc)] Multiplicative ℤ

theorem affineLimitEquivalence_shift (x : Limit (affineStep α f g hc)) :
    affineLimitEquivalence α f g hc (shift (affineStep α f g hc) x)=
      affineShift α f g hc (affineLimitEquivalence α f g hc x) := by
  obtain ⟨i,a,rfl⟩ := DirectLimit.exists_eq_mk (transition (affineStep α f g hc)) x
  rfl

def affineTorusEquivalence : Torus (affineStep α f g hc) ≃* AffineTorus α f g hc :=
  SemidirectProduct.congr (affineLimitEquivalence α f g hc) (MulEquiv.refl _) (by
    intro z
    apply MulEquiv.ext
    intro x
    exact intertwine_zpow (affineLimitEquivalence α f g hc) (shift (affineStep α f g hc))
      (affineShift α f g hc) (affineLimitEquivalence_shift α f g hc) z.toAdd x)

/-- Reassociation retains the same translation, linear and stable coordinates. -/
def reassociateTorus : AffineTorus α f g hc ≃* (Limit g) ⋊[torusAction α f g hc] Torus f where
  toFun a := ⟨a.left.left,⟨a.left.right,a.right⟩⟩
  invFun a := ⟨⟨a.left,a.right.left⟩,a.right.right⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := by
    apply SemidirectProduct.ext
    · change a.left.left * action α f g hc a.left.right ((((affineShift α f g hc)^a.right.toAdd) b.left).left)=
        a.left.left * action α f g hc a.left.right (((shift g)^a.right.toAdd) b.left.left)
      rw [affineShift_zpow_left]
    · apply SemidirectProduct.ext
      · change a.left.right * (((affineShift α f g hc)^a.right.toAdd) b.left).right=
          a.left.right * ((shift f)^a.right.toAdd) b.left.right
        rw [affineShift_zpow_right]
      · rfl

def fullGroupEquivalence : Torus (affineStep α f g hc) ≃* (Limit g) ⋊[torusAction α f g hc] Torus f :=
  (affineTorusEquivalence α f g hc).trans (reassociateTorus α f g hc)

end

open SequentialLimit
variable {P Q V : Type*} [Group P] [Group Q] [Group V]
variable (α : P →* MulAut V) (β : Q →* MulAut V)
variable (f : Monoid.End P) (h : Monoid.End Q) (g : Monoid.End V)
variable (hcα : ∀ x v, g (α x v)=α (f x) (g v))
variable (hcβ : ∀ x v, g (β x v)=β (h x) (g v))
variable (q : P →* Q) (hq : ∀ x, q (f x)=h (q x))
variable (hαβ : ∀ x v, α x v=β (q x) v)

def affineQuotient : (V ⋊[α] P) →* (V ⋊[β] Q) :=
  SemidirectProduct.map (MonoidHom.id V) q (by intro x; ext v; exact hαβ x v)

theorem affineQuotient_surjective (hs : Function.Surjective q) :
    Function.Surjective (affineQuotient α β q hαβ) := by
  intro a
  obtain ⟨p,hp⟩ := hs a.right
  exact ⟨⟨a.left,p⟩,SemidirectProduct.ext rfl hp⟩

include hq in
theorem affineQuotient_natural (a : V ⋊[α] P) :
    affineQuotient α β q hαβ (affineStep α f g hcα a)=
      affineStep β h g hcβ (affineQuotient α β q hαβ a) :=
  SemidirectProduct.ext rfl (hq a.right)

theorem affineQuotient_kernel (hk : ∀ x, q x=1 → f x=1) (a : V ⋊[α] P)
    (ha : affineQuotient α β q hαβ a=1) : affineStep α f g hcα a=1 := by
  have hl : a.left=1 := congrArg SemidirectProduct.left ha
  have hr : q a.right=1 := congrArg SemidirectProduct.right ha
  apply SemidirectProduct.ext
  · change g a.left=1
    rw [hl,map_one]
  · exact hk a.right hr

def affineQuotientTorusEquivalence (hs : Function.Surjective q) (hk : ∀ x, q x=1 → f x=1) :
    Torus (affineStep α f g hcα) ≃* Torus (affineStep β h g hcβ) :=
  quotientTorusEquiv _ _ (affineQuotient α β q hαβ)
    (affineQuotient_natural α β f h g hcα hcβ q hq hαβ) (affineQuotient_surjective α β q hαβ hs)
    (affineQuotient_kernel α β f g hcα q hαβ hk)

def affineQuotientFullEquivalence (hs : Function.Surjective q) (hk : ∀ x, q x=1 → f x=1) :
    Torus (affineStep α f g hcα) ≃* (Limit g) ⋊[torusAction β h g hcβ] Torus h :=
  (affineQuotientTorusEquivalence α β f h g hcα hcβ q hq hαβ hs hk).trans
    (fullGroupEquivalence β h g hcβ)

end FiniteAlgebraicEnvelopes.LimitAction

namespace FiniteAlgebraicEnvelopes.Steinberg
open scoped commutatorElement
variable {R ι : Type*} [Ring R] [Fintype ι] [DecidableEq ι]

def diagonalUnits : (ι → Rˣ) →* (Matrix ι ι R)ˣ where
  toFun d :=
    { val := Matrix.diagonal (fun i => (d i : R))
      inv := Matrix.diagonal (fun i => (↑((d i)⁻¹) : R))
      val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
      inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp }
  map_one' := by apply Units.ext; simp
  map_mul' d e := by apply Units.ext; simp [Matrix.diagonal_mul_diagonal]

@[simp] theorem diagonalUnits_val (d : ι → Rˣ) :
    (diagonalUnits d).val=Matrix.diagonal (fun i => (d i : R)) := rfl

def singleDiagonal (p : ι) : Rˣ →* (Matrix ι ι R)ˣ := diagonalUnits.comp
  { toFun := fun u i => if i=p then u else 1
    map_one' := by funext i; simp
    map_mul' := by intro a b; funext i; by_cases hi : i=p <;> simp [hi] }

@[simp] theorem singleDiagonal_val (p : ι) (u : Rˣ) :
    (singleDiagonal p u).val=Matrix.diagonal (fun i => if i=p then (u:R) else 1) := by
  change Matrix.diagonal (fun i => (↑(if i=p then u else 1):R))=_
  congr 1
  funext i
  by_cases hi : i=p <;> simp [hi]

variable {G : Type*} [_root_.Group G]

def firstFactor : G →* G × G where
  toFun g := (g,1)
  map_one' := rfl
  map_mul' _ _ := by ext <;> simp

def inputDiagonal (f : G×G →* Rˣ) := (singleDiagonal (ι:=Fin 6) (R:=R) 0).comp (f.comp firstFactor)

end FiniteAlgebraicEnvelopes.Steinberg

namespace FiniteAlgebraicEnvelopes

section
universe u
namespace LiftedAction
variable {Γ X : Type*} [Group Γ] [MulAction Γ X]

@[instance_reducible] def action : MulAction (ULift.{u} Γ) (ULift.{u} X) where
  smul g x := ⟨g.down • x.down⟩
  one_smul x := by cases x; exact congrArg ULift.up (one_smul Γ _)
  mul_smul g h x := by cases x; exact congrArg ULift.up (mul_smul g.down h.down _)

attribute [local instance] action

@[simp] lemma down_smul (g : ULift.{u} Γ) (x : ULift.{u} X) : (g • x).down=g.down • x.down := rfl

instance faithful [FaithfulSMul Γ X] : FaithfulSMul (ULift.{u} Γ) (ULift.{u} X) where
  eq_of_smul_eq_smul := by
    intro g h he
    apply ULift.ext
    apply eq_of_smul_eq_smul (α:=X)
    intro x
    exact congrArg ULift.down (he (ULift.up x))

def stabilizerEquivalence (x : ULift.{u} X) :
    MulAction.stabilizer (ULift.{u} Γ) x ≃* MulAction.stabilizer Γ x.down where
  toFun g := ⟨g.val.down,by
    have hg := g.property
    change (g.val • x)=x at hg
    exact congrArg ULift.down hg⟩
  invFun g := ⟨ULift.up g.val,by
    change ULift.up (g.val • x.down)=x
    rw [show g.val • x.down=x.down from g.property]⟩
  left_inv g := by apply Subtype.ext; rfl
  right_inv g := by apply Subtype.ext; rfl
  map_mul' g h := rfl

end LiftedAction

open scoped commutatorElement

end

end FiniteAlgebraicEnvelopes

end

end OAI
end

section
-- module Solutions.OAIFAE.BinaryCategory
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Self-similar binary group categories, associativity, symmetry, naturality, and braids.
-/

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory

section
universe u
open CategoryTheory

/-- Binary self-similarity data for a group, with the associativity laws in
explicit multiplicative orientation. The concrete finite structural quotient
supplies every field; this is not an assumption on the main theorem's input. -/
structure Data (H : Type u) [Group H] where
  tensor : H × H →* H
  a : H
  naturality : ∀ g h k,a * tensor (g,tensor (h,k)) * a⁻¹=tensor (tensor (g,h),k)
  pentagon : a*a=tensor (a,1)*a*tensor (1,a)

inductive Object (H : Type u)
  | zero | positive
  deriving DecidableEq

variable {H : Type u} [Group H]

@[ext] structure Hom (A B : Object H) where
  val : H
  object_eq : A=B
  unit_eq : A=.zero → val=1

namespace Hom

def id (A : Object H) : Hom A A := ⟨1,rfl,fun _=>rfl⟩
def comp {A B C : Object H} (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨g.val*f.val,f.object_eq.trans g.object_eq,by
    intro h
    rw [f.unit_eq h,g.unit_eq (f.object_eq.symm.trans h),mul_one]⟩
end Hom

instance instCategoryObject : Category (Object H) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := by apply Hom.ext; exact mul_one _
  comp_id f := by apply Hom.ext; exact one_mul _
  assoc f g h := by apply Hom.ext; exact (mul_assoc _ _ _).symm

@[simp] lemma id_val (A : Object H) : (𝟙 A : Hom A A).val=1 := rfl
@[simp] lemma comp_val {A B C : Object H} (f : A ⟶ B) (g : B ⟶ C) :
    (f≫g).val=g.val*f.val := rfl

namespace Object
omit [Group H]
abbrev tensor : Object H → Object H → Object H
  | .zero,B => B
  | .positive,_ => .positive
@[simp] lemma tensor_zero (A : Object H) : tensor A .zero=A := by cases A <;> rfl
@[simp] lemma zero_tensor (A : Object H) : tensor .zero A=A := rfl
@[simp] lemma tensor_assoc (A B C : Object H) : tensor (tensor A B) C=tensor A (tensor B C) := by
  cases A <;> cases B <;> cases C <;> rfl
end Object

variable (d : Data H)

def tensorVal (A B : Object H) (f g : H) : H :=
  match A,B with
  | .zero,_ => g
  | _,.zero => f
  | .positive,.positive => d.tensor (f,g)

@[simp] lemma tensorVal_zero_left (B : Object H) (f g : H) : tensorVal d .zero B f g=g := rfl

def tensorHom {A₁ A₂ B₁ B₂ : Object H} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    Object.tensor A₁ B₁ ⟶ Object.tensor A₂ B₂ :=
  ⟨tensorVal d A₁ B₁ f.val g.val,congrArg₂ Object.tensor f.object_eq g.object_eq,by
    cases A₁ <;> cases B₁
    · intro _; exact g.unit_eq rfl
    · intro h; cases h
    · intro h; cases h
    · intro h; cases h⟩

lemma tensorHom_val {A₁ A₂ B₁ B₂ : Object H} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    (tensorHom d f g).val=tensorVal d A₁ B₁ f.val g.val := rfl

lemma tensor_id (A B : Object H) : tensorHom d (𝟙 A) (𝟙 B)=𝟙 (Object.tensor A B) := by
  apply Hom.ext
  cases A <;> cases B <;> simp only [tensorHom_val,tensorVal,id_val]
  exact d.tensor.map_one

lemma tensor_comp {A₁ A₂ A₃ B₁ B₂ B₃ : Object H}
    (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : A₂ ⟶ A₃) (k : B₂ ⟶ B₃) :
    tensorHom d f g ≫ tensorHom d h k=tensorHom d (f≫h) (g≫k) := by
  have ha := f.object_eq; have hb := g.object_eq
  subst A₂; subst B₂
  apply Hom.ext
  cases A₁ <;> cases B₁ <;> simp only [comp_val,tensorHom_val,tensorVal]
  exact (d.tensor.map_mul (h.val,k.val) (f.val,g.val)).symm

def iso {A B : Object H} (h : A=B) (g : H) (hg : A=.zero → g=1) : A ≅ B where
  hom := ⟨g,h,hg⟩
  inv := ⟨g⁻¹,h.symm,by intro hb; rw [hg (h.trans hb),inv_one]⟩
  hom_inv_id := by apply Hom.ext; exact inv_mul_cancel _
  inv_hom_id := by apply Hom.ext; exact mul_inv_cancel _

def associatorVal : Object H → Object H → Object H → H
  | .positive,.positive,.positive => d.a⁻¹
  | _,_,_ => 1

def associator (A B C : Object H) :
    Object.tensor (Object.tensor A B) C ≅ Object.tensor A (Object.tensor B C) :=
  iso (Object.tensor_assoc A B C) (associatorVal d A B C) (by
    intro h; cases A <;> cases B <;> cases C <;> first | rfl | cases h)

def leftUnitor (A : Object H) : Object.tensor .zero A ≅ A := iso rfl 1 (fun _=>rfl)
def rightUnitor (A : Object H) : Object.tensor A .zero ≅ A :=
  iso (Object.tensor_zero A) 1 (fun _=>rfl)

@[instance_reducible] def monoidalStruct : MonoidalCategoryStruct (Object H) where
  tensorObj := Object.tensor
  whiskerLeft A _ _ g := tensorHom d (𝟙 A) g
  whiskerRight f B := tensorHom d f (𝟙 B)
  tensorHom := tensorHom d
  tensorUnit := .zero
  associator := associator d
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

lemma associator_natural {A₁ A₂ B₁ B₂ C₁ C₂ : Object H}
    (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) (h : C₁ ⟶ C₂) :
    tensorHom d (tensorHom d f g) h ≫ (associator d A₂ B₂ C₂).hom=
      (associator d A₁ B₁ C₁).hom ≫ tensorHom d f (tensorHom d g h) := by
  have ha := f.object_eq; have hb := g.object_eq; have hc := h.object_eq
  subst A₂; subst B₂; subst C₂
  have hf := f.unit_eq; have hg := g.unit_eq; have hh := h.unit_eq
  apply Hom.ext
  change associatorVal d A₁ B₁ C₁ * tensorVal d (Object.tensor A₁ B₁) C₁
      (tensorVal d A₁ B₁ f.val g.val) h.val=
    tensorVal d A₁ (Object.tensor B₁ C₁) f.val (tensorVal d B₁ C₁ g.val h.val) *
      associatorVal d A₁ B₁ C₁
  cases A₁ <;> cases B₁ <;> cases C₁ <;>
    simp_all only [associatorVal,tensorVal,one_mul,mul_one,forall_const]
  rw [← d.naturality f.val g.val h.val]
  group

lemma leftUnitor_natural {A B : Object H} (f : A ⟶ B) :
    tensorHom d (𝟙 (.zero : Object H)) f ≫ (leftUnitor B).hom=(leftUnitor A).hom ≫ f := by
  apply Hom.ext
  simp only [comp_val,tensorHom_val,leftUnitor,iso,tensorVal,one_mul,mul_one]

lemma rightUnitor_natural {A B : Object H} (f : A ⟶ B) :
    tensorHom d f (𝟙 (.zero : Object H)) ≫ (rightUnitor B).hom=(rightUnitor A).hom ≫ f := by
  apply Hom.ext
  cases A
  · simp only [comp_val,tensorHom_val,rightUnitor,iso,tensorVal,id_val,mul_one]
    exact (f.unit_eq rfl).symm
  · simp only [comp_val,tensorHom_val,rightUnitor,iso,tensorVal,one_mul,mul_one]

lemma pentagon (A B C E : Object H) :
    tensorHom d (associator d A B C).hom (𝟙 E) ≫
      (associator d A (Object.tensor B C) E).hom ≫
        tensorHom d (𝟙 A) (associator d B C E).hom =
      (associator d (Object.tensor A B) C E).hom ≫
        (associator d A B (Object.tensor C E)).hom := by
  apply Hom.ext
  change (tensorVal d A (Object.tensor (Object.tensor B C) E) 1 (associatorVal d B C E) *
    associatorVal d A (Object.tensor B C) E) *
      tensorVal d (Object.tensor (Object.tensor A B) C) E (associatorVal d A B C) 1=
    associatorVal d A B (Object.tensor C E) * associatorVal d (Object.tensor A B) C E
  have hone : d.tensor (1,1)=1 := d.tensor.map_one
  cases A <;> cases B <;> cases C <;> cases E <;>
    simp only [associatorVal,tensorVal,hone,one_mul,mul_one]
  have hm := congrArg (fun z : H=>z⁻¹) d.pentagon
  simpa only [mul_inv_rev,← map_inv,Prod.inv_mk,inv_one,mul_assoc] using hm.symm

lemma triangle (A B : Object H) :
    (associator d A .zero B).hom ≫ tensorHom d (𝟙 A) (leftUnitor B).hom=
      tensorHom d (rightUnitor A).hom (𝟙 B) := by
  apply Hom.ext
  change tensorVal d A (Object.tensor .zero B) 1 1 * associatorVal d A .zero B=
    tensorVal d (Object.tensor A .zero) B 1 1
  cases A <;> cases B <;> simp only [associatorVal,tensorVal,mul_one]

@[instance_reducible] def monoidal : MonoidalCategory (Object H) := by
  letI := monoidalStruct d
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensor_id d)
    (id_tensorHom := by intros; rfl)
    (tensorHom_id := by intros; rfl)
    (tensorHom_comp_tensorHom := tensor_comp d)
    (associator_naturality := associator_natural d)
    (leftUnitor_naturality := leftUnitor_natural d)
    (rightUnitor_naturality := rightUnitor_natural d)
    (pentagon := pentagon d)
    (triangle := triangle d)

end

section
universe u
open CategoryTheory
variable {H : Type u} [Group H] (d : Data H)

structure SymmetryData where
  c : H
  square : c*c=1
  naturality : ∀ g h,c*d.tensor (g,h)*c⁻¹=d.tensor (h,g)
  hexagon : c=d.a*d.tensor (1,c)*d.a⁻¹*d.tensor (c,1)*d.a

variable (q : SymmetryData d)
lemma symmetry_inv : q.c⁻¹=q.c := inv_eq_of_mul_eq_one_right q.square

def braidingVal : Object H → Object H → H
  | .positive,.positive => q.c
  | _,_ => 1

def braiding (A B : Object H) : Object.tensor A B ≅ Object.tensor B A :=
  iso (by cases A <;> cases B <;> rfl) (braidingVal d q A B) (by
    intro h; cases A <;> cases B <;> first | rfl | cases h)

lemma braiding_natural {A₁ A₂ B₁ B₂ : Object H} (f : A₁ ⟶ A₂) (g : B₁ ⟶ B₂) :
    tensorHom d f g ≫ (braiding d q A₂ B₂).hom=
      (braiding d q A₁ B₁).hom ≫ tensorHom d g f := by
  have ha := f.object_eq; have hb := g.object_eq
  subst A₂; subst B₂
  have hf := f.unit_eq; have hg := g.unit_eq
  apply Hom.ext
  change braidingVal d q A₁ B₁ * tensorVal d A₁ B₁ f.val g.val=
    tensorVal d B₁ A₁ g.val f.val * braidingVal d q A₁ B₁
  cases A₁ <;> cases B₁ <;> simp_all only [braidingVal,tensorVal,one_mul,mul_one,forall_const]
  calc
    _=(q.c*d.tensor (f.val,g.val)*q.c⁻¹)*q.c := by group
    _=_ := by rw [q.naturality]

lemma hexagon_equation : d.a⁻¹*q.c*d.a⁻¹=d.tensor (1,q.c)*d.a⁻¹*d.tensor (q.c,1) := by
  conv_lhs => arg 1; arg 2; rw [q.hexagon]
  group

lemma hexagon_equation_reverse : d.a*q.c*d.a=d.tensor (q.c,1)*d.a*d.tensor (1,q.c) := by
  have h := congrArg (fun z : H=>z⁻¹) (hexagon_equation d q)
  simpa only [mul_inv_rev,inv_inv,← map_inv,Prod.inv_mk,inv_one,symmetry_inv,mul_assoc] using h

lemma braiding_hexagon_forward (A B C : Object H) :
    (associator d A B C).hom ≫ (braiding d q A (Object.tensor B C)).hom ≫
      (associator d B C A).hom =
    tensorHom d (braiding d q A B).hom (𝟙 C) ≫ (associator d B A C).hom ≫
      tensorHom d (𝟙 B) (braiding d q A C).hom := by
  apply Hom.ext
  change (associatorVal d B C A * braidingVal d q A (Object.tensor B C)) * associatorVal d A B C=
    (tensorVal d B (Object.tensor A C) 1 (braidingVal d q A C) * associatorVal d B A C) *
      tensorVal d (Object.tensor A B) C (braidingVal d q A B) 1
  have hone : d.tensor (1,1)=1 := d.tensor.map_one
  cases A <;> cases B <;> cases C <;>
    simp only [associatorVal,braidingVal,tensorVal,hone,one_mul,mul_one]
  exact hexagon_equation d q

lemma braiding_hexagon_reverse (A B C : Object H) :
    (associator d A B C).inv ≫ (braiding d q (Object.tensor A B) C).hom ≫
      (associator d C A B).inv =
    tensorHom d (𝟙 A) (braiding d q B C).hom ≫ (associator d A C B).inv ≫
      tensorHom d (braiding d q A C).hom (𝟙 B) := by
  apply Hom.ext
  change ((associatorVal d C A B)⁻¹ * braidingVal d q (Object.tensor A B) C) *
      (associatorVal d A B C)⁻¹=
    (tensorVal d (Object.tensor A C) B (braidingVal d q A C) 1 * (associatorVal d A C B)⁻¹) *
      tensorVal d A (Object.tensor B C) 1 (braidingVal d q B C)
  have hone : d.tensor (1,1)=1 := d.tensor.map_one
  cases A <;> cases B <;> cases C <;>
    simp only [associatorVal,braidingVal,tensorVal,hone,one_mul,mul_one,inv_one,inv_inv]
  exact hexagon_equation_reverse d q

lemma braiding_symmetry (A B : Object H) :
    (braiding d q A B).hom ≫ (braiding d q B A).hom=𝟙 (Object.tensor A B) := by
  apply Hom.ext
  change braidingVal d q B A * braidingVal d q A B=1
  cases A <;> cases B <;> simp only [braidingVal,one_mul]
  exact q.square

@[instance_reducible] def symmetric : letI := monoidal d; SymmetricCategory (Object H) := by
  letI := monoidal d
  exact
    { braiding := braiding d q
      braiding_naturality_right := fun X _ _ f=>braiding_natural d q (𝟙 X) f
      braiding_naturality_left := fun f Z=>braiding_natural d q f (𝟙 Z)
      hexagon_forward := braiding_hexagon_forward d q
      hexagon_reverse := braiding_hexagon_reverse d q
      symmetry := braiding_symmetry d q }

end

section
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma tensor_conjugate (a b g h : H) :
    d.tensor (a*g*a⁻¹,b*h*b⁻¹)=d.tensor (a,b)*d.tensor (g,h)*(d.tensor (a,b))⁻¹ := by
  change d.tensor (((a,b)*(g,h))*(a,b)⁻¹)=_
  rw [map_mul,map_mul,map_inv]

lemma tensor_commute {a b g h : H} (ha : Commute a g) (hb : Commute b h) :
    Commute (d.tensor (a,b)) (d.tensor (g,h)) := by
  apply Commute.map
  change (a*g,b*h)=(g*a,h*b)
  exact Prod.ext ha.eq hb.eq

/-- The four-leaf middle transposition, expressed only in associator, symmetry
and binary tensor; its naturality is needed in the colour-orbit reduction. -/
def middleSwap : H :=
  d.a*d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*d.a⁻¹

lemma middleSwap_naturality (g : H) :
    Commute (middleSwap d q) (d.tensor (d.tensor (g,g),d.tensor (g,g))) := by
  let D := d.tensor (g,g)
  let Q := d.tensor (g,d.tensor (D,g))
  let K := d.a*d.tensor (1,d.a⁻¹)
  let C := d.tensor (1,d.tensor (q.c,1))
  have hc : Commute q.c D := by
    have h := q.naturality g g
    change q.c*D*q.c⁻¹=D at h
    change q.c*D=D*q.c
    calc
      _=(q.c*D*q.c⁻¹)*q.c := by group
      _=_ := by rw [h]
  have hC : Commute C Q :=
    tensor_commute d (Commute.one_left g)
      (tensor_commute d hc (Commute.one_left g))
  have hi : d.a⁻¹*d.tensor (D,g)*d.a=d.tensor (g,D) := by
    have h := d.naturality g g g
    change d.a*d.tensor (g,D)*d.a⁻¹=d.tensor (D,g) at h
    rw [← h]
    group
  have hK : K*Q*K⁻¹=d.tensor (D,D) := by
    calc
      _=d.a*(d.tensor (1,d.a⁻¹)*Q*(d.tensor (1,d.a⁻¹))⁻¹)*d.a⁻¹ := by
        dsimp [K]; group
      _=d.a*d.tensor (g,d.a⁻¹*d.tensor (D,g)*d.a)*d.a⁻¹ := by
        rw [← tensor_conjugate]
        simp only [one_mul,inv_one,mul_one,inv_inv]
      _=d.a*d.tensor (g,d.tensor (g,D))*d.a⁻¹ := by rw [hi]
      _=d.tensor (D,D) := d.naturality g g D
  have hM : middleSwap d q=K*C*K⁻¹ := by
    change d.a*d.tensor (1,d.a⁻¹*d.tensor (q.c,1)*d.a)*d.a⁻¹=_
    have ht := tensor_conjugate d (1:H) d.a⁻¹ (1:H) (d.tensor (q.c,1))
    simp only [inv_one,mul_one,inv_inv] at ht
    rw [ht]
    dsimp [K,C]
    group
  have hm := hC.map (MulAut.conj K).toMonoidHom
  change Commute (K*C*K⁻¹) (K*Q*K⁻¹) at hm
  rwa [hK,← hM] at hm

end

section
universe u
open CategoryTheory
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

/-- Adjacent swaps in a fixed left-associated triple. -/
def firstSwap : H := d.tensor (q.c,1)
def secondSwap : H := d.a*d.tensor (1,q.c)*d.a⁻¹

lemma adjacent_braid : firstSwap d q*secondSwap d q*firstSwap d q=
    secondSwap d q*firstSwap d q*secondSwap d q := by
  let := monoidal d
  let := symmetric d q
  have h := congrArg (fun f : (Object.positive : Object H) ⟶ Object.positive=>f.val)
    (CategoryTheory.BraidedCategory.yang_baxter (Object.positive : Object H) Object.positive Object.positive)
  simp only [comp_val] at h
  change ((((((d.a⁻¹ * d.tensor (q.c,1)) * (d.a⁻¹)⁻¹) * d.tensor (1,q.c)) * d.a⁻¹) * d.tensor (q.c,1)) * (d.a⁻¹)⁻¹)=
    (((d.tensor (1,q.c) * d.a⁻¹) * d.tensor (q.c,1)) * (d.a⁻¹)⁻¹) * d.tensor (1,q.c) at h
  simp only [inv_inv] at h
  have hh := congrArg (fun z : H=>d.a*z*d.a⁻¹) h
  dsimp only [firstSwap,secondSwap]
  convert hh using 1 <;> group

end

/- General naturality of the adjacent permutations on decorated triples. -/
universe u

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

end

end OAI
end

section
-- module Solutions.OAIFAE.BinaryCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Binary combs, folds, permutations, and coherent exchanges.
-/

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory

section
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

def left : H →* H where
  toFun g := d.tensor (g,1)
  map_one' := map_one d.tensor
  map_mul' g h := by simpa only [Prod.mk_mul_mk,mul_one] using d.tensor.map_mul (g,1) (h,1)
def right : H →* H where
  toFun g := d.tensor (1,g)
  map_one' := map_one d.tensor
  map_mul' g h := by simpa only [Prod.mk_mul_mk,mul_one] using d.tensor.map_mul (1,g) (1,h)

lemma left_right (g h : H) : Commute (left d g) (right d h) := by
  change d.tensor (g,1)*d.tensor (1,h)=d.tensor (1,h)*d.tensor (g,1)
  rw [← map_mul,← map_mul]
  simp only [Prod.mk_mul_mk,one_mul,mul_one]

lemma assoc_LL (g : H) : d.a * left d g * d.a⁻¹ = left d (left d g) := by
  change d.a*d.tensor (g,1)*d.a⁻¹=d.tensor (d.tensor (g,1),1)
  simpa only [show d.tensor (1,1)=1 from map_one d.tensor] using d.naturality g 1 1
lemma assoc_LR (g : H) : d.a * right d (left d g) * d.a⁻¹ = left d (right d g) :=
  d.naturality 1 g 1
lemma assoc_RR (g : H) : d.a * right d (right d g) * d.a⁻¹ = right d g := by
  change d.a*d.tensor (1,d.tensor (1,g))*d.a⁻¹=d.tensor (1,g)
  simpa only [show d.tensor (1,1)=1 from map_one d.tensor] using d.naturality 1 1 g

/-- The first adjacent swap on a right-associated comb with at least three leaves. -/
def combHead : H := d.a⁻¹*left d q.c*d.a

lemma combHead_square : combHead d q * combHead d q = 1 := by
  have h : left d q.c * left d q.c = 1 := by rw [← map_mul,q.square,map_one]
  dsimp only [combHead]
  calc
    _=d.a⁻¹*(left d q.c*left d q.c)*d.a := by group
    _=1 := by rw [h,mul_one,inv_mul_cancel]

lemma combHead_distant (g : H) : Commute (combHead d q) (right d (right d g)) := by
  have ha := assoc_RR d g
  have hb : right d (right d g) = d.a⁻¹ * right d g * d.a := by
    calc
      _ = d.a⁻¹ * (d.a * right d (right d g) * d.a⁻¹) * d.a := by group
      _ = _ := by rw [ha]
  rw [hb,combHead]
  simpa only [inv_inv] using (left_right d q.c g).conj d.a⁻¹

lemma combHead_braid_last :
    combHead d q * right d q.c * combHead d q =
      right d q.c * combHead d q * right d q.c := by
  have h := adjacent_braid d q
  dsimp only [firstSwap,secondSwap] at h
  change left d q.c * (d.a * right d q.c * d.a⁻¹) * left d q.c =
    (d.a * right d q.c * d.a⁻¹) * left d q.c * (d.a * right d q.c * d.a⁻¹) at h
  have hh := congrArg (fun z : H => d.a⁻¹*z*d.a) h
  dsimp only [combHead]
  convert hh using 1 <;> group

lemma combHead_conj_first :
    (d.a*d.a) * combHead d q * (d.a*d.a)⁻¹ = left d (firstSwap d q) := by
  dsimp only [combHead,firstSwap]
  calc
    _=d.a * left d q.c * d.a⁻¹ := by group
    _=_ := assoc_LL d q.c

lemma combHead_conj_second :
    (d.a*d.a) * right d (combHead d q) * (d.a*d.a)⁻¹ = left d (secondSwap d q) := by
  have hp : d.a*d.a=left d d.a*d.a*right d d.a := d.pentagon
  rw [hp,combHead,map_mul,map_mul,map_inv]
  calc
    _=left d d.a * (d.a * right d (left d q.c) * d.a⁻¹) * (left d d.a)⁻¹ := by group
    _=left d d.a * left d (right d q.c) * (left d d.a)⁻¹ := by rw [assoc_LR]
    _=_ := by rw [← map_inv,← map_mul,← map_mul]; rfl

lemma combHead_braid :
    combHead d q * right d (combHead d q) * combHead d q =
      right d (combHead d q) * combHead d q * right d (combHead d q) := by
  apply (MulAut.conj (d.a*d.a)).injective
  change (d.a*d.a) * (_*_*_) * (d.a*d.a)⁻¹ = (d.a*d.a) * (_*_*_) * (d.a*d.a)⁻¹
  have hh (g h k : H) : (d.a*d.a) * (g*h*k) * (d.a*d.a)⁻¹ =
      ((d.a*d.a)*g*(d.a*d.a)⁻¹) * ((d.a*d.a)*h*(d.a*d.a)⁻¹) *
      ((d.a*d.a)*k*(d.a*d.a)⁻¹) := by group
  rw [hh,hh,combHead_conj_first,combHead_conj_second,← map_mul,← map_mul,
    ← map_mul,← map_mul,adjacent_braid]

/-- Whisker an endomorphism past `n` initial leaves of a right comb. -/
def rightPower : ℕ → H →* H
  | 0 => MonoidHom.id H
  | n+1 => (right d).comp (rightPower n)

@[simp] lemma rightPower_zero (g : H) : rightPower d 0 g = g := rfl
@[simp] lemma rightPower_succ (n : ℕ) (g : H) :
    rightPower d (n+1) g = right d (rightPower d n g) := rfl
lemma rightPower_add (m n : ℕ) (g : H) :
    rightPower d (m+n) g = rightPower d m (rightPower d n g) := by
  induction m with
  | zero => simp only [Nat.zero_add,rightPower_zero]
  | succ m ih => rw [Nat.succ_add,rightPower_succ,rightPower_succ,ih]
lemma rightPower_succ' (n : ℕ) (g : H) :
    rightPower d (n+1) g = rightPower d n (right d g) := by
  rw [rightPower_add]; rfl

/-- `n` adjacent generators acting on the `n+1` leaf right comb. -/
def combSwap (n i : ℕ) : H :=
  if i < n then rightPower d i (if i+1=n then q.c else combHead d q) else 1

lemma combSwap_last (n : ℕ) : combSwap d q (n+1) n = rightPower d n q.c := by
  simp only [combSwap,Nat.lt_succ_self,↓reduceIte]
lemma combSwap_internal {n i : ℕ} (hi : i+1<n) :
    combSwap d q n i = rightPower d i (combHead d q) := by
  simp only [combSwap,show i<n by omega,show ¬ i+1=n by omega,↓reduceIte]

lemma combSwap_braid {n i : ℕ} (hi : i+1<n) :
    combSwap d q n (i+1) * combSwap d q n i * combSwap d q n (i+1) =
      combSwap d q n i * combSwap d q n (i+1) * combSwap d q n i := by
  rw [combSwap_internal d q hi]
  by_cases ht : i+2=n
  · subst n
    rw [show i+2=i+1+1 from rfl,combSwap_last,rightPower_succ',← map_mul,← map_mul,
      ← map_mul,← map_mul,combHead_braid_last]
  · rw [combSwap_internal d q (by omega),rightPower_succ',← map_mul,← map_mul,
      ← map_mul,← map_mul,combHead_braid]

end

universe u

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

/-- Consecutive indexing of two positive blocks, in predecessor-size notation. -/
def sumIndex (m n : ℕ) : Fin (m+1) ⊕ Fin (n+1) ≃ Fin (m+n+1+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] lemma sumIndex_left_val (m n : ℕ) (i : Fin (m+1)) :
    (sumIndex m n (Sum.inl i) : ℕ)=i := rfl
@[simp] lemma sumIndex_right_val (m n : ℕ) (i : Fin (n+1)) :
    (sumIndex m n (Sum.inr i) : ℕ)=m+1+i := rfl

def sumPermutation (m n : ℕ) :
    Equiv.Perm (Fin (m+1)) × Equiv.Perm (Fin (n+1)) →* Equiv.Perm (Fin (m+n+1+1)) :=
  (Equiv.permCongrHom (sumIndex m n)).toMonoidHom.comp (Equiv.Perm.sumCongrHom _ _)

lemma sumPermutation_swap_left (m n : ℕ) (i j : Fin (m+1)) :
    sumPermutation m n (Equiv.swap i j,1)=
      Equiv.swap (sumIndex m n (Sum.inl i)) (sumIndex m n (Sum.inl j)) := by
  change (Equiv.permCongrHom (sumIndex m n)) (Equiv.Perm.sumCongr (Equiv.swap i j) 1)=_
  rw [Equiv.Perm.sumCongr_swap_one]
  exact Equiv.symm_trans_swap_trans _ _ _

lemma sumPermutation_swap_right (m n : ℕ) (i j : Fin (n+1)) :
    sumPermutation m n (1,Equiv.swap i j)=
      Equiv.swap (sumIndex m n (Sum.inr i)) (sumIndex m n (Sum.inr j)) := by
  change (Equiv.permCongrHom (sumIndex m n)) (Equiv.Perm.sumCongr 1 (Equiv.swap i j))=_
  rw [Equiv.Perm.sumCongr_one_swap]
  exact Equiv.symm_trans_swap_trans _ _ _

lemma equiv_size {m n : ℕ} (e : Fin (m+1) ≃ Fin (n+1)) : m=n := by
  have h := Fintype.card_congr e
  simpa only [Fintype.card_fin,Nat.add_right_cancel_iff] using h

def sumEquiv {m n p q : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (q+1)) :
    Fin (m+n+1+1) ≃ Fin (p+q+1+1) :=
  (sumIndex m n).symm.trans ((Equiv.sumCongr e f).trans (sumIndex p q))

@[simp] lemma sumEquiv_left {m n p q : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (q+1))
    (i : Fin (m+1)) : sumEquiv e f (sumIndex m n (Sum.inl i))=sumIndex p q (Sum.inl (e i)) := by
  simp only [sumEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inl]

@[simp] lemma sumEquiv_right {m n p q : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (q+1))
    (i : Fin (n+1)) : sumEquiv e f (sumIndex m n (Sum.inr i))=sumIndex p q (Sum.inr (f i)) := by
  simp only [sumEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,Sum.map_inr]

/-- Exchange two consecutive positive blocks. -/
def exchangeEquiv (m n : ℕ) : Fin (m+n+1+1) ≃ Fin (n+m+1+1) :=
  (sumIndex m n).symm.trans ((Equiv.sumComm _ _).trans (sumIndex n m))

@[simp] lemma exchangeEquiv_left (m n : ℕ) (i : Fin (m+1)) :
    exchangeEquiv m n (sumIndex m n (Sum.inl i))=sumIndex n m (Sum.inr i) := by
  simp only [exchangeEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumComm_apply,Sum.swap_inl]

@[simp] lemma exchangeEquiv_right (m n : ℕ) (i : Fin (n+1)) :
    exchangeEquiv m n (sumIndex m n (Sum.inr i))=sumIndex n m (Sum.inl i) := by
  simp only [exchangeEquiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumComm_apply,Sum.swap_inr]

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

namespace FiniteAlgebraicEnvelopes.BinaryGroupCategory
universe u
variable {H : Type u} [Group H] (d : Data H) (q : SymmetryData d)

lemma exchangeEquiv_val (m n : ℕ) (i : Fin (m+n+1+1)) :
    (exchangeEquiv m n i : ℕ)=if (i:ℕ)< m+1 then n+1+i else i-(m+1) := by
  obtain ⟨j,rfl⟩ := (sumIndex m n).surjective i
  cases j with
  | inl j => simp only [exchangeEquiv_left,sumIndex_left_val,sumIndex_right_val,j.isLt,↓reduceIte]
  | inr j => simp only [exchangeEquiv_right,sumIndex_left_val,sumIndex_right_val,
      show ¬ m+1+(j:ℕ)< m+1 by omega,↓reduceIte,Nat.add_sub_cancel_left]

lemma sumEquiv_valWith {m n p r : ℕ} (e : Fin (m+1) ≃ Fin (p+1)) (f : Fin (n+1) ≃ Fin (r+1))
    (E F : ℕ → ℕ) (he : ∀ i,(e i : ℕ)=E i) (hf : ∀ i,(f i : ℕ)=F i)
    (i : Fin (m+n+1+1)) :
    (sumEquiv e f i : ℕ)=if (i:ℕ)< m+1 then E i else p+1+F (i-(m+1)) := by
  obtain ⟨j,rfl⟩ := (sumIndex m n).surjective i
  cases j with
  | inl j => simp only [sumEquiv_left,sumIndex_left_val,he,j.isLt,↓reduceIte]
  | inr j => simp only [sumEquiv_right,sumIndex_right_val,hf,
      show ¬ m+1+(j:ℕ)< m+1 by omega,↓reduceIte,Nat.add_sub_cancel_left]

end FiniteAlgebraicEnvelopes.BinaryGroupCategory

end

end OAI
end

section
-- module Solutions.OAIFAE.CantorBricks
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Cantor prefixes, bricks, charts, finite-table group, localization, and displacement.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable

/-- The Cantor cube used by the twisted Brin--Thompson construction. -/
abbrev Cube (X : Type u) := X → Stream' Bool

/-- A dyadic brick has only finitely many nonempty coordinate prefixes. -/
structure Prefix (X : Type u) where
  word : X → List Bool
  finite_support : {x | word x ≠ []}.Finite

namespace Prefix
variable {X : Type u}

def empty : Prefix X := ⟨fun _ => [], by simp⟩

def attach (p : Prefix X) (z : Cube X) : Cube X :=
  fun x => Stream'.appendStream' (p.word x) (z x)

@[simp] theorem empty_attach (z : Cube X) : empty.attach z = z := by
  funext x
  exact Stream'.nil_append_stream _

theorem attach_injective (p : Prefix X) : Function.Injective p.attach := by
  intro z w he
  funext x
  exact Stream'.append_right_injective (p.word x) (z x) (w x) (congrFun he x)

end Prefix

variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]

/-- Coordinate permutation by the input group; precomposition is contravariant. -/
def twist (g : Γ) : Equiv.Perm (Cube X) where
  toFun z x := z (g⁻¹ • x)
  invFun z x := z (g • x)
  left_inv z := by funext x; simp
  right_inv z := by funext x; simp

@[simp] lemma twist_apply (g : Γ) (z : Cube X) (x : X) :
    twist g z x = z (g⁻¹ • x) := rfl

@[simp] lemma twist_one : twist (1 : Γ) = (1 : Equiv.Perm (Cube X)) := by
  ext z x n
  simp

lemma twist_mul (g h : Γ) : twist (g*h) = twist (X:=X) g * twist h := by
  ext z x n
  simp [mul_smul]

def twistHom : Γ →* Equiv.Perm (Cube X) where
  toFun := twist
  map_one' := twist_one
  map_mul' := twist_mul

theorem twist_injective [FaithfulSMul Γ X] : Function.Injective (twistHom (Γ:=Γ) (X:=X)) := by
  classical
  intro g h he
  have hcoord (x : X) : g⁻¹ • x = h⁻¹ • x := by
    by_contra hn
    let z : Cube X := fun y _ => if y=g⁻¹ • x then true else false
    have he' := congrFun (congrFun (Equiv.congr_fun he z) x) 0
    change (if g⁻¹ • x=g⁻¹ • x then true else false) =
      (if h⁻¹ • x=g⁻¹ • x then true else false) at he'
    simp [Ne.symm hn] at he'
  exact inv_injective (eq_of_smul_eq_smul hcoord)

/-- The elementary swap in a single cube coordinate. -/
def bitFlip (x : X) : Equiv.Perm (Cube X) := by
  classical
  exact {
    toFun := fun z y n => if y=x ∧ n=0 then !(z y n) else z y n
    invFun := fun z y n => if y=x ∧ n=0 then !(z y n) else z y n
    left_inv := by intro z; funext y n; by_cases h : y=x ∧ n=0 <;> simp [h]
    right_inv := by intro z; funext y n; by_cases h : y=x ∧ n=0 <;> simp [h] }

@[simp] lemma bitFlip_apply (x : X) (z : Cube X) (y : X) (n : ℕ) :
    bitFlip x z y n = if y=x ∧ n=0 then !(z y n) else z y n := rfl

end

universe u v
attribute [local instance] Classical.propDecidable

end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes.DisplacementCommutator
universe u v
variable {G : Type u} [Group G] {Y : Type v}

/-- A permutation is supported in a set when it fixes its complement pointwise. -/
def Supported (ρ : G →* Equiv.Perm Y) (s : Set Y) (g : G) : Prop :=
  ∀ x, x∉s → ρ g x=x

end FiniteAlgebraicEnvelopes.DisplacementCommutator

end

end OAI
end

section
-- module Solutions.OAIFAE.Trees
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Coordinate grids, binary trees, and tree-pair representatives.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma count_flatMap_ge {I : Type*} (f : I → List X) (l : List I) {i : I}
    (hi : i∈l) (x : X) : (f i).count x≤(l.flatMap f).count x := by
  classical
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.flatMap_cons,List.count_append]
    rcases List.mem_cons.mp hi with rfl|hi
    · omega
    · exact (ih hi).trans (Nat.le_add_left _ _)

end Prefix
end

section
universe u v
attribute [local instance] Classical.propDecidable

/-- A finite coloured binary splitting forest with one root. -/
inductive Tree (X : Type v) : Type v
  | leaf : Tree X
  | split : X → Tree X → Tree X → Tree X

namespace Tree
variable {X : Type v}

/-- Leaf indices stay in the small universe, even for large colour sets. -/
abbrev Leaves : Tree X → Type
  | .leaf => PUnit
  | .split _ a b => Leaves a ⊕ Leaves b

instance leaves_fintype (t : Tree X) : Fintype t.Leaves := by
  induction t with
  | leaf => exact inferInstanceAs (Fintype PUnit)
  | split x a b ha hb =>
    letI : Fintype a.Leaves := ha
    letI : Fintype b.Leaves := hb
    exact inferInstanceAs (Fintype (a.Leaves ⊕ b.Leaves))

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
namespace Prefix
variable {X : Type v}

lemma count_repeated_nodup (l : List X) (hl : l.Nodup) (n : X → ℕ) (x : X) :
    (l.flatMap (fun y => List.replicate (n y) y)).count x=if x∈l then n x else 0 := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha,hl⟩ := List.nodup_cons.mp hl
    rw [List.flatMap_cons,List.count_append,ih hl]
    by_cases hxa : x=a
    · subst x; simp [ha]
    · simp [hxa,Ne.symm hxa,List.count_replicate]

end Prefix
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.Generators
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Concrete finite generators of the twisted group.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Tree

abbrev linear (x : X) : ℕ → Tree X
  | 0 => .leaf
  | n+1 => .split x .leaf (linear x n)

end Tree
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators

/-- Use one fixed equality decision so dependent comb induction does not change
which decision procedure is stored in a transposition. The permutation is the
usual Mathlib transposition. -/
abbrev fixedSwap {A : Type*} (a b : A) : Equiv.Perm A :=
  @Equiv.swap A (Classical.decEq A) a b

end Generators
end

section
universe u v
attribute [local instance] Classical.propDecidable
variable {Γ : Type u} {X : Type v} [Group Γ] [MulAction Γ X]
namespace Generators
variable (x : X) [MulAction.IsPretransitive Γ X]

lemma swap_eq_fixedSwap {A : Type*} [DecidableEq A] (a b : A) :
    Equiv.swap a b = fixedSwap a b := by
  ext z
  by_cases h : z=a <;> by_cases k : z=b <;> simp [fixedSwap, Equiv.swap_apply_def,h,k]

lemma fixedSwap_self {A : Type*} (a : A) : fixedSwap a a = 1 := by
  simp only [fixedSwap, Equiv.swap_self]
  rfl

lemma fixedSwap_comm {A : Type*} (a b : A) : fixedSwap a b = fixedSwap b a := by
  exact Equiv.swap_comm a b

lemma sum_swap_right {A B : Type} (i j : B) :
    Equiv.sumCongr (Equiv.refl A) (fixedSwap i j)=
      fixedSwap (Sum.inr i) (Sum.inr j) := by
  classical
  apply Equiv.ext
  intro z
  cases z with
  | inl z => simp [Equiv.swap_apply_def]
  | inr z => simp only [Equiv.sumCongr_apply,Equiv.swap_apply_def]; split_ifs <;> simp_all [Equiv.swap_apply_def]

end Generators
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.FinitePresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Finite presentation seeds, localization, and structural relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe u v
attribute [local instance] Classical.propDecidable

lemma commute_homs_of_generators {K H : Type*} [Group K] [Group H]
    (s : Set K) (hs : Subgroup.closure s=⊤) (a b : K →* H)
    (h : ∀ i∈s,∀ j∈s,Commute (a i) (b j)) (g k : K) : Commute (a g) (b k) := by
  have hg : g∈Subgroup.closure s := by rw [hs]; trivial
  have hk : k∈Subgroup.closure s := by rw [hs]; trivial
  refine Subgroup.closure_induction₂ (p:=fun g k _ _ => Commute (a g) (b k))
    (fun i j hi hj => h i hi j hj) ?_ ?_ ?_ ?_ ?_ ?_ hg hk
  · intro z _; simpa only [map_one] using Commute.one_left (b z)
  · intro z _; simpa only [map_one] using Commute.one_right (a z)
  · intro i j z _ _ _ hi hj
    simpa only [map_mul] using hi.mul_left hj
  · intro i j z _ _ _ hi hj
    simpa only [map_mul] using hi.mul_right hj
  · intro i j _ _ hi
    simpa only [map_inv] using hi.inv_left
  · intro i j _ _ hi
    simpa only [map_inv] using hi.inv_right

end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

namespace FiniteAlgebraicEnvelopes
namespace FiniteLocalizationClosure
universe u v
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Group K]
variable (f : K →* K) (a : K) (s r : Finset K)

/-- The discrepancy between twice-localizing and conjugating a localization. -/
def discrepancy (g : K) : K := f (f g) * (a * f g * a⁻¹)⁻¹

def baseRelations : Finset K := r ∪ s.image (discrepancy f a)
def relations : Finset K := baseRelations f a s r ∪ (baseRelations f a s r).image f

def kernel : Subgroup K := Subgroup.normalClosure (relations f a s r : Set K)
instance instNormalKernel : (kernel f a s r).Normal := Subgroup.normalClosure_normal
abbrev Quotient := K ⧸ kernel f a s r

def project : K →* Quotient f a s r := QuotientGroup.mk' _

lemma project_base {g : K} (hg : g∈baseRelations f a s r) : project f a s r g=1 :=
  (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Finset.mem_union_left _ hg))

lemma project_local_base {g : K} (hg : g∈baseRelations f a s r) : project f a s r (f g)=1 :=
  (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩)))

variable (hs : Subgroup.closure (s : Set K)=⊤)
include hs

lemma twice_eq_conjugate (g : K) :
    project f a s r (f (f g))=project f a s r (a * f g * a⁻¹) := by
  have he : (project f a s r).comp (f.comp f)=
      (project f a s r).comp ((MulAut.conj a).toMonoidHom.comp f) := by
    apply MonoidHom.eq_of_eqOn_dense hs
    intro k hk
    have h := project_base f a s r (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k,hk,rfl⟩))
    change project f a s r (f (f k) * (a*f k*a⁻¹)⁻¹)=1 at h
    rw [map_mul,map_inv] at h
    exact mul_inv_eq_one.mp h
  exact DFunLike.congr_fun he g

/-- Adding a finite set of relations, their first localizations, and the finite
self-similarity checks suffices to make the entire normal closure stable under f.
No infinitely iterated family is silently assumed finite. -/
lemma kernel_stable : kernel f a s r ≤ (kernel f a s r).comap f := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact Subgroup.subset_normalClosure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g,hg,rfl⟩))
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hg
    change f (f k)∈kernel f a s r
    apply (QuotientGroup.eq_one_iff _).mp
    change project f a s r (f (f k))=1
    rw [twice_eq_conjugate f a s r hs,map_mul,map_mul,map_inv,project_local_base f a s r hk]
    simp

def localization : Quotient f a s r →* Quotient f a s r :=
  QuotientGroup.map _ _ f (kernel_stable f a s r hs)

lemma localization_project (g : K) :
    localization f a s r hs (project f a s r g)=project f a s r (f g) := rfl

variable {H : Type v} [Group H]
variable (e : K →* H) (l : H →* H)
variable (he : ∀ g,e (f g)=l (e g))
variable (hl : ∀ h,l (l h)=e a*l h*(e a)⁻¹)
variable (hr : ∀ g∈r,e g=1)
include he hl hr

omit hs in
lemma relations_valid : (relations f a s r : Set K) ⊆ (e.ker : Set K) := by
  have hb : ∀ g∈baseRelations f a s r,e g=1 := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg|hg
    · exact hr g hg
    · obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hg
      change e (f (f k) * (a*f k*a⁻¹)⁻¹)=1
      simp only [map_mul,map_inv,he,hl,mul_inv_cancel]
  intro g hg
  rcases Finset.mem_union.mp hg with hg|hg
  · exact hb g hg
  · obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hg
    change e (f k)=1
    rw [he,hb k hk,map_one]

omit hs in
def evaluate : Quotient f a s r →* H :=
  QuotientGroup.lift _ e (Subgroup.normalClosure_le_normal (relations_valid f a s r e l he hl hr))

omit hs in
lemma evaluate_surjective (he_surj : Function.Surjective e) :
    Function.Surjective (evaluate f a s r e l he hl hr) := by
  intro h
  obtain ⟨g,hg⟩ := he_surj h
  exact ⟨QuotientGroup.mk g,hg⟩

end FiniteLocalizationClosure
end FiniteAlgebraicEnvelopes

end

end OAI
end

section
-- module Solutions.OAIFAE.TreeRefinement
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Tree prefixes, common refinements, and quotient refinement relations.
-/

namespace FiniteAlgebraicEnvelopes.TwistedBrinThompson

section
universe v
attribute [local instance] Classical.propDecidable
namespace Tree
variable {X : Type v}

/-- Syntactic coherence generated exclusively by commuting two different
coordinate splits. No semantic equality is admitted as a generating relation. -/
inductive Coherent : Tree X → Tree X → Prop
  | refl (t) : Coherent t t
  | symm {s t} : Coherent s t → Coherent t s
  | trans {r s t} : Coherent r s → Coherent s t → Coherent r t
  | split (x) {a b c d} : Coherent a c → Coherent b d →
      Coherent (.split x a b) (.split x c d)
  | interchange {x y : X} (hxy : x≠y) (a b c d) :
      Coherent (.split x (.split y a b) (.split y c d))
        (.split y (.split x a c) (.split x b d))

end Tree
end

universe u v
attribute [local instance] Classical.propDecidable
end FiniteAlgebraicEnvelopes.TwistedBrinThompson

end

end OAI
end

section
-- module Solutions.OAIFAE.DecoratedPresentation
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Stabilizer cocycles, decorations, and explicit finite endpoint relations.
-/

namespace FiniteAlgebraicEnvelopes.FiniteLocalizationClosure
universe u
attribute [local instance] Classical.propDecidable
variable {K : Type u} [Group K] (f : K →* K) (a : K) (s : Finset K)
variable {r r' : Finset K} (h : r ⊆ r')
include h

lemma baseRelations_mono : baseRelations f a s r ⊆ baseRelations f a s r' :=
  Finset.union_subset_union h (Finset.Subset.refl _)

lemma relations_mono : relations f a s r ⊆ relations f a s r' :=
  Finset.union_subset_union (baseRelations_mono f a s h)
    (Finset.image_subset_image (baseRelations_mono f a s h))

lemma kernel_mono : kernel f a s r ≤ kernel f a s r' :=
  Subgroup.normalClosure_mono (relations_mono f a s h)

def quotientMap : Quotient f a s r →* Quotient f a s r' :=
  QuotientGroup.map _ _ (MonoidHom.id K) (kernel_mono f a s h)

lemma quotientMap_project (g : K) :
    quotientMap f a s h (project f a s r g)=project f a s r' g := rfl

lemma quotientMap_surjective : Function.Surjective (quotientMap f a s h) := by
  intro z
  obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective z
  exact ⟨QuotientGroup.mk g,rfl⟩

lemma quotientMap_localization (hs : Subgroup.closure (s : Set K)=⊤) (z : Quotient f a s r) :
    quotientMap f a s h (localization f a s r hs z)=
      localization f a s r' hs (quotientMap f a s h z) := by
  obtain ⟨g,hg⟩ := QuotientGroup.mk_surjective z
  change project f a s r g=z at hg
  rw [← hg,localization_project,quotientMap_project,quotientMap_project,localization_project]

end FiniteAlgebraicEnvelopes.FiniteLocalizationClosure

namespace FiniteAlgebraicEnvelopes.StabilizerCocycle
universe u v w
variable {Γ : Type u} {X : Type v} {H : Type w}
variable [Group Γ] [MulAction Γ X] [Group H]
variable (x : X) (R D : Γ →* H)
variable (hfixed : ∀ k : MulAction.stabilizer Γ x,R k.val=D k.val)
include hfixed

/-- The difference of two copies of the acting group descends to its orbit
when those copies agree on the point stabilizer. -/
lemma equal_of_smul_eq {g h : Γ} (he : g • x=h • x) :
    R g * (D g)⁻¹=R h * (D h)⁻¹ := by
  have hk : h⁻¹*g∈MulAction.stabilizer Γ x := by
    change (h⁻¹*g) • x=x
    rw [mul_smul,he,inv_smul_smul]
  have hf := hfixed ⟨h⁻¹*g,hk⟩
  change R (h⁻¹*g)=D (h⁻¹*g) at hf
  simp only [map_mul,map_inv] at hf
  have hr : R g=R h*((D h)⁻¹*D g) := by
    rw [← hf]
    group
  rw [hr]
  group

variable [MulAction.IsPretransitive Γ X]

omit hfixed in
/-- The orbit-indexed difference; the selected representative is immaterial. -/
def value (y : X) : H :=
  let g := (MulAction.exists_smul_eq Γ x y).choose
  R g * (D g)⁻¹

lemma value_smul (g : Γ) : value x R D (g • x)=R g*(D g)⁻¹ :=
  equal_of_smul_eq x R D hfixed (MulAction.exists_smul_eq Γ x (g • x)).choose_spec

lemma value_base : value x R D x=1 := by
  simpa only [one_smul,map_one,inv_one,mul_one] using value_smul x R D hfixed (1 : Γ)

/-- Exact covariance of the orbit-indexed difference. -/
lemma covariance (g : Γ) (y : X) :
    R g*value x R D y=value x R D (g • y)*D g := by
  obtain ⟨h,rfl⟩ := MulAction.exists_smul_eq Γ x y
  rw [← mul_smul,value_smul x R D hfixed,value_smul x R D hfixed]
  simp only [map_mul,mul_inv_rev]
  group

end FiniteAlgebraicEnvelopes.StabilizerCocycle

end

end OAI
end

section
-- module Solutions.OAIFAE.EndpointCoherence
attribute [-instance] _root_.OAI.FiniteAlgebraicEnvelopes.LiftedAction.faithful
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-!
Associators, symmetries, coordinate invariance, and coherence of endpoint quotient data.
-/

namespace FiniteAlgebraicEnvelopes
universe u v w
variable {Γ : Type u} {X : Type v} {H : Type w} [Group Γ] [MulAction Γ X] [Group H]

/-- A grid relation propagates along ordered-pair orbits, because the middle
transposition commutes with four identical leaf labels. -/
theorem covariant_interchange (R D : Γ → H) (E : X → X → H) (M : H)
    (hc : ∀ g a b,R g*E a b=E (g • a) (g • b)*D g)
    (hm : ∀ g,Commute M (D g))
    {a b c d : X} (g : Γ) (hga : g • a=c) (hgb : g • b=d)
    (hab : E a b=E b a*M) : E c d=E d c*M := by
  apply mul_right_cancel (b:=D g)
  calc
    E c d*D g=R g*E a b := by rw [hc,hga,hgb]
    _=R g*(E b a*M) := by rw [hab]
    _=(E d c*D g)*M := by rw [← mul_assoc,hc,hga,hgb]
    _=(E d c*M)*D g := by rw [mul_assoc,← (hm g).eq,← mul_assoc]

end FiniteAlgebraicEnvelopes

end

end OAI
end


