-- Prove2me | Definitions.Def_NuclearUltrapower
-- name    : NuclearUltrapower
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:20.18496+00:00
-- url     : https://prove2.me/theorems/b00dca11-a32c-439b-897e-4a264f05b363
-- statement:
--   Dyadic is the ring Z[1/2] (the localization of the integers away from 2), Vector3 is the module of triples over it, and SL3Z is the group of 3x3 integer matrices of determinant 1. The group G is the semidirect product of the additive group of Vector3 (written multiplicatively) by SL3Z × Z, where (M,k) acts on a vector by applying M and then multiplying by 2^k; this is checked to be a group action by automorphisms. For a C*-algebra B and a free ultrafilter ω on the natural numbers (free meaning no finite set belongs to ω), BoundedSeq is the algebra of bounded B-valued sequences with the supremum norm, two sequences are identified when their difference tends to 0 along ω, and NormUltrapower B ω is the resulting quotient star algebra, the norm ultrapower. Complex Hilbert spaces are bundled without any separability assumption. For two non-unital C*-algebras, the minimal tensor norm of an element of the algebraic tensor product is the supremum of its operator norms under spatial representations on a tensor product of Hilbert spaces, and the maximal tensor norm is the supremum over pairs of representations on one Hilbert space with commuting ranges. B is nuclear if, for every non-unital C*-algebra C (not necessarily unital, nonzero or separable) and every tensor x in B⊗C, these two norms agree. A nonzero unital C*-algebra is bundled as UnitalCStar. IsFullGroupAlgebra(A,ι) says that the unitary representation ι of G in A has dense linear span and that every unitary representation of G in a unital C*-algebra D extends uniquely to a unital star homomorphism A→D, so A is the full group C*-algebra. The Cuntz relations for two elements s₀,s₁ say that each is an isometry (s_i*s_i=1) and that s₀s₀*+s₁s₁*=1, and IsCuntzTwoAlgebra says O satisfies them and is universal for them, with unique unital star homomorphisms to any other algebra satisfying them. MainStatementWithCuntzCorollary is a defined proposition, not an established theorem. It asserts that there exist a full group C*-algebra A of G that is separable, such that for every nuclear unital C*-algebra B and every free ultrafilter ω there is no injective unital star homomorphism from A into the norm ultrapower of B, and moreover there exists a Cuntz algebra O_2 for which, for every free ultrafilter, A does not embed injectively into the norm ultrapower of O_2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/NuclearUltrapower.lean; bytes 16..9109
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section
universe u v w
open Filter
open scoped TensorProduct Topology
namespace NuclearUltrapower

/- The dyadic coefficient ring is exactly Z[1/2]. -/
abbrev Dyadic := Localization.Away (2 : ℤ)
abbrev Vector3 := Fin 3 → Dyadic
abbrev SL3Z := Matrix.SpecialLinearGroup (Fin 3) ℤ

noncomputable def dyadicTwo : Dyadicˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := Dyadic) (2 : ℤ) (dvd_refl _)).unit

noncomputable def matrixAction (M : SL3Z) : Vector3 ≃ₗ[Dyadic] Vector3 :=
  Matrix.SpecialLinearGroup.toLin'
    (Matrix.SpecialLinearGroup.map (Int.castRingHom Dyadic) M)

noncomputable def dilationAction (g : SL3Z × Multiplicative ℤ) :
    Vector3 ≃ₗ[Dyadic] Vector3 :=
  (matrixAction g.1).trans (LinearEquiv.smulOfUnit (dyadicTwo ^ g.2.toAdd))

noncomputable def groupAction :
    (SL3Z × Multiplicative ℤ) →* MulAut (Multiplicative Vector3) where
  toFun g := AddEquiv.toMultiplicative (dilationAction g).toAddEquiv
  map_one' := by
    ext v i
    simp [dilationAction, matrixAction, LinearEquiv.smulOfUnit]
  map_mul' g h := by
    ext v i
    simp [dilationAction, matrixAction, LinearEquiv.smulOfUnit, zpow_add,
      map_mul, mul_smul, Units.smul_def, mul_left_comm]

/-- The exact group of the semidirect-product construction. -/
abbrev G := SemidirectProduct (Multiplicative Vector3)
  (SL3Z × Multiplicative ℤ) groupAction

section UltrapowerDefinition
variable (B : Type u) [CStarAlgebra B] (ω : Ultrafilter ℕ)

/-- Bounded sequences, with their supremum norm. N is discrete. -/
abbrev BoundedSeq := BoundedContinuousFunction ℕ B

/-- Equality modulo I_omega(B). This is equivalent to norm-null difference. -/
def ultraRel (x y : BoundedSeq B) : Prop :=
  Tendsto (fun n => x n - y n) (ω : Filter ℕ) (𝓝 0)

/-- The ring congruence defining the norm (not algebraic) ultrapower. -/
def ultraCon : RingCon (BoundedSeq B) where
  r := ultraRel B ω
  iseqv := {
    refl := fun x => by simp [ultraRel]
    symm := fun {x y} h => by
      simpa only [ultraRel, neg_sub, neg_zero] using h.neg
    trans := fun {x y z} hxy hyz => by
      simpa only [ultraRel, sub_add_sub_cancel, zero_add] using hxy.add hyz }
  add' := by
    intro x y z t hxy hzt
    simpa only [ultraRel, BoundedContinuousFunction.add_apply, ← add_sub_add_comm, zero_add]
      using hxy.add hzt
  mul' := by
    intro x y z t hxy hzt
    have h₁ := hxy.zero_mul_isBoundedUnder_le (Filter.isBoundedUnder_of ⟨‖z‖, fun index => z.norm_coe_le_norm index⟩)
    have h₂ := Filter.isBoundedUnder_le_mul_tendsto_zero (Filter.isBoundedUnder_of ⟨‖y‖, fun index => y.norm_coe_le_norm index⟩) hzt
    simpa only [ultraRel, BoundedContinuousFunction.mul_apply, sub_mul, mul_sub,
      sub_add_sub_cancel, zero_add] using h₁.add h₂

/-- The exact quotient l-infinity(N,B)/I_omega(B) as a complex star algebra.
The quotient identifies sequences whose difference tends to zero along the ultrafilter. -/
abbrev NormUltrapower := (ultraCon B ω).Quotient

instance : Star (NormUltrapower B ω) where
  star := Quotient.map' star (fun first second hypothesis => by
    change ultraRel B ω (star first) (star second)
    simpa only [ultraRel, star_sub, star_zero, BoundedContinuousFunction.star_apply] using hypothesis.star)

instance : StarRing (NormUltrapower B ω) where
  star_involutive := by
    intro x
    induction x using Quotient.inductionOn with | h x =>
      exact congrArg Quotient.mk'' (star_star x)
  star_mul := by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg Quotient.mk'' (star_mul x y)
  star_add := by
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact congrArg Quotient.mk'' (star_add x y)

instance : StarModule ℂ (NormUltrapower B ω) where
  star_smul := by
    intro c x
    induction x using Quotient.inductionOn with | h x =>
      exact congrArg Quotient.mk'' (star_smul c x)

/-- Freeness: no finite subset of N belongs to the ultrafilter. -/
def IsFree (ω : Ultrafilter ℕ) : Prop :=
  ∀ F : Finset ℕ, (F : Set ℕ) ∉ (ω : Filter ℕ)

end UltrapowerDefinition

/-- A bundled complex Hilbert space, without any separability assumption. -/
structure ComplexHilbert where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] ComplexHilbert.normed ComplexHilbert.inner ComplexHilbert.complete
instance : CoeSort ComplexHilbert (Type u) := ⟨ComplexHilbert.carrier⟩

section TensorNormDefinitions
variable {B : Type u} {C : Type v} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

/-- Spatial evaluation of the algebraic tensor product on separate Hilbert spaces.
Its operator norm is unchanged on the Hilbert completion. -/
def spatialEval (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    B ⊗[ℂ] C →ₗ[ℂ] ((H ⊗[ℂ] K) →L[ℂ] (H ⊗[ℂ] K)) :=
  TensorProduct.lift (LinearMap.mk₂ ℂ (fun b c => TensorProduct.mapL (ρ b) (σ c))
    (by intros; simp [TensorProduct.mapL_add_left])
    (by intros; simp [TensorProduct.mapL_smul_left])
    (by intros; simp [TensorProduct.mapL_add_right])
    (by intros; simp [TensorProduct.mapL_smul_right]))

/-- Evaluation on one Hilbert space; used only when the two ranges commute. -/
def commutingEval (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    B ⊗[ℂ] C →ₗ[ℂ] (H →L[ℂ] H) :=
  (LinearMap.mul' ℂ (H →L[ℂ] H)).comp
    (TensorProduct.map
      (show B →ₗ[ℂ] (H →L[ℂ] H) from
        { toFun := ρ, map_add' := map_add ρ, map_smul' := map_smul ρ })
      (show C →ₗ[ℂ] (H →L[ℂ] H) from
        { toFun := σ, map_add' := map_add σ, map_smul' := map_smul σ }))

/-- The minimal C*-tensor norm: supremum over spatial representations. -/
def minTensorNorm (x : B ⊗[ℂ] C) : ℝ :=
  sSup {r | ∃ (H K : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (K →L[ℂ] K)),
    r = ‖spatialEval H K ρ σ x‖}

/-- The maximal C*-tensor norm: supremum over commuting representations. -/
def maxTensorNorm (x : B ⊗[ℂ] C) : ℝ :=
  sSup {r | ∃ (H : ComplexHilbert.{w})
    (ρ : B →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (σ : C →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
    (∀ b c, Commute (ρ b) (σ c)) ∧ r = ‖commutingEval H ρ σ x‖}

/-- Nuclearity in the tensor-norm convention of the tensor-norm formulation.
The second C*-algebra need not be unital, nonzero, or separable. -/
def IsNuclear (B : Type u) [NonUnitalCStarAlgebra B] : Prop :=
  ∀ (C : Type v) [NonUnitalCStarAlgebra C] (x : B ⊗[ℂ] C),
    minTensorNorm.{u, v, max u v} x = maxTensorNorm.{u, v, max u v} x
end TensorNormDefinitions

/-- A nonzero unital complex C*-algebra. -/
structure UnitalCStar where
  carrier : Type u
  [cstar : CStarAlgebra carrier]
  [nontrivial : Nontrivial carrier]
attribute [instance] UnitalCStar.cstar UnitalCStar.nontrivial
instance : CoeSort UnitalCStar (Type u) := ⟨UnitalCStar.carrier⟩

/-- The universal property defining the full, not the reduced, group C*-algebra.
The dense generation clause makes the intended completion explicit.
This is definition data, not a hypothesis silently supplied to the main claim. -/
def IsFullGroupAlgebra (A : UnitalCStar.{u}) (ι : G →* unitary A) : Prop :=
  Dense (Submodule.span ℂ (Set.range (fun g => (ι g : A))) : Set A) ∧
  ∀ (D : UnitalCStar.{u}) (ρ : G →* unitary D),
    ∃! φ : A →⋆ₐ[ℂ] D, ∀ g, φ (ι g) = (ρ g : D)

/-- The two Cuntz relations, including unit preservation explicitly. -/
def CuntzTwoRelations {D : Type u} [CStarAlgebra D] (s : Fin 2 → D) : Prop :=
  (∀ i, star (s i) * s i = 1) ∧ ∑ i, s i * star (s i) = 1

/-- The universal nonzero unital C*-algebra on the two Cuntz isometries. -/
def IsCuntzTwoAlgebra (O : UnitalCStar.{u}) (s : Fin 2 → O) : Prop :=
  CuntzTwoRelations s ∧
  ∀ (D : UnitalCStar.{u}) (r : Fin 2 → D), CuntzTwoRelations r →
    ∃! φ : O →⋆ₐ[ℂ] D, ∀ i, φ (s i) = r i

/-- The manuscript's main statement including its explicitly stated O_2
corollary. Both universal C*-algebras must be constructed to prove this. -/
def MainStatementWithCuntzCorollary : Prop :=
  ∃ (A : UnitalCStar.{u}) (ι : G →* unitary A),
    IsFullGroupAlgebra A ι ∧ TopologicalSpace.SeparableSpace A ∧
    (∀ (B : UnitalCStar.{u}), IsNuclear.{u, u} B →
      ∀ (ω : Ultrafilter ℕ), IsFree ω →
        ¬ ∃ φ : A →⋆ₐ[ℂ] NormUltrapower B ω, Function.Injective φ) ∧
    ∃ (O : UnitalCStar.{u}) (s : Fin 2 → O), IsCuntzTwoAlgebra O s ∧
      ∀ (ω : Ultrafilter ℕ), IsFree ω →
        ¬ ∃ φ : A →⋆ₐ[ℂ] NormUltrapower O ω, Function.Injective φ

end NuclearUltrapower
end

namespace NuclearUltrapower



end NuclearUltrapower
end OAI


