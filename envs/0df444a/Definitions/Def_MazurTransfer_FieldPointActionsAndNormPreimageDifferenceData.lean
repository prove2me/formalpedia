-- Prove2me | Definitions.Def_MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
-- name    : MazurTransfer_FieldPointActionsAndNormPreimageDifferenceData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T21:47:09.024517+00:00
-- url     : https://prove2.me/theorems/94a7bea3-a674-4758-8338-e157979f2993
-- title:
--   Field automorphism actions on over-category points and equivariant preimage differences
-- statement:
--   Let R be a commutative ring, K an R-algebra field, and X a scheme over Spec R. Pullback along the spectrum automorphism of K defines the original field-automorphism action on X(K). Retain its complete original constructors, composition laws, action homomorphisms for group objects, and scalar extension of rational points. For a group with an action, retain the difference sigma(b) b inverse. The named downstream consumers are the actual rational Picard norm Kummer actions and preimage cocycles. All twelve original full types and all six non-proof constructor values are preserved.
-- source:
--   Original MazurTheorem FieldAutomorphismOverPointAction complete module and EquivariantNormPreimageCocycle.difference constructor. Apache-2.0; retains original headers. Design boundary: point action and immediate functoriality laws plus the preimage-difference constructor; named downstream consumer: Order13ActualPicardNormKummerCocycles.

/-
Generic constructor boundary: retain the original field-point automorphism
maps, their immediate functoriality laws, and the original preimage-difference
function. Named downstream consumers: the original actual Picard norm
Kummer actionHom, rationalPoint and difference constructors.
The two original per-file copyright and provenance headers are retained below.
-/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an algebra automorphism acts on field-valued points
by precomposition with its spectrum map, preserving base maps.
Named downstream consumer: actual Picard norm Kummer cocycles.
-/
import Mathlib

noncomputable section
namespace MazurTransfer.FieldAutomorphismOverPointAction
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

abbrev fieldBase : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

def fieldAut (σ : K ≃ₐ[R] K) : Over.mk (fieldBase R K) ⟶ Over.mk (fieldBase R K) :=
  Over.homMk (Spec.map (CommRingCat.ofHom σ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) = _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact σ.commutes a)

theorem fieldAut_one : fieldAut R K 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((1 : K ≃ₐ[R] K).toRingHom)) = 𝟙 _
  have h : CommRingCat.ofHom ((1 : K ≃ₐ[R] K).toRingHom) = 𝟙 _ := by
    ext a
    rfl
  rw [h, Spec.map_id]

theorem fieldAut_mul (σ τ : K ≃ₐ[R] K) :
    fieldAut R K (σ * τ) = fieldAut R K σ ≫ fieldAut R K τ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom ((σ * τ).toRingHom)) =
    Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom τ.toRingHom)
  rw [← Spec.map_comp]
  congr 1

variable {R K}
variable {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of R))

def act (σ : K ≃ₐ[R] K) (a : Over.mk (fieldBase R K) ⟶ Over.mk t) :=
  fieldAut R K σ ≫ a

theorem act_one (a : Over.mk (fieldBase R K) ⟶ Over.mk t) : act t 1 a = a := by
  rw [act, fieldAut_one, Category.id_comp]

theorem act_mul (σ τ : K ≃ₐ[R] K) (a : Over.mk (fieldBase R K) ⟶ Over.mk t) :
    act t (σ * τ) a = act t σ (act t τ a) := by
  simp only [act, fieldAut_mul, Category.assoc]

theorem act_comp (σ : K ≃ₐ[R] K) (a : Over.mk (fieldBase R K) ⟶ Over.mk t)
    (φ : Over.mk t ⟶ Over.mk t) :
    act t σ (a ≫ φ) = act t σ a ≫ φ := (Category.assoc _ _ _).symm

variable [GrpObj (Over.mk t)]

def actHom (σ : K ≃ₐ[R] K) :
    (Over.mk (fieldBase R K) ⟶ Over.mk t) →* (Over.mk (fieldBase R K) ⟶ Over.mk t) where
  toFun := act t σ
  map_one' := MonObj.comp_one _
  map_mul' a b := MonObj.comp_mul _ a b

def rationalPoint (a : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk t) :
    Over.mk (fieldBase R K) ⟶ Over.mk t :=
  (Over.homMk (fieldBase R K) (by simp) :
    Over.mk (fieldBase R K) ⟶ Over.mk (𝟙 (Spec (CommRingCat.of R)))) ≫ a

theorem rationalPoint_fixed (σ : K ≃ₐ[R] K)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk t) :
    act t σ (rationalPoint t a) = rationalPoint t a := by
  unfold act rationalPoint
  rw [← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact Over.w (fieldAut R K σ)

end MazurTransfer.FieldAutomorphismOverPointAction
#print axioms MazurTransfer.FieldAutomorphismOverPointAction.fieldAut_mul
#print axioms MazurTransfer.FieldAutomorphismOverPointAction.actHom
#print axioms MazurTransfer.FieldAutomorphismOverPointAction.rationalPoint_fixed

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a preimage of an invariant point under an equivariant
endomorphism gives a kernel-valued cocycle; another preimage changes it
by a kernel coboundary. Named downstream consumer: actual Picard norms.
-/
namespace MazurTransfer.EquivariantNormPreimageCocycle
variable {G H : Type*} [Group G] [CommGroup H]
variable (ρ : G → H →* H) (f : H →* H)

def difference (b : H) (σ : G) : H := ρ σ b * b⁻¹


end MazurTransfer.EquivariantNormPreimageCocycle
#print axioms MazurTransfer.EquivariantNormPreimageCocycle.difference


