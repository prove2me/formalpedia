-- Prove2me | Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
-- name    : ReciprocityTheory_NeutralLocalFields_Reciprocity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:07.717873+00:00
-- url     : https://prove2.me/theorems/2f338c00-90ca-4a17-a6ce-5b75164d5e79
-- title:
--   Reciprocity
-- statement:
--   Definitions and structural lemmas for Reciprocity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/Reciprocity.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Topology
namespace Neutral.B1
section Galois
variable (F : Type*) [Field F]
structure IsFiniteAbelian (L : IntermediateField F (AlgebraicClosure F)) : Prop where
  finiteDimensional : FiniteDimensional F L
  isGalois : IsGalois F L
  comm : ∀ a b : L ≃ₐ[F] L, a * b = b * a
def toAb : Field.absoluteGaloisGroup F →* Field.absoluteGaloisGroupAbelianization F :=
  QuotientGroup.mk' _
def abRestrict (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L) :
    Field.absoluteGaloisGroupAbelianization F →* (L ≃ₐ[F] L) :=
  haveI := h.finiteDimensional
  haveI := h.isGalois
  letI : CommGroup (L ≃ₐ[F] L) := { (inferInstance : Group (L ≃ₐ[F] L)) with mul_comm := h.comm }
  QuotientGroup.lift _ (AlgEquiv.restrictNormalHom L : Field.absoluteGaloisGroup F →* (L ≃ₐ[F] L))
    (by
      refine Subgroup.topologicalClosure_minimal _ ?_ ?_
      · exact Abelianization.commutator_subset_ker _
      · have e : ((AlgEquiv.restrictNormalHom L : Gal(AlgebraicClosure F/F) →* (L ≃ₐ[F] L)).ker :
            Set Gal(AlgebraicClosure F/F)) = (L.fixingSubgroup : Set Gal(AlgebraicClosure F/F)) := by
          rw [IntermediateField.restrictNormalHom_ker]
        have hc : IsClosed ((AlgEquiv.restrictNormalHom L :
            Gal(AlgebraicClosure F/F) →* (L ≃ₐ[F] L)).ker : Set Gal(AlgebraicClosure F/F)) :=
          e ▸ L.fixingSubgroup_isClosed
        exact hc)
end Galois
section Local
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
def integersBar : Subalgebra 𝒪[K] (AlgebraicClosure K) :=
  integralClosure 𝒪[K] (AlgebraicClosure K)
def maxIdealBar : Set (AlgebraicClosure K) :=
  {y | y ∈ integersBar K ∧ (y = 0 ∨ y⁻¹ ∉ integersBar K)}
def IsUniformiser (π : K) : Prop :=
  ∃ hπ : π ∈ 𝒪[K], Irreducible (⟨π, hπ⟩ : 𝒪[K])
def IsFrobeniusLift (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : Prop :=
  ∀ x ∈ integersBar K, g x - x ^ Nat.card 𝓀[K] ∈ maxIdealBar K
def normGroup (L : IntermediateField K (AlgebraicClosure K)) : Subgroup Kˣ :=
  (Units.map (Algebra.norm K : L →* K)).range
def IsLocalArtinMap (Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K) : Prop :=
  Continuous Art ∧ Function.Injective Art ∧ DenseRange Art ∧
  (∀ π : Kˣ, IsUniformiser K (π : K) → ∀ g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      toAb K g = Art π →
      IsFrobeniusLift K g) ∧
  (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L),
      Function.Surjective ((abRestrict K L h).comp Art) ∧
      ((abRestrict K L h).comp Art).ker = normGroup K L)
def LocalReciprocity [IsNonarchimedeanLocalField K] : Prop :=
  ∃ Art : Kˣ →* Field.absoluteGaloisGroupAbelianization K, IsLocalArtinMap K Art
def LocalExistence [IsNonarchimedeanLocalField K] : Prop :=
  ∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
    ∃ (L : IntermediateField K (AlgebraicClosure K)) (_ : IsFiniteAbelian K L), normGroup K L = H
end Local
section Global
variable (K : Type*) [Field K] [NumberField K]
abbrev Ideles : Type _ := (AdeleRing (𝓞 K) K)ˣ
def diagUnits : Kˣ →* Ideles K :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom
abbrev IdeleClassGroup : Type _ := Ideles K ⧸ (diagUnits K).range
def IsUnramifiedIn (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L] [Algebra K L] : Prop :=
  ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal → Q.ramificationIdx (𝓞 K) = 1
def IsFrobAt (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] (τ : L ≃ₐ[K] L)
    (Q : Ideal (𝓞 L)) : Prop :=
  (galRestrict (𝓞 K) K L (𝓞 L) τ).toAlgHom.IsArithFrobAt Q
def IsComplexConjugationAt (w : InfinitePlace K) (L : Type*) [Field L] [Algebra K L]
    (τ : L ≃ₐ[K] L) : Prop :=
  ∀ φ : L →+* ℂ, φ.comp (algebraMap K L) = w.embedding →
    ∀ x : L, starRingEnd ℂ (φ x) = φ (τ x)
def IsUniformiserAt (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : Prop :=
  ∃ hx : x ∈ v.adicCompletionIntegers K, Irreducible (⟨x, hx⟩ : v.adicCompletionIntegers K)
def IsSupportedAt (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  (∀ w : InfinitePlace K, (a : AdeleRing (𝓞 K) K).1 w = 1) ∧
  ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (a : AdeleRing (𝓞 K) K).2 v' = 1
def IsGlobalArtinMap (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K) :
    Prop :=
  Continuous Art ∧ Function.Surjective Art ∧
  ((Art.ker : Set (IdeleClassGroup K)) = connectedComponent 1) ∧
  (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (v : HeightOneSpectrum (𝓞 K)), IsUnramifiedIn K v L →
      ∀ a : Ideles K, IsSupportedAt K a v →
        (IsUniformiserAt K v ((a : AdeleRing (𝓞 K) K).2 v) →
          ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
            haveI := h.finiteDimensional
            IsFrobAt K L (abRestrict K L h (Art (QuotientGroup.mk a))) Q) ∧
        (Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 →
          abRestrict K L h (Art (QuotientGroup.mk a)) = 1)) ∧
  (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (w : InfinitePlace K), w.IsReal →
      ∀ a : Ideles K, (∀ v : HeightOneSpectrum (𝓞 K), (a : AdeleRing (𝓞 K) K).2 v = 1) →
        (∀ w' : InfinitePlace K, w' ≠ w → (a : AdeleRing (𝓞 K) K).1 w' = 1) →
        (a : AdeleRing (𝓞 K) K).1 w = -1 →
        IsComplexConjugationAt K w L (abRestrict K L h (Art (QuotientGroup.mk a))))
def GlobalReciprocity : Prop :=
  ∃ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art
def GlobalExistence : Prop :=
  ∀ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art →
    ∀ H : Subgroup (IdeleClassGroup K), IsOpen (H : Set (IdeleClassGroup K)) → H.FiniteIndex →
      ∃ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L),
        ((abRestrict K L h).comp Art).ker = H
def rayUnits (m₀ : Ideal (𝓞 K)) (mInf : Set (InfinitePlace K)) : Set (Ideles K) :=
  {a | (∀ w ∈ mInf, IsSquare ((a : AdeleRing (𝓞 K) K).1 w)) ∧
    ∀ v : HeightOneSpectrum (𝓞 K),
      Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 ∧
      ∃ x ∈ m₀, Valued.v ((a : AdeleRing (𝓞 K) K).2 v - 1) ≤
        Valued.v (algebraMap K (v.adicCompletion K) (x : K))}
open Classical in

def finiteSingle (v : HeightOneSpectrum (𝓞 K)) :
    v.adicCompletion K →* FiniteAdeleRing (𝓞 K) K where
  toFun x := RestrictedProduct.mulSingle
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletionIntegers K) v x
  map_one' := RestrictedProduct.mulSingle_one _ _
  map_mul' x y := RestrictedProduct.mulSingle_mul _ _ x y
def localIdele (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* Ideles K :=
  Units.map
    { toFun := fun x => ((1 : InfiniteAdeleRing K), finiteSingle K v x)
      map_one' := Prod.ext rfl (map_one (finiteSingle K v))
      map_mul' := fun x y => Prod.ext (mul_one 1).symm (map_mul (finiteSingle K v) x y) }
def RayClassFieldExistence : Prop :=
  ∀ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art →
    ∀ m₀ : Ideal (𝓞 K), m₀ ≠ ⊥ → ∀ mInf : Set (InfinitePlace K), (∀ w ∈ mInf, w.IsReal) →
      ∃ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L),
        (∀ a : Ideles K, abRestrict K L h (Art (QuotientGroup.mk a)) = 1 ↔
          ∃ k : Kˣ, ∃ u ∈ rayUnits K m₀ mInf, a = diagUnits K k * u) ∧
        ∀ v : HeightOneSpectrum (𝓞 K), ¬ m₀ ≤ v.asIdeal → IsUnramifiedIn K v L
def localNormGroup (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L] [Algebra K L] :
    Subgroup (v.adicCompletion K)ˣ :=
  (Units.map (Algebra.norm (v.adicCompletion K) :
    TensorProduct K (v.adicCompletion K) L →* v.adicCompletion K)).range
example (v : HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    Module.Free (v.adicCompletion K) (TensorProduct K (v.adicCompletion K) L) ∧
      Module.Finite (v.adicCompletion K) (TensorProduct K (v.adicCompletion K) L) :=
  ⟨inferInstance, inferInstance⟩
open Pointwise in

def decompGroup (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] (Q : Ideal (𝓞 L)) :
    Subgroup (L ≃ₐ[K] L) :=
  (MulAction.stabilizer (𝓞 L ≃ₐ[𝓞 K] 𝓞 L) Q).comap
    (galRestrict (𝓞 K) K L (𝓞 L)).toMonoidHom
def localComposite (Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K)
    (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
    (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ →* (L ≃ₐ[K] L) :=
  (abRestrict K L h).comp
    (Art.comp ((QuotientGroup.mk' (diagUnits K).range).comp (localIdele K v)))
def LocalGlobalCompatibility : Prop :=
  ∀ Art : IdeleClassGroup K →* Field.absoluteGaloisGroupAbelianization K, IsGlobalArtinMap K Art →
    ∀ (L : IntermediateField K (AlgebraicClosure K)) (h : IsFiniteAbelian K L)
      (v : HeightOneSpectrum (𝓞 K)),
      (localComposite K Art L h v).ker = localNormGroup K v L ∧
      (∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
        haveI := h.finiteDimensional
        (localComposite K Art L h v).range = decompGroup K L Q) ∧
      (∀ π : (v.adicCompletion K)ˣ, IsUniformiserAt K v (π : v.adicCompletion K) →
        ∀ Q : Ideal (𝓞 L), Q.IsPrime → Q.LiesOver v.asIdeal →
          haveI := h.finiteDimensional
          IsFrobAt K L (localComposite K Art L h v π) Q)
end Global
section Chebotarev
variable (K : Type*) [Field K] [NumberField K]
def frobeniusSet (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (C : ConjClasses (L ≃ₐ[K] L)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {v | IsUnramifiedIn K v L ∧ ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver v.asIdeal ∧
    ∃ σ ∈ C.carrier, IsFrobAt K L σ Q}
def ChebotarevDensity' (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] (C : ConjClasses (L ≃ₐ[K] L)) : Prop :=
  NumberField.Set.HasDirichletDensity (frobeniusSet K L C)
    ((Nat.card C.carrier : ℝ) / (Nat.card (L ≃ₐ[K] L) : ℝ))
end Chebotarev
end Neutral.B1


