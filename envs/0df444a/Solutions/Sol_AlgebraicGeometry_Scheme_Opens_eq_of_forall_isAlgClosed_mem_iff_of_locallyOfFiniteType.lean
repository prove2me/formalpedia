-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Opens.eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ccd7273c-d5a3-598f-aa69-e0e790e4706a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace ClopenGC4

theorem exists_point_of_isClosed {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X))
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    ∃ p : Spec (CommRingCat.of K) ⟶ X,
      p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ∧ p (IsLocalRing.closedPoint K) = x := by

  have hfin : IsFinite (X.fromSpecResidueField x ≫ f) := by
    rw [isClosed_singleton_iff_isClosedImmersion] at hx
    rw [isFinite_iff_locallyOfFiniteType_of_jacobsonSpace]
    infer_instance
  let φ : CommRingCat.of k ⟶ X.residueField x := Spec.preimage (X.fromSpecResidueField x ≫ f)
  have hφ : Spec.map φ = X.fromSpecResidueField x ≫ f := Spec.map_preimage _
  have hφfin : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; exact hfin
  letI : Algebra k (X.residueField x) := φ.hom.toAlgebra
  haveI : Module.Finite k (X.residueField x) := hφfin
  haveI : Algebra.IsIntegral k (X.residueField x) := Algebra.IsIntegral.of_finite k _
  haveI : Algebra.IsAlgebraic k (X.residueField x) := Algebra.IsIntegral.isAlgebraic
  let ψ : X.residueField x →ₐ[k] K := IsAlgClosed.lift
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext r
    change ψ (φ.hom r) = algebraMap k K r
    exact ψ.commutes r
  · simp only [Scheme.Hom.comp_base, TopCat.comp_app]
    exact Scheme.fromSpecResidueField_apply x _

end ClopenGC4

namespace ClopenGC4

theorem false_of_mem_diff {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (U V : X.Opens)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : k →+* K) (p : Spec (CommRingCat.of K) ⟶ X),
      p ≫ f = Spec.map (CommRingCat.ofHom i) → ∀ y : ↥(Spec (CommRingCat.of K)), (p.base y ∈ U ↔ p.base y ∈ V))
    (hne : ((U : Set X) ∩ (V : Set X)ᶜ).Nonempty) : False := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hlc : IsLocallyClosed ((U : Set X) ∩ (V : Set X)ᶜ) :=
    U.isOpen.isLocallyClosed.inter V.isOpen.isClosed_compl.isLocallyClosed
  obtain ⟨x, ⟨hxU, hxV⟩, hxcl⟩ := nonempty_inter_closedPoints hne hlc
  obtain ⟨p, hpf, hpx⟩ := exists_point_of_isClosed f x hxcl (AlgebraicClosure k)
  have hiff := h (AlgebraicClosure k) (algebraMap k (AlgebraicClosure k)) p hpf (IsLocalRing.closedPoint _)
  have hpx' : p.base (IsLocalRing.closedPoint (AlgebraicClosure k)) = x := hpx
  rw [hpx'] at hiff
  exact hxV (hiff.mp hxU)

end ClopenGC4

open ClopenGC4 in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U V : X.Opens)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (i : k →+* K) (p : Spec (CommRingCat.of K) ⟶ X),
      p ≫ f = Spec.map (CommRingCat.ofHom i) → ∀ y : ↥(Spec (CommRingCat.of K)), (p.base y ∈ U ↔ p.base y ∈ V)) :
    U = V := by
  ext x
  constructor
  · intro hxU
    by_contra hxV
    exact false_of_mem_diff f U V h ⟨x, hxU, hxV⟩
  · intro hxV
    by_contra hxU
    exact false_of_mem_diff f V U (fun K _ _ i p hp y => (h K i p hp y).symm) ⟨x, hxV, hxU⟩

end S_AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Opens_eq_of_forall_isAlgClosed_mem_iff_of_locallyOfFiniteType (solution)
