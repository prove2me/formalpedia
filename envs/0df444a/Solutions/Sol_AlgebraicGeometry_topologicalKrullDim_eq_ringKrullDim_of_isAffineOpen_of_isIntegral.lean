-- Prove2me | solution 1 for AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cb8a7837-5cad-5802-8dfd-f48639489c69

import Mathlib
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "LocallyOfFiniteType Spec IsIntegral Scheme Scheme.basicOpen_zero exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen Scheme.ΓSpecIso"
namespace DimAffineOpen
p2m_open "AlgebraicGeometry"

theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  have h := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k m
  have h0 : ringKrullDim (A ⧸ m) = 0 := by
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    exact ringKrullDim_eq_zero_of_field (A ⧸ m)
  rwa [h0, add_zero] at h

theorem ringKrullDim_le_ringKrullDim_localization (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {g : A} (hg : g ≠ 0)
    (L : Type v) [CommRing L] [Algebra A L] [IsLocalization.Away g L] :
    ringKrullDim A ≤ ringKrullDim L := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_noZeroDivisors]
  have hg' : g ∉ (⊥ : Ideal A).jacobson := by rw [hjac]; simpa using hg
  rw [Ideal.jacobson, Ideal.mem_sInf] at hg'
  simp only [Set.mem_setOf_eq, not_forall, exists_prop] at hg'
  obtain ⟨M, ⟨-, hM⟩, hgM⟩ := hg'
  haveI : M.IsMaximal := hM
  have hdisj : Disjoint ((Submonoid.powers g : Submonoid A) : Set A) (M : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hgM (hM.isPrime.mem_of_pow_mem n hn)
  have hMap : (M.map (algebraMap A L)).height = M.height :=
    IsLocalization.height_map_of_disjoint (Submonoid.powers g) M hdisj
  haveI : (M.map (algebraMap A L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) L M hM.isPrime hdisj
  calc ringKrullDim A = M.height := (height_eq_ringKrullDim_of_isMaximal k M).symm
    _ = (M.map (algebraMap A L)).height := by rw [hMap]
    _ ≤ ringKrullDim L := Ideal.height_le_ringKrullDim_of_isPrime

section TopologyB

attribute [local instance] specializationOrder

theorem topologicalKrullDim_le_of_forall_exists_isOpenEmbedding {X : Type u} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] (n : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Type u) (_ : TopologicalSpace U) (g : U → X),
      IsOpenEmbedding g ∧ x ∈ Set.range g ∧ topologicalKrullDim U ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨U, _, g, hg, ⟨y, rfl⟩, hU⟩ := h x
  haveI : QuasiSober U := hg.quasiSober
  haveI : T0Space U := hg.isEmbedding.t0Space
  rw [hg.coheight_eq (x := y)]
  calc (↑(Order.coheight y) : WithBot ℕ∞) ≤ Order.krullDim U := Order.coheight_le_krullDim _
    _ = topologicalKrullDim U :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U))).symm
    _ ≤ n := hU

end TopologyB

theorem topologicalKrullDim_affineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim ↥U = ringKrullDim Γ(X, U) := by
  have h : topologicalKrullDim (Spec Γ(X, U)) = ringKrullDim Γ(X, U) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph] at h
  exact h

section Charts

variable {k : Type u} [Field k]

noncomputable abbrev chartAlgebra {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) : Algebra k Γ(X, U) :=
  ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

theorem chart_finiteType {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := chartAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

theorem ringKrullDim_sections_le {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsIntegral X] {U U' : X.Opens} (hU : IsAffineOpen U)
    (hU' : IsAffineOpen U') (hUne : (U : Set X).Nonempty) (hU'ne : (U' : Set X).Nonempty) :
    ringKrullDim Γ(X, U') ≤ ringKrullDim Γ(X, U) := by

  obtain ⟨z, hzU, hzU'⟩ := nonempty_preirreducible_inter U.2 U'.2 hUne hU'ne
  obtain ⟨g, hgU, hzg⟩ := hU'.exists_basicOpen_le ⟨z, hzU⟩ hzU'
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hzg
    exact hzg
  haveI : Nonempty U' := ⟨⟨z, hzU'⟩⟩
  letI := chartAlgebra f U'
  haveI := chart_finiteType f hU'
  haveI := hU'.isLocalization_basicOpen g
  have h1 : ringKrullDim Γ(X, U') ≤ ringKrullDim Γ(X, X.basicOpen g) :=
    ringKrullDim_le_ringKrullDim_localization k hg _
  have h2 : ringKrullDim Γ(X, X.basicOpen g) = topologicalKrullDim ↥(X.basicOpen g) :=
    (topologicalKrullDim_affineOpen (hU'.basicOpen g)).symm
  have h3 : topologicalKrullDim ↥(X.basicOpen g) ≤ topologicalKrullDim ↥U :=
    Topology.IsInducing.topologicalKrullDim_le (IsEmbedding.inclusion hgU).isInducing
  rw [← topologicalKrullDim_affineOpen hU]
  exact h1.trans (h2.le.trans h3)

theorem topologicalKrullDim_le_ringKrullDim {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X ≤ ringKrullDim Γ(X, U) := by
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding (X := X) _ fun ξ => ?_
  obtain ⟨U', hU', hξU', -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := ξ) (U := ⊤) trivial
  refine ⟨↥U', inferInstance, Subtype.val, U'.2.isOpenEmbedding_subtypeVal, ⟨⟨ξ, hξU'⟩, rfl⟩, ?_⟩
  rw [topologicalKrullDim_affineOpen hU']
  exact ringKrullDim_sections_le f hU hU' hUne ⟨ξ, hξU'⟩

theorem main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) := by
  refine le_antisymm (topologicalKrullDim_le_ringKrullDim f hU hUne) ?_
  rw [← topologicalKrullDim_affineOpen hU]
  exact topologicalKrullDim_subspace_le X (U : Set X)

end Charts

end AlgebraicGeometry.DimAffineOpen

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral.AlgebraicGeometry in

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X = ringKrullDim Γ(X, U) :=
  AlgebraicGeometry.DimAffineOpen.main f hU hUne

end S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral (solution)
