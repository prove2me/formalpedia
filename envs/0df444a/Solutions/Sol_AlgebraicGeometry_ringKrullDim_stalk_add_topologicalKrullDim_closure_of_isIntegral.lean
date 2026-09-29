-- Prove2me | solution 1 for AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/826ca133-28e2-5df5-b200-1f8ca13a6d40

import Mathlib
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "LocallyOfFiniteType Spec IsIntegral Scheme exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen Scheme.ΓSpecIso topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral"
namespace CodimFormula
p2m_open "AlgebraicGeometry"

theorem eq_sub_of_natCast_add_eq (h n : ℕ) (d : WithBot ℕ∞)
    (hd : (h : WithBot ℕ∞) + d = n) : d = ((n - h : ℕ) : WithBot ℕ∞) ∧ h ≤ n := by
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h1 : ((h : ℕ∞) : WithBot ℕ∞) + ((⊤ : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hd
      rw [← WithBot.coe_add, WithBot.coe_inj] at h1
      simp at h1
    | coe m =>
      have h1 : ((h : ℕ∞) : WithBot ℕ∞) + ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hd
      rw [← WithBot.coe_add, WithBot.coe_inj] at h1
      have h2 : h + m = n := by exact_mod_cast h1
      refine ⟨?_, by omega⟩
      have : m = n - h := by omega
      subst this
      rfl

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

theorem topologicalKrullDim_zeroLocus {A : Type u} [CommRing A] (I : Ideal A) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) = ringKrullDim (A ⧸ I) := by
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [_root_.range_comap_of_surjective (A ⧸ I) _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  let e : PrimeSpectrum (A ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (I : Set A) :=
    hce.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (A ⧸ I)]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

theorem topologicalKrullDim_le_of_isEmbedding_image {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) (s : Set X) (t : Set Y)
    (hst : f '' s ⊆ t) : topologicalKrullDim s ≤ topologicalKrullDim t := by
  let φ : s → t := fun z => ⟨f z.1, hst ⟨z.1, z.2, rfl⟩⟩
  have hφ : IsInducing φ := (hf.isInducing.comp IsInducing.subtypeVal).codRestrict _
  exact Topology.IsInducing.topologicalKrullDim_le hφ

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

theorem chart_numbers {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [LocallyOfFiniteType f]
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ∃ n h : ℕ, h ≤ n ∧ topologicalKrullDim X = n ∧
      ringKrullDim (X.presheaf.stalk x) = h ∧
      topologicalKrullDim (PrimeSpectrum.zeroLocus
        (((hU.primeIdealOf ⟨x, hx⟩).asIdeal : Ideal Γ(X, U)) : Set Γ(X, U))) = ((n - h : ℕ) : WithBot ℕ∞) := by
  haveI : Nonempty U := ⟨⟨x, hx⟩⟩
  letI := chartAlgebra f U
  haveI := chart_finiteType f hU
  haveI : IsNoetherianRing Γ(X, U) := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  set p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hx⟩ with hp

  have hX : topologicalKrullDim X = ringKrullDim Γ(X, U) :=
    AlgebraicGeometry.topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen_of_isIntegral f hU ⟨x, hx⟩

  have hdf := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k p.asIdeal

  have hfin : p.asIdeal.height ≠ ⊤ := by
    haveI : p.asIdeal.FiniteHeight := inferInstance
    exact Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  obtain ⟨h, hh⟩ := ENat.ne_top_iff_exists.mp hfin

  obtain ⟨n, hn⟩ : ∃ n : ℕ, ringKrullDim Γ(X, U) = n := by
    obtain ⟨m, hm, -⟩ := Ideal.exists_le_maximal p.asIdeal (Ideal.IsPrime.ne_top inferInstance)
    haveI := hm
    have hdm := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k m
    have h0 : ringKrullDim (Γ(X, U) ⧸ m) = 0 := by
      letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
      exact ringKrullDim_eq_zero_of_field _
    rw [h0, add_zero] at hdm
    have hmfin : m.height ≠ ⊤ := by
      haveI : m.FiniteHeight := inferInstance
      exact Ideal.height_ne_top hm.ne_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hmfin
    exact ⟨n, by rw [← hdm, ← hn]; rfl⟩
  rw [hn, ← hh] at hdf
  obtain ⟨hquot, hle⟩ := eq_sub_of_natCast_add_eq h n _ hdf
  refine ⟨n, h, hle, hX.trans hn, ?_, ?_⟩
  ·
    letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x), ← hh]
    rfl
  · rw [topologicalKrullDim_zeroLocus, hquot]

theorem fromSpec_mem_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : PrimeSpectrum Γ(X, U)) (hq : hU.primeIdealOf ⟨x, hx⟩ ≤ q) :
    hU.fromSpec q ∈ closure ({x} : Set X) := by
  have hs : hU.primeIdealOf ⟨x, hx⟩ ⤳ q := (PrimeSpectrum.le_iff_specializes _ _).mp hq
  have hs' := hs.map hU.fromSpec.continuous
  rw [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at hs'
  exact specializes_iff_mem_closure.mp hs'

theorem primeIdealOf_le_of_mem_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (c : X) (hcU : c ∈ U) (hc : c ∈ closure ({x} : Set X)) :
    hU.primeIdealOf ⟨x, hx⟩ ≤ hU.primeIdealOf ⟨c, hcU⟩ := by
  rw [PrimeSpectrum.le_iff_specializes]
  refine (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp ?_
  have e1 := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have e2 := hU.fromSpec_primeIdealOf ⟨c, hcU⟩
  have hs : x ⤳ c := specializes_iff_mem_closure.mpr hc
  convert hs using 1

theorem zeroLocus_le_closure {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus
        (((hU.primeIdealOf ⟨x, hx⟩).asIdeal : Ideal Γ(X, U)) : Set Γ(X, U))) ≤
      topologicalKrullDim (closure ({x} : Set X)) := by
  refine topologicalKrullDim_le_of_isEmbedding_image hU.fromSpec.isOpenEmbedding.isEmbedding _ _ ?_
  rintro _ ⟨q, hq, rfl⟩
  refine fromSpec_mem_closure hU x hx q ?_
  exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hq

theorem closure_le {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [LocallyOfFiniteType f]
    (x : X) (n h : ℕ) (hXn : topologicalKrullDim X = n)
    (hxh : ringKrullDim (X.presheaf.stalk x) = h) :
    topologicalKrullDim (closure ({x} : Set X)) ≤ ((n - h : ℕ) : WithBot ℕ∞) := by
  haveI : QuasiSober (closure ({x} : Set X)) :=
    (IsClosedEmbedding.subtypeVal isClosed_closure).quasiSober
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding _ fun c => ?_

  obtain ⟨U', hU', hcU', -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := c.1) (U := ⊤) trivial
  have hxU' : x ∈ U' := by
    obtain ⟨y, hyU', hyx⟩ := mem_closure_iff.mp c.2 U' U'.isOpen hcU'
    rw [Set.mem_singleton_iff] at hyx
    rwa [hyx] at hyU'
  set p' : PrimeSpectrum Γ(X, U') := hU'.primeIdealOf ⟨x, hxU'⟩ with hp'
  let Z : Set (PrimeSpectrum Γ(X, U')) := PrimeSpectrum.zeroLocus ((p'.asIdeal : Ideal Γ(X, U')) : Set Γ(X, U'))

  let g : Z → closure ({x} : Set X) := fun q =>
    ⟨hU'.fromSpec q.1, fromSpec_mem_closure hU' x hxU' q.1
      ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp q.2)⟩
  have hgemb : IsEmbedding g :=
    ((hU'.fromSpec.isOpenEmbedding.isEmbedding).comp IsEmbedding.subtypeVal).codRestrict _ _
  have hrange : Set.range g = Subtype.val ⁻¹' (U' : Set X) := by
    ext c'
    constructor
    · rintro ⟨q, rfl⟩
      show hU'.fromSpec q.1 ∈ (U' : Set X)
      have := hU'.range_fromSpec ▸ Set.mem_range_self (f := hU'.fromSpec) q.1
      exact this
    · intro hc'
      refine ⟨⟨hU'.primeIdealOf ⟨c'.1, hc'⟩, ?_⟩, ?_⟩
      · show hU'.primeIdealOf ⟨c'.1, hc'⟩ ∈ PrimeSpectrum.zeroLocus _
        rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
        exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
          (primeIdealOf_le_of_mem_closure hU' x hxU' c'.1 hc' c'.2)
      · apply Subtype.ext
        exact hU'.fromSpec_primeIdealOf ⟨c'.1, hc'⟩
  have hopen : IsOpen (Set.range g) := by
    rw [hrange]
    exact U'.isOpen.preimage continuous_subtype_val
  have hg : IsOpenEmbedding g := ⟨hgemb, hopen⟩
  have hcg : c ∈ Set.range g := by rw [hrange]; exact hcU'
  refine ⟨Z, inferInstance, g, hg, hcg, ?_⟩

  obtain ⟨n', h', -, hXn', hxh', hZ⟩ := chart_numbers f hU' x hxU'
  have hn : n' = n := by
    have := hXn'.symm.trans hXn
    exact_mod_cast this
  have hh : h' = h := by
    have := hxh'.symm.trans hxh
    exact_mod_cast this
  subst hn hh
  exact hZ.le

theorem main {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X] [LocallyOfFiniteType f]
    (x : X) :
    ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim ↥(closure ({x} : Set X)) =
      topologicalKrullDim X := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨n, h, hle, hXn, hxh, hZ⟩ := chart_numbers f hU x hxU
  have hC : topologicalKrullDim (closure ({x} : Set X)) = ((n - h : ℕ) : WithBot ℕ∞) :=
    le_antisymm (closure_le f x n h hXn hxh) (hZ ▸ zeroLocus_le_closure hU x hxU)
  rw [hxh, hC, hXn]
  have : h + (n - h) = n := by omega
  exact_mod_cast this

end Charts

end AlgebraicGeometry.CodimFormula

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral.AlgebraicGeometry in

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [LocallyOfFiniteType f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) + topologicalKrullDim ↥(closure ({x} : Set X)) =
      topologicalKrullDim X :=
  AlgebraicGeometry.CodimFormula.main f x

end S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_add_topologicalKrullDim_closure_of_isIntegral (solution)
