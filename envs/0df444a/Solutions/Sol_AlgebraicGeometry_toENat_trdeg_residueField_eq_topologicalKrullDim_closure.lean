-- Prove2me | solution 1 for AlgebraicGeometry.toENat_trdeg_residueField_eq_topologicalKrullDim_closure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/4775f5dc-ebae-55fe-bc78-6a04044c5665

import Mathlib
import Theorems.Thm_Algebra_ringKrullDim_eq_toENat_trdeg_of_finiteType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace L1TrdegClosure

open Topology

section TopologyB

attribute [local instance] specializationOrder

theorem topologicalKrullDim_le_of_forall_exists_isOpenEmbedding {Z : Type u} [TopologicalSpace Z]
    [QuasiSober Z] [T0Space Z] (n : WithBot ℕ∞)
    (h : ∀ z : Z, ∃ (V : Type u) (_ : TopologicalSpace V) (g : V → Z),
      IsOpenEmbedding g ∧ z ∈ Set.range g ∧ topologicalKrullDim V ≤ n) :
    topologicalKrullDim Z ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Z)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun z => ?_
  obtain ⟨V, _, g, hg, ⟨y, rfl⟩, hV⟩ := h z
  haveI : QuasiSober V := hg.quasiSober
  haveI : T0Space V := hg.isEmbedding.t0Space
  rw [hg.coheight_eq (x := y)]
  calc (↑(Order.coheight y) : WithBot ℕ∞) ≤ Order.krullDim V := Order.coheight_le_krullDim _
    _ = topologicalKrullDim V :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := V))).symm
    _ ≤ n := hV

end TopologyB

theorem chart_top {X : Scheme.{u}} {x : X} {U : X.Opens} (hU : IsAffineOpen U) (hxU : x ∈ U) :
    ∃ g : PrimeSpectrum (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) → ↥(closure ({x} : Set X)),
      IsOpenEmbedding g ∧ ∀ z : ↥(closure ({x} : Set X)), z.1 ∈ (U : Set X) → z ∈ Set.range g := by
  have hmk : Function.Surjective (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :=
    Ideal.Quotient.mk_surjective
  have hc : IsClosedEmbedding
      (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hmk
  have hcr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) =
      closure {hU.primeIdealOf ⟨x, hxU⟩} := by
    rw [range_comap_of_surjective _ _ hmk, Ideal.mk_ker,
      ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, PrimeSpectrum.vanishingIdeal_singleton]
  have hF : IsOpenEmbedding hU.fromSpec.base := hU.fromSpec.isOpenEmbedding
  have hFq : hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hg₀ : IsEmbedding (hU.fromSpec.base ∘
      PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) :=
    hF.isEmbedding.comp hc.isEmbedding

  have hfwd : ∀ p, (hU.fromSpec.base ∘
      PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) p ∈
        closure ({x} : Set X) ∧
      (hU.fromSpec.base ∘
        PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) p ∈ (U : Set X) := by
    intro p
    refine ⟨?_, ?_⟩
    · have hle : hU.primeIdealOf ⟨x, hxU⟩ ≤
          PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) p := by
        intro a ha
        change Ideal.Quotient.mk _ a ∈ p.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
        exact p.asIdeal.zero_mem
      have hsp : hU.primeIdealOf ⟨x, hxU⟩ ⤳
          PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) p :=
        (PrimeSpectrum.le_iff_specializes _ _).mp hle
      have hsp' : hU.fromSpec.base (hU.primeIdealOf ⟨x, hxU⟩) ⤳ hU.fromSpec.base
          (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) p) :=
        hsp.map hU.fromSpec.continuous
      rw [hFq] at hsp'
      exact specializes_iff_mem_closure.mp hsp'
    · have : (hU.fromSpec.base ∘
          PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) p ∈
          Set.range hU.fromSpec.base := ⟨_, rfl⟩
      rwa [hU.range_fromSpec] at this

  have hbwd : ∀ y : X, y ∈ closure ({x} : Set X) → y ∈ (U : Set X) →
      y ∈ Set.range (hU.fromSpec.base ∘
        PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) := by
    intro y hy hyU
    rw [← hU.range_fromSpec] at hyU
    obtain ⟨p, rfl⟩ := hyU
    have hsp : x ⤳ hU.fromSpec.base p := specializes_iff_mem_closure.mpr hy
    rw [← hFq] at hsp
    have hsp' : hU.primeIdealOf ⟨x, hxU⟩ ⤳ p := hF.isEmbedding.isInducing.specializes_iff.mp hsp
    have hp : p ∈ Set.range
        (PrimeSpectrum.comap (Ideal.Quotient.mk (hU.primeIdealOf ⟨x, hxU⟩).asIdeal)) := by
      rw [hcr]; exact specializes_iff_mem_closure.mp hsp'
    obtain ⟨p', rfl⟩ := hp
    exact ⟨p', rfl⟩
  refine ⟨fun p => ⟨_, (hfwd p).1⟩, ⟨(IsEmbedding.subtypeVal.of_comp_iff).mp hg₀, ?_⟩, ?_⟩
  · have hrange : Set.range (fun p => (⟨_, (hfwd p).1⟩ : ↥(closure ({x} : Set X)))) =
        Subtype.val ⁻¹' (U : Set X) := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        exact (hfwd p).2
      · intro hz
        obtain ⟨p, hp⟩ := hbwd z.1 z.2 hz
        exact ⟨p, Subtype.ext hp⟩
    rw [hrange]
    exact U.isOpen.preimage continuous_subtype_val
  · intro z hz
    obtain ⟨p, hp⟩ := hbwd z.1 z.2 hz
    exact ⟨p, Subtype.ext hp⟩

section Chart

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

noncomputable abbrev chartAlgebra (U : X.Opens) : Algebra k Γ(X, U) :=
  ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

theorem chart_finiteType [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := chartAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

noncomputable abbrev resAlgebra (x : X) : Algebra k (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

theorem chart_alg [LocallyOfFiniteType f] {x : X} {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) :
    letI := resAlgebra f x
    ringKrullDim (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) := by
  letI : Algebra k (X.residueField x) := resAlgebra f x
  letI : Algebra k Γ(X, U) := chartAlgebra f U
  haveI : Algebra.FiniteType k Γ(X, U) := chart_finiteType f hU
  letI algSt : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩

  have hev : ∀ a : k, (X.evaluation U x hxU).hom (algebraMap k Γ(X, U) a) = algebraMap k (X.residueField x) a := by
    intro a
    simp only [RingHom.algebraMap_toAlgebra, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_comp, Scheme.evaluation, Scheme.Hom.appLE, Scheme.Hom.appTop,
      TopCat.Presheaf.germ_res_apply]
    rfl

  have hker : RingHom.ker (X.evaluation U x hxU).hom = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    ext a
    rw [RingHom.mem_ker]
    change (X.residue x).hom ((X.presheaf.germ U x hxU).hom a) = 0 ↔ _
    exact (IsLocalRing.residue_eq_zero_iff _).trans
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal a)
  rw [← hker]
  haveI hprime : (RingHom.ker (X.evaluation U x hxU).hom).IsPrime := RingHom.ker_isPrime _

  letI algQ : Algebra (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) :=
    (RingHom.kerLift (X.evaluation U x hxU).hom).toAlgebra
  haveI : IsScalarTower k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [← Ideal.Quotient.mk_algebraMap,
      RingHom.algebraMap_toAlgebra (RingHom.kerLift (X.evaluation U x hxU).hom), RingHom.kerLift_mk]
    exact (hev a).symm
  haveI : FaithfulSMul (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective _)
  haveI : FaithfulSMul k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap k _).injective

  haveI : Algebra.IsAlgebraic (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨s, rfl⟩ := X.residue_surjective x z
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl s

    have ht : (X.evaluation U x hxU).hom t ≠ 0 := by
      intro h0
      have : (t : Γ(X, U)) ∈ RingHom.ker (X.evaluation U x hxU).hom := h0
      rw [hker] at this
      exact t.2 this
    have hz : (X.residue x).hom s * (X.evaluation U x hxU).hom t = (X.evaluation U x hxU).hom a := by
      change (X.residue x).hom s * (X.residue x).hom ((X.presheaf.germ U x hxU).hom t) =
        (X.residue x).hom ((X.presheaf.germ U x hxU).hom a)
      rw [← map_mul]
      exact congrArg _ hat
    have hz' : (X.residue x).hom s =
        algebraMap (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) (Ideal.Quotient.mk _ a) *
          (algebraMap (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom) (X.residueField x) (Ideal.Quotient.mk _ t))⁻¹ := by
      rw [RingHom.algebraMap_toAlgebra, RingHom.kerLift_mk, RingHom.kerLift_mk,
        eq_mul_inv_iff_mul_eq₀ ht, hz]
    rw [hz']
    exact (isAlgebraic_algebraMap _).mul (isAlgebraic_algebraMap _).inv

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom)
  have hs' := hs.algebraMap_comp (A := X.residueField x)
  rw [Algebra.ringKrullDim_eq_toENat_trdeg_of_finiteType k (Γ(X, U) ⧸ RingHom.ker (X.evaluation U x hxU).hom),
    ← hs.cardinalMk_eq_trdeg, ← hs'.cardinalMk_eq_trdeg]

theorem main [LocallyOfFiniteType f] (x : X) :
    letI := resAlgebra f x
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({x} : Set X)) := by
  letI := resAlgebra f x
  haveI : QuasiSober ↥(closure ({x} : Set X)) :=
    (isClosed_closure.isClosedEmbedding_subtypeVal).quasiSober
  apply le_antisymm
  · obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    obtain ⟨g, hg, -⟩ := chart_top hU hxU
    rw [← chart_alg f hU hxU, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact Topology.IsInducing.topologicalKrullDim_le hg.isEmbedding.isInducing
  · refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding _ fun z => ?_
    obtain ⟨U, hU, hzU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := z.1) (U := ⊤) trivial
    have hxU : x ∈ U := by
      obtain ⟨y, hyU, hyx⟩ := mem_closure_iff.mp z.2 U U.isOpen hzU
      rw [Set.mem_singleton_iff] at hyx
      exact hyx ▸ hyU
    obtain ⟨g, hg, hrg⟩ := chart_top hU hxU
    refine ⟨_, inferInstance, g, hg, hrg z hzU, ?_⟩
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, chart_alg f hU hxU]

end Chart

end L1TrdegClosure

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra
    (Cardinal.toENat (Algebra.trdeg k (X.residueField x)) : WithBot ℕ∞) =
      topologicalKrullDim ↥(closure ({x} : Set X)) :=
  L1TrdegClosure.main f x

end S_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure
end P2MW
export P2MW.S_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure (solution)
