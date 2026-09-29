-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.IdealSheafData.isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/d037d585-45ac-5b44-b336-52b1033c59a7

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp isClosedImmersion_iff Surjective Scheme.Hom.finrank_comp_left_of_isIso sigmaMk_mk IsClosedImmersion.isIso_lift Scheme.IdealSheafData.radical_ideal Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal IsZariskiLocalAtSource.sigmaDesc ι_sigmaSpec_assoc Scheme.Hom exists_basicOpen_le_affine_inter Flat.SpecMap_iff IsFinite Scheme.Hom.support_ker Spec Spec.map Scheme Scheme.IdealSheafData.vanishingIdeal IsZariskiLocalAtSource Scheme.Hom.comp_base Scheme.IdealSheafData.ker_subschemeι Scheme.IdealSheafData.vanishingIdeal_ideal Flat IsClosedImmersion IsReduced IsClosedImmersion.lift sigmaSpec Scheme.Hom.finrank_SpecMap_algebraMap Spec.map_id IsClosedImmersion.lift_fac IsFinite.SpecMap_iff IsAffineOpen IsAffineOpen.fromSpec_primeIdealOf Scheme.Hom.ker_apply sigmaMk Scheme.IdealSheafData.ext Scheme.IdealSheafData.vanishingIdeal_support Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.IdealSheafData isClosedImmersion_of_comp_eq_id"
namespace PtsRankS17
p2m_open "AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem map_germ_ideal_eq (I : X.IdealSheafData) {x : X} (V W : X.affineOpens)
    (hV : x ∈ (V : X.Opens)) (hW : x ∈ (W : X.Opens)) :
    Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom (I.ideal V) =
      Ideal.map (X.presheaf.germ (W : X.Opens) x hW).hom (I.ideal W) := by
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter V.2 W.2 x ⟨hV, hW⟩
  have key : ∀ (T : X.affineOpens) (hT : x ∈ (T : X.Opens))
      (hle : (X.affineBasicOpen f : X.Opens) ≤ (T : X.Opens)),
      Ideal.map (X.presheaf.germ (T : X.Opens) x hT).hom (I.ideal T) =
        Ideal.map (X.presheaf.germ (X.affineBasicOpen f : X.Opens) x hxf).hom
          (I.ideal (X.affineBasicOpen f)) := by
    intro T hT hle
    rw [← I.map_ideal (U := X.affineBasicOpen f) (V := T) hle, Ideal.map_map]
    congr 1
    rw [← TopCat.Presheaf.germ_res X.presheaf (homOfLE hle) x hxf, CommRingCat.hom_comp]
    rfl
  rw [key V hV (X.basicOpen_le f), key W hW]
  change X.basicOpen f ≤ (W : X.Opens)
  rw [hfg]
  exact X.basicOpen_le g

theorem ideal_le_primeIdealOf_of_mem_support (U : X.affineOpens) (a : (U : X.Opens)) (K : X.IdealSheafData)
    (ha : (a : X) ∈ (K.support : Set X)) : K.ideal U ≤ (U.2.primeIdealOf a).asIdeal := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  haveI := hU.isLocalization_stalk a
  intro f hf
  have hz : (a : X) ∈ X.zeroLocus (K.ideal U : Set Γ(X, U)) :=
    (Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) a.2).mp ha
  have hnb : (a : X) ∉ X.basicOpen f := (X.mem_zeroLocus_iff _ _).mp hz f hf
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (a : X)) (hU.primeIdealOf a).asIdeal f,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact hnb ((X.mem_basicOpen (U := U) f a a.2).mpr hu)

theorem map_germ_ideal_eq_top_of_not_mem_support (U : X.affineOpens) (a : (U : X.Opens)) (K : X.IdealSheafData)
    (ha : (a : X) ∉ (K.support : Set X)) :
    Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk (a : X))) (K.ideal U) = ⊤ := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  have ha' : ¬ ∀ f ∈ (K.ideal U : Set Γ(X, U)), (a : X) ∉ X.basicOpen f := fun h =>
    ha ((Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) a.2).mpr ((X.mem_zeroLocus_iff _ _).mpr h))
  push_neg at ha'
  obtain ⟨f, hf, hfa⟩ := ha'
  have hu : IsUnit ((X.presheaf.germ (U : X.Opens) (a : X) a.2).hom f) := (X.mem_basicOpen (U := U) f a a.2).mp hfa
  have hmem : (X.presheaf.germ (U : X.Opens) (a : X) a.2).hom f ∈
      Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk (a : X))) (K.ideal U) := Ideal.mem_map_of_mem _ hf
  exact Ideal.eq_top_of_isUnit_mem _ hmem hu

theorem ideal_le_of_forall_map_germ_le {V : X.Opens} (hV : IsAffineOpen V) {I' J' : Ideal Γ(X, V)}
    (h : ∀ (x : X) (hx : x ∈ V),
      I'.map (X.presheaf.germ V x hx).hom ≤ J'.map (X.presheaf.germ V x hx).hom) :
    I' ≤ J' := by
  intro a ha
  let K : Ideal Γ(X, V) :=
    { carrier := {c | c * a ∈ J'}
      add_mem' := fun {c d} hc hd => by
        simp only [Set.mem_setOf_eq, add_mul]; exact J'.add_mem hc hd
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul]; exact J'.zero_mem
      smul_mem' := fun c d hd => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, mul_assoc]; exact J'.mul_mem_left c hd }
  suffices hK : K = ⊤ by
    have h1 : (1 : Γ(X, V)) ∈ K := hK ▸ Submodule.mem_top
    have h1' : 1 * a ∈ J' := h1
    rwa [one_mul] at h1'
  rw [← Ideal.span_eq K, ← hV.iSup_basicOpen_eq_self_iff]
  refine le_antisymm (iSup_le fun f => X.basicOpen_le (f : Γ(X, V))) fun x hx => ?_
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : V)
  haveI := hV.isLocalization_stalk ⟨x, hx⟩
  have hmem : algebraMap Γ(X, V) (X.presheaf.stalk x) a ∈
      J'.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
    h x hx (Ideal.mem_map_of_mem _ ha)
  obtain ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, hjs⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _).mp hmem
  simp only at hjs
  rw [← map_mul] at hjs
  obtain ⟨⟨c, hc⟩, hcas⟩ :=
    (IsLocalization.eq_iff_exists (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl _).mp hjs
  simp only at hcas
  have hf : c * s ∈ K := by
    show c * s * a ∈ J'
    rw [mul_assoc, mul_comm s a, hcas]
    exact J'.mul_mem_left c hj
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨c * s, hf⟩, ?_⟩
  rw [X.mem_basicOpen _ x hx]
  exact IsLocalization.map_units (M := (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    (X.presheaf.stalk x) ⟨c * s, mul_mem hc hs⟩

theorem vanishingIdeal_support_le (K : X.IdealSheafData) {N : ℕ} (x : Fin N → X)
    (hsupp : (K.support : Set X) = Set.range x)
    (hmax : ∀ i, ∃ (U : X.affineOpens) (hU : x i ∈ (U : X.Opens)),
      Ideal.map (X.presheaf.germ (U : X.Opens) (x i) hU).hom (K.ideal U) = IsLocalRing.maximalIdeal (X.presheaf.stalk (x i))) :
    Scheme.IdealSheafData.vanishingIdeal K.support ≤ K := by
  classical
  intro U
  have hU : IsAffineOpen (U : X.Opens) := U.2
  refine ideal_le_of_forall_map_germ_le hU (fun a ha => ?_)
  by_cases hasupp : a ∈ (K.support : Set X)
  ·
    have hasupp' := hasupp
    rw [hsupp] at hasupp'
    obtain ⟨j, rfl⟩ := hasupp'
    obtain ⟨W, hjW, hKj⟩ := hmax j
    rw [map_germ_ideal_eq K W U hjW ha] at hKj
    rw [hKj]
    letI := X.presheaf.algebra_section_stalk (⟨x j, ha⟩ : (U : X.Opens))
    haveI := hU.isLocalization_stalk ⟨x j, ha⟩

    have hle : (Scheme.IdealSheafData.vanishingIdeal K.support).ideal U ≤ (hU.primeIdealOf ⟨x j, ha⟩).asIdeal := by
      intro f hf
      rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hf
      apply hf
      show hU.fromSpec.base (hU.primeIdealOf ⟨x j, ha⟩) ∈ (K.support : Set X)
      rw [IsAffineOpen.fromSpec_primeIdealOf]
      exact hasupp
    calc Ideal.map (X.presheaf.germ (U : X.Opens) (x j) ha).hom ((Scheme.IdealSheafData.vanishingIdeal K.support).ideal U)
        ≤ Ideal.map (algebraMap Γ(X, U) (X.presheaf.stalk (x j))) (hU.primeIdealOf ⟨x j, ha⟩).asIdeal := Ideal.map_mono hle
      _ = IsLocalRing.maximalIdeal _ := IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  ·
    letI := X.presheaf.algebra_section_stalk (⟨a, ha⟩ : (U : X.Opens))
    have := map_germ_ideal_eq_top_of_not_mem_support U ⟨a, ha⟩ K hasupp
    exact le_of_le_of_eq le_top this.symm

end AlgebraicGeometry.PtsRankS17

open AlgebraicGeometry.PtsRankS17 in
theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of k))
    (K : X.IdealSheafData) {N : ℕ} (x : Fin N → X) (hx : Function.Injective x)
    (hsupp : (K.support : Set X) = Set.range x)
    (hmax : ∀ i, ∃ (U : X.affineOpens) (hU : x i ∈ (U : X.Opens)),
      Ideal.map (X.presheaf.germ (U : X.Opens) (x i) hU).hom (K.ideal U) = IsLocalRing.maximalIdeal (X.presheaf.stalk (x i)))
    (hrat : ∀ i, ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ q = 𝟙 _ ∧ x i ∈ Set.range s.base) :
    IsFinite (K.subschemeι ≫ q) ∧ ∀ t : Spec (CommRingCat.of k), (K.subschemeι ≫ q).finrank t = N := by
  classical
  choose s hsq hsx using hrat

  haveI hsci : ∀ i, IsClosedImmersion (s i) := fun i => isClosedImmersion_of_comp_eq_id q (s i) (hsq i)
  have hrange : ∀ i, Set.range (s i).base = {x i} := by
    intro i
    obtain ⟨pt, hpt⟩ := hsx i
    ext y; constructor
    · rintro ⟨pt', rfl⟩; rw [Set.mem_singleton_iff, ← hpt, Subsingleton.elim pt' pt]
    · intro hy; rw [Set.mem_singleton_iff] at hy; exact ⟨pt, hpt.trans hy.symm⟩
  have hcl : ∀ i, IsClosed ({x i} : Set X) := fun i => (hrange i) ▸ (s i).isClosedEmbedding.isClosed_range

  let R : ULift.{u} (Fin N) → CommRingCat.{u} := fun _ => CommRingCat.of k
  let φ₀ : (∐ fun i => Spec (R i)) ⟶ X := Sigma.desc (fun i => s i.down)
  haveI : IsIso (sigmaSpec R) := inferInstance
  let φ : Spec (CommRingCat.of ((i : ULift.{u} (Fin N)) → (R i))) ⟶ X := inv (sigmaSpec R) ≫ φ₀

  have hφ₀base : ∀ (i : ULift.{u} (Fin N)) (y : Spec (R i)), φ₀.base ((Sigma.ι (fun i => Spec (R i)) i).base y) = x i.down := by
    intro i y
    have h1 : ((Sigma.ι (fun i => Spec (R i)) i) ≫ φ₀) = s i.down := Sigma.ι_desc _ _
    have h2 : φ₀.base ((Sigma.ι (fun i => Spec (R i)) i).base y) = (s i.down).base y := by
      rw [← h1]; rfl
    rw [h2, ← Set.mem_singleton_iff, ← hrange]; exact ⟨y, rfl⟩
  haveI hφ₀ : IsClosedImmersion φ₀ := by
    rw [isClosedImmersion_iff]
    refine ⟨IsZariskiLocalAtSource.sigmaDesc (fun i => inferInstance), ?_⟩
    have hpt : ∀ z : (∐ fun i => Spec (R i) : Scheme.{u}), ∃ (i : ULift.{u} (Fin N)) (y : Spec (R i)),
        z = (Sigma.ι (fun i => Spec (R i)) i).base y := by
      intro z
      obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun i => Spec (R i))).surjective z
      exact ⟨i, y, sigmaMk_mk _ _ _⟩
    have hinj : Function.Injective φ₀.base := by
      intro z₁ z₂ h
      obtain ⟨i₁, y₁, rfl⟩ := hpt z₁
      obtain ⟨i₂, y₂, rfl⟩ := hpt z₂
      rw [hφ₀base, hφ₀base] at h
      have hi : i₁ = i₂ := ULift.ext _ _ (hx h)
      subst hi
      rw [Subsingleton.elim y₁ y₂]
    have hclosed : IsClosedMap φ₀.base := by
      intro C _
      have hsub : φ₀.base '' C ⊆ Set.range x := by
        rintro _ ⟨z, _, rfl⟩
        obtain ⟨i, y, rfl⟩ := hpt z
        exact ⟨i.down, (hφ₀base i y).symm⟩
      have hfin : (φ₀.base '' C).Finite := (Set.finite_range x).subset hsub
      rw [← Set.biUnion_of_singleton (φ₀.base '' C)]
      refine hfin.isClosed_biUnion (fun p hp => ?_)
      obtain ⟨i, rfl⟩ := hsub hp
      exact hcl i
    exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap φ₀.base.hom.continuous hinj hclosed
  haveI hφ : IsClosedImmersion φ := inferInstance

  have hrangeφ : Set.range φ.base = Set.range x := by
    have hsurj : Function.Surjective (inv (sigmaSpec R)).base := (inv (sigmaSpec R)).surjective
    have : Set.range φ.base = Set.range φ₀.base := by
      show Set.range (inv (sigmaSpec R) ≫ φ₀).base = _
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj.range_eq, Set.image_univ]
    rw [this]
    apply Set.Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun i => Spec (R i))).surjective z
      rw [sigmaMk_mk]
      exact ⟨i.down, (hφ₀base i y).symm⟩
    · rintro _ ⟨i, rfl⟩
      obtain ⟨pt, -⟩ := hsx i
      exact ⟨(Sigma.ι (fun i => Spec (R i)) ⟨i⟩).base pt, hφ₀base ⟨i⟩ pt⟩

  have hsuppφ : φ.ker.support = K.support := by
    apply TopologicalSpace.Closeds.ext
    rw [Scheme.Hom.support_ker, hrangeφ, hsupp]
    have hclR : IsClosed (Set.range x) := by
      rw [← Set.biUnion_of_singleton (Set.range x)]
      refine (Set.finite_range x).isClosed_biUnion (fun p hp => ?_)
      obtain ⟨i, rfl⟩ := hp
      exact hcl i
    exact hclR.closure_eq
  have hKrad : K = Scheme.IdealSheafData.vanishingIdeal K.support :=
    le_antisymm (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp le_rfl)
      (vanishingIdeal_support_le K x hsupp hmax)
  have hφrad : φ.ker = Scheme.IdealSheafData.vanishingIdeal φ.ker.support := by
    rw [Scheme.IdealSheafData.vanishingIdeal_support]
    apply Scheme.IdealSheafData.ext
    funext U
    rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]

    symm
    apply Ideal.IsRadical.radical
    intro a ⟨n, hn⟩
    rw [RingHom.mem_ker, map_pow] at hn
    rw [RingHom.mem_ker]
    exact IsReduced.eq_zero _ ⟨n, hn⟩
  have hker : φ.ker = K := by
    rw [hφrad, hsuppφ, ← hKrad]

  have hφq : φ ≫ q = Spec.map (CommRingCat.ofHom (algebraMap k ((i : ULift.{u} (Fin N)) → (R i)))) := by
    rw [Category.assoc, IsIso.inv_comp_eq]
    refine Sigma.hom_ext _ _ (fun i => ?_)
    rw [Sigma.ι_desc_assoc, hsq, ι_sigmaSpec_assoc, ← Spec.map_comp]
    change 𝟙 _ = Spec.map (CommRingCat.ofHom ((Pi.evalRingHom (fun _ => k) i).comp (algebraMap k ((i : ULift.{u} (Fin N)) → (R i)))))
    have : (Pi.evalRingHom (fun _ => k) i).comp (algebraMap k ((i : ULift.{u} (Fin N)) → (R i))) = RingHom.id k := by
      ext a; rfl
    rw [this]
    change 𝟙 _ = Spec.map (𝟙 (CommRingCat.of k))
    rw [Spec.map_id]
  set e := IsClosedImmersion.lift K.subschemeι φ (by rw [Scheme.IdealSheafData.ker_subschemeι, hker]) with he
  haveI : IsIso e := IsClosedImmersion.isIso_lift K.subschemeι φ (by rw [Scheme.IdealSheafData.ker_subschemeι, hker])
  have hefac : e ≫ K.subschemeι = φ := IsClosedImmersion.lift_fac _ _ _
  let g : Spec (CommRingCat.of ((i : ULift.{u} (Fin N)) → (R i))) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k ((i : ULift.{u} (Fin N)) → (R i))))
  haveI : Module.Finite k ((i : ULift.{u} (Fin N)) → (R i)) := inferInstance
  haveI : Module.Flat k ((i : ULift.{u} (Fin N)) → (R i)) := inferInstance
  haveI hgfin : IsFinite g := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  haveI hgflat : Flat g := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have hcomp : K.subschemeι ≫ q = inv e ≫ g := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hefac, hφq]
  refine ⟨?_, ?_⟩
  · rw [hcomp]; infer_instance
  · intro t
    rw [hcomp, Scheme.Hom.finrank_comp_left_of_isIso]
    change (Spec.map (CommRingCat.ofHom (algebraMap k ((i : ULift.{u} (Fin N)) → (R i))))).finrank t = N
    rw [Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
    simp [R]
    rfl

end S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isFinite_and_finrank_subschemeIota_comp_eq_of_map_germ_eq_maximalIdeal (solution)
