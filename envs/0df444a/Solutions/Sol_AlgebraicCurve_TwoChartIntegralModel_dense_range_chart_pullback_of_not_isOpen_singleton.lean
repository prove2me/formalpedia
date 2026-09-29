-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.dense_range_chart_pullback_of_not_isOpen_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cbf7c48c-69e5-549d-aa98-7ad952945ddf

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton.AlgebraicCurve.TwoChartIntegralModel"
open scoped TensorProduct

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "mem_chartAlg_iff subset_chartAlg chartAlgFin chartAlgInf chartAlgMid jInvChartInf inclInf isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf fibre"
namespace DenseChartGen
p2m_open "AlgebraicCurve.TwoChartIntegralModel AlgebraicCurve"

private theorem range_chart_eq
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type u) [CommRing κ] [Algebra R κ]
    (c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A)))) :
    Set.range c.base = (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base ⁻¹' Set.range ι.base := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have s : IsPullback (c ≫ pullback.snd _ _)
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R κ))) (ι ≫ f) := by
    rw [hcsnd, hι]
    exact sq
  have H : IsPullback c
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom))
      (pullback.fst _ _) ι :=
    IsPullback.of_right s hcfst (IsPullback.of_hasPullback _ _).flip
  have hc : c = H.isoPullback.hom ≫ pullback.fst _ _ := (H.isoPullback_hom_fst).symm
  rw [← Scheme.Pullback.range_fst, hc]
  ext x; constructor
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.hom.base y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨H.isoPullback.inv.base y, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]⟩

private theorem exists_chart
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (A : Type u) [CommRing A] [Algebra R A] (ι : Spec (CommRingCat.of A) ⟶ X)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (κ : Type u) [CommRing κ] [Algebra R κ] :
    ∃ c : Spec (CommRingCat.of (κ ⊗[R] A)) ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap R κ))),
      c ≫ pullback.fst _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := A)).toRingHom) ≫ ι ∧
      c ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) := by
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R κ A)
  have hcompat : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := A)).toRingHom) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := κ) (B := A))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R κ)) := by
    rw [Category.assoc, hι]
    exact sq.w.symm
  exact ⟨pullback.lift _ _ hcompat, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

set_option maxHeartbeats 16000000 in
private theorem finite_setOf_tmul_mem
    {R : Type u} [CommRing R] {F : Type u} [Field F] [Algebra R F] (S : Subalgebra R F) (s : F) (hs : s ∈ S)
    (hint : ∀ x : ↥S, IsIntegral ↥(Algebra.adjoin R ({s} : Set F)) (x : F))
    (κ : Type u) [Field κ] [Algebra R κ] [Algebra.FiniteType κ (κ ⊗[R] ↥S)] :
    {z : PrimeSpectrum (κ ⊗[R] ↥S) | ((1 : κ) ⊗ₜ[R] (⟨s, hs⟩ : ↥S)) ∈ z.asIdeal}.Finite := by
  classical
  set t : κ ⊗[R] ↥S := (1 : κ) ⊗ₜ[R] (⟨s, hs⟩ : ↥S) with ht
  set I : Ideal (κ ⊗[R] ↥S) := Ideal.span {t} with hI
  set A := Algebra.adjoin R ({s} : Set F) with hA
  have hAS : A ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.2 hs)

  let θ : ↥A →+* (κ ⊗[R] ↥S) ⧸ I :=
    (Ideal.Quotient.mk I).comp ((Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥S)).toRingHom.comp
      (Subalgebra.inclusion hAS).toRingHom)
  have hθ : ∀ a : ↥A, θ a ∈ Set.range (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I) : κ →+* (κ ⊗[R] ↥S) ⧸ I) := by
    intro a
    obtain ⟨a, ha⟩ := a
    refine Algebra.adjoin_induction (hx := ha) ?_ ?_ ?_ ?_
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      refine ⟨0, ?_⟩
      rw [map_zero]
      symm
      show Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] (Subalgebra.inclusion hAS ⟨x, Algebra.subset_adjoin hx⟩)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, hI]
      apply Ideal.subset_span
      rw [Set.mem_singleton_iff, ht]
      congr 1
      exact Subtype.ext hx
    · intro r
      refine ⟨algebraMap R κ r, ?_⟩
      show algebraMap κ ((κ ⊗[R] ↥S) ⧸ I) (algebraMap R κ r) =
        Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight (Subalgebra.inclusion hAS (algebraMap R (↥A) r)))
      rw [AlgHom.commutes, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rintro x y hx hy ⟨cx, hcx⟩ ⟨cy, hcy⟩
      refine ⟨cx + cy, ?_⟩
      rw [map_add, hcx, hcy, ← map_add]
      rfl
    · rintro x y hx hy ⟨cx, hcx⟩ ⟨cy, hcy⟩
      refine ⟨cx * cy, ?_⟩
      rw [map_mul, hcx, hcy, ← map_mul]
      rfl

  letI : Algebra ↥A ↥S := (Subalgebra.inclusion hAS).toRingHom.toAlgebra
  haveI : IsScalarTower ↥A ↥S F := IsScalarTower.of_algebraMap_eq fun a => rfl
  have hgen : ∀ x : ↥S, Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] x) ∈ integralClosure κ ((κ ⊗[R] ↥S) ⧸ I) := by
    intro x
    rw [mem_integralClosure_iff]
    rcases subsingleton_or_nontrivial ((κ ⊗[R] ↥S) ⧸ I) with hBI | hBI
    · rw [Subsingleton.elim (Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] x)) 0]; exact isIntegral_zero
    have hx : IsIntegral ↥A x :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥A ↥S F) Subtype.val_injective).1 (hint x)
    obtain ⟨p, hpm, hpx⟩ := hx

    have hroot : (p.map θ).eval (Ideal.Quotient.mk I ((1 : κ) ⊗ₜ[R] x)) = 0 := by
      rw [Polynomial.eval_map]
      have : (Ideal.Quotient.mk I).comp (Algebra.TensorProduct.includeRight (R := R) (A := κ) (B := ↥S)).toRingHom
          (Polynomial.eval₂ (algebraMap ↥A ↥S) x p) = 0 := by
        rw [hpx, map_zero]
      rw [Polynomial.hom_eval₂] at this
      exact this

    have hlifts : p.map θ ∈ Polynomial.lifts (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I)) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      rw [Polynomial.coeff_map]
      exact hθ _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts (hpm.map θ)
    refine ⟨q, hqm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map, hq]
    exact hroot

  have htop : integralClosure κ ((κ ⊗[R] ↥S) ⧸ I) = ⊤ := by
    refine top_unique fun z _ => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction b using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subalgebra.zero_mem _
    | tmul a x =>
        have h1 : a ⊗ₜ[R] x = (a ⊗ₜ[R] (1 : ↥S)) * ((1 : κ) ⊗ₜ[R] x) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have h2 : Ideal.Quotient.mk I (a ⊗ₜ[R] (1 : ↥S)) = (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I) : κ →+* (κ ⊗[R] ↥S) ⧸ I) a := by
          rw [← Ideal.Quotient.mk_algebraMap]
          rfl
        rw [h1, map_mul, h2]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a) (hgen x)
    | add u v hu hv => rw [map_add]; exact Subalgebra.add_mem _ (hu trivial) (hv trivial)
  haveI hintQ : Algebra.IsIntegral κ ((κ ⊗[R] ↥S) ⧸ I) := integralClosure_eq_top_iff.1 htop

  haveI : Ring.KrullDimLE 0 ((κ ⊗[R] ↥S) ⧸ I) := Ring.KrullDimLE.mk₀ fun P hP => by
    haveI := hP
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := κ) (S := (κ ⊗[R] ↥S) ⧸ I) P ?_
    rw [Ideal.eq_bot_of_prime (Ideal.comap (algebraMap κ ((κ ⊗[R] ↥S) ⧸ I)) P)]
    exact Ideal.bot_isMaximal
  haveI : IsNoetherianRing (κ ⊗[R] ↥S) := Algebra.FiniteType.isNoetherianRing κ _
  haveI : IsNoetherianRing ((κ ⊗[R] ↥S) ⧸ I) := inferInstance
  haveI : IsArtinianRing ((κ ⊗[R] ↥S) ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero (R := (κ ⊗[R] ↥S) ⧸ I)
  haveI : Finite {J : Ideal ((κ ⊗[R] ↥S) ⧸ I) // J.IsPrime} :=
    (IsArtinianRing.setOf_isPrime_finite ((κ ⊗[R] ↥S) ⧸ I)).to_subtype

  have hIle : ∀ z : PrimeSpectrum (κ ⊗[R] ↥S), t ∈ z.asIdeal → RingHom.ker (Ideal.Quotient.mk I) ≤ z.asIdeal := by
    intro z hz
    rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
    exact hz
  refine Set.finite_coe_iff.1 (Finite.of_injective
    (fun z : {z : PrimeSpectrum (κ ⊗[R] ↥S) | t ∈ z.asIdeal} =>
      (⟨z.1.asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hIle z.1 z.2)⟩ :
        {J : Ideal ((κ ⊗[R] ↥S) ⧸ I) // J.IsPrime})) ?_)
  rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
  have h' : (z.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) =
      (z'.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) :=
    congrArg (fun J : {J : Ideal ((κ ⊗[R] ↥S) ⧸ I) // J.IsPrime} => J.1.comap (Ideal.Quotient.mk I)) h
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    sup_eq_left.2 (hIle z hz), sup_eq_left.2 (hIle z' hz')] at h'
  exact Subtype.ext (PrimeSpectrum.ext h')

private theorem ig_ιFin_eq_ιInf_iff (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (x₀ : XFin R F j) (xi : XInf R F j) :
    (ιFin R F j).base x₀ = (ιInf R F j).base xi ↔
      ∃ w : XMid R F j, (fFin R F j).base w = x₀ ∧ (fInf R F j).base w = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, w, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (F := span (fFin R F j) (fInf R F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · exact match fi, fj, h₁, h₂ with
        | .init _, .init _, h₁, h₂ => ⟨w, h₁, h₂⟩
    · exact nomatch fj
    · exact nomatch fi
  · rintro ⟨w, rfl, rfl⟩
    change (fFin R F j ≫ ιFin R F j).base w = (fInf R F j ≫ ιInf R F j).base w
    rw [glue_condition]

private theorem ig_range_fInf (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] :
    Set.range (fInf R F j).base =
      ((PrimeSpectrum.basicOpen (jInvChartInf R F j) :
        TopologicalSpace.Opens (PrimeSpectrum ↥(chartAlgInf R F j))) :
          Set (PrimeSpectrum ↥(chartAlgInf R F j))) := by
  letI := (inclInf R F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R F j
  exact PrimeSpectrum.localization_away_comap_range ↥(chartAlgMid R F j) (jInvChartInf R F j)

private theorem ig_ιInf_mem_range_ιFin_iff (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)] (xi : XInf R F j) :
    (ιInf R F j).base xi ∈ Set.range (ιFin R F j).base ↔
      jInvChartInf R F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← ig_range_fInf R F j, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨w, -, hw⟩ := (ig_ιFin_eq_ιInf_iff R F j x₀ xi).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(fFin R F j).base w, (ig_ιFin_eq_ιInf_iff R F j _ _).mpr ⟨w, rfl, rfl⟩⟩

end AlgebraicCurve.TwoChartIntegralModel.DenseChartGen

open AlgebraicCurve.TwoChartIntegralModel.DenseChartGen in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (R : Type u) [CommRing R]
    (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    [Algebra.FiniteType R ↥(chartAlgInf R F j)]
    (κ : Type u) [Field κ] [Algebra R κ]

    (c : Spec (CommRingCat.of (κ ⊗[R] ↥(chartAlgFin R F j))) ⟶
      pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ))))
    (hcfst : c ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j))).toRingHom) ≫ ιFin R F j)
    (hcsnd : c ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := R) (A := κ) (B := ↥(chartAlgFin R F j)))))

    (hniso : ∀ x : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))),
      ¬ IsOpen ({x} : Set ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))))) :
    Dense (Set.range c.base) := by
  classical

  haveI : Algebra.FiniteType κ (κ ⊗[R] ↥(chartAlgInf R F j)) := inferInstance

  obtain ⟨c', hc'fst, hc'snd⟩ := exists_chart (toBase R F j) ↥(chartAlgInf R F j)
    (ιInf R F j) (ιInf_toBase R F j) κ
  have hrange := range_chart_eq (toBase R F j) ↥(chartAlgFin R F j)
    (ιFin R F j) (ιFin_toBase R F j) κ c hcfst hcsnd
  have hrange' := range_chart_eq (toBase R F j) ↥(chartAlgInf R F j)
    (ιInf R F j) (ιInf_toBase R F j) κ c' hc'fst hc'snd

  have hfin := finite_setOf_tmul_mem (chartAlgInf R F j) (j⁻¹)
    (subset_chartAlg R F _ rfl) (fun x => (mem_chartAlg_iff R F).1 x.2) κ

  have hcompl : (Set.range c.base)ᶜ ⊆ c'.base ''
      {z | ((1 : κ) ⊗ₜ[R] (⟨j⁻¹, subset_chartAlg R F _ rfl⟩ :
        ↥(chartAlgInf R F j))) ∈ z.asIdeal} := by
    intro w hw
    rw [Set.mem_compl_iff, hrange, Set.mem_preimage] at hw
    rcases mem_range_ιFin_or_mem_range_ιInf R F j
        ((pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base w)
      with hfin' | hinf
    · exact absurd hfin' hw
    · have hw' : w ∈ Set.range c'.base := by rw [hrange']; exact hinf
      obtain ⟨z, rfl⟩ := hw'
      refine ⟨z, ?_, rfl⟩

      have hz : (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R κ)))).base
          (c'.base z) = (ιInf R F j).base
            ((Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := κ)
              (B := ↥(chartAlgInf R F j))).toRingHom)).base z) := by
        rw [← Scheme.Hom.comp_apply, hc'fst, Scheme.Hom.comp_apply]
      rw [hz, ig_ιInf_mem_range_ιFin_iff R F j, not_not] at hw
      exact hw
  have hfinc : (Set.range c.base)ᶜ.Finite := (hfin.image c'.base).subset hcompl

  rw [dense_iff_inter_open]
  intro U hU hUne
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have hUsub : U ⊆ (Set.range c.base)ᶜ := fun u hu hu' => by
    have : u ∈ U ∩ Set.range c.base := ⟨hu, hu'⟩
    rw [hempty] at this
    exact this
  obtain ⟨x, -, hx⟩ := exists_isOpen_singleton_of_isOpen_finite (hfinc.subset hUsub) hUne hU
  exact hniso x hx

end S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_dense_range_chart_pullback_of_not_isOpen_singleton (solution)
