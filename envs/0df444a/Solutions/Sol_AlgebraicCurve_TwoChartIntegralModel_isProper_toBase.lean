-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.isProper_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/7fd207d8-61e7-5bbc-95a3-c9549b9f4028

import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "TwoChartIntegralModel"
p2m_open "AlgebraicCurve"

namespace TwoChartIntegralModel
p2m_export "AlgebraicCurve.TwoChartIntegralModel" "j_ne_zero chartAlg subset_chartAlg coe_chartIncl chartAlgFin chartAlgInf chartAlgMid jChartFin jInvChartInf coe_jChartFin coe_jInvChartInf inclFin inclInf isLocalization_away_inclFin isLocalization_away_inclInf XFin XInf XMid fFin fInf ιFin ιInf glue_condition toBase ιFin_toBase ιInf_toBase mem_range_ιFin_or_mem_range_ιInf"
p2m_open "AlgebraicCurve.TwoChartIntegralModel"

namespace Proper

variable (R₀ : Type u) [CommRing R₀] (F : Type u) [Field F] [Algebra R₀ F] (j : F) [Fact (j ≠ 0)]

set_option quotPrecheck false in
local notation "X₀" => AlgebraicCurve.TwoChartIntegralModel R₀ F j

theorem ιFin_eq_ιInf_iff (x₀ : XFin R₀ F j) (xi : XInf R₀ F j) :
    (ιFin R₀ F j).base x₀ = (ιInf R₀ F j).base xi ↔
      ∃ u : XMid R₀ F j, (fFin R₀ F j).base u = x₀ ∧ (fInf R₀ F j).base u = xi := by
  constructor
  · intro h
    obtain ⟨k, fi, fj, u, h₁, h₂⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span (fFin R₀ F j) (fInf R₀ F j))
        (i := WalkingSpan.left) (j := WalkingSpan.right) (xi := x₀) (xj := xi)).mp h
    rcases k with (_ | _ | _)
    · cases fi
      cases fj
      exact ⟨u, h₁, h₂⟩
    · cases fj
    · cases fi
  · rintro ⟨u, rfl, rfl⟩
    change (fFin R₀ F j ≫ ιFin R₀ F j).base u = (fInf R₀ F j ≫ ιInf R₀ F j).base u
    rw [glue_condition]

theorem range_fInf : Set.range (fInf R₀ F j).base =
    ((PrimeSpectrum.basicOpen (jInvChartInf R₀ F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgInf R₀ F j))) :
      Set (PrimeSpectrum (chartAlgInf R₀ F j))) := by
  letI := (inclInf R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf R₀ F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R₀ F j) (jInvChartInf R₀ F j)

theorem range_fFin : Set.range (fFin R₀ F j).base =
    ((PrimeSpectrum.basicOpen (jChartFin R₀ F j) :
        TopologicalSpace.Opens (PrimeSpectrum (chartAlgFin R₀ F j))) :
      Set (PrimeSpectrum (chartAlgFin R₀ F j))) := by
  letI := (inclFin R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R₀ F j
  exact PrimeSpectrum.localization_away_comap_range (chartAlgMid R₀ F j) (jChartFin R₀ F j)

theorem ιInf_mem_range_ιFin_iff (xi : XInf R₀ F j) :
    (ιInf R₀ F j).base xi ∈ Set.range (ιFin R₀ F j).base ↔ jInvChartInf R₀ F j ∉ xi.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fInf, Set.mem_range]
  constructor
  · rintro ⟨x₀, h⟩
    obtain ⟨u, -, hu⟩ := (ιFin_eq_ιInf_iff R₀ F j x₀ xi).mp h
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(fFin R₀ F j).base u, (ιFin_eq_ιInf_iff R₀ F j _ _).mpr ⟨u, rfl, rfl⟩⟩

theorem ιFin_mem_range_ιInf_iff (x₀ : XFin R₀ F j) :
    (ιFin R₀ F j).base x₀ ∈ Set.range (ιInf R₀ F j).base ↔ jChartFin R₀ F j ∉ x₀.asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← range_fFin, Set.mem_range]
  constructor
  · rintro ⟨xi, h⟩
    obtain ⟨u, hu, -⟩ := (ιFin_eq_ιInf_iff R₀ F j x₀ xi).mp h.symm
    exact ⟨u, hu⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(fInf R₀ F j).base u, ((ιFin_eq_ιInf_iff R₀ F j _ _).mpr ⟨u, rfl, rfl⟩).symm⟩

theorem mem_range_ιInf_of_not_mem_range_ιFin {x : X₀}
    (hx : x ∉ Set.range (ιFin R₀ F j).base) : x ∈ Set.range (ιInf R₀ F j).base :=
  (mem_range_ιFin_or_mem_range_ιInf R₀ F j x).resolve_left hx

abbrev ιMid : XMid R₀ F j ⟶ X₀ := fFin R₀ F j ≫ ιFin R₀ F j

scoped instance isOpenImmersion_ιMid : IsOpenImmersion (ιMid R₀ F j) := IsOpenImmersion.comp _ _

theorem ιMid_eq' : ιMid R₀ F j = fInf R₀ F j ≫ ιInf R₀ F j := glue_condition R₀ F j

scoped instance compactSpace : CompactSpace X₀ := by
  refine ⟨?_⟩
  have h : Set.range (ιFin R₀ F j).base ∪ Set.range (ιInf R₀ F j).base = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_range_ιFin_or_mem_range_ιInf R₀ F j x
  rw [← h]
  exact (isCompact_range (ιFin R₀ F j).base.hom.continuous).union
    (isCompact_range (ιInf R₀ F j).base.hom.continuous)

scoped instance quasiCompact_toBase : QuasiCompact (toBase R₀ F j) :=
  (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr inferInstance

section FiniteType

variable [IsNoetherianRing R₀] [Algebra.FiniteType R₀ (chartAlgFin R₀ F j)]
  [Algebra.FiniteType R₀ (chartAlgInf R₀ F j)]

scoped instance isNoetherianRing_chartAlgFin : IsNoetherianRing (chartAlgFin R₀ F j) :=
  Algebra.FiniteType.isNoetherianRing R₀ _

scoped instance isNoetherianRing_chartAlgInf : IsNoetherianRing (chartAlgInf R₀ F j) :=
  Algebra.FiniteType.isNoetherianRing R₀ _

scoped instance isNoetherianRing_chartAlgMid : IsNoetherianRing (chartAlgMid R₀ F j) := by
  letI := (inclFin R₀ F j).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin R₀ F j
  exact IsLocalization.isNoetherianRing (Submonoid.powers (jChartFin R₀ F j)) _ inferInstance

scoped instance isLocallyNoetherian : IsLocallyNoetherian X₀ := by
  refine (isLocallyNoetherian_iff_openCover (X := X₀)
    (Scheme.IsLocallyDirected.openCover (span (fFin R₀ F j) (fInf R₀ F j)))).mpr ?_
  rintro (_ | _ | _)
  · change IsLocallyNoetherian (XMid R₀ F j)
    infer_instance
  · change IsLocallyNoetherian (XFin R₀ F j)
    infer_instance
  · change IsLocallyNoetherian (XInf R₀ F j)
    infer_instance

scoped instance quasiSeparated_toBase : QuasiSeparated (toBase R₀ F j) :=
  QuasiSeparated.of_quasiSeparatedSpace _

scoped instance locallyOfFiniteType_toBase : LocallyOfFiniteType (toBase R₀ F j) := by
  have h₀' : LocallyOfFiniteType (ιFin R₀ F j ≫ toBase R₀ F j) := by
    rw [ιFin_toBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hInf' : LocallyOfFiniteType (ιInf R₀ F j ≫ toBase R₀ F j) := by
    rw [ιInf_toBase, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Scheme.IsLocallyDirected.openCover (span (fFin R₀ F j) (fInf R₀ F j))) ?_
  rintro (_ | _ | _)
  · have key : (Scheme.IsLocallyDirected.openCover (span (fFin R₀ F j) (fInf R₀ F j))).f none ≫
        toBase R₀ F j = fFin R₀ F j ≫ (ιFin R₀ F j ≫ toBase R₀ F j) := by
      show colimit.ι (span (fFin R₀ F j) (fInf R₀ F j)) none ≫ toBase R₀ F j = _
      rw [← colimit.w (span (fFin R₀ F j) (fInf R₀ F j)) WalkingSpan.Hom.fst]
      erw [Category.assoc]
    erw [key]
    haveI := h₀'
    exact inferInstanceAs (LocallyOfFiniteType (fFin R₀ F j ≫ (ιFin R₀ F j ≫ toBase R₀ F j)))
  · change LocallyOfFiniteType (ιFin R₀ F j ≫ toBase R₀ F j)
    exact h₀'
  · change LocallyOfFiniteType (ιInf R₀ F j ≫ toBase R₀ F j)
    exact hInf'

end FiniteType

section RingLemmas

variable {B R K : Type*} [CommRing B] [CommRing R] [CommRing K]

def liftOfRange (j : R →+* K) (hj : Function.Injective j) (g : B →+* K)
    (h : ∀ b, g b ∈ j.range) : B →+* R :=
  (RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩).symm.toRingHom.comp
    (g.codRestrict j.range h)

theorem liftOfRange_spec (j : R →+* K) (hj : Function.Injective j) (g : B →+* K)
    (h : ∀ b, g b ∈ j.range) (b : B) : j (liftOfRange j hj g h b) = g b := by
  set e := RingEquiv.ofBijective j.rangeRestrict
      ⟨fun _ _ e => hj (congrArg Subtype.val e), j.rangeRestrict_surjective⟩
  have : e (e.symm ⟨g b, h b⟩) = ⟨g b, h b⟩ := e.apply_symm_apply _
  exact congrArg Subtype.val this

theorem comp_liftOfRange (j : R →+* K) (hj : Function.Injective j) (g : B →+* K)
    (h : ∀ b, g b ∈ j.range) : j.comp (liftOfRange j hj g h) = g :=
  RingHom.ext (liftOfRange_spec j hj g h)

end RingLemmas

theorem SpecMap_cancel {R K Y : CommRingCat.{u}} (j : R ⟶ K) (hj : Function.Injective j)
    (u v : Spec R ⟶ Spec Y) (h : Spec.map j ≫ u = Spec.map j ≫ v) : u = v := by
  haveI : Mono j := ConcreteCategory.mono_of_injective j hj
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  rw [cancel_mono] at h'
  rw [← Spec.map_preimage u, ← Spec.map_preimage v, h']

section Existence

variable {R₀ F j}

structure ChartDatum (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) where

  g : CommRingCat.of (A : Type u) ⟶ CommRingCat.of S.K
  fac : Spec.map g ≫ ι = S.i₁
  compat : CommRingCat.ofHom (algebraMap R₀ A) ≫ g =
    Spec.preimage S.i₂ ≫ CommRingCat.ofHom (algebraMap S.R S.K)

def chartDatumOfMem (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) [IsOpenImmersion ι]
    (hι : ι ≫ toBase R₀ F j = Spec.map (CommRingCat.ofHom (algebraMap R₀ A)))
    (hx : S.i₁.base (closedPoint S.K) ∈ Set.range ι.base) : ChartDatum S A ι := by
  have H : Set.range S.i₁.base ⊆ Set.range ι.base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint S.K := Subsingleton.elim _ _
    exact hx
  refine ⟨Spec.preimage (IsOpenImmersion.lift ι S.i₁ H), ?_, ?_⟩
  · rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← hι,
      ← Category.assoc, IsOpenImmersion.lift_fac]
    exact S.commSq.w

theorem hasLift_of_chartDatum (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι)
    (hrange : ∀ a : A, D.g.hom a ∈ (algebraMap S.R S.K).range) : S.commSq.HasLift := by
  let ψ : (A : Type u) →+* S.R :=
    liftOfRange (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) D.g.hom hrange
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap S.R S.K) = D.g := by
    ext a
    exact liftOfRange_spec (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) _ hrange a
  let l : Spec (.of S.R) ⟶ X₀ := Spec.map (CommRingCat.ofHom ψ) ≫ ι
  have fac_left : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁ := by
    rw [← D.fac, ← hψ, Spec.map_comp, Category.assoc]
  refine CommSq.HasLift.mk' ⟨l, fac_left, ?_⟩
  apply SpecMap_cancel (CommRingCat.ofHom (algebraMap S.R S.K)) (IsFractionRing.injective S.R S.K)
  rw [← Category.assoc, fac_left, S.commSq.w]

theorem algebraMap_mem_range (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι) (c : R₀) :
    D.g.hom (algebraMap R₀ A c) ∈ (algebraMap S.R S.K).range := by
  refine ⟨(Spec.preimage S.i₂).hom c, ?_⟩
  have := congrArg (fun f : CommRingCat.of R₀ ⟶ CommRingCat.of S.K => f.hom c) D.compat
  exact this.symm

theorem mem_range_of_isIntegral (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι)
    (T : Set F) (hTA : T ⊆ A) (hAT : A ≤ chartAlg R₀ F T)
    (hT : ∀ (t : F) (ht : t ∈ T), D.g.hom ⟨t, hTA ht⟩ ∈ (algebraMap S.R S.K).range) (a : A) :
    D.g.hom a ∈ (algebraMap S.R S.K).range := by
  classical
  haveI : IsIntegrallyClosed S.R := GCDMonoid.toIsIntegrallyClosed
  have hadjA : Algebra.adjoin R₀ T ≤ A := Algebra.adjoin_le hTA
  let incl : Algebra.adjoin R₀ T →+* A := (Subalgebra.inclusion hadjA).toRingHom
  let g₀ : Algebra.adjoin R₀ T →+* S.K := D.g.hom.comp incl

  have hg₀ : ∀ (y : F) (hy : y ∈ Algebra.adjoin R₀ T),
      D.g.hom ⟨y, hadjA hy⟩ ∈ (algebraMap S.R S.K).range := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => exact hT y hy
    | algebraMap c => exact algebraMap_mem_range S A ι D c
    | add y z hy hz ihy ihz =>
      have : (⟨y + z, hadjA (add_mem hy hz)⟩ : A) = ⟨y, hadjA hy⟩ + ⟨z, hadjA hz⟩ := rfl
      rw [this, map_add]
      exact add_mem ihy ihz
    | mul y z hy hz ihy ihz =>
      have : (⟨y * z, hadjA (mul_mem hy hz)⟩ : A) = ⟨y, hadjA hy⟩ * ⟨z, hadjA hz⟩ := rfl
      rw [this, map_mul]
      exact mul_mem ihy ihz
  have hg₀' : ∀ y, g₀ y ∈ (algebraMap S.R S.K).range := fun y => hg₀ y y.2
  let g₁ : Algebra.adjoin R₀ T →+* S.R :=
    liftOfRange (algebraMap S.R S.K) (IsFractionRing.injective S.R S.K) g₀ hg₀'
  have hg₁ : (algebraMap S.R S.K).comp g₁ = g₀ := comp_liftOfRange _ _ _ _

  obtain ⟨f, hf, hfa⟩ : IsIntegral (Algebra.adjoin R₀ T) (a : F) := hAT a.2
  have hval : (algebraMap (Algebra.adjoin R₀ T) F) = A.val.toRingHom.comp incl :=
    RingHom.ext fun _ => rfl
  have hfaA : Polynomial.eval₂ incl a f = 0 := by
    apply Subtype.val_injective
    have h := Polynomial.hom_eval₂ f incl A.val.toRingHom a
    change A.val.toRingHom (Polynomial.eval₂ incl a f) = ((0 : A) : F)
    rw [h, ← hval]
    exact hfa
  have hfaK : Polynomial.eval₂ g₀ (D.g.hom a) f = 0 := by
    have h := Polynomial.hom_eval₂ f incl D.g.hom a
    rw [hfaA, map_zero] at h
    exact h.symm
  have hint : IsIntegral S.R (D.g.hom a) := by
    refine ⟨f.map g₁, hf.map g₁, ?_⟩
    rw [Polynomial.eval₂_map, hg₁, hfaK]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨y, hy⟩

theorem ιFin_toBase' : ιFin R₀ F j ≫ toBase R₀ F j =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (chartAlgFin R₀ F j))) := ιFin_toBase R₀ F j

theorem ιInf_toBase' : ιInf R₀ F j ≫ toBase R₀ F j =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (chartAlgInf R₀ F j))) := ιInf_toBase R₀ F j

theorem ιMid_toBase : ιMid R₀ F j ≫ toBase R₀ F j =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ (chartAlgMid R₀ F j))) := by
  rw [Category.assoc, ιFin_toBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg Spec.map (congrArg CommRingCat.ofHom
    (RingHom.ext fun c => ((inclFin R₀ F j).commutes c)))

theorem inclFin_j_mul_inclInf_jInv :
    inclFin R₀ F j (jChartFin R₀ F j) * inclInf R₀ F j (jInvChartInf R₀ F j) = 1 :=
  Subtype.ext (by
    rw [Subalgebra.coe_mul, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf,
      Subalgebra.coe_one, mul_inv_cancel₀ (j_ne_zero j)])

theorem base_eq (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι) :
    ι.base ((Spec.map D.g).base (closedPoint S.K)) = S.i₁.base (closedPoint S.K) := by
  rw [← D.fac]
  rfl

theorem not_mem_of_ne_zero (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) (D : ChartDatum S A ι) (a : A) (ha : D.g.hom a ≠ 0) :
    a ∉ ((Spec.map D.g).base (closedPoint S.K)).asIdeal := by
  intro hmem
  apply ha
  have h : D.g.hom a ∈ (closedPoint S.K).asIdeal := hmem
  change D.g.hom a ∈ maximalIdeal S.K at h
  rwa [maximalIdeal_eq_bot, Ideal.mem_bot] at h

theorem comp_eq_of_fac (S : ValuativeCommSq (toBase R₀ F j)) (A : Subalgebra R₀ F)
    (ι : Spec (CommRingCat.of A) ⟶ X₀) [IsOpenImmersion ι] (D : ChartDatum S A ι)
    (DMid : ChartDatum S (chartAlgMid R₀ F j) (ιMid R₀ F j)) (i : A →ₐ[R₀] chartAlgMid R₀ F j)
    (hi : Spec.map (CommRingCat.ofHom i.toRingHom) ≫ ι = ιMid R₀ F j) :
    CommRingCat.ofHom i.toRingHom ≫ DMid.g = D.g := by
  apply Spec.map_injective
  rw [← cancel_mono ι, Spec.map_comp, Category.assoc, hi, D.fac, DMid.fac]

theorem hasLift_of_mem_range_ιFin (S : ValuativeCommSq (toBase R₀ F j))
    (hx : S.i₁.base (closedPoint S.K) ∈ Set.range (ιFin R₀ F j).base) : S.commSq.HasLift := by
  let D := chartDatumOfMem S (chartAlgFin R₀ F j) (ιFin R₀ F j) (ιFin_toBase' ) hx

  have hfin : D.g.hom (jChartFin R₀ F j) ∈ (algebraMap S.R S.K).range → S.commSq.HasLift := by
    intro hj
    refine hasLift_of_chartDatum S _ _ D (mem_range_of_isIntegral S _ _ D {j}
      (subset_chartAlg R₀ F _) le_rfl ?_)
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    exact hj
  rcases ValuationRing.isInteger_or_isInteger S.R (D.g.hom (jChartFin R₀ F j)) with h | h
  · exact hfin (RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h))
  by_cases hj0 : D.g.hom (jChartFin R₀ F j) = 0
  · exact hfin (hj0 ▸ zero_mem _)

  have hp := base_eq S _ _ D
  have hjp := not_mem_of_ne_zero S _ _ D _ hj0
  have hxInf : S.i₁.base (closedPoint S.K) ∈ Set.range (ιInf R₀ F j).base := by
    rw [← hp]
    exact (ιFin_mem_range_ιInf_iff R₀ F j _).mpr hjp
  obtain ⟨q, hq⟩ := hxInf
  obtain ⟨u, hu₁, hu₂⟩ := (ιFin_eq_ιInf_iff R₀ F j _ q).mp (hp.trans hq.symm)
  have hxMid : S.i₁.base (closedPoint S.K) ∈ Set.range (ιMid R₀ F j).base := by
    refine ⟨u, ?_⟩
    rw [← hp, ← hu₁]
    rfl
  let DInf := chartDatumOfMem S (chartAlgInf R₀ F j) (ιInf R₀ F j) ιInf_toBase' ⟨q, hq⟩
  let DMid := chartDatumOfMem S (chartAlgMid R₀ F j) (ιMid R₀ F j) ιMid_toBase hxMid
  have cFin : CommRingCat.ofHom (inclFin R₀ F j).toRingHom ≫ DMid.g = D.g :=
    comp_eq_of_fac S _ _ D DMid (inclFin R₀ F j) rfl
  have cInf : CommRingCat.ofHom (inclInf R₀ F j).toRingHom ≫ DMid.g = DInf.g :=
    comp_eq_of_fac S _ _ DInf DMid (inclInf R₀ F j) (ιMid_eq' R₀ F j).symm
  have hprod : D.g.hom (jChartFin R₀ F j) * DInf.g.hom (jInvChartInf R₀ F j) = 1 := by
    rw [← cFin, ← cInf]
    change DMid.g.hom (inclFin R₀ F j (jChartFin R₀ F j)) * DMid.g.hom (inclInf R₀ F j (jInvChartInf R₀ F j)) = 1
    rw [← map_mul, inclFin_j_mul_inclInf_jInv, map_one]
  have hinv : DInf.g.hom (jInvChartInf R₀ F j) = (D.g.hom (jChartFin R₀ F j))⁻¹ :=
    eq_inv_of_mul_eq_one_right hprod
  refine hasLift_of_chartDatum S _ _ DInf (mem_range_of_isIntegral S _ _ DInf {j⁻¹}
    (subset_chartAlg R₀ F _) le_rfl ?_)
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  subst ht
  change DInf.g.hom (jInvChartInf R₀ F j) ∈ _
  rw [hinv]
  exact RingHom.mem_range.mpr (RingHom.mem_rangeS.mp h)

theorem hasLift_of_mem_range_ιInf (S : ValuativeCommSq (toBase R₀ F j))
    (hx : S.i₁.base (closedPoint S.K) ∈ Set.range (ιInf R₀ F j).base) : S.commSq.HasLift := by
  by_cases hx' : S.i₁.base (closedPoint S.K) ∈ Set.range (ιFin R₀ F j).base
  · exact hasLift_of_mem_range_ιFin S hx'

  let D := chartDatumOfMem S (chartAlgInf R₀ F j) (ιInf R₀ F j) ιInf_toBase' hx
  have hp := base_eq S _ _ D
  have hj0 : D.g.hom (jInvChartInf R₀ F j) = 0 := by
    by_contra h
    apply hx'
    rw [← hp]
    exact (ιInf_mem_range_ιFin_iff R₀ F j _).mpr (not_mem_of_ne_zero S _ _ D _ h)
  refine hasLift_of_chartDatum S _ _ D (mem_range_of_isIntegral S _ _ D {j⁻¹}
    (subset_chartAlg R₀ F _) le_rfl ?_)
  intro t ht
  rw [Set.mem_singleton_iff] at ht
  subst ht
  change D.g.hom (jInvChartInf R₀ F j) ∈ _
  rw [hj0]
  exact zero_mem _

variable (R₀ F j) in

theorem valuativeCriterion_existence : ValuativeCriterion.Existence (toBase R₀ F j) := by
  intro S
  rcases mem_range_ιFin_or_mem_range_ιInf R₀ F j (S.i₁.base (closedPoint S.K)) with hx | hx
  · exact hasLift_of_mem_range_ιFin S hx
  · exact hasLift_of_mem_range_ιInf S hx

end Existence

section Uniqueness

variable {R₀ F j}

theorem range_subset_of_closedPoint_mem {R : Type u} [CommRing R] [IsLocalRing R]
    (l : Spec (CommRingCat.of R) ⟶ X₀) {Y : Scheme.{u}} (ι : Y ⟶ X₀)
    [IsOpenImmersion ι] (h : l.base (closedPoint R) ∈ Set.range ι.base) :
    Set.range l.base ⊆ Set.range ι.base := by
  rintro _ ⟨z, rfl⟩
  have htop := Scheme.preimage_eq_top_of_closedPoint_mem l (U := ι.opensRange) h
  have hz : z ∈ l ⁻¹ᵁ ι.opensRange := by rw [htop]; trivial
  exact hz

theorem liftStruct_eq_of_mem_range {A : Type u} [CommRing A]
    (ιA : Spec (CommRingCat.of A) ⟶ X₀) [IsOpenImmersion ιA]
    (S : ValuativeCommSq (toBase R₀ F j)) (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range ιA.base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range ιA.base) : l₁ = l₂ := by
  have H₁ := range_subset_of_closedPoint_mem l₁.l ιA h₁
  have H₂ := range_subset_of_closedPoint_mem l₂.l ιA h₂
  let m₁ := IsOpenImmersion.lift ιA l₁.l H₁
  let m₂ := IsOpenImmersion.lift ιA l₂.l H₂
  have e₁ : m₁ ≫ ιA = l₁.l := IsOpenImmersion.lift_fac _ _ _
  have e₂ : m₂ ≫ ιA = l₂.l := IsOpenImmersion.lift_fac _ _ _
  have hF : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₁ =
      Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ m₂ := by
    rw [← cancel_mono ιA, Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
  haveI : Mono (CommRingCat.ofHom (algebraMap S.R S.K)) :=
    ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)
  have hm : m₁ = m₂ := by
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, ← Spec.map_comp, ← Spec.map_comp] at hF
    have := Spec.map_injective hF
    rw [cancel_mono] at this
    rw [← Spec.map_preimage m₁, ← Spec.map_preimage m₂, this]
  ext
  rw [← e₁, ← e₂, hm]

theorem false_of_liftStruct_cross (S : ValuativeCommSq (toBase R₀ F j))
    (l₁ l₂ : S.commSq.LiftStruct)
    (h₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιFin R₀ F j).base)
    (h₁' : l₁.l.base (closedPoint S.R) ∉ Set.range (ιInf R₀ F j).base)
    (h₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf R₀ F j).base)
    (h₂' : l₂.l.base (closedPoint S.R) ∉ Set.range (ιFin R₀ F j).base) : False := by
  have H₁ := range_subset_of_closedPoint_mem l₁.l (ιFin R₀ F j) h₁
  have H₂ := range_subset_of_closedPoint_mem l₂.l (ιInf R₀ F j) h₂
  let G₁ : CommRingCat.of (chartAlgFin R₀ F j) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ιFin R₀ F j) l₁.l H₁)
  let G₂ : CommRingCat.of (chartAlgInf R₀ F j) ⟶ CommRingCat.of S.R :=
    Spec.preimage (IsOpenImmersion.lift (ιInf R₀ F j) l₂.l H₂)
  have e₁ : Spec.map G₁ ≫ ιFin R₀ F j = l₁.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have e₂ : Spec.map G₂ ≫ ιInf R₀ F j = l₂.l := by
    rw [Spec.map_preimage]; exact IsOpenImmersion.lift_fac _ _ _
  have ht₁ : G₁ (jChartFin R₀ F j) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₁'
    rw [← e₁, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ιFin_mem_range_ιInf_iff]
    exact hn
  have ht₂ : G₂ (jInvChartInf R₀ F j) ∈ maximalIdeal S.R := by
    by_contra hn
    apply h₂'
    rw [← e₂, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, ιInf_mem_range_ιFin_iff]
    exact hn
  let alg := CommRingCat.ofHom (algebraMap S.R S.K)
  have hov : Set.range (Spec.map alg ≫ Spec.map G₁).base ⊆ Set.range (fFin R₀ F j).base := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = closedPoint S.K := Subsingleton.elim _ _
    have hx : (ιFin R₀ F j).base ((Spec.map alg ≫ Spec.map G₁).base (closedPoint S.K)) ∈
        Set.range (ιInf R₀ F j).base := by
      refine ⟨(Spec.map alg ≫ Spec.map G₂).base (closedPoint S.K), ?_⟩
      change ((Spec.map alg ≫ Spec.map G₂) ≫ ιInf R₀ F j).base (closedPoint S.K) =
        ((Spec.map alg ≫ Spec.map G₁) ≫ ιFin R₀ F j).base (closedPoint S.K)
      rw [Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
    rw [ιFin_mem_range_ιInf_iff] at hx
    rw [range_fFin]
    exact hx
  let u := IsOpenImmersion.lift (fFin R₀ F j) (Spec.map alg ≫ Spec.map G₁) hov
  have hu₀ : u ≫ fFin R₀ F j = Spec.map alg ≫ Spec.map G₁ := IsOpenImmersion.lift_fac _ _ _
  have hui : u ≫ fInf R₀ F j = Spec.map alg ≫ Spec.map G₂ := by
    rw [← cancel_mono (ιInf R₀ F j), Category.assoc, ← glue_condition, ← Category.assoc, hu₀,
      Category.assoc, Category.assoc, e₁, e₂, l₁.fac_left, l₂.fac_left]
  let W := Spec.preimage u
  have hW₀ : CommRingCat.ofHom (inclFin R₀ F j).toRingHom ≫ W = G₁ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hu₀
  have hWi : CommRingCat.ofHom (inclInf R₀ F j).toRingHom ≫ W = G₂ ≫ alg := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage]
    exact hui
  have k₁ : W (inclFin R₀ F j (jChartFin R₀ F j)) = algebraMap S.R S.K (G₁ (jChartFin R₀ F j)) :=
    congrArg (fun f : CommRingCat.of (chartAlgFin R₀ F j) ⟶ CommRingCat.of S.K =>
      f (jChartFin R₀ F j)) hW₀
  have k₂ : W (inclInf R₀ F j (jInvChartInf R₀ F j)) = algebraMap S.R S.K (G₂ (jInvChartInf R₀ F j)) :=
    congrArg (fun f : CommRingCat.of (chartAlgInf R₀ F j) ⟶ CommRingCat.of S.K =>
      f (jInvChartInf R₀ F j)) hWi
  have hone : algebraMap S.R S.K (G₁ (jChartFin R₀ F j) * G₂ (jInvChartInf R₀ F j)) =
      algebraMap S.R S.K 1 := by
    rw [map_mul, map_one, ← k₁, ← k₂, ← map_mul, inclFin_j_mul_inclInf_jInv, map_one]
  have hone' := IsFractionRing.injective S.R S.K hone
  exact (maximalIdeal S.R).ne_top_iff_one.mp (maximalIdeal.isMaximal S.R).ne_top
    (hone' ▸ Ideal.mul_mem_right _ _ ht₁)

variable (R₀ F j) in

theorem valuativeCriterion_uniqueness : ValuativeCriterion.Uniqueness (toBase R₀ F j) := by
  intro S
  refine ⟨fun l₁ l₂ => ?_⟩
  by_cases a₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιFin R₀ F j).base <;>
    by_cases a₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιFin R₀ F j).base
  · exact liftStruct_eq_of_mem_range (ιFin R₀ F j) S l₁ l₂ a₁ a₂
  · have b₂ := mem_range_ιInf_of_not_mem_range_ιFin R₀ F j a₂
    by_cases b₁ : l₁.l.base (closedPoint S.R) ∈ Set.range (ιInf R₀ F j).base
    · exact liftStruct_eq_of_mem_range (ιInf R₀ F j) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross S l₁ l₂ a₁ b₁ b₂ a₂).elim
  · have b₁ := mem_range_ιInf_of_not_mem_range_ιFin R₀ F j a₁
    by_cases b₂ : l₂.l.base (closedPoint S.R) ∈ Set.range (ιInf R₀ F j).base
    · exact liftStruct_eq_of_mem_range (ιInf R₀ F j) S l₁ l₂ b₁ b₂
    · exact (false_of_liftStruct_cross S l₂ l₁ a₂ b₂ b₁ a₁).elim
  · exact liftStruct_eq_of_mem_range (ιInf R₀ F j) S l₁ l₂
      (mem_range_ιInf_of_not_mem_range_ιFin R₀ F j a₁) (mem_range_ιInf_of_not_mem_range_ιFin R₀ F j a₂)

end Uniqueness

theorem isProper_toBase' [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ ↥(chartAlgFin R₀ F j)]
    [Algebra.FiniteType R₀ ↥(chartAlgInf R₀ F j)] :
    IsProper (toBase R₀ F j) :=
  IsProper.of_valuativeCriterion (toBase R₀ F j)
    ((ValuativeCriterion.iff).mpr
      ⟨valuativeCriterion_existence R₀ F j, valuativeCriterion_uniqueness R₀ F j⟩)

end Proper
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel.Proper"

end TwoChartIntegralModel
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel.Proper P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel"

end AlgebraicCurve
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel.Proper P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel.Proper P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve"

p2m_open "AlgebraicGeometry AlgebraicCurve P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase.AlgebraicCurve.TwoChartIntegralModel"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (F : Type u) [Field F] [Algebra R F]
    (j : F) [Fact (j ≠ 0)]
    [Algebra.FiniteType R ↥(chartAlgFin R F j)]
    [Algebra.FiniteType R ↥(chartAlgInf R F j)] :
    IsProper (toBase R F j) :=
  AlgebraicCurve.TwoChartIntegralModel.Proper.isProper_toBase' R F j

end S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_isProper_toBase (solution)
