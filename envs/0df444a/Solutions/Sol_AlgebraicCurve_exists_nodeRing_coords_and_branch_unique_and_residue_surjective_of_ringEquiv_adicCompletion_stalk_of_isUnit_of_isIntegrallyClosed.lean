-- Prove2me | solution 1 for AlgebraicCurve.exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/a9de6070-a2a7-5040-9329-53b58eded8bb

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_AlgebraicCurve_exists_subring_ringEquiv_stalk_of_iso_pullback
import Theorems.Thm_IsLocalRing_exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv
import Theorems.Thm_AlgebraicCurve_localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing
import Theorems.Thm_AlgebraicCurve_mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
import Theorems.Thm_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete
import Theorems.Thm_AlgebraicGeometry_Scheme_isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType
import Theorems.Thm_AlgebraicCurve_SemistableModel_localRing_le_and_exists_mem_localRing_mul_eq_of_specializes
import Theorems.Thm_ModularCurve_UVCrossingModel_mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
import Theorems.Thm_AlgebraicCurve_ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne
import Theorems.Thm_AlgebraicCurve_exists_sub_algebraMap_not_isUnit_and_exists_eq_mul_add_of_iso_pullback_of_maximalIdeal_eq_span
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry ModularCurve ModularCurve.UVCrossingModel

namespace SLIMSkel

theorem coordAdapted
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (w : ℕ) (hw : 1 ≤ w)
    {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    (ι : AdicCompletion (maximalIdeal O) O ≃+* UVCrossingModel W (π ^ w))
    (t : O) (ht : ι (algebraMap O (AdicCompletion (maximalIdeal O) O) t) = const (π ^ w) π)
    (𝔭₁ 𝔭₂ : Ideal O) [𝔭₁.IsPrime] [𝔭₂.IsPrime] (ht₁ : t ∈ 𝔭₁) (ht₂ : t ∈ 𝔭₂)
    (h₁ : 𝔭₁ ≠ maximalIdeal O) (h₂ : 𝔭₂ ≠ maximalIdeal O) (hne : 𝔭₁ ≠ 𝔭₂) :
    ∃ xn yn u : O, IsUnit u ∧ xn * yn = t ^ w * u ∧
      maximalIdeal O = Ideal.span {xn, yn, t} ∧ xn ∈ 𝔭₁ ∧ yn ∈ 𝔭₂ := by
  obtain ⟨xn, yn, u, γ, γ', hu, hγ, hγ', hx, hy, hxy, hmax⟩ :=
    ModularCurve.UVCrossingModel.exists_mul_eq_pow_mul_and_maximalIdeal_eq_span_of_ringEquiv_adicCompletion_pow
      π hπ w hw ι t ht 𝔭₁ 𝔭₂ hne ht₁ ht₂ h₁ h₂
  rcases ModularCurve.UVCrossingModel.mem_iff_ringEquiv_adicCompletion_mem_span_or_swap_of_ne π hπ w hw ι t ht
      𝔭₁ 𝔭₂ hne ht₁ ht₂ h₁ h₂ with ⟨hp₁, hp₂⟩ | ⟨hp₁, hp₂⟩
  · refine ⟨xn, yn, u, hu, hxy, hmax, (hp₁ xn).mpr ?_, (hp₂ yn).mpr ?_⟩
    · rw [hx]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [hy]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · refine ⟨yn, xn, u, hu, by rw [mul_comm, hxy], ?_, (hp₁ yn).mpr ?_, (hp₂ xn).mpr ?_⟩
    · rw [hmax]
      apply le_antisymm <;> rw [Ideal.span_le] <;> intro z hz <;>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz <;>
        rcases hz with rfl | rfl | rfl <;> apply Ideal.subset_span <;> simp
    · rw [hy]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · rw [hx]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem maximalIdeal_eq_span_of_ord_eq_one {K Fb : Type} [Field K] [Field Fb] [Algebra K Fb]
    (v : Place K Fb) (π : ↥v.toValuationSubring) (hπ : v.ord (π : Fb) = 1) :
    maximalIdeal ↥v.toValuationSubring = Ideal.span {π} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↥v.toValuationSubring
  have hπ0 : (π : Fb) ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at hπ; exact zero_ne_one hπ
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hπ0 hϖ
  rw [hπ, zpow_one] at hu
  have hassoc : Associated ϖ π := by
    refine ⟨u, Subtype.ext ?_⟩
    rw [mul_comm]; exact hu.symm
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact Ideal.span_singleton_eq_span_singleton.mpr hassoc

end SLIMSkel

theorem solution
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] [HenselianLocalRing A₀]
    (ι₀ : A₀ →+* ↥A) [IsLocalHom ι₀] (hι₀ : Function.Injective ι₀)
    (hres₀ : Function.Surjective ((IsLocalRing.residue ↥A).comp ι₀))
    (ϖ₀ : A₀) (hϖ₀ : maximalIdeal A₀ = Ideal.span {ϖ₀})
    (halg : ∀ a : ↥A, IsAlgebraic ↥(ι₀.range) a)
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]
    (iso : X ≅ Limits.pullback toBase₀ (Spec.map (CommRingCat.ofHom ι₀)))
    (hiso : iso.hom ≫ Limits.pullback.snd toBase₀ (Spec.map (CommRingCat.ofHom ι₀)) = toBase)

    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x)
    (η₁ η₂ : X) (h₁ : η₁ ⤳ x) (h₂ : η₂ ⤳ x) (h₁x : η₁ ≠ x) (h₂x : η₂ ≠ x) (h₁₂ : η₁ ≠ η₂)
    (hη : ∀ η : X, η ⤳ x → η ≠ x → toBase.base η = closedPoint ↥A → η = η₁ ∨ η = η₂)
    {Fbar₁ : Type} [Field Fbar₁] [Algebra (ResidueField ↥A) Fbar₁]
    {Fbar₂ : Type} [Field Fbar₂] [Algebra (ResidueField ↥A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (hR₁ : R₁.integers.toSubring = SemistableModel.localRing X φ η₁)
    (hR₂ : R₂.integers.toSubring = SemistableModel.localRing X φ η₂)

    (x₀ : X₀) (hx₀ : (iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x = x₀)
    (w : ℕ) (hw : 1 ≤ w) (hwu : IsUnit ((w : ℕ) : A₀))
    (e : AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀) ≃+*
      UVCrossingModel (AdicCompletion (maximalIdeal A₀) A₀)
        ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w))
    (he : ∀ a : A₀,
      e (algebraMap (X₀.presheaf.stalk x₀) (AdicCompletion (maximalIdeal (X₀.presheaf.stalk x₀)) (X₀.presheaf.stalk x₀))
          ((X₀.presheaf.germ ⊤ x₀ trivial).hom
            (toBase₀.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom a)))) =
        const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
          (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) a)) :
    let 𝒩 : Subring F := SemistableModel.localRing X φ x
    ∃ (x₁ : Place (ResidueField ↥A) Fbar₁) (x₂ : Place (ResidueField ↥A) Fbar₂) (S : Set (Place L F)) (xn yn u : F),

      (∀ P : Place L F, P ∈ S ↔
        ∀ f : F, f ∈ 𝒩 → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
          (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ 𝒩, f * g = 1)) ∧

      (∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring) ∧
      (∀ a : ↥A, algebraMap L F (a : L) ∈ 𝒩) ∧

      xn ∈ 𝒩 ∧ yn ∈ 𝒩 ∧ u ∈ 𝒩 ∧ (∃ u' ∈ 𝒩, u * u' = 1) ∧
      (∀ h₁ : xn ∈ R₁.integers, R₁.residue ⟨xn, h₁⟩ = 0) ∧
      (∀ h₂ : xn ∈ R₂.integers, x₂.ord (R₂.residue ⟨xn, h₂⟩) = 1) ∧
      (∀ h₂ : yn ∈ R₂.integers, R₂.residue ⟨yn, h₂⟩ = 0) ∧
      (∀ h₁ : yn ∈ R₁.integers, x₁.ord (R₁.residue ⟨yn, h₁⟩) = 1) ∧
      xn * yn = algebraMap L F ((ι₀ ϖ₀ : ↥A) : L) ^ w * u ∧

      (∀ Q' : Place (ResidueField ↥A) Fbar₁,
        (∀ (f : F) (hf : f ∈ R₁.integers), f ∈ 𝒩 → R₁.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) → Q' = x₁) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar₂,
        (∀ (f : F) (hf : f ∈ R₂.integers), f ∈ 𝒩 → R₂.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) → Q' = x₂) ∧

      (∀ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers), f ∈ 𝒩 →
        ∃ (m₁ : R₁.residue ⟨f, hf₁⟩ ∈ x₁.toValuationSubring) (m₂ : R₂.residue ⟨f, hf₂⟩ ∈ x₂.toValuationSubring)
          (c : ResidueField ↥A),
          IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m₁⟩ = algebraMap (ResidueField ↥A) x₁.ResidueField c ∧
          IsLocalRing.residue ↥x₂.toValuationSubring ⟨_, m₂⟩ = algebraMap (ResidueField ↥A) x₂.ResidueField c) ∧

      (∀ (g₁ : Fbar₁) (g₂ : Fbar₂) (m₁ : g₁ ∈ x₁.toValuationSubring) (m₂ : g₂ ∈ x₂.toValuationSubring) (c : ResidueField ↥A),
        IsLocalRing.residue ↥x₁.toValuationSubring ⟨g₁, m₁⟩ = algebraMap (ResidueField ↥A) x₁.ResidueField c →
        IsLocalRing.residue ↥x₂.toValuationSubring ⟨g₂, m₂⟩ = algebraMap (ResidueField ↥A) x₂.ResidueField c →
          ∃ (f : F) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers), f ∈ 𝒩 ∧
            R₁.residue ⟨f, hf₁⟩ = g₁ ∧ R₂.residue ⟨f, hf₂⟩ = g₂) := by
  intro 𝒩
  subst hx₀

  let S : Set (Place L F) := {P | ∀ f : F, f ∈ 𝒩 → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
    (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ 𝒩, f * g = 1)}
  have hS : ∀ P : Place L F, P ∈ S ↔ ∀ f : F, f ∈ 𝒩 → f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
      (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ 𝒩, f * g = 1) := fun P => Iff.rfl

  obtain ⟨hK6, hAconst⟩ := AlgebraicCurve.localRing_le_integers_and_forall_mem_toValuationSubring_and_algebraMap_mem_localRing A hrk X toBase φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀ iso hiso
    x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ _ rfl w hw e he S hS
  have hK7 := AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_toValuationSubring_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed A hrk X toBase hn φ hφ A₀ ι₀ hι₀ ϖ₀ hϖ₀ halg X₀ toBase₀
    iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ _ rfl w hw e he S hS
  have h𝒩R₁ : ∀ f : F, f ∈ 𝒩 → f ∈ R₁.integers := fun f hf => (hK6 f hf).1
  have h𝒩R₂ : ∀ f : F, f ∈ 𝒩 → f ∈ R₂.integers := fun f hf => (hK6 f hf).2.1

  obtain ⟨𝒩₀, θ, hθv, hmem₀, hle, hloc₀, hnoe₀, hconst₀, hθc⟩ :=
    AlgebraicCurve.exists_subring_ringEquiv_stalk_of_iso_pullback A X toBase φ hφ A₀ ι₀ hι₀ X₀ toBase₀ iso hiso x
  haveI := hloc₀
  haveI := hnoe₀
  let c₀ : A₀ →+* ↑(X₀.presheaf.stalk ((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).base x)) :=
    (X₀.presheaf.germ ⊤ _ trivial).hom.comp (toBase₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv.hom)
  obtain ⟨σ, ι, hσ, hconst, htr⟩ := IsLocalRing.exists_ringHom_ringEquiv_adicCompletion_uvCrossingModel_of_ringEquiv ϖ₀ w c₀ e he θ

  have hirr₀ : Irreducible ϖ₀ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).mpr hϖ₀
  obtain ⟨hdom, hdvr, hcompl, hirr, -, -⟩ := IsDiscreteValuationRing.adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete A₀ ϖ₀ hirr₀
  have hwuÂ : IsUnit ((w : ℕ) : AdicCompletion (maximalIdeal A₀) A₀) := by
    simpa using hwu.map (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀))

  let t : ↥𝒩₀ := ⟨algebraMap L F ((ι₀ ϖ₀ : ↥A) : L), hconst₀ ϖ₀⟩
  have hθt : θ (c₀ ϖ₀) = t := Subtype.ext (hθc ϖ₀)
  have ht : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) t) =
      const ((algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) ^ w)
        (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) := by
    rw [← hθt, htr, ← he ϖ₀]
    rfl

  let ψ₁ : ↥𝒩₀ →+* Fbar₁ :=
    R₁.residue.comp (Subring.inclusion (show 𝒩₀ ≤ R₁.integers.toSubring from fun f hf => h𝒩R₁ f (hle hf)))
  let ψ₂ : ↥𝒩₀ →+* Fbar₂ :=
    R₂.residue.comp (Subring.inclusion (show 𝒩₀ ≤ R₂.integers.toSubring from fun f hf => h𝒩R₂ f (hle hf)))
  have hψ₁ : ∀ f : ↥𝒩₀, ψ₁ f = R₁.residue ⟨(f : F), h𝒩R₁ f (hle f.2)⟩ := fun f => rfl
  have hψ₂ : ∀ f : ↥𝒩₀, ψ₂ f = R₂.residue ⟨(f : F), h𝒩R₂ f (hle f.2)⟩ := fun f => rfl
  haveI hp₁ : (RingHom.ker ψ₁).IsPrime := RingHom.ker_isPrime ψ₁
  haveI hp₂ : (RingHom.ker ψ₂).IsPrime := RingHom.ker_isPrime ψ₂

  have hres_const : ∀ (a : ↥A), a ∈ maximalIdeal ↥A →
      (∀ h, R₁.residue ⟨algebraMap L F (a : L), h⟩ = 0) ∧ (∀ h, R₂.residue ⟨algebraMap L F (a : L), h⟩ = 0) := by
    intro a ha
    have h0 : IsLocalRing.residue ↥A a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := R₁.residue_algebraMap a
      rw [h0, map_zero] at this
      convert this
    · have := R₂.residue_algebraMap a
      rw [h0, map_zero] at this
      convert this
  have hϖA : (ι₀ ϖ₀ : ↥A) ∈ maximalIdeal ↥A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hirr₀.not_isUnit ((isUnit_map_iff ι₀ ϖ₀).mp hu)
  have ht₁ : t ∈ RingHom.ker ψ₁ := by
    rw [RingHom.mem_ker, hψ₁]; exact (hres_const _ hϖA).1 _
  have ht₂ : t ∈ RingHom.ker ψ₂ := by
    rw [RingHom.mem_ker, hψ₂]; exact (hres_const _ hϖA).2 _

  obtain ⟨hp₁₂, hp₁m, hp₂m⟩ :=
    AlgebraicCurve.ker_residue_ne_and_ne_maximalIdeal_of_iso_pullback_of_specializes_of_ne A hrk X toBase φ hφ A₀ ι₀ hι₀ hres₀ ϖ₀ hϖ₀ halg X₀ toBase₀
    iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ _ rfl w hw hwu e he 𝒩₀ hmem₀ hle
    (fun f hf => h𝒩R₁ f (hle hf)) (fun f hf => h𝒩R₂ f (hle hf))

  have hπÂ : maximalIdeal (AdicCompletion (maximalIdeal A₀) A₀) =
      Ideal.span {algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hirr
  obtain ⟨xn₀, yn₀, u₀, hu₀, hxy₀, hmax₀, hxn₁, hyn₂⟩ :=
    SLIMSkel.coordAdapted (O := ↥𝒩₀) (algebraMap A₀ (AdicCompletion (maximalIdeal A₀) A₀) ϖ₀) hπÂ w hw ι t ht
      (RingHom.ker ψ₁) (RingHom.ker ψ₂) ht₁ ht₂ hp₁m hp₂m hp₁₂
  have hyn₁ : yn₀ ∉ RingHom.ker ψ₁ := by
    intro hmem
    apply hp₁m
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top hp₁)) ?_
    rw [hmax₀, Ideal.span_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hxn₁
    · exact hmem
    · exact ht₁
  have hxn₂ : xn₀ ∉ RingHom.ker ψ₂ := by
    intro hmem
    apply hp₂m
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top hp₂)) ?_
    rw [hmax₀, Ideal.span_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hmem
    · exact hyn₂
    · exact ht₂

  let j𝒩 : ↑(X.presheaf.stalk x) →+* F := (φ.symm : X.functionField ≃+* F).toRingHom.comp
    (algebraMap (X.presheaf.stalk x) X.functionField)
  have hj𝒩 : Function.Injective j𝒩 :=
    (φ.symm : X.functionField ≃+* F).injective.comp (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
  have hj𝒩r : j𝒩.range = 𝒩 := rfl
  let e𝒩 : ↑(X.presheaf.stalk x) ≃+* ↥𝒩 :=
    RingEquiv.ofBijective j𝒩.rangeRestrict ⟨fun a b h => hj𝒩 (congrArg Subtype.val h), j𝒩.rangeRestrict_surjective⟩
  have he𝒩 : ∀ g, ((e𝒩 g : ↥𝒩) : F) = φ.symm (algebraMap (X.presheaf.stalk x) X.functionField g) := fun g => rfl
  haveI h𝒩loc : IsLocalRing ↥𝒩 :=
    IsLocalRing.of_surjective' (e𝒩.toRingHom : ↑(X.presheaf.stalk x) →+* ↥𝒩) (fun y => e𝒩.surjective y)
  have hincl : ∀ f : ↥𝒩₀, IsUnit (⟨(f : F), hle f.2⟩ : ↥𝒩) → IsUnit f := by
    intro f hf
    obtain ⟨g, rfl⟩ := θ.surjective f
    have hfg : (⟨((θ g : ↥𝒩₀) : F), hle (θ g).2⟩ : ↥𝒩) =
        e𝒩 (((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).stalkMap x).hom g) :=
      Subtype.ext (by rw [he𝒩]; exact hθv g)
    rw [hfg] at hf
    have hg : IsUnit (((iso.hom ≫ Limits.pullback.fst toBase₀ (Spec.map (CommRingCat.ofHom ι₀))).stalkMap x).hom g) := by
      simpa using hf.map e𝒩.symm
    exact ((isUnit_map_iff _ g).mp hg).map θ

  obtain ⟨hres, hrawmax⟩ := AlgebraicCurve.exists_sub_algebraMap_not_isUnit_and_exists_eq_mul_add_of_iso_pullback_of_maximalIdeal_eq_span A hrk X toBase hn φ hφ A₀ ι₀ hι₀ hres₀ ϖ₀ hϖ₀ halg X₀ toBase₀
    iso hiso x hx hxc η₁ η₂ h₁ h₂ h₁x h₂x h₁₂ hη R₁ R₂ hR₁ hR₂ _ rfl w hw hwu e he 𝒩₀ θ hθv hle hAconst
    xn₀ yn₀ t rfl hmax₀

  let ynN : ↥𝒩 := ⟨(yn₀ : F), hle yn₀.2⟩
  let xnN : ↥𝒩 := ⟨(xn₀ : F), hle xn₀.2⟩
  have hynu : ¬ IsUnit ynN := fun hu => by
    have := hincl yn₀ hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hmax₀.symm ▸ Ideal.subset_span (by simp)) this
  have hxnu : ¬ IsUnit xnN := fun hu => by
    have := hincl xn₀ hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hmax₀.symm ▸ Ideal.subset_span (by simp)) this
  have hyn0 : R₁.residue ⟨(ynN : F), h𝒩R₁ _ ynN.2⟩ ≠ 0 := fun h0 => hyn₁ (by rw [RingHom.mem_ker, hψ₁]; exact h0)
  have hxn0 : R₂.residue ⟨(xnN : F), h𝒩R₂ _ xnN.2⟩ ≠ 0 := fun h0 => hxn₂ (by rw [RingHom.mem_ker, hψ₂]; exact h0)
  have hmax₁ : ∀ f : ↥𝒩, ¬ IsUnit f →
      ∃ g h : ↥𝒩, R₁.residue ⟨(h : F), h𝒩R₁ h h.2⟩ = 0 ∧ f = ynN * g + h := by
    intro f hf
    obtain ⟨α, β, γ, δ, p, hp, hfe⟩ := hrawmax f hf
    refine ⟨β, xnN * α + ⟨(t : F), hle t.2⟩ * γ + ⟨algebraMap L F (p : L), hAconst p⟩ * δ, ?_, ?_⟩
    · let ρ : ↥𝒩 →+* Fbar₁ :=
        R₁.residue.comp (Subring.inclusion (show 𝒩 ≤ R₁.integers.toSubring from fun f hf => h𝒩R₁ f hf))
      have hρ : ∀ f : ↥𝒩, ρ f = R₁.residue ⟨(f : F), h𝒩R₁ f f.2⟩ := fun f => rfl
      rw [← hρ, map_add, map_add, map_mul, map_mul, map_mul, hρ xnN, hρ ⟨(t : F), hle t.2⟩,
        hρ ⟨algebraMap L F (p : L), hAconst p⟩]
      have h0a : R₁.residue ⟨((xnN : ↥𝒩) : F), h𝒩R₁ _ xnN.2⟩ = 0 := by
        have := hxn₁; rw [RingHom.mem_ker, hψ₁] at this; exact this
      have h0t : R₁.residue ⟨((⟨(t : F), hle t.2⟩ : ↥𝒩) : F), h𝒩R₁ _ (hle t.2)⟩ = 0 := (hres_const _ hϖA).1 _
      have h0p : R₁.residue ⟨((⟨algebraMap L F (p : L), hAconst p⟩ : ↥𝒩) : F), h𝒩R₁ _ (hAconst p)⟩ = 0 :=
        (hres_const p hp).1 _
      rw [h0a, h0t, h0p]; ring
    · rw [hfe]; ring
  have hmax₂ : ∀ f : ↥𝒩, ¬ IsUnit f →
      ∃ g h : ↥𝒩, R₂.residue ⟨(h : F), h𝒩R₂ h h.2⟩ = 0 ∧ f = xnN * g + h := by
    intro f hf
    obtain ⟨α, β, γ, δ, p, hp, hfe⟩ := hrawmax f hf
    refine ⟨α, ynN * β + ⟨(t : F), hle t.2⟩ * γ + ⟨algebraMap L F (p : L), hAconst p⟩ * δ, ?_, ?_⟩
    · let ρ : ↥𝒩 →+* Fbar₂ :=
        R₂.residue.comp (Subring.inclusion (show 𝒩 ≤ R₂.integers.toSubring from fun f hf => h𝒩R₂ f hf))
      have hρ : ∀ f : ↥𝒩, ρ f = R₂.residue ⟨(f : F), h𝒩R₂ f f.2⟩ := fun f => rfl
      rw [← hρ, map_add, map_add, map_mul, map_mul, map_mul, hρ ynN, hρ ⟨(t : F), hle t.2⟩,
        hρ ⟨algebraMap L F (p : L), hAconst p⟩]
      have h0a : R₂.residue ⟨((ynN : ↥𝒩) : F), h𝒩R₂ _ ynN.2⟩ = 0 := by
        have := hyn₂; rw [RingHom.mem_ker, hψ₂] at this; exact this
      have h0t : R₂.residue ⟨((⟨(t : F), hle t.2⟩ : ↥𝒩) : F), h𝒩R₂ _ (hle t.2)⟩ = 0 := (hres_const _ hϖA).2 _
      have h0p : R₂.residue ⟨((⟨algebraMap L F (p : L), hAconst p⟩ : ↥𝒩) : F), h𝒩R₂ _ (hAconst p)⟩ = 0 :=
        (hres_const p hp).2 _
      rw [h0a, h0t, h0p]; ring
    · rw [hfe]; ring

  let cA : ↥A →+* ↑(X.presheaf.stalk x) :=
    (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
  have hNq : IsNoetherianRing (↑(X.presheaf.stalk x) ⧸ Ideal.map cA (maximalIdeal ↥A)) :=
    AlgebraicGeometry.Scheme.isNoetherianRing_stalk_quotient_map_maximalIdeal_of_locallyOfFiniteType ↥A X toBase x hx
  have hjc : ∀ a : ↥A, ((e𝒩 (cA a) : ↥𝒩) : F) = algebraMap L F (a : L) := by
    intro a
    rw [he𝒩]
    apply φ.injective
    rw [RingEquiv.apply_symm_apply, hφ a]
    change ((X.presheaf.germ ⊤ x trivial) ≫ X.presheaf.stalkSpecializes _).hom _ = _
    rw [TopCat.Presheaf.germ_stalkSpecializes]
    rfl
  have hnoeth₁ : IsNoetherianRing
      ↥(R₁.residue.comp (Subring.inclusion (show 𝒩 ≤ R₁.integers.toSubring from fun f hf => h𝒩R₁ f hf))).range := by
    haveI := hNq
    let ρ : ↥𝒩 →+* Fbar₁ :=
      R₁.residue.comp (Subring.inclusion (show 𝒩 ≤ R₁.integers.toSubring from fun f hf => h𝒩R₁ f hf))
    have hρ : ∀ f : ↥𝒩, ρ f = R₁.residue ⟨(f : F), h𝒩R₁ f f.2⟩ := fun f => rfl

    let τ : ↑(X.presheaf.stalk x) →+* ↥ρ.range := ρ.rangeRestrict.comp e𝒩.toRingHom
    have hτ : ∀ s, s ∈ Ideal.map cA (maximalIdeal ↥A) → τ s = 0 := by
      intro s hs
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨a, ha, rfl⟩
        apply Subtype.ext
        change ρ (e𝒩 (cA a)) = 0
        rw [hρ]
        have hval : ((e𝒩 (cA a) : ↥𝒩) : F) = algebraMap L F (a : L) := hjc a
        have := (hres_const a ha).1 (h𝒩R₁ _ (hval ▸ (e𝒩 (cA a)).2))
        convert this using 2
        exact Subtype.ext hval
      · simp
      · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
      · intro r s _ hs; rw [smul_eq_mul, map_mul, hs, mul_zero]
    have hsurj : Function.Surjective (Ideal.Quotient.lift (Ideal.map cA (maximalIdeal ↥A)) τ hτ) := by
      intro y
      obtain ⟨n, rfl⟩ := ρ.rangeRestrict_surjective y
      obtain ⟨s, rfl⟩ := e𝒩.surjective n
      exact ⟨Ideal.Quotient.mk _ s, by simp [τ]⟩
    exact isNoetherianRing_of_surjective _ _ _ hsurj
  have hnoeth₂ : IsNoetherianRing
      ↥(R₂.residue.comp (Subring.inclusion (show 𝒩 ≤ R₂.integers.toSubring from fun f hf => h𝒩R₂ f hf))).range := by
    haveI := hNq
    let ρ : ↥𝒩 →+* Fbar₂ :=
      R₂.residue.comp (Subring.inclusion (show 𝒩 ≤ R₂.integers.toSubring from fun f hf => h𝒩R₂ f hf))
    have hρ : ∀ f : ↥𝒩, ρ f = R₂.residue ⟨(f : F), h𝒩R₂ f f.2⟩ := fun f => rfl

    let τ : ↑(X.presheaf.stalk x) →+* ↥ρ.range := ρ.rangeRestrict.comp e𝒩.toRingHom
    have hτ : ∀ s, s ∈ Ideal.map cA (maximalIdeal ↥A) → τ s = 0 := by
      intro s hs
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
      · rintro _ ⟨a, ha, rfl⟩
        apply Subtype.ext
        change ρ (e𝒩 (cA a)) = 0
        rw [hρ]
        have hval : ((e𝒩 (cA a) : ↥𝒩) : F) = algebraMap L F (a : L) := hjc a
        have := (hres_const a ha).2 (h𝒩R₂ _ (hval ▸ (e𝒩 (cA a)).2))
        convert this using 2
        exact Subtype.ext hval
      · simp
      · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
      · intro r s _ hs; rw [smul_eq_mul, map_mul, hs, mul_zero]
    have hsurj : Function.Surjective (Ideal.Quotient.lift (Ideal.map cA (maximalIdeal ↥A)) τ hτ) := by
      intro y
      obtain ⟨n, rfl⟩ := ρ.rangeRestrict_surjective y
      obtain ⟨s, rfl⟩ := e𝒩.surjective n
      exact ⟨Ideal.Quotient.mk _ s, by simp [τ]⟩
    exact isNoetherianRing_of_surjective _ _ _ hsurj
  have hfrac₁ : ∀ z : Fbar₁, ∃ f g : ↥𝒩, R₁.residue ⟨(g : F), h𝒩R₁ g g.2⟩ ≠ 0 ∧
      z * R₁.residue ⟨(g : F), h𝒩R₁ g g.2⟩ = R₁.residue ⟨(f : F), h𝒩R₁ f f.2⟩ := by
    intro z
    obtain ⟨r, rfl⟩ := R₁.residue_surjective z
    have hr : (r : F) ∈ SemistableModel.localRing X φ η₁ := by rw [← hR₁]; exact r.2
    obtain ⟨f, g, hf, hg, ⟨g', hg', hgg'⟩, hzg⟩ :=
      (AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes X φ h₁).2 _ hr
    have hg'R : g' ∈ R₁.integers := by
      change g' ∈ R₁.integers.toSubring; rw [hR₁]; exact hg'
    refine ⟨⟨f, hf⟩, ⟨g, hg⟩, ?_, ?_⟩
    · apply R₁.residue_ne_zero_of_isUnit
      refine isUnit_iff_exists_inv.mpr ⟨⟨g', hg'R⟩, Subtype.ext ?_⟩
      exact hgg'
    · rw [← map_mul]
      congr 1
      exact Subtype.ext hzg
  have hfrac₂ : ∀ z : Fbar₂, ∃ f g : ↥𝒩, R₂.residue ⟨(g : F), h𝒩R₂ g g.2⟩ ≠ 0 ∧
      z * R₂.residue ⟨(g : F), h𝒩R₂ g g.2⟩ = R₂.residue ⟨(f : F), h𝒩R₂ f f.2⟩ := by
    intro z
    obtain ⟨r, rfl⟩ := R₂.residue_surjective z
    have hr : (r : F) ∈ SemistableModel.localRing X φ η₂ := by rw [← hR₂]; exact r.2
    obtain ⟨f, g, hf, hg, ⟨g', hg', hgg'⟩, hzg⟩ :=
      (AlgebraicCurve.SemistableModel.localRing_le_and_exists_mem_localRing_mul_eq_of_specializes X φ h₂).2 _ hr
    have hg'R : g' ∈ R₂.integers := by
      change g' ∈ R₂.integers.toSubring; rw [hR₂]; exact hg'
    refine ⟨⟨f, hf⟩, ⟨g, hg⟩, ?_, ?_⟩
    · apply R₂.residue_ne_zero_of_isUnit
      refine isUnit_iff_exists_inv.mpr ⟨⟨g', hg'R⟩, Subtype.ext ?_⟩
      exact hgg'
    · rw [← map_mul]
      congr 1
      exact Subtype.ext hzg
  obtain ⟨x₁, hrat₁, hcar₁, hnu₁, hpos₁, hord₁, heval₁, huniq₁⟩ :=
    AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range A R₁ 𝒩 h𝒩R₁ hAconst hres ynN hynu hyn0 hmax₁ hnoeth₁ hfrac₁
  obtain ⟨x₂, hrat₂, hcar₂, hnu₂, hpos₂, hord₂, heval₂, huniq₂⟩ :=
    AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range A R₂ 𝒩 h𝒩R₂ hAconst hres xnN hxnu hxn0 hmax₂ hnoeth₂ hfrac₂

  refine ⟨x₁, x₂, S, (xn₀ : F), (yn₀ : F), (u₀ : F), hS, ?_, hAconst, hle xn₀.2, hle yn₀.2, hle u₀.2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro f
    exact ⟨hK6 f, fun h => hK7 f h.1 h.2.1 h.2.2⟩
  ·
    obtain ⟨v, hv⟩ := hu₀.exists_right_inv
    exact ⟨(v : F), hle v.2, by have := congrArg Subtype.val hv; simpa using this⟩
  · intro h; have := hxn₁; rw [RingHom.mem_ker, hψ₁] at this; exact this
  · intro h; exact hord₂
  · intro h; have := hyn₂; rw [RingHom.mem_ker, hψ₂] at this; exact this
  · intro h; exact hord₁
  · have := congrArg Subtype.val hxy₀
    simpa using this
  · intro Q' hQ'
    exact huniq₁ Q' (fun f => hQ' f (h𝒩R₁ f f.2) f.2)
  · intro Q' hQ'
    exact huniq₂ Q' (fun f => hQ' f (h𝒩R₂ f f.2) f.2)
  ·
    intro f hf₁ hf₂ hf
    obtain ⟨a, ha⟩ := hres ⟨f, hf⟩
    exact ⟨(hcar₁ _).mpr ⟨⟨f, hf⟩, rfl⟩, (hcar₂ _).mpr ⟨⟨f, hf⟩, rfl⟩, IsLocalRing.residue ↥A a,
      heval₁ ⟨f, hf⟩ a ha _, heval₂ ⟨f, hf⟩ a ha _⟩
  ·
    intro g₁ g₂ m₁ m₂ c hg₁ hg₂

    let ρ₁ : ↥𝒩 →+* Fbar₁ :=
      R₁.residue.comp (Subring.inclusion (show 𝒩 ≤ R₁.integers.toSubring from fun f hf => h𝒩R₁ f hf))
    let ρ₂ : ↥𝒩 →+* Fbar₂ :=
      R₂.residue.comp (Subring.inclusion (show 𝒩 ≤ R₂.integers.toSubring from fun f hf => h𝒩R₂ f hf))
    have hρ₁ : ∀ f : ↥𝒩, ρ₁ f = R₁.residue ⟨(f : F), h𝒩R₁ f f.2⟩ := fun f => rfl
    have hρ₂ : ∀ f : ↥𝒩, ρ₂ f = R₂.residue ⟨(f : F), h𝒩R₂ f f.2⟩ := fun f => rfl

    obtain ⟨f₁, hf₁⟩ := (hcar₁ g₁).mp m₁

    obtain ⟨a₁, ha₁⟩ := hres f₁
    have hc : algebraMap (ResidueField ↥A) x₁.ResidueField (IsLocalRing.residue ↥A a₁) =
        algebraMap (ResidueField ↥A) x₁.ResidueField c := by
      rw [← heval₁ f₁ a₁ ha₁ ((hcar₁ _).mpr ⟨f₁, rfl⟩), ← hg₁]
      congr 1
      exact Subtype.ext hf₁
    have hc' : IsLocalRing.residue ↥A a₁ = c := (algebraMap (ResidueField ↥A) x₁.ResidueField).injective hc

    have m₂' : R₂.residue ⟨(f₁ : F), h𝒩R₂ f₁ f₁.2⟩ ∈ x₂.toValuationSubring := (hcar₂ _).mpr ⟨f₁, rfl⟩
    have hdiff : (⟨g₂, m₂⟩ : ↥x₂.toValuationSubring) - ⟨_, m₂'⟩ ∈ maximalIdeal ↥x₂.toValuationSubring := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, hg₂, heval₂ f₁ a₁ ha₁ m₂', hc']

    have hgen := SLIMSkel.maximalIdeal_eq_span_of_ord_eq_one x₂ ⟨_, (hcar₂ _).mpr ⟨xnN, rfl⟩⟩ hord₂
    rw [hgen, Ideal.mem_span_singleton'] at hdiff
    obtain ⟨q, hq⟩ := hdiff
    obtain ⟨f', hf'⟩ := (hcar₂ (q : Fbar₂)).mp q.2

    refine ⟨((f₁ + xnN * f' : ↥𝒩) : F), h𝒩R₁ _ (f₁ + xnN * f').2, h𝒩R₂ _ (f₁ + xnN * f').2,
      (f₁ + xnN * f').2, ?_, ?_⟩
    · rw [← hρ₁, map_add, map_mul, hρ₁, hρ₁, hρ₁, hf₁]
      have : R₁.residue ⟨(xnN : F), h𝒩R₁ xnN xnN.2⟩ = 0 := by
        have := hxn₁; rw [RingHom.mem_ker, hψ₁] at this; exact this
      rw [this, zero_mul, add_zero]
    · rw [← hρ₂, map_add, map_mul, hρ₂, hρ₂, hρ₂, hf']
      have := congrArg Subtype.val hq
      change (q : Fbar₂) * R₂.residue ⟨(xnN : F), h𝒩R₂ xnN xnN.2⟩ = g₂ - R₂.residue ⟨(f₁ : F), h𝒩R₂ f₁ f₁.2⟩ at this
      rw [mul_comm, this]
      ring

end S_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicCurve_exists_nodeRing_coords_and_branch_unique_and_residue_surjective_of_ringEquiv_adicCompletion_stalk_of_isUnit_of_isIntegrallyClosed (solution)
