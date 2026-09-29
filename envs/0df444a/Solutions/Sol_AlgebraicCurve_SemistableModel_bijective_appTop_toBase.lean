-- Prove2me | solution 1 for AlgebraicCurve.SemistableModel.bijective_appTop_toBase
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cdc1ffc7-f8e0-5c7e-9580-29e80b33910a

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel
import Theorems.Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental
import Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableModel_bijective_appTop_toBase
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u u'

namespace GlobalSectionsE133

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases h0 : f = 0
  · simp [h0]
  have hle : v.adicValuation f ≤ 1 := by
    rw [show f = ((⟨f, hf⟩ : v.toValuationSubring) : F) from rfl, v.adicValuation_coe]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne : v.adicValuation f ≠ 0 := v.adicValuation_ne_zero h0
  unfold Place.ord
  have : WithZero.log (v.adicValuation f) ≤ WithZero.log 1 :=
    (WithZero.log_le_log hne one_ne_zero).mpr hle
  rw [WithZero.log_one] at this
  omega

theorem ord_eq_zero_of_forall_mem {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {f : F} (hf0 : f ≠ 0) (hf : ∀ v : Place K F, f ∈ v.toValuationSubring) (v : Place K F) : v.ord f = 0 := by
  obtain ⟨D, hD, hdeg⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor f hf0
  have hnn : ∀ w, 0 ≤ D w := fun w => by rw [hD]; exact ord_nonneg_of_mem w (hf w)
  have hsum : D.sum (fun w n => n * (w.deg : ℤ)) = 0 := by
    have := hdeg
    rw [Divisor.degree, Finsupp.liftAddHom_apply] at this
    simpa using this
  rw [Finsupp.sum, Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_nonneg (hnn w) (by positivity))] at hsum
  rw [← hD]
  by_cases hv : v ∈ D.support
  · have h1 := hsum v hv
    have hdegpos : 0 < (v.deg : ℤ) := by
      haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
      have : 0 < v.deg := Module.finrank_pos
      exact_mod_cast this
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · omega
  · exact Finsupp.notMem_support_iff.mp hv

end GlobalSectionsE133

open GlobalSectionsE133

theorem solution
    {L : Type u} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type u'} [Field F] [Algebra L F]
    {ιV ιE : Type*} {Fbar : ιV → Type*} [∀ i, Field (Fbar i)] [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    {C : ∀ i, ComponentChart A F (Fbar i)} {An : ιE → Annulus A F} {src tgt : ιE → ιV}
    {xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e))}
    {xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e))}
    (M : SemistableModel A F Fbar C An src tgt xs xt) [IsCurveOver L F] [Algebra.EssFiniteType L F] :
    Function.Bijective M.toBase.appTop := by
  classical
  let γ : _ →+* _ := (M.X.presheaf.germ ⊤ (genericPoint M.X) trivial).hom
  have hγinj : Function.Injective γ := germ_injective_of_isIntegral M.X (U := ⊤) (genericPoint M.X) trivial
  let eA := Scheme.ΓSpecIso (CommRingCat.of ↥A)
  have hbase : ∀ a : ↥A, γ (M.toBase.appTop (eA.inv a)) = M.ffEquiv (algebraMap L F (a : L)) := fun a =>
    (M.ffEquiv_algebraMap a).symm
  constructor
  · intro s₁ s₂ h
    have h1 := hbase (eA.hom s₁)
    have h2 := hbase (eA.hom s₂)
    rw [eA.hom_inv_id_apply] at h1 h2
    have h12 : M.ffEquiv (algebraMap L F ((eA.hom s₁ : ↥A) : L)) = M.ffEquiv (algebraMap L F ((eA.hom s₂ : ↥A) : L)) := by
      rw [← h1, ← h2]
      exact congrArg γ h
    have h3 : eA.hom s₁ = eA.hom s₂ :=
      Subtype.ext ((algebraMap L F).injective (M.ffEquiv.injective h12))
    have := congrArg eA.inv h3
    rwa [eA.hom_inv_id_apply, eA.hom_inv_id_apply] at this
  · intro s
    set σ := γ s with hσ
    set u : F := M.ffEquiv.symm σ with hu
    have hσu : M.ffEquiv u = σ := by rw [hu]; exact M.ffEquiv.apply_symm_apply σ
    have hloc : ∀ x : M.X, u ∈ SemistableModel.localRing M.X M.ffEquiv x := by
      intro x
      refine ⟨(M.X.presheaf.germ ⊤ x trivial).hom s, ?_⟩
      show M.ffEquiv.symm (algebraMap _ _ ((M.X.presheaf.germ ⊤ x trivial).hom s)) = M.ffEquiv.symm σ
      congr 1
      show (M.X.presheaf.germ ⊤ x trivial ≫ M.X.presheaf.stalkSpecializes _).hom s =
        (M.X.presheaf.germ ⊤ (genericPoint M.X) trivial).hom s
      rw [TopCat.Presheaf.germ_stalkSpecializes]
    have hP : ∀ P : Place L F, u ∈ P.toValuationSubring := fun P => by
      have := hloc (M.pt P)
      rw [M.localRing_pt] at this
      exact this
    by_cases hu0 : u = 0
    · refine ⟨0, hγinj ?_⟩
      rw [map_zero, map_zero]
      show 0 = σ
      rw [← hσu, hu0, map_zero]
    have hord : ∀ v : Place L F, v.ord u = 0 := ord_eq_zero_of_forall_mem hu0 hP
    haveI : PerfectField L := inferInstance
    obtain ⟨x, hx, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := L) (F := F)
    haveI := hfd
    obtain ⟨c, hc⟩ := Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hx hord
    have hcA : c ∈ A := by
      by_contra hcA
      have hc0 : c ≠ 0 := by
        rintro rfl
        apply hu0
        rw [← hc, map_zero]
      have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
      have hmax : (⟨c⁻¹, hcinv⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hU
        apply hcA
        obtain ⟨w, hw⟩ := hU
        have h1 : ((w : ↥A) : L) * (((w⁻¹ : (↥A)ˣ) : ↥A) : L) = 1 := by
          rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
        rw [hw] at h1
        have h3 : (((w⁻¹ : (↥A)ˣ) : ↥A) : L) = c := by
          have := eq_inv_of_mul_eq_one_right h1
          rw [this, inv_inv]
        rw [← h3]
        exact ((w⁻¹ : (↥A)ˣ) : ↥A).2

      obtain ⟨x₀, hx₀⟩ : ∃ x₀ : M.X, M.toBase.base x₀ = IsLocalRing.closedPoint ↥A := by
        have hcl : IsClosed (Set.range M.toBase.base) := M.toBase.isClosedMap.isClosed_range
        exact (IsLocalRing.specializes_closedPoint (M.toBase.base (genericPoint M.X))).mem_closed hcl ⟨_, rfl⟩
      set a : ↥A := ⟨c⁻¹, hcinv⟩ with ha
      have hss' : M.toBase.appTop (eA.inv a) * s = 1 := by
        apply hγinj
        rw [map_mul, map_one, hbase]
        show M.ffEquiv (algebraMap L F (c⁻¹)) * σ = 1
        rw [← hσu, ← map_mul, ← hc, ← map_mul, inv_mul_cancel₀ hc0, map_one, map_one]
      have hunit : IsUnit (M.toBase.appTop (eA.inv a)) := isUnit_iff_exists_inv.mpr ⟨s, hss'⟩
      have h2 : IsUnit ((M.X.presheaf.germ ⊤ x₀ trivial).hom (M.toBase.appTop (eA.inv a))) := hunit.map _
      change IsUnit ((M.X.presheaf.germ (M.toBase ⁻¹ᵁ ⊤) x₀ trivial).hom (M.toBase.app ⊤ (eA.inv a))) at h2
      rw [← Scheme.Hom.germ_stalkMap_apply M.toBase ⊤ x₀ trivial] at h2
      have h3 := isUnit_of_map_unit (M.toBase.stalkMap x₀).hom _ h2
      have h4 : IsUnit (algebraMap ↥A ((Spec.structureSheaf ↥A).presheaf.stalk (M.toBase.base x₀)) a) := h3
      rw [IsLocalization.AtPrime.isUnit_to_map_iff ((Spec.structureSheaf ↥A).presheaf.stalk (M.toBase.base x₀))
        (M.toBase.base x₀).asIdeal a, hx₀] at h4
      exact h4 hmax
    refine ⟨eA.inv ⟨c, hcA⟩, hγinj ?_⟩
    rw [hbase]
    show M.ffEquiv (algebraMap L F c) = σ
    rw [hc, hσu]

end S_AlgebraicCurve_SemistableModel_bijective_appTop_toBase
end P2MW
export P2MW.S_AlgebraicCurve_SemistableModel_bijective_appTop_toBase (solution)
