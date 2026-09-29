-- Prove2me | solution 1 for AlgebraicCurve.ConstantReduction.isPointwise_of_hasPrincipalDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/f9282fac-04ce-57c4-b4ca-96b6bfb8c182

import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_ModularCurve_FinitePlaceLift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

noncomputable section

namespace P2MIsPointwise

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ord_nonneg_of_mem {K' E : Type*} [Field K'] [Field E] [Algebra K' E] (v : Place K' E) {f : E}
    (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : E) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := v.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (v.adicValuation f))
  omega

theorem ord_pos_of_evalAt_eq_zero {K' E : Type*} [Field K'] [Field E] [Algebra K' E] (v : Place K' E)
    (hv : v.IsRational) {f : E} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) :
    0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf0 hf).lt_or_eq with h | h
  · exact h
  · exact absurd h0 (v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h.symm)

theorem mem_maximalIdeal_of_ord_pos {K' E : Type*} [Field K'] [Field E] [Algebra K' E] (v : Place K' E)
    {f : E} (hf : f ∈ v.toValuationSubring) (h : 0 < v.ord f) :
    (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rw [hu] at this
  change v.ord f = 0 at this
  omega

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (g : α → β) (D : α →₀ ℤ) (q : β) :
    Finsupp.mapDomain g D q = ∑ P ∈ D.support, if g P = q then D P else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun P _ => by rw [Finsupp.single_apply]

theorem ord_le_ord_residue [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    (g : F) (hg : g ∈ R.integers) (hres : R.residue ⟨g, hg⟩ ≠ 0)
    (v₀ : Place K F) (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → g ∈ P.toValuationSubring) :
    v₀.ord g ≤ (R.placeMap v₀).ord (R.residue ⟨g, hg⟩) := by
  classical
  have hg0 : g ≠ 0 := by
    intro h0; apply hres
    have : (⟨g, hg⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) g hg0
  have hpush := R.mapDomain_placeMap ⟨g, hg⟩ hres D hD (R.placeMap v₀)
  rw [mapDomain_apply_eq_sum] at hpush
  have hnn : ∀ P ∈ D.support, 0 ≤ (if R.placeMap P = R.placeMap v₀ then D P else 0) := by
    intro P _
    split_ifs with hP
    · rw [hD P]; exact ord_nonneg_of_mem P hg0 (hreg P hP)
    · exact le_rfl
  by_cases h₀ : v₀ ∈ D.support
  · have := Finset.single_le_sum hnn h₀
    rw [if_pos rfl, hD, hpush] at this
    exact this
  · rw [Finsupp.notMem_support_iff] at h₀
    rw [← hD v₀, h₀, ← hpush]
    exact Finset.sum_nonneg hnn

theorem evalAt_mem [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place K F) (hv₀ : v₀.IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    v₀.evalAt f ∈ A := by
  classical
  by_contra ha
  set a : K := v₀.evalAt f with ha_def
  have ha0 : a ≠ 0 := fun h => ha (h ▸ A.zero_mem)
  have hainv_A : a⁻¹ ∈ A := (A.mem_or_inv_mem a).resolve_left ha
  have hmapa : algebraMap K F a ∉ R.integers := fun h => ha ((R.algebraMap_mem_iff a).mp h)
  have hmapainv : algebraMap K F a⁻¹ ∈ R.integers := (R.algebraMap_mem_iff a⁻¹).mpr hainv_A
  have hnonunit : (⟨algebraMap K F a⁻¹, hmapainv⟩ : R.integers) ∈ maximalIdeal R.integers := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := hu
    apply hmapa
    have hwinv : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 = algebraMap K F a := by
      have h1 : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 * algebraMap K F a⁻¹ = 1 := by
        have := congrArg (fun z : R.integers => (z : F)) w.inv_mul
        simpa [hw] using this
      rw [map_inv₀] at h1
      have hane : algebraMap K F a ≠ 0 := (map_ne_zero _).mpr ha0
      calc ((w⁻¹ : (R.integers)ˣ) : R.integers).1
          = ((w⁻¹ : (R.integers)ˣ) : R.integers).1 * (algebraMap K F a)⁻¹ * algebraMap K F a := by
            rw [mul_assoc, inv_mul_cancel₀ hane, mul_one]
        _ = algebraMap K F a := by rw [h1, one_mul]
    rw [← hwinv]
    exact ((w⁻¹ : (R.integers)ˣ) : R.integers).2
  have hg_mem : a⁻¹ • f ∈ R.integers := by rw [Algebra.smul_def]; exact mul_mem hmapainv hf
  have hg_max : (⟨a⁻¹ • f, hg_mem⟩ : R.integers) ∈ maximalIdeal R.integers := by
    have : (⟨a⁻¹ • f, hg_mem⟩ : R.integers) = ⟨algebraMap K F a⁻¹, hmapainv⟩ * ⟨f, hf⟩ :=
      Subtype.ext (Algebra.smul_def _ _)
    rw [this]; exact Ideal.mul_mem_right _ _ hnonunit
  have hres_g : R.residue ⟨a⁻¹ • f, hg_mem⟩ = 0 := by
    have : (⟨a⁻¹ • f, hg_mem⟩ : R.integers) ∈ RingHom.ker R.residue := by rw [R.ker_residue]; exact hg_max
    exact this
  set h : F := a⁻¹ • f - 1 with hh_def
  have hh_mem : h ∈ R.integers := sub_mem hg_mem (one_mem _)
  have hres_h : R.residue ⟨h, hh_mem⟩ = -1 := by
    have : (⟨h, hh_mem⟩ : R.integers) = ⟨a⁻¹ • f, hg_mem⟩ - 1 := Subtype.ext rfl
    rw [this, map_sub, map_one, hres_g, zero_sub]
  have hres_h_ne : R.residue ⟨h, hh_mem⟩ ≠ 0 := by rw [hres_h]; exact neg_ne_zero.mpr one_ne_zero
  have hh0 : h ≠ 0 := by
    intro h0; apply hres_h_ne
    have : (⟨h, hh_mem⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hh_reg : ∀ P, R.placeMap P = R.placeMap v₀ → h ∈ P.toValuationSubring := fun P hP =>
    sub_mem (by rw [Algebra.smul_def]; exact mul_mem (P.algebraMap_mem' _) (hreg P hP)) (one_mem _)
  have hh_val : v₀.evalAt h = 0 := by
    have hf0 : f ∈ v₀.toValuationSubring := hreg v₀ rfl
    have hsm : a⁻¹ • f ∈ v₀.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v₀.algebraMap_mem' _) hf0
    have e1 : v₀.evalAt h = v₀.evalAt (a⁻¹ • f) - v₀.evalAt 1 := by
      apply v₀.algebraMap_residueField_injective
      rw [map_sub, v₀.algebraMap_evalAt hv₀ (sub_mem hsm (one_mem _)), v₀.algebraMap_evalAt hv₀ hsm,
        v₀.algebraMap_evalAt hv₀ (one_mem _), ← map_sub]
      rfl
    rw [e1, v₀.evalAt_one, Algebra.smul_def, v₀.evalAt_mul_of_mem hv₀ (v₀.algebraMap_mem' _) hf0,
      v₀.evalAt_algebraMap_eq, ← ha_def, inv_mul_cancel₀ ha0, sub_self]
  have hord_v₀ : 0 < v₀.ord h := ord_pos_of_evalAt_eq_zero v₀ hv₀ hh0 (hh_reg v₀ rfl) hh_val
  have hle := ord_le_ord_residue R h hh_mem hres_h_ne v₀ hh_reg
  have hrhs : (R.placeMap v₀).ord (R.residue ⟨h, hh_mem⟩) = 0 := by
    rw [hres_h, show (-1 : Fbar) = algebraMap (ResidueField A) Fbar (-1) by rw [map_neg, map_one]]
    exact ConstantReduction.ord_algebraMap (L := ResidueField A) (F := Fbar) _ (neg_ne_zero.mpr one_ne_zero)
  omega

theorem residue_sq [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place K F) (hv₀ : v₀.IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    ∃ (hm : (R.residue ⟨f, hf⟩ : Fbar) ∈ (R.placeMap v₀).toValuationSubring),
      algebraMap (ResidueField A) (R.placeMap v₀).ResidueField
          (IsLocalRing.residue A ⟨v₀.evalAt f, evalAt_mem R f hf v₀ hv₀ hreg⟩)
        = IsLocalRing.residue (R.placeMap v₀).toValuationSubring ⟨R.residue ⟨f, hf⟩, hm⟩ := by
  set a : A := ⟨v₀.evalAt f, evalAt_mem R f hf v₀ hv₀ hreg⟩ with ha
  set Q := R.placeMap v₀ with hQ

  have hconstF : algebraMap K F (a : K) ∈ R.integers := (R.algebraMap_mem_iff _).mpr a.2
  have hres_const : R.residue ⟨algebraMap K F (a : K), hconstF⟩
      = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := R.residue_algebraMap a
  have ha2bar_mem : algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have ha2bar_res : IsLocalRing.residue Q.toValuationSubring ⟨_, ha2bar_mem⟩
      = algebraMap (ResidueField A) Q.ResidueField (IsLocalRing.residue A a) := by
    rw [IsScalarTower.algebraMap_apply (ResidueField A) Q.toValuationSubring Q.ResidueField]
    rfl

  set g : F := f - algebraMap K F (a : K) with hg
  have hg_mem : g ∈ R.integers := sub_mem hf hconstF
  have hres_g : R.residue ⟨g, hg_mem⟩ = R.residue ⟨f, hf⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
    have : (⟨g, hg_mem⟩ : R.integers) = ⟨f, hf⟩ - ⟨algebraMap K F (a : K), hconstF⟩ := Subtype.ext rfl
    rw [this, map_sub, hres_const]
  by_cases hzero : R.residue ⟨g, hg_mem⟩ = 0
  ·
    have hfbar : R.residue ⟨f, hf⟩ = algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
      rw [hres_g, sub_eq_zero] at hzero; exact hzero
    refine ⟨by rw [hfbar]; exact ha2bar_mem, ?_⟩
    rw [← ha2bar_res]
    congr 1
    exact Subtype.ext hfbar.symm
  ·
    have hg_reg : ∀ P, R.placeMap P = R.placeMap v₀ → g ∈ P.toValuationSubring := fun P hP =>
      sub_mem (hreg P hP) (P.algebraMap_mem' _)
    have hg0 : g ≠ 0 := by
      intro h0; apply hzero
      have : (⟨g, hg_mem⟩ : R.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hval : v₀.evalAt g = 0 := by
      have e1 : v₀.evalAt g = v₀.evalAt f - v₀.evalAt (algebraMap K F (a : K)) := by
        apply v₀.algebraMap_residueField_injective
        rw [map_sub, v₀.algebraMap_evalAt hv₀ (hg_reg v₀ rfl), v₀.algebraMap_evalAt hv₀ (hreg v₀ rfl),
          v₀.algebraMap_evalAt hv₀ (v₀.algebraMap_mem' _), ← map_sub]
        rfl
      rw [e1, v₀.evalAt_algebraMap_eq, ha]
      exact sub_self _
    have hpos : 0 < v₀.ord g := ord_pos_of_evalAt_eq_zero v₀ hv₀ hg0 (hg_reg v₀ rfl) hval
    have hle := ord_le_ord_residue R g hg_mem hzero v₀ hg_reg
    have hQpos : 0 < Q.ord (R.residue ⟨g, hg_mem⟩) := lt_of_lt_of_le hpos hle
    have hgbar_mem : R.residue ⟨g, hg_mem⟩ ∈ Q.toValuationSubring :=
      Q.mem_toValuationSubring_of_ord_nonneg_alt hzero hQpos.le
    have hfbar_eq : R.residue ⟨f, hf⟩ = R.residue ⟨g, hg_mem⟩ + algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
      rw [hres_g]; ring
    have hfbar_mem : R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring := by
      rw [hfbar_eq]; exact add_mem hgbar_mem ha2bar_mem
    refine ⟨hfbar_mem, ?_⟩

    have hsplit : (⟨R.residue ⟨f, hf⟩, hfbar_mem⟩ : Q.toValuationSubring)
        = ⟨R.residue ⟨g, hg_mem⟩, hgbar_mem⟩ + ⟨_, ha2bar_mem⟩ := Subtype.ext hfbar_eq
    have hgbar_res : IsLocalRing.residue Q.toValuationSubring ⟨R.residue ⟨g, hg_mem⟩, hgbar_mem⟩ = 0 :=
      (IsLocalRing.residue_eq_zero_iff _).mpr (mem_maximalIdeal_of_ord_pos Q hgbar_mem hQpos)
    rw [hsplit, map_add, hgbar_res, zero_add, ha2bar_res]

end P2MIsPointwise

end

theorem solution
    {K : Type*} [Field K] {A : ValuationSubring K} {F : Type*} [Field F] [Algebra K F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [AlgebraicCurve.HasPrincipalDivisors K F] (R : AlgebraicCurve.ConstantReduction A F Fbar) :
    R.IsPointwise := by
  intro P hP f hf hfib
  obtain ⟨hm, h⟩ := P2MIsPointwise.residue_sq R f hf P hP hfib
  exact ⟨hm, P2MIsPointwise.evalAt_mem R f hf P hP hfib, h⟩

end S_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors
end P2MW
export P2MW.S_AlgebraicCurve_ConstantReduction_isPointwise_of_hasPrincipalDivisors (solution)
