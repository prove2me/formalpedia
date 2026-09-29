-- Prove2me | solution 1 for AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ee253216-d09a-5e6d-900b-468b814ffebb

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace CuspPoleAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  have h1 : v.adicValuation f ≤ 1 := by
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := v.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (v.adicValuation f))
  omega

theorem not_mem_iff_ord_neg (v : Place K F) (f : F) : f ∉ v.toValuationSubring ↔ v.ord f < 0 := by
  constructor
  · intro hmem
    have hf0 : f ≠ 0 := fun h0 => hmem (h0 ▸ zero_mem _)
    by_contra hle
    exact hmem (v.mem_toValuationSubring_of_ord_nonneg_alt hf0 (not_lt.mp hle))
  · intro h hmem
    exact absurd (ord_nonneg_of_mem v hmem) (not_le.mpr h)

theorem min_ord_le_ord_add (v : Place K F) {f g : F} (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  have hle := v.adicValuation.map_add f g
  show min (-(WithZero.log (v.adicValuation f))) (-(WithZero.log (v.adicValuation g))) ≤
    -(WithZero.log (v.adicValuation (f + g)))
  rcases le_max_iff.mp hle with h | h
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hf)).mpr h
    exact le_trans (min_le_left _ _) (neg_le_neg this)
  · have := (WithZero.log_le_log (v.adicValuation_ne_zero hfg) (v.adicValuation_ne_zero hg)).mpr h
    exact le_trans (min_le_right _ _) (neg_le_neg this)

theorem ord_add_eq_of_ord_neg (v : Place K F) {f g : F} (hf : v.ord f < 0) (hg : g ∈ v.toValuationSubring) :
    v.ord (f + g) = v.ord f := by
  have hfmem : f ∉ v.toValuationSubring := (not_mem_iff_ord_neg v f).mpr hf
  have hf0 : f ≠ 0 := fun h0 => hfmem (h0 ▸ zero_mem _)
  have hfgmem : f + g ∉ v.toValuationSubring := by
    intro h
    apply hfmem
    have : f = (f + g) - g := by ring
    rw [this]; exact sub_mem h hg
  have hfg0 : f + g ≠ 0 := fun h0 => hfgmem (h0 ▸ zero_mem _)
  have hg0 : 0 ≤ v.ord g := ord_nonneg_of_mem v hg
  have hng : 0 ≤ v.ord (-g) := ord_nonneg_of_mem v (neg_mem hg)
  have h1 := min_ord_le_ord_add v hfg0
  have h2 : min (v.ord (f + g)) (v.ord (-g)) ≤ v.ord f := by
    have := min_ord_le_ord_add v (f := f + g) (g := -g) (by rw [add_neg_cancel_right]; exact hf0)
    rwa [add_neg_cancel_right] at this
  rcases le_total (v.ord (f + g)) (v.ord (-g)) with h3 | h3
  · rw [min_eq_left h3] at h2
    rw [min_eq_left (le_trans hf.le hg0)] at h1
    exact le_antisymm h2 h1
  · rw [min_eq_right h3] at h2
    omega

theorem max_neg_ord_sub_eq (v : Place K F) (u : F) {c : F} (hc : c ∈ v.toValuationSubring) :
    max 0 (-(v.ord (u - c))) = max 0 (-(v.ord u)) := by
  by_cases hu : u ∈ v.toValuationSubring
  · have h1 := ord_nonneg_of_mem v hu
    have h2 := ord_nonneg_of_mem v (sub_mem hu hc)
    rw [max_eq_left (by omega), max_eq_left (by omega)]
  · have hlt := (not_mem_iff_ord_neg v u).mp hu
    rw [sub_eq_add_neg, ord_add_eq_of_ord_neg v hlt (neg_mem hc)]

theorem eq_zero_of_forall_mem (x : F) (hx : ∀ Q : Place K F, x ∈ Q.toValuationSubring)
    (D : Divisor K F) (hD : ∀ Q : Place K F, D Q = max 0 (-(Q.ord x))) : D = 0 := by
  ext Q
  rw [hD Q, Finsupp.coe_zero, Pi.zero_apply, max_eq_left]
  have := ord_nonneg_of_mem Q (hx Q)
  omega

theorem ord_pos_of_evalAt_eq_zero (v : Place K F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf).lt_or_eq with h | h
  · exact h
  · exact absurd h0 (v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h.symm)

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (g : α → β) (D : α →₀ ℤ) (q : β) :
    Finsupp.mapDomain g D q = ∑ P ∈ D.support, if g P = q then D P else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun P _ => by rw [Finsupp.single_apply]

theorem mapDomain_nonneg {α β : Type*} (g : α → β) {D : α →₀ ℤ} (hD : ∀ a, 0 ≤ D a) (q : β) :
    0 ≤ Finsupp.mapDomain g D q := by
  classical
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_nonneg fun P _ => by split_ifs <;> simp [hD P]

theorem le_mapDomain_apply {α β : Type*} (g : α → β) {D : α →₀ ℤ} (hD : ∀ a, 0 ≤ D a) (a : α) :
    D a ≤ Finsupp.mapDomain g D (g a) := by
  classical
  rw [mapDomain_apply_eq_sum]
  by_cases ha : a ∈ D.support
  · have := Finset.single_le_sum (f := fun P => if g P = g a then D P else 0)
      (fun P _ => by by_cases h : g P = g a <;> simp [h, hD P]) ha
    simpa using this
  · rw [Finsupp.notMem_support_iff.mp ha]
    exact Finset.sum_nonneg fun P _ => by split_ifs <;> simp [hD P]

theorem exists_of_mapDomain_ne_zero {α β : Type*} (g : α → β) (D : α →₀ ℤ) {q : β}
    (hq : Finsupp.mapDomain g D q ≠ 0) : ∃ a ∈ D.support, g a = q := by
  classical
  rw [mapDomain_apply_eq_sum] at hq
  by_contra h
  push Not at h
  exact hq (Finset.sum_eq_zero fun P hP => if_neg (h P hP))

theorem degree_eq_sum (D : Divisor K F) : Divisor.degree D = ∑ P ∈ D.support, D P * (P.deg : ℤ) := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  rfl

theorem eq_zero_of_degree_eq_zero {E : Divisor K F} (hE : ∀ Q, 0 ≤ E Q) (hdeg : ∀ Q ∈ E.support, 0 < Q.deg)
    (h0 : Divisor.degree E = 0) : E = 0 := by
  classical
  rw [degree_eq_sum] at h0
  have hterm : ∀ Q ∈ E.support, 0 ≤ E Q * (Q.deg : ℤ) := fun Q _ =>
    mul_nonneg (hE Q) (by exact_mod_cast (Nat.zero_le _))
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0
  rw [← Finsupp.support_eq_empty, Finset.eq_empty_iff_forall_notMem]
  intro Q hQ
  have h1 := hall Q hQ
  have h2 : (0 : ℤ) < Q.deg := by exact_mod_cast hdeg Q hQ
  have h3 : E Q = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · omega
  exact (Finsupp.mem_support_iff.mp hQ) h3

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]

theorem le_mapDomain_of_unit {E : Type*} [Field E] [Algebra L E] [HasPrincipalDivisors L E]
    (R : ConstantReduction A E Fbar) (f : E) (hf : f ∈ R.integers) (hres : R.residue ⟨f, hf⟩ ≠ 0)
    (Du : Divisor L E) (hDu : ∀ P : Place L E, Du P = max 0 (-(P.ord f)))
    (Dū : Divisor (ResidueField ↥A) Fbar)
    (hDū : ∀ Q : Place (ResidueField ↥A) Fbar, Dū Q = max 0 (-(Q.ord (R.residue ⟨f, hf⟩)))) :
    ∃ Zf : Divisor L E, (∀ P, Zf P = P.ord f + Du P) ∧ (∀ P, 0 ≤ Zf P) ∧
      (∀ Q, Finsupp.mapDomain R.placeMap Zf Q - Finsupp.mapDomain R.placeMap Du Q = Q.ord (R.residue ⟨f, hf⟩)) ∧
      (∀ Q, Dū Q ≤ Finsupp.mapDomain R.placeMap Du Q) := by
  classical
  have hf0 : f ≠ 0 := by
    intro h0; apply hres
    have : (⟨f, hf⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨Df, hDf, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := E) f hf0
  have hpush := R.mapDomain_placeMap ⟨f, hf⟩ hres Df hDf
  refine ⟨Df + Du, fun P => by rw [Finsupp.add_apply, hDf P], fun P => ?_, fun Q => ?_, fun Q => ?_⟩
  · rw [Finsupp.add_apply, hDf P, hDu P]
    omega
  · rw [Finsupp.mapDomain_add, Finsupp.add_apply, add_sub_cancel_right, hpush Q]
  · have hDu0 : ∀ P, 0 ≤ Du P := fun P => by rw [hDu P]; exact le_max_left _ _
    have hZ0 : ∀ P, 0 ≤ (Df + Du) P := fun P => by
      rw [Finsupp.add_apply, hDf P, hDu P]; omega
    have h1 : Finsupp.mapDomain R.placeMap (Df + Du) Q - Finsupp.mapDomain R.placeMap Du Q =
        Q.ord (R.residue ⟨f, hf⟩) := by
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, add_sub_cancel_right, hpush Q]
    have h2 := mapDomain_nonneg R.placeMap hZ0 Q
    have h3 := mapDomain_nonneg R.placeMap hDu0 Q
    rw [hDū Q]
    apply max_le h3
    omega

end CuspPoleAux

open CuspPoleAux in
theorem solution
    {L : Type} [Field L] {A : ValuationSubring L}
    {F : Type} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : ConstantReduction A F Fbar)
    (u : F) (hu : u ∈ R.integers)
    (Du : Divisor L F) (hDu : ∀ P : Place L F, Du P = max 0 (-(P.ord u)))
    (Dū : Divisor (ResidueField ↥A) Fbar)
    (hDū : ∀ Q : Place (ResidueField ↥A) Fbar, Dū Q = max 0 (-(Q.ord (R.residue ⟨u, hu⟩))))
    (hdeg : Divisor.degree Dū = Divisor.degree Du) (hnc : Dū ≠ 0)
    (hfin : ∀ P : Place L F, P.ord u < 0 → 0 < P.deg) :
    Finsupp.mapDomain R.placeMap Du = Dū ∧
    (∀ P' : Place L F, P'.ord u < 0 → (R.placeMap P').ord (R.residue ⟨u, hu⟩) < 0) ∧
    (∀ P : Place L F, P.IsRational → u ∈ P.toValuationSubring → P.evalAt u ∈ A →
      ∀ P' : Place L F, P'.ord u < 0 → R.placeMap P' ≠ R.placeMap P) := by
  classical

  have hconst : ∀ x : Fbar, (∀ Q : Place (ResidueField ↥A) Fbar, x ∈ Q.toValuationSubring) →
      R.residue ⟨u, hu⟩ ≠ x := by
    intro x hx hEq
    apply hnc
    exact eq_zero_of_forall_mem x hx Dū (fun Q => by rw [hDū Q, hEq])
  have hres : R.residue ⟨u, hu⟩ ≠ 0 := hconst 0 (fun Q => zero_mem _)
  have hDu0 : ∀ P, 0 ≤ Du P := fun P => by rw [hDu P]; exact le_max_left _ _
  have hDū0 : ∀ Q, 0 ≤ Dū Q := fun Q => by rw [hDū Q]; exact le_max_left _ _

  obtain ⟨Zu, hZu, hZu0, hdiff, hle⟩ := le_mapDomain_of_unit R u hu hres Du hDu Dū hDū
  have ha : Finsupp.mapDomain R.placeMap Du = Dū := by
    have hE0 : ∀ Q, 0 ≤ (Finsupp.mapDomain R.placeMap Du - Dū) Q := fun Q => by
      rw [Finsupp.sub_apply]; linarith [hle Q]
    have hEdeg : Divisor.degree (Finsupp.mapDomain R.placeMap Du - Dū) = 0 := by
      rw [map_sub, R.degree_mapDomain, hdeg, sub_self]
    have hEsupp : ∀ Q ∈ (Finsupp.mapDomain R.placeMap Du - Dū).support, 0 < Q.deg := by
      intro Q hQ
      have hQ' : Finsupp.mapDomain R.placeMap Du Q ≠ 0 := by
        intro h0
        have h1 := Finsupp.mem_support_iff.mp hQ
        rw [Finsupp.sub_apply, h0] at h1
        have h2 := hle Q
        rw [h0] at h2
        have h3 := hDū0 Q
        omega
      obtain ⟨P, hP, hPQ⟩ := exists_of_mapDomain_ne_zero R.placeMap Du hQ'
      have hpole : P.ord u < 0 := by
        have h1 := Finsupp.mem_support_iff.mp hP
        rw [hDu P] at h1
        by_contra h2
        exact h1 (max_eq_left (by omega))
      rw [← hPQ, R.deg_placeMap]
      exact hfin P hpole
    have := eq_zero_of_degree_eq_zero hE0 hEsupp hEdeg
    rwa [sub_eq_zero] at this

  have hb : ∀ P' : Place L F, P'.ord u < 0 → (R.placeMap P').ord (R.residue ⟨u, hu⟩) < 0 := by
    intro P' hP'
    have h1 : 0 < Du P' := by rw [hDu P']; exact lt_max_of_lt_right (by omega)
    have h2 := le_mapDomain_apply R.placeMap hDu0 P'
    rw [ha, hDū] at h2
    by_contra h3
    rw [max_eq_left (by omega)] at h2
    omega
  refine ⟨ha, hb, ?_⟩

  intro P hP huP haA P' hP' hEq
  set a : ↥A := ⟨P.evalAt u, haA⟩ with ha_def
  have hcF : algebraMap L F (a : L) ∈ R.integers := (R.algebraMap_mem_iff _).mpr a.2
  set f : F := u - algebraMap L F (a : L) with hf_def
  have hf : f ∈ R.integers := sub_mem hu hcF
  have hres_f : R.residue ⟨f, hf⟩ =
      R.residue ⟨u, hu⟩ - algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a) := by
    have : (⟨f, hf⟩ : R.integers) = ⟨u, hu⟩ - ⟨algebraMap L F (a : L), hcF⟩ := Subtype.ext rfl
    rw [this, map_sub, R.residue_algebraMap a]
  have hres_f0 : R.residue ⟨f, hf⟩ ≠ 0 := by
    rw [hres_f, sub_ne_zero]
    exact hconst _ (fun Q => Q.algebraMap_mem' _)
  have hf0 : f ≠ 0 := by
    intro h0; apply hres_f0
    have : (⟨f, hf⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hDu' : ∀ P₁ : Place L F, Du P₁ = max 0 (-(P₁.ord f)) := fun P₁ => by
    rw [hDu P₁, hf_def, max_neg_ord_sub_eq P₁ u (P₁.algebraMap_mem' _)]
  have hDū' : ∀ Q : Place (ResidueField ↥A) Fbar, Dū Q = max 0 (-(Q.ord (R.residue ⟨f, hf⟩))) := fun Q => by
    rw [hDū Q, hres_f, max_neg_ord_sub_eq Q _ (Q.algebraMap_mem' _)]
  obtain ⟨Zf, hZf, hZf0, hdiff', -⟩ := le_mapDomain_of_unit R f hf hres_f0 Du hDu' Dū hDū'

  have hfP : f ∈ P.toValuationSubring := sub_mem huP (P.algebraMap_mem' _)
  have hval : P.evalAt f = 0 := by
    have e1 : P.evalAt f = P.evalAt u - P.evalAt (algebraMap L F (a : L)) := by
      apply P.algebraMap_residueField_injective
      rw [map_sub, P.algebraMap_evalAt hP hfP, P.algebraMap_evalAt hP huP,
        P.algebraMap_evalAt hP (P.algebraMap_mem' _), ← map_sub]
      rfl
    rw [e1, P.evalAt_algebraMap_eq, ha_def]
    exact sub_self _
  have hpos : 0 < P.ord f := ord_pos_of_evalAt_eq_zero P hP hf0 hfP hval
  have h1 := hdiff' (R.placeMap P)
  rw [ha] at h1
  have h2 := le_mapDomain_apply R.placeMap hZf0 P
  have h3 := hZf P
  have h4 : 0 ≤ Du P := hDu0 P

  have h5 := hb P' hP'
  rw [hEq] at h5
  have h6 : (R.placeMap P).ord (R.residue ⟨f, hf⟩) = (R.placeMap P).ord (R.residue ⟨u, hu⟩) := by
    rw [hres_f, sub_eq_add_neg]
    exact ord_add_eq_of_ord_neg _ h5 (neg_mem ((R.placeMap P).algebraMap_mem' _))
  have h7 := hDū (R.placeMap P)
  rw [max_eq_right (by omega)] at h7
  omega

end S_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
end P2MW
export P2MW.S_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos (solution)
