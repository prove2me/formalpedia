-- Prove2me | solution 1 for AlgebraicCurve.Annulus.ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3b7be1fd-788d-5245-9a52-0872f5aa48d9

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq.AlgebraicCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord_zero Divisor HasPrincipalDivisors IsCurveOver"
p2m_open "AlgebraicCurve"

namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_zero ord_mul ord_inv ord_coe_unit algebraMap_mem' toValuationSubring IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt"
p2m_open "AlgebraicCurve.Place"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0
    apply h
    rw [v.evalAt_of_mem hf, h0, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]
  have hu : IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    by_contra hnu
    apply hres
    rwa [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  obtain ⟨u, hu⟩ := hu
  have := v.ord_coe_unit u
  rwa [hu] at this

p2m_export "AlgebraicCurve.Place" "ord_eq_zero_of_evalAt_ne_zero"

private theorem _root_.AlgebraicCurve.Place.evalAt_sub_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, v.algebraMap_evalAt hv (sub_mem hf hg),
    ← map_sub]
  rfl

p2m_export "AlgebraicCurve.Place" "evalAt_sub_of_mem"

private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have : IsLocalRing.residue v.toValuationSubring ⟨algebraMap K F a, v.algebraMap_mem' a⟩ =
      algebraMap K v.ResidueField a := rfl
  rw [this, v.residueInv_algebraMap]

p2m_export "AlgebraicCurve.Place" "evalAt_algebraMap"
end Place

namespace Annulus
p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus dom mem_dom param ord_param_sub"
p2m_open "AlgebraicCurve.Annulus"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

private theorem _root_.AlgebraicCurve.Annulus.ord_param_sub_evalAt_of_ne (An : Annulus A F) {P Q : Place L F} (hP : P ∈ An.dom)
    (hQ : Q ∈ An.dom) (hPQ : P ≠ Q) : Q.ord (An.param - algebraMap L F (P.evalAt An.param)) = 0 := by
  obtain ⟨hQrat, hzQ, -, -, -⟩ := An.mem_dom Q hQ
  obtain ⟨-, -, ⟨hPA, hPm⟩, hP0, hPmod⟩ := An.mem_dom P hP
  refine Q.ord_eq_zero_of_evalAt_ne_zero (sub_mem hzQ (Q.algebraMap_mem' _)) ?_
  rw [Q.evalAt_sub_of_mem hQrat hzQ (Q.algebraMap_mem' _), Q.evalAt_algebraMap, sub_ne_zero]
  intro hEq
  obtain ⟨R, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨P.evalAt An.param, hPA⟩ hPm hP0 hPmod
  exact hPQ ((huniq P ⟨hP, rfl⟩).trans (huniq Q ⟨hQ, hEq⟩).symm)

p2m_export "AlgebraicCurve.Annulus" "ord_param_sub_evalAt_of_ne"

private theorem _root_.AlgebraicCurve.Annulus.depth_pos_and_lt (An : Annulus A F) {π : A} (hπ0 : π ≠ 0)
    {w : ℕ} (hw : ∃ u : Aˣ, An.modulus = u * π ^ w)
    {P : Place L F} (hP : P ∈ An.dom) {d : ℕ} {u : Aˣ} {h : P.evalAt An.param ∈ A}
    (hd : (⟨P.evalAt An.param, h⟩ : A) = u * π ^ d) : 0 < d ∧ d < w := by
  obtain ⟨-, -, ⟨hA, hm⟩, hne, m', hm', hmod⟩ := An.mem_dom P hP
  obtain ⟨u', hu'⟩ := hw
  have hAeq : (⟨P.evalAt An.param, hA⟩ : A) = u * π ^ d := hd
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · exfalso
      rw [pow_zero, mul_one] at hAeq
      rw [hAeq] at hm
      exact (IsLocalRing.mem_maximalIdeal _).mp hm u.isUnit
    · exact hd0
  refine ⟨hd0, ?_⟩
  by_contra hdw
  push Not at hdw

  have hmodA : (u' : A) * π ^ w = (u * π ^ d) * m' := by
    rw [← hu', ← hAeq]
    apply Subtype.ext
    rw [MulMemClass.coe_mul]
    exact hmod
  have hsplit : (π : A) ^ d = π ^ (d - w) * π ^ w := by rw [← pow_add, Nat.sub_add_cancel hdw]
  rw [hsplit] at hmodA
  have hu'eq : (u' : A) = u * π ^ (d - w) * m' := by
    apply mul_right_cancel₀ (pow_ne_zero w hπ0)
    rw [hmodA]; ring
  apply (IsLocalRing.mem_maximalIdeal _).mp _ u'.isUnit
  rw [hu'eq]
  exact Ideal.mul_mem_left _ _ hm'

p2m_export "AlgebraicCurve.Annulus" "depth_pos_and_lt"
end Annulus

namespace ComponentChart
p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue nodes residue_algebraMap ker_residue dom"
p2m_open "AlgebraicCurve.ComponentChart"

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

private theorem _root_.AlgebraicCurve.ComponentChart.inv_mem_and_residue_inv (C : ComponentChart A F Fbar) {x : F} (hx : x ∈ C.integers)
    (hres : C.residue ⟨x, hx⟩ ≠ 0) :
    ∃ hinv : x⁻¹ ∈ C.integers, C.residue ⟨x⁻¹, hinv⟩ = (C.residue ⟨x, hx⟩)⁻¹ := by
  have hunit : IsUnit (⟨x, hx⟩ : C.integers) := by
    by_contra hnu
    apply hres
    have hmax : (⟨x, hx⟩ : C.integers) ∈ IsLocalRing.maximalIdeal C.integers :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    rw [← C.ker_residue] at hmax
    exact hmax
  obtain ⟨wu, hwu⟩ := hunit
  have hmul : ((wu⁻¹ : C.integersˣ) : C.integers).1 * x = 1 := by
    have := congrArg (fun y : C.integers => (y : F)) wu.inv_mul
    simpa [hwu] using this
  have hval : ((wu⁻¹ : C.integersˣ) : C.integers).1 = x⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hinv : x⁻¹ ∈ C.integers := by rw [← hval]; exact ((wu⁻¹ : C.integersˣ) : C.integers).2
  refine ⟨hinv, ?_⟩
  have : (⟨x⁻¹, hinv⟩ : C.integers) = ((wu⁻¹ : C.integersˣ) : C.integers) := Subtype.ext hval.symm
  rw [this, map_units_inv, hwu]

p2m_export "AlgebraicCurve.ComponentChart" "inv_mem_and_residue_inv"

private theorem _root_.AlgebraicCurve.ComponentChart.algebraMap_mem (C : ComponentChart A F Fbar) (b : A) : algebraMap L F (b : L) ∈ C.integers :=
  (C.algebraMap_mem_iff (b : L)).mpr b.2

p2m_export "AlgebraicCurve.ComponentChart" "algebraMap_mem"

private theorem _root_.AlgebraicCurve.ComponentChart.residue_algebraMap_eq_zero (C : ComponentChart A F Fbar) (b : A)
    (hb : b ∈ IsLocalRing.maximalIdeal A) : C.residue ⟨algebraMap L F (b : L), C.algebraMap_mem b⟩ = 0 := by
  have := C.residue_algebraMap b
  rw [(IsLocalRing.residue_eq_zero_iff _).mpr hb, map_zero] at this
  exact this

p2m_export "AlgebraicCurve.ComponentChart" "residue_algebraMap_eq_zero"
end ComponentChart

end AlgebraicCurve

theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (e₀ : Fin m) (P P' : Place L F) (hP : P ∈ (An e₀).dom) (hP' : P' ∈ (An e₀).dom) (hPP' : P ≠ P')
    (d : ℕ) (u u' : Aˣ) (h : P.evalAt (An e₀).param ∈ A) (h' : P'.evalAt (An e₀).param ∈ A)
    (hd : (⟨P.evalAt (An e₀).param, h⟩ : A) = u * π ^ d)
    (hd' : (⟨P'.evalAt (An e₀).param, h'⟩ : A) = u' * π ^ d)
    :
    let g : F := ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) /
      ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param))
    g ≠ 0 ∧
      (∀ Q : Place L F, Q.ord g = Q.ord ((An e₀).param - algebraMap L F (P.evalAt (An e₀).param)) -
        Q.ord ((An e₀).param - algebraMap L F (P'.evalAt (An e₀).param))) ∧
      (∀ Q ∈ (An e₀).dom, Q.ord g = (Finsupp.single P 1 - Finsupp.single P' 1 : Divisor L F) Q) ∧
      (∃ hs : g ∈ (C (src e₀)).integers, (C (src e₀)).residue ⟨g, hs⟩ = 1) ∧
      (∃ ht : g ∈ (C (tgt e₀)).integers, (C (tgt e₀)).residue ⟨g, ht⟩ =
        algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e₀)) (IsLocalRing.residue A ((u : A) * ↑u'⁻¹))) := by
  intro g
  classical
  have _ := hratBar; have _ := hratF; have _ := hnodes; have _ := hcover; have _ := hπ

  set z : F := (An e₀).param with hz_def
  set a : L := P.evalAt z with ha_def
  set a' : L := P'.evalAt z with ha'_def
  have hg_def : g = (z - algebraMap L F a) / (z - algebraMap L F a') := rfl
  have haA : (⟨a, h⟩ : A) = u * π ^ d := hd
  have ha'A : (⟨a', h'⟩ : A) = u' * π ^ d := hd'
  have haL : a = ((u * π ^ d : A) : L) := by rw [← haA]
  have ha'L : a' = ((u' * π ^ d : A) : L) := by rw [← ha'A]
  obtain ⟨hd0, hdw⟩ := (An e₀).depth_pos_and_lt hπ0 (hw e₀) hP hd
  have ham : (⟨a, h⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨-, -, ⟨hA, hm⟩, -, -⟩ := (An e₀).mem_dom P hP; exact hm
  have ha'm : (⟨a', h'⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    obtain ⟨-, -, ⟨hA, hm⟩, -, -⟩ := (An e₀).mem_dom P' hP'; exact hm
  have ha0 : a ≠ 0 := by obtain ⟨-, -, -, hne, -⟩ := (An e₀).mem_dom P hP; exact hne
  have ha'0 : a' ≠ 0 := by obtain ⟨-, -, -, hne, -⟩ := (An e₀).mem_dom P' hP'; exact hne

  have hordP : P.ord (z - algebraMap L F a) = 1 := (An e₀).ord_param_sub P hP
  have hordP' : P'.ord (z - algebraMap L F a') = 1 := (An e₀).ord_param_sub P' hP'
  have hne : z - algebraMap L F a ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordP; exact zero_ne_one hordP
  have hne' : z - algebraMap L F a' ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordP'; exact zero_ne_one hordP'
  have hg0 : g ≠ 0 := div_ne_zero hne hne'
  have hglob : ∀ Q : Place L F, Q.ord g = Q.ord (z - algebraMap L F a) - Q.ord (z - algebraMap L F a') := by
    intro Q
    rw [hg_def, div_eq_mul_inv, Q.ord_mul hne (inv_ne_zero hne'), Q.ord_inv]; ring
  refine ⟨hg0, hglob, ?_, ?_, ?_⟩
  ·
    intro Q hQ
    rw [hglob, Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
    by_cases hQP : P = Q
    · subst hQP
      have h2 : P.ord (z - algebraMap L F a') = 0 :=
        (An e₀).ord_param_sub_evalAt_of_ne hP' hP (Ne.symm hPP')
      rw [hordP, h2, if_pos rfl, if_neg (Ne.symm hPP')]
    · by_cases hQP' : P' = Q
      · subst hQP'
        have h1 : P'.ord (z - algebraMap L F a) = 0 := (An e₀).ord_param_sub_evalAt_of_ne hP hP' hPP'
        rw [hordP', h1, if_neg hQP, if_pos rfl]
      · rw [(An e₀).ord_param_sub_evalAt_of_ne hP hQ hQP, (An e₀).ord_param_sub_evalAt_of_ne hP' hQ hQP',
          if_neg hQP, if_neg hQP']
  ·

    set Cs := C (src e₀) with hCs
    obtain ⟨-, hzC, hzord, -⟩ := (hatt e₀).1
    have hres_z : Cs.residue ⟨z, hzC⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hzord; exact zero_ne_one hzord
    have hnum : z - algebraMap L F a ∈ Cs.integers := sub_mem hzC (Cs.algebraMap_mem ⟨a, h⟩)
    have hden : z - algebraMap L F a' ∈ Cs.integers := sub_mem hzC (Cs.algebraMap_mem ⟨a', h'⟩)
    have hres_num : Cs.residue ⟨z - algebraMap L F a, hnum⟩ = Cs.residue ⟨z, hzC⟩ := by
      have : (⟨z - algebraMap L F a, hnum⟩ : Cs.integers) =
          ⟨z, hzC⟩ - ⟨algebraMap L F a, Cs.algebraMap_mem ⟨a, h⟩⟩ := rfl
      rw [this, map_sub, Cs.residue_algebraMap_eq_zero ⟨a, h⟩ ham, sub_zero]
    have hres_den : Cs.residue ⟨z - algebraMap L F a', hden⟩ = Cs.residue ⟨z, hzC⟩ := by
      have : (⟨z - algebraMap L F a', hden⟩ : Cs.integers) =
          ⟨z, hzC⟩ - ⟨algebraMap L F a', Cs.algebraMap_mem ⟨a', h'⟩⟩ := rfl
      rw [this, map_sub, Cs.residue_algebraMap_eq_zero ⟨a', h'⟩ ha'm, sub_zero]
    obtain ⟨hdinv, hres_dinv⟩ := Cs.inv_mem_and_residue_inv hden (by rw [hres_den]; exact hres_z)
    have hgmem : g ∈ Cs.integers := by
      rw [hg_def, div_eq_mul_inv]; exact mul_mem hnum hdinv
    refine ⟨hgmem, ?_⟩
    have hprod : (⟨g, hgmem⟩ : Cs.integers) =
        ⟨z - algebraMap L F a, hnum⟩ * ⟨(z - algebraMap L F a')⁻¹, hdinv⟩ := by
      apply Subtype.ext
      show g = (z - algebraMap L F a) * (z - algebraMap L F a')⁻¹
      rw [hg_def, div_eq_mul_inv]
    rw [hprod, map_mul, hres_num, hres_dinv, hres_den, mul_inv_cancel₀ hres_z]
  ·

    set Ct := C (tgt e₀) with hCt
    obtain ⟨-, hz'C, hz'ord, -⟩ := (hatt e₀).2
    obtain ⟨-, -, hM0, hzz'⟩ := hpair e₀
    set z' : F := (An' e₀).param with hz'_def
    set M : A := (An e₀).modulus with hM_def
    have hres_z' : Ct.residue ⟨z', hz'C⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hz'ord; exact zero_ne_one hz'ord
    obtain ⟨hz'inv, hres_z'inv⟩ := Ct.inv_mem_and_residue_inv hz'C hres_z'
    have hz'0 : z' ≠ 0 := by
      intro h0
      apply hM0
      have : algebraMap L F (M : L) = 0 := by rw [← hzz', h0, zero_mul]
      exact (map_eq_zero _).mp this
    have hzM : z = algebraMap L F (M : L) * z'⁻¹ := by
      rw [← hzz', mul_comm z' z, mul_assoc, mul_inv_cancel₀ hz'0, mul_one]

    obtain ⟨v, hv⟩ := hw e₀
    have hq : ∀ (b : L) (ub : Aˣ) (hb : b ∈ A), (⟨b, hb⟩ : A) = ub * π ^ d →
        ∃ hqA : (M : L) / b ∈ A, (⟨(M : L) / b, hqA⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
          (⟨(M : L) / b, hqA⟩ : A) = v * ↑ub⁻¹ * π ^ (w e₀ - d) := by
      intro b ub hb hbA
      have hb0 : (b : L) ≠ 0 := by
        intro hb0
        have : (⟨b, hb⟩ : A) = 0 := Subtype.ext hb0
        rw [this] at hbA
        exact (mul_ne_zero (Units.ne_zero ub) (pow_ne_zero d hπ0)) hbA.symm
      have hbL : b = ((ub * π ^ d : A) : L) := by rw [← hbA]
      have hkey : ((v * ↑ub⁻¹ * π ^ (w e₀ - d) : A) : L) * b = (M : L) := by
        rw [hbL, ← Subring.coe_mul, hM_def, hv]
        congr 1
        rw [show (v : A) * ↑ub⁻¹ * π ^ (w e₀ - d) * (↑ub * π ^ d) =
          v * (↑ub⁻¹ * ↑ub) * (π ^ (w e₀ - d) * π ^ d) by ring, Units.inv_mul, mul_one, ← pow_add,
          Nat.sub_add_cancel hdw.le]
      have hqeq : (M : L) / b = ((v * ↑ub⁻¹ * π ^ (w e₀ - d) : A) : L) := by
        rw [div_eq_iff hb0]; exact hkey.symm
      refine ⟨by rw [hqeq]; exact Subtype.mem _, ?_, ?_⟩
      · have : (⟨(M : L) / b, by rw [hqeq]; exact Subtype.mem _⟩ : A) = v * ↑ub⁻¹ * π ^ (w e₀ - d) :=
          Subtype.ext hqeq
        rw [this]
        exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hπ _ (Nat.sub_pos_of_lt hdw))
      · exact Subtype.ext hqeq
    obtain ⟨hqA, hqm, -⟩ := hq a u h haA
    obtain ⟨hq'A, hq'm, -⟩ := hq a' u' h' ha'A

    have hfac : ∀ (b : L) (hb0 : b ≠ 0), z - algebraMap L F b =
        algebraMap L F b * (algebraMap L F ((M : L) / b) * z'⁻¹ - 1) := by
      intro b hb0
      rw [hzM, mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_div_cancel₀ _ hb0]
    have hr_mem : ∀ (b : L) (hbA : (M : L) / b ∈ A), (⟨(M : L) / b, hbA⟩ : A) ∈ IsLocalRing.maximalIdeal A →
        ∃ hr : algebraMap L F ((M : L) / b) * z'⁻¹ - 1 ∈ Ct.integers, Ct.residue ⟨_, hr⟩ = -1 := by
      intro b hbA hbm
      have hc : algebraMap L F ((M : L) / b) ∈ Ct.integers := Ct.algebraMap_mem ⟨_, hbA⟩
      have hr : algebraMap L F ((M : L) / b) * z'⁻¹ - 1 ∈ Ct.integers :=
        sub_mem (mul_mem hc hz'inv) (one_mem _)
      refine ⟨hr, ?_⟩
      have : (⟨algebraMap L F ((M : L) / b) * z'⁻¹ - 1, hr⟩ : Ct.integers) =
          ⟨algebraMap L F ((M : L) / b), hc⟩ * ⟨z'⁻¹, hz'inv⟩ - 1 := rfl
      rw [this, map_sub, map_mul, map_one, Ct.residue_algebraMap_eq_zero ⟨_, hbA⟩ hbm, zero_mul, zero_sub]
    obtain ⟨hr, hres_r⟩ := hr_mem a hqA hqm
    obtain ⟨hr', hres_r'⟩ := hr_mem a' hq'A hq'm
    obtain ⟨hr'inv, hres_r'inv⟩ := Ct.inv_mem_and_residue_inv hr' (by rw [hres_r']; exact neg_ne_zero.mpr one_ne_zero)

    have hconst : a / a' = ((u * ↑u'⁻¹ : A) : L) := by
      rw [haL, ha'L, div_eq_iff (by rw [← ha'L]; exact ha'0), ← Subring.coe_mul]
      congr 1
      rw [show (u : A) * ↑u'⁻¹ * (↑u' * π ^ d) = u * (↑u'⁻¹ * ↑u') * π ^ d by ring, Units.inv_mul, mul_one]
    have hcmem : algebraMap L F (a / a') ∈ Ct.integers := by rw [hconst]; exact Ct.algebraMap_mem _
    have hres_c : Ct.residue ⟨algebraMap L F (a / a'), hcmem⟩ =
        algebraMap (IsLocalRing.ResidueField A) (Fbar (tgt e₀)) (IsLocalRing.residue A ((u : A) * ↑u'⁻¹)) := by
      have : (⟨algebraMap L F (a / a'), hcmem⟩ : Ct.integers) =
          ⟨algebraMap L F ((u * ↑u'⁻¹ : A) : L), Ct.algebraMap_mem _⟩ :=
        Subtype.ext (congrArg (algebraMap L F) hconst)
      rw [this]
      exact Ct.residue_algebraMap _

    have hgeq : g = algebraMap L F (a / a') *
        ((algebraMap L F ((M : L) / a) * z'⁻¹ - 1) * (algebraMap L F ((M : L) / a') * z'⁻¹ - 1)⁻¹) := by
      rw [hg_def, hfac a ha0, hfac a' ha'0]
      simp only [map_div₀]
      rw [div_eq_mul_inv _ (algebraMap L F a' * _), mul_inv]
      ring
    have hgmem : g ∈ Ct.integers := by
      rw [hgeq]; exact mul_mem hcmem (mul_mem hr hr'inv)
    refine ⟨hgmem, ?_⟩
    have hprod : (⟨g, hgmem⟩ : Ct.integers) = ⟨algebraMap L F (a / a'), hcmem⟩ *
        (⟨algebraMap L F ((M : L) / a) * z'⁻¹ - 1, hr⟩ * ⟨(algebraMap L F ((M : L) / a') * z'⁻¹ - 1)⁻¹, hr'inv⟩) :=
      Subtype.ext hgeq
    rw [hprod, map_mul, map_mul, hres_c, hres_r, hres_r'inv, hres_r']
    simp

end S_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq
end P2MW
export P2MW.S_AlgebraicCurve_Annulus_ord_sub_div_sub_and_residue_src_eq_one_and_residue_tgt_eq_of_depth_eq (solution)
