-- Prove2me | solution 1 for AlgebraicCurve.SemistableCovering.forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/25ce53c3-8a52-55f9-822b-a1ed2264d9c8

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_AlgebraicCurve_Annulus_sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Place_ord_smul_of_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_SemistableCovering_forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open AlgebraicCurve IsLocalRing

namespace AF8ExactPotential

section ValRing

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem exists_fourth_root [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0) :
    ∃ s : A, s ∈ maximalIdeal A ∧ (s : L) ≠ 0 ∧ s ^ 4 = π := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (π : L) (by norm_num : 0 < 4)
  have hπL : (π : L) ≠ 0 := by exact_mod_cast hπ0
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hπL
    rw [← ht]; simp
  have htA : t ∈ A := by
    rcases A.mem_or_inv_mem t with h | h
    · exact h
    · exfalso
      have hinv : (π : L)⁻¹ ∈ A := by
        rw [← ht, ← inv_pow]
        exact pow_mem h 4
      have hunit : IsUnit π := by
        refine ⟨⟨π, ⟨(π : L)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
        · exact Subtype.ext (mul_inv_cancel₀ hπL)
        · exact Subtype.ext (inv_mul_cancel₀ hπL)
      exact (IsLocalRing.mem_maximalIdeal _).mp hπ hunit
  refine ⟨⟨t, htA⟩, ?_, ht0, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply (IsLocalRing.mem_maximalIdeal _).mp hπ
    have : π = (⟨t, htA⟩ : A) ^ 4 := Subtype.ext (by push_cast; exact ht.symm)
    rw [this]
    exact hu.pow 4
  · exact Subtype.ext (by push_cast; exact ht)

end ValRing

section Charts

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]

theorem const_ne_zero {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (C : ComponentChart A F Fb) {f : F} {c : L} (hc : c • f ∈ C.integers)
    (hres : C.residue ⟨c • f, hc⟩ ≠ 0) : c ≠ 0 := by
  rintro rfl
  apply hres
  have : (⟨(0 : L) • f, hc⟩ : C.integers) = 0 := Subtype.ext (by simp)
  rw [this, map_zero]

theorem width_pos (π : A) (An : Annulus A F) {W : ℕ} {u₀ : Aˣ}
    (hW : An.modulus = u₀ * π ^ W) : 0 < W := by
  rcases Nat.eq_zero_or_pos W with h | h
  · exfalso
    subst h
    rw [pow_zero, mul_one] at hW
    have := An.modulus_mem
    rw [hW] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp this (Units.isUnit u₀)
  · exact h

theorem exists_two_radii [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0)
    (An : Annulus A F) {W : ℕ} {u₀ : Aˣ} (hW : An.modulus = u₀ * π ^ W) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom,
      A.valuation (Q₁.evalAt An.param) ≠ A.valuation (Q₂.evalAt An.param) := by
  have hWpos := width_pos π An hW
  obtain ⟨s, hs, hs0, hs4⟩ := exists_fourth_root π hπ hπ0
  have hadm : ∀ (j : ℕ), 0 < j → j < 4 * W →
      ∃! P : Place L F, P ∈ An.dom ∧ P.evalAt An.param = ((s ^ j : A) : L) := by
    intro j hj hjW
    apply An.existsUnique_evalAt_eq
    · exact Ideal.pow_mem_of_mem _ hs j hj
    · push_cast; exact pow_ne_zero _ hs0
    · refine ⟨u₀ * s ^ (4 * W - j), ?_, ?_⟩
      · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hs _ (by omega))
      · rw [hW, ← hs4]
        push_cast
        have hsplit : (s : L) ^ (4 * W) = (s : L) ^ j * (s : L) ^ (4 * W - j) := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        rw [← pow_mul, hsplit]
        ring
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := hadm 1 one_pos (by omega)
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := hadm 2 (by norm_num) (by omega)
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁v, hQ₂v]
  push_cast
  rw [pow_one, Valuation.map_pow]
  intro heq
  have hvs0 : A.valuation (s : L) ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact hs0
  have hone : A.valuation (s : L) = 1 := by
    have : A.valuation (s : L) * 1 = A.valuation (s : L) * A.valuation (s : L) := by
      rw [mul_one, ← sq]; exact heq
    exact (mul_left_cancel₀ hvs0 this).symm
  rw [← ValuationSubring.valuation_eq_one_iff] at hone
  exact (IsLocalRing.mem_maximalIdeal _).mp hs hone

@[reducible] def toRP {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (C : ComponentChart A F Fb) : RegularProlongation A F Fb where
  integers := C.integers
  residue := C.residue
  algebraMap_mem_iff := C.algebraMap_mem_iff
  residue_surjective := C.residue_surjective
  ker_residue := C.ker_residue
  residue_algebraMap := C.residue_algebraMap
  exists_smul_mem := C.exists_smul_mem

theorem isAttached_transport {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
    (An' : Annulus A F) (C : ComponentChart A F Fb) (x : Place (ResidueField A) Fb)
    (hatt : An'.IsAttached C x) {y : F} (hy : An'.param = y) {S : Set (Place L F)}
    (hS : An'.dom = S) :
    ∃ hz : y ∈ C.integers, x.ord (C.residue ⟨y, hz⟩) = 1 ∧
      ∀ (f : F) (hf : f ∈ C.integers), C.residue ⟨f, hf⟩ ≠ 0 → (∀ P ∈ S, P.ord f = 0) →
        ∀ P ∈ S, ∃ h : P.evalAt f * (P.evalAt y) ^ (-(x.ord (C.residue ⟨f, hf⟩))) ∈ A,
          IsUnit (⟨_, h⟩ : A) := by
  subst hy; subst hS
  exact hatt.2

theorem two_end_mass [IsAlgClosed L] (π : A) (hπ : π ∈ maximalIdeal A) (hπ0 : π ≠ 0)
    {Fs : Type*} [Field Fs] [Algebra (ResidueField A) Fs]
    {Ft : Type*} [Field Ft] [Algebra (ResidueField A) Ft]
    (An An' : Annulus A F) (hdom : An'.dom = An.dom)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    {W : ℕ} {u₀ : Aˣ} (hW : An.modulus = u₀ * π ^ W)
    (Cs : ComponentChart A F Fs) (xs : Place (ResidueField A) Fs) (hatts : An.IsAttached Cs xs)
    (Ct : ComponentChart A F Ft) (xt : Place (ResidueField A) Ft) (hattt : An'.IsAttached Ct xt)
    (f : F) (hf0 : f ≠ 0)
    (cs : L) (hcs : cs • f ∈ Cs.integers) (hress : Cs.residue ⟨cs • f, hcs⟩ ≠ 0)
    (ct : L) (hct : ct • f ∈ Ct.integers) (hrest : Ct.residue ⟨ct • f, hct⟩ ≠ 0)
    (E : Divisor L F) (hEsupp : ∀ P ∈ E.support, P ∈ An.dom) (hE : ∀ P ∈ An.dom, E P = P.ord f) :
    (E.sum fun _ n => n) = xs.ord (Cs.residue ⟨cs • f, hcs⟩) + xt.ord (Ct.residue ⟨ct • f, hct⟩) := by
  have hcs0 : cs ≠ 0 := const_ne_zero Cs hcs hress
  have hct0 : ct ≠ 0 := const_ne_zero Ct hct hrest
  have hz0 : An.param ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at htwo
    exact hmod0 ((map_eq_zero _).mp htwo.symm)
  have hkey : An'.param = algebraMap L F (An.modulus : L) * An.param⁻¹ := by
    rw [← htwo, mul_inv_cancel_right₀ hz0]
  obtain ⟨hza, hxa, hslope_a⟩ := hatts.2
  obtain ⟨hzb, hxb, hslope_b⟩ := isAttached_transport An' Ct xt hattt hkey hdom
  set c' : L := cs / ct with hc'
  have hc'0 : c' ≠ 0 := div_ne_zero hcs0 hct0
  have heq : (algebraMap L F c')⁻¹ * (cs • f) = ct • f := by
    rw [hc', Algebra.smul_def, Algebra.smul_def, map_div₀]
    have : algebraMap L F cs ≠ 0 := (map_ne_zero _).mpr hcs0
    field_simp
  have hhb : (algebraMap L F c')⁻¹ * (cs • f) ∈ Ct.integers := by rw [heq]; exact hct
  have hsub : (⟨(algebraMap L F c')⁻¹ * (cs • f), hhb⟩ : Ct.integers) = ⟨ct • f, hct⟩ :=
    Subtype.ext heq
  have hresb : Ct.residue ⟨(algebraMap L F c')⁻¹ * (cs • f), hhb⟩ ≠ 0 := by
    rw [hsub]; exact hrest
  have hwide := exists_two_radii π hπ hπ0 An hW
  have hsm0 : cs • f ≠ 0 := smul_ne_zero hcs0 hf0
  have hE' : ∀ P ∈ An.dom, E P = P.ord (cs • f) := fun P hP => by
    rw [hE P hP, Place.ord_smul_of_ne_zero P hcs0 f]
  obtain ⟨hmass, -⟩ :=
    AlgebraicCurve.Annulus.sum_eq_ord_add_ord_and_prod_valuation_evalAt_zpow_eq_of_regularProlongation
      An hmod0 (toRP Cs) xs hza hxa hslope_a (toRP Ct) xt hzb hxb hslope_b hwide
      (cs • f) hsm0 hcs hress c' hc'0 hhb hresb E hEsupp hE'
  rw [hmass]
  show xs.ord (Cs.residue ⟨cs • f, hcs⟩) + xt.ord (Ct.residue ⟨_, hhb⟩) = _
  rw [hsub]

end Charts

section Finsupp

variable {α : Type*}

theorem eq_zero_of_nonneg_of_sum_eq_zero (G : α →₀ ℤ) (hG : ∀ a, 0 ≤ G a)
    (hsum : (G.sum fun _ n => n) = 0) : G = 0 := by
  have hall : ∀ a ∈ G.support, G a = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hG a)).mp hsum
  ext a
  by_cases ha : a ∈ G.support
  · exact hall a ha
  · exact Finsupp.notMem_support_iff.mp ha

theorem mapDomain_apply_eq_sum {β : Type*} [DecidableEq β] (φ : α → β) (D : α →₀ ℤ) (b : β) :
    Finsupp.mapDomain φ D b = ∑ a ∈ D.support, if φ a = b then D a else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  show (Finsupp.single (φ a) (D a)) b = _
  rw [Finsupp.single_apply]

end Finsupp

section Degree

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]

theorem degree_eq_sum (D : Divisor K F) : Divisor.degree D = D.sum fun _ n => n := by
  have : Divisor.degree D = D.sum fun Q n => n * (Q.deg : ℤ) := by
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply]
    rfl
  rw [this]
  apply Finsupp.sum_congr
  intro Q _
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed Q]
  simp

end Degree

end AF8ExactPotential

open AF8ExactPotential in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
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
    (hw1 : ∀ e, w e = 1)
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
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (φ : Fin n → ℤ)
    :
    let k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e)
    let wt : Fin n → L := fun i => (((π : A) : L) ^ (φ i))⁻¹
    ∀ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers),
      (∀ i, (C i).residue ⟨wt i • g, hg i⟩ ≠ 0) →
      (∀ e, ∀ P ∈ (An e).dom, 0 ≤ P.ord g) →
      (∀ e, (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩) = k e) →
      (∀ e, (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩) = -k e) →

      (∀ e, ∀ P ∈ (An e).dom, P.ord g = 0) ∧

      (∀ i (Dg : Divisor L F), (∀ P ∈ (C i).dom, Dg P = P.ord g) → (∀ P, P ∉ (C i).dom → Dg P = 0) →
        (Dg.sum fun _ l => l) =
          ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0))) := by
  intro k wt g hg hres hreg hexs hext
  classical
  haveI hκ : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField A
  have hk : ∀ e, k e = φ (tgt e) - φ (src e) := fun e => rfl
  have hwt : ∀ i, wt i = (((π : A) : L) ^ (φ i))⁻¹ := fun i => rfl
  have hπL : ((π : A) : L) ≠ 0 := fun h0 => hπ0 (Subtype.ext h0)
  have hwt0 : ∀ i, wt i ≠ 0 := fun i => by rw [hwt]; exact inv_ne_zero (zpow_ne_zero _ hπL)
  have hg0_of : ∀ i : Fin n, g ≠ 0 := by
    intro i h0
    apply hres i
    have : (⟨wt i • g, hg i⟩ : (C i).integers) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero]

  have part1 : ∀ e, ∀ P ∈ (An e).dom, P.ord g = 0 := by
    intro e
    have hg0 : g ≠ 0 := hg0_of (src e)
    obtain ⟨Dfull, hDfull, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) g hg0
    set E : Divisor L F := Dfull.filter (· ∈ (An e).dom) with hE
    have hE_in : ∀ P ∈ (An e).dom, E P = P.ord g := fun P hP => by
      rw [hE, Finsupp.filter_apply_pos _ _ hP, hDfull P]
    have hE_supp : ∀ P ∈ E.support, P ∈ (An e).dom := by
      intro P hP
      rw [hE, Finsupp.support_filter, Finset.mem_filter] at hP
      exact hP.2
    have hE_nonneg : ∀ P, 0 ≤ E P := by
      intro P
      by_cases hP : P ∈ (An e).dom
      · rw [hE_in P hP]; exact hreg e P hP
      · rw [hE, Finsupp.filter_apply_neg _ _ hP]
    obtain ⟨u₀, hu₀⟩ := hw e
    have hmass := two_end_mass π hπ hπ0 (An e) (An' e) (hpair e).1 (hpair e).2.2.1 (hpair e).2.2.2 hu₀
      (C (src e)) (xs e) (hatt e).1 (C (tgt e)) (xt e) (hatt e).2 g hg0
      (wt (src e)) (hg (src e)) (hres (src e)) (wt (tgt e)) (hg (tgt e)) (hres (tgt e)) E hE_supp hE_in
    rw [hexs e, hext e, add_neg_cancel] at hmass
    have hE0 := eq_zero_of_nonneg_of_sum_eq_zero E hE_nonneg hmass
    intro P hP
    rw [← hE_in P hP, hE0, Finsupp.coe_zero, Pi.zero_apply]
  refine ⟨part1, ?_⟩

  intro i Dg hDg_in hDg_out

  have hnode_ord : ∀ x ∈ (C i).nodes, x.ord ((C i).residue ⟨wt i • g, hg i⟩) =
      ∑ e, ((if (⟨src e, xs e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ then k e else 0) +
        (if (⟨tgt e, xt e⟩ : Σ j, Place (ResidueField A) (Fbar j)) = ⟨i, x⟩ then -k e else 0)) := by
    intro x hx
    obtain ⟨e, he | he⟩ := hnodes.1 i x hx
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp he
      subst h1
      have h3 := eq_of_heq h2
      subst h3
      rw [hexs e, Finset.sum_add_distrib, Finset.sum_eq_single_of_mem e (Finset.mem_univ e), if_pos rfl,
        Finset.sum_eq_zero, add_zero]
      · intro e' _
        rw [if_neg]
        intro he'
        have := hnodes.2 (src e) (xs e) (hatt e).1.1 (Sum.inr e') (Sum.inl e) he' rfl
        exact Sum.inr_ne_inl this
      · intro e' _ hne
        rw [if_neg]
        intro he'
        have := hnodes.2 (src e) (xs e) (hatt e).1.1 (Sum.inl e') (Sum.inl e) he' rfl
        exact hne (Sum.inl_injective this)
    · obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp he
      subst h1
      have h3 := eq_of_heq h2
      subst h3
      rw [hext e, Finset.sum_add_distrib, Finset.sum_eq_zero, zero_add,
        Finset.sum_eq_single_of_mem e (Finset.mem_univ e), if_pos rfl]
      · intro e' _ hne
        rw [if_neg]
        intro he'
        have := hnodes.2 (tgt e) (xt e) (hatt e).2.1 (Sum.inr e') (Sum.inr e) he' rfl
        exact hne (Sum.inr_injective this)
      · intro e' _
        rw [if_neg]
        intro he'
        have := hnodes.2 (tgt e) (xt e) (hatt e).2.1 (Sum.inl e') (Sum.inr e) he' rfl
        exact Sum.inl_ne_inr this

  have hnode_sum : ∑ x ∈ (C i).nodes, x.ord ((C i).residue ⟨wt i • g, hg i⟩) =
      -∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)) := by
    rw [Finset.sum_congr rfl hnode_ord, Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_add_distrib, neg_add]
    congr 1
    · by_cases hi : src e = i
      · subst hi
        rw [if_pos rfl, Finset.sum_eq_single_of_mem (xs e) (hatt e).1.1, if_pos rfl, hk]
        · ring
        · intro x _ hx
          rw [if_neg]
          intro heq
          apply hx
          obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp heq
          exact (eq_of_heq h2).symm
      · rw [if_neg hi, neg_zero]
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        intro heq
        exact hi (Sigma.mk.inj_iff.mp heq).1
    · by_cases hi : tgt e = i
      · subst hi
        rw [if_pos rfl, Finset.sum_eq_single_of_mem (xt e) (hatt e).2.1, if_pos rfl, hk]
        intro x _ hx
        rw [if_neg]
        intro heq
        apply hx
        obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp heq
        exact (eq_of_heq h2).symm
      · rw [if_neg hi, neg_zero]
        apply Finset.sum_eq_zero
        intro x _
        rw [if_neg]
        intro heq
        exact hi (Sigma.mk.inj_iff.mp heq).1

  set f : (C i).integers := ⟨wt i • g, hg i⟩ with hf
  have hmap : ∀ Q, Q ∉ (C i).nodes → Finsupp.mapDomain (C i).placeMap Dg Q = Q.ord ((C i).residue f) := by
    intro Q hQ
    refine (C i).mapDomain_placeMap f (hres i) Dg (fun P hP => ?_) hDg_out Q hQ
    rw [hDg_in P hP]
    show P.ord g = P.ord (wt i • g)
    rw [Place.ord_smul_of_ne_zero P (hwt0 i) g]
  set M : Divisor (ResidueField A) (Fbar i) := Finsupp.mapDomain (C i).placeMap Dg with hM
  have hM_node : ∀ Q ∈ (C i).nodes, M Q = 0 := by
    intro Q hQ
    rw [hM, mapDomain_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro P hP
    rw [if_neg]
    intro hPQ
    have hPdom : P ∈ (C i).dom := by
      by_contra hPd
      exact (Finsupp.mem_support_iff.mp hP) (hDg_out P hPd)
    exact (C i).placeMap_not_mem_nodes P hPdom (hPQ ▸ hQ)
  obtain ⟨Dh, hDh, hDh_deg⟩ := HasPrincipalDivisors.exists_divisor (K := ResidueField A) _ (hres i)
  have hDh0 : (Dh.sum fun _ l => l) = 0 := by rw [← degree_eq_sum]; exact hDh_deg

  set T : Finset (Place (ResidueField A) (Fbar i)) := Dh.support ∪ (C i).nodes ∪ M.support with hT
  have hsumT : ∀ (G : Divisor (ResidueField A) (Fbar i)), G.support ⊆ T → (G.sum fun _ l => l) = ∑ Q ∈ T, G Q :=
    fun G hG => Finsupp.sum_of_support_subset G hG _ (fun _ _ => rfl)
  have hDhT : (Dh.sum fun _ l => l) = ∑ Q ∈ T, Dh Q := hsumT Dh (by
    intro Q hQ; rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hQ))
  have hMT : (M.sum fun _ l => l) = ∑ Q ∈ T, M Q := hsumT M (by
    intro Q hQ; rw [hT]; exact Finset.mem_union_right _ hQ)
  have hpt : ∀ Q, Dh Q = M Q + if Q ∈ (C i).nodes then Dh Q else 0 := by
    intro Q
    by_cases hQ : Q ∈ (C i).nodes
    · rw [if_pos hQ, hM_node Q hQ, zero_add]
    · rw [if_neg hQ, add_zero, hDh Q, ← hmap Q hQ]
  have hnodesT : (C i).nodes ⊆ T := by
    intro Q hQ; rw [hT]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hQ)
  have hsplit : ∑ Q ∈ T, Dh Q = (∑ Q ∈ T, M Q) + ∑ x ∈ (C i).nodes, Dh x := by
    rw [Finset.sum_congr rfl (fun Q _ => hpt Q), Finset.sum_add_distrib, ← Finset.sum_filter]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext Q
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hnodesT h, h⟩⟩

  have hDgM : (Dg.sum fun _ l => l) = (M.sum fun _ l => l) := by
    rw [hM, Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [hDgM, hMT]
  have h1 : (∑ Q ∈ T, M Q) = -∑ x ∈ (C i).nodes, Dh x := by
    have := hsplit
    rw [← hDhT, hDh0] at this
    linarith
  rw [h1]
  have h2 : ∑ x ∈ (C i).nodes, Dh x = ∑ x ∈ (C i).nodes, x.ord ((C i).residue ⟨wt i • g, hg i⟩) :=
    Finset.sum_congr rfl (fun x _ => hDh x)
  rw [h2, hnode_sum, neg_neg]

end
end S_AlgebraicCurve_SemistableCovering_forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
end P2MW
export P2MW.S_AlgebraicCurve_SemistableCovering_forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one (solution)
