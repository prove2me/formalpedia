-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.false_of_annulus_attached_regularProlongation_of_smoothPointPackage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/b429faf6-9b77-5016-9ea7-8af190704413

import Mathlib
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

namespace SmoothPointExcludesAnnulus

section PlaceLemmas

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem one_le_ord_of_mem_maximalIdeal (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring)
    (hf0 : f ≠ 0) (hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring) :
    1 ≤ v.ord f := by
  have h0 : 0 ≤ v.ord f := ord_nonneg_of_mem v hf
  rcases h0.lt_or_eq with hlt | heq
  · omega
  · exfalso
    exact (IsLocalRing.mem_maximalIdeal _).mp hmax (v.isUnit_mk_of_ord_eq_zero hf0 heq.symm)

theorem ord_algebraMap (v : Place K F) (c : K) : v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := ord_nonneg_of_mem v (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
      rw [← map_inv₀]; exact v.algebraMap_mem' _
    exact ord_nonneg_of_mem v hmem'
  rw [v.ord_inv] at h2
  omega

end PlaceLemmas

section ValueGroup

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem eq_of_zpow_eq_zpow {a b : Γ₀} {N : ℤ} (hN : N ≠ 0) (h : a ^ N = b ^ N) : a = b := by
  rcases N with k | k
  · rw [Int.ofNat_eq_natCast] at hN h
    rw [zpow_natCast, zpow_natCast] at h
    have hk : k ≠ 0 := fun h0 => hN (by rw [h0]; rfl)
    exact pow_left_injective hk h
  · rw [zpow_negSucc, zpow_negSucc, inv_inj] at h
    exact pow_left_injective (Nat.succ_ne_zero k) h

theorem eq_zpow_of_mul_zpow_neg_eq_one {x y : Γ₀} (hy : y ≠ 0) {k : ℤ} (h : x * y ^ (-k) = 1) :
    x = y ^ k := by
  have hyk : y ^ k ≠ 0 := zpow_ne_zero k hy
  calc x = x * y ^ (-k) * y ^ k := by rw [mul_assoc, zpow_neg, inv_mul_cancel₀ hyk, mul_one]
    _ = y ^ k := by rw [h, one_mul]

theorem zpow_le_one_of_le_one_of_nonneg {μ : Γ₀} (hμ : μ ≤ 1) {k : ℤ} (hk : 0 ≤ k) : μ ^ k ≤ 1 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  rw [zpow_natCast]
  exact pow_le_one₀ zero_le' hμ

theorem zpow_lt_one_of_lt_one_of_pos {μ : Γ₀} (hμ : μ < 1) {k : ℤ} (hk : 1 ≤ k) : μ ^ k < 1 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k by omega)
  rw [zpow_natCast]
  have hn : n ≠ 0 := by
    intro h0; rw [h0] at hk; norm_num at hk
  exact pow_lt_one₀ zero_le' hμ hn

end ValueGroup

end SmoothPointExcludesAnnulus

open SmoothPointExcludesAnnulus in
theorem solution
    {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)

    (S : Subring F) (hAS : ∀ a : ↥A, algebraMap L F (a : L) ∈ S)
    (φ : Polynomial ↥A →+* ↥S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified)
    (hφC : ∀ a : ↥A, ((φ (Polynomial.C a) : ↥S) : F) = algebraMap L F (a : L))
    (χ₀ : ↥S →+* ResidueField ↥A) (hχ₀C : ∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a)
    (hχ₀t : χ₀ (φ Polynomial.X) = 0)

    (hchart : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
      ∃! χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
        (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c)

    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)
    (hres : ∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f))
    (hordQ : Q.ord (R.residue ⟨((φ Polynomial.X : ↥S) : F), hSR (φ Polynomial.X)⟩) = 1)

    (D : Set (Place L F))
    (hD : ∀ P ∈ D, P.IsRational ∧ (∀ f : ↥S, (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
      (∀ f : ↥S, A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))

    (hsec : ∀ χ : ↥S →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
      (∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f) →
      ∃! P, P ∈ D ∧ ∀ f : ↥S, P.evalAt (f : F) = ((χ f : ↥A) : L))

    (hval : ∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔ ∃ g h : ↥S, P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F))

    (hloc : ∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
      ∃ (c : L) (u : (↥S)ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥S) : F))
    (hloc' : ∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)

    (An' An : Annulus A F)
    (hAn : An'.dom = An.dom ∧ An'.modulus = An.modulus ∧ (An.modulus : L) ≠ 0 ∧
      An'.param * An.param = algebraMap L F (An.modulus : L))
    (hnear : ∃ hz : An'.param ∈ R.integers, Q.ord (R.residue ⟨An'.param, hz⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ R.integers), R.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An'.dom, P.ord g = 0) →
        ∀ P ∈ An'.dom, ∃ h : P.evalAt g * (P.evalAt An'.param) ^ (-(Q.ord (R.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    {Fbar' : Type*} [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
    (Rx : RegularProlongation A F Fbar') (bx : Place (ResidueField ↥A) Fbar')
    (hfar : ∃ hz : An.param ∈ Rx.integers, bx.ord (Rx.residue ⟨An.param, hz⟩) = 1 ∧
      ∀ (g : F) (hg : g ∈ Rx.integers), Rx.residue ⟨g, hg⟩ ≠ 0 → (∀ P ∈ An.dom, P.ord g = 0) →
        ∀ P ∈ An.dom, ∃ h : P.evalAt g * (P.evalAt An.param) ^ (-(bx.ord (Rx.residue ⟨g, hg⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (hdom : ∃ P₁ ∈ An'.dom, ∃ P₂ ∈ An'.dom, A.valuation (P₁.evalAt An'.param) ≠ A.valuation (P₂.evalAt An'.param))

    (hsep : ∃ f : ↥S, χ₀ f = 0 ∧ (f : F) ≠ 0 ∧ (f : F) ∈ Rx.integers ∧ (f : F)⁻¹ ∈ Rx.integers ∧
      ∀ P ∈ An'.dom, P.ord (f : F) = 0) :
    False := by
  classical
  obtain ⟨f, hχf, hf0, hfC, hfiC, hford⟩ := hsep
  obtain ⟨hdomeq, -, hmod0, hzz⟩ := hAn
  obtain ⟨hzC, -, hfarlaw⟩ := hfar
  obtain ⟨hz'R, -, hnearlaw⟩ := hnear

  have hresC : Rx.residue ⟨(f : F), hfC⟩ ≠ 0 := by
    intro h0
    have hmem : (⟨(f : F), hfC⟩ : Rx.integers) ∈ RingHom.ker Rx.residue := h0
    rw [Rx.ker_residue] at hmem
    refine (IsLocalRing.mem_maximalIdeal _).mp hmem ⟨⟨⟨(f : F), hfC⟩, ⟨(f : F)⁻¹, hfiC⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hf0)
    · exact Subtype.ext (inv_mul_cancel₀ hf0)
  set k' : ℤ := bx.ord (Rx.residue ⟨(f : F), hfC⟩) with hk'

  have hford_far : ∀ P ∈ An.dom, P.ord (f : F) = 0 := fun P hP => hford P (by rw [hdomeq]; exact hP)
  have far := hfarlaw (f : F) hfC hresC hford_far

  obtain ⟨c, hgR, hresg⟩ := R.exists_smul_mem (f : F) hf0
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hgR hresg
  have hg_def : c • (f : F) = algebraMap L F c * (f : F) := Algebra.smul_def c (f : F)
  set k₁ : ℤ := Q.ord (R.residue ⟨c • (f : F), hgR⟩) with hk₁

  have hgord : ∀ P ∈ An'.dom, P.ord (c • (f : F)) = 0 := by
    intro P hP
    rw [hg_def, Place.ord_mul _ (by simpa using hc0) hf0, ord_algebraMap, hford P hP, add_zero]
  have near := hnearlaw (c • (f : F)) hgR hresg hgord

  set v := A.valuation with hv
  have hμ0 : v (An.modulus : L) ≠ 0 := (Valuation.ne_zero_iff _).mpr hmod0
  have hμ1 : v (An.modulus : L) < 1 := (A.valuation_lt_one_iff An.modulus).mp An.modulus_mem
  have hvc0 : v c ≠ 0 := (Valuation.ne_zero_iff _).mpr hc0

  have key : ∀ P ∈ An'.dom,
      v c * v (An.modulus : L) ^ k' = v (P.evalAt An'.param) ^ (k₁ + k') := by
    intro P hP
    have hP' : P ∈ An.dom := by rw [← hdomeq]; exact hP
    obtain ⟨hPrat, hz'P, -, hz'P0, -⟩ := An'.mem_dom P hP
    obtain ⟨-, hzP, -, hzP0, -⟩ := An.mem_dom P hP'

    have hfP : (f : F) ∈ P.toValuationSubring :=
      P.mem_toValuationSubring_of_ord_nonneg_alt hf0 (hford P hP).ge
    have hgP : P.evalAt (c • (f : F)) = c * P.evalAt (f : F) := by
      rw [hg_def, P.evalAt_mul_of_mem hPrat (P.algebraMap_mem' c) hfP, P.evalAt_algebraMap_eq]
    have hzz' : P.evalAt An'.param * P.evalAt An.param = (An.modulus : L) := by
      rw [← P.evalAt_mul_of_mem hPrat hz'P hzP, hzz, P.evalAt_algebraMap_eq]

    obtain ⟨hfarA, hfarU⟩ := far P hP'
    obtain ⟨hnearA, hnearU⟩ := near P hP
    have e_far : v (P.evalAt (f : F) * P.evalAt An.param ^ (-k')) = 1 :=
      (A.valuation_eq_one_iff _).mp hfarU
    have e_near : v (P.evalAt (c • (f : F)) * P.evalAt An'.param ^ (-k₁)) = 1 :=
      (A.valuation_eq_one_iff _).mp hnearU
    rw [map_mul, map_zpow₀] at e_far e_near
    rw [hgP, map_mul] at e_near
    set a := v (P.evalAt An'.param) with ha
    set b := v (P.evalAt An.param) with hb
    have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mpr hz'P0
    have hb0 : b ≠ 0 := (Valuation.ne_zero_iff _).mpr hzP0
    have hab : a * b = v (An.modulus : L) := by rw [ha, hb, ← map_mul, hzz']

    have e1 : v (P.evalAt (f : F)) = b ^ k' := eq_zpow_of_mul_zpow_neg_eq_one hb0 e_far
    have e2 : v c * v (P.evalAt (f : F)) = a ^ k₁ := eq_zpow_of_mul_zpow_neg_eq_one ha0 e_near
    rw [zpow_add₀ ha0, ← e2, ← hab, mul_zpow, e1]
    simp only [mul_comm, mul_left_comm]

  obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := hdom
  have hsum : k₁ + k' = 0 := by
    by_contra hN
    apply hne
    have e1 := key P₁ hP₁
    have e2 := key P₂ hP₂
    rw [e1] at e2
    exact eq_of_zpow_eq_zpow hN e2

  have hvc : v c = v (An.modulus : L) ^ k₁ := by
    have e := key P₁ hP₁
    rw [hsum, zpow_zero] at e
    have hk' : k' = -k₁ := by omega
    rw [hk'] at e
    exact eq_zpow_of_mul_zpow_neg_eq_one hμ0 e

  have hgS : c • (f : F) ∈ S := by
    refine hloc' _ hgR (fun P hP => ?_)
    rw [hg_def]
    exact mul_mem (P.algebraMap_mem' c) ((hD P hP).2.1 f).1

  obtain ⟨hmQ, hresQ⟩ := hres ⟨c • (f : F), hgS⟩
  have hk₁0 : 0 ≤ k₁ := ord_nonneg_of_mem Q hmQ
  have hcA : c ∈ A := by
    rw [← A.valuation_le_one_iff, ← hv, hvc]
    exact zpow_le_one_of_le_one_of_nonneg hμ1.le hk₁0

  have hgS_eq : (⟨c • (f : F), hgS⟩ : ↥S) = ⟨algebraMap L F ((⟨c, hcA⟩ : ↥A) : L), hAS ⟨c, hcA⟩⟩ * f :=
    Subtype.ext hg_def
  have hχg : χ₀ ⟨c • (f : F), hgS⟩ = 0 := by
    rw [hgS_eq, map_mul, hχf, mul_zero]
  rw [hχg, map_zero] at hresQ
  have hmax : (⟨R.residue ⟨c • (f : F), hgR⟩, hmQ⟩ : ↥Q.toValuationSubring) ∈
      maximalIdeal ↥Q.toValuationSubring := (IsLocalRing.residue_eq_zero_iff _).mp hresQ
  have hk₁1 : 1 ≤ k₁ := one_le_ord_of_mem_maximalIdeal Q hmQ hresg hmax

  have hcmax : (⟨c, hcA⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [A.valuation_lt_one_iff]
    show v c < 1
    rw [hvc]
    exact zpow_lt_one_of_lt_one_of_pos hμ1 hk₁1
  apply hresg
  have hgR_eq : (⟨c • (f : F), hgR⟩ : ↥R.integers) =
      ⟨algebraMap L F ((⟨c, hcA⟩ : ↥A) : L), (R.algebraMap_mem_iff _).mpr hcA⟩ * ⟨(f : F), hSR f⟩ :=
    Subtype.ext hg_def
  rw [hgR_eq, map_mul, R.residue_algebraMap ⟨c, hcA⟩, (IsLocalRing.residue_eq_zero_iff _).mpr hcmax,
    map_zero, zero_mul]

end S_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_false_of_annulus_attached_regularProlongation_of_smoothPointPackage (solution)
