-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:49.189805+00:00
-- url     : https://prove2.me/theorems/4b102d0a-081d-4458-a019-e5eb778e6a7e
-- title:
--   PDiv Cycle Hom Loc Laurent
-- statement:
--   Definitions and structural lemmas for PDiv Cycle Hom Loc Laurent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDivCycleHomLocLaurent.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
namespace HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
section Fractions
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
abbrev fr : MRing ι R →+* FractionRing (MRing ι R ⧸ P) :=
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).comp (Ideal.Quotient.mk P)
variable {P W}
theorem fr_ne_zero {f : MRing ι R} (hf : f ∉ P) : fr P f ≠ 0 := by
  intro h
  apply hf
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact IsFractionRing.injective _ (FractionRing (MRing ι R ⧸ P)) (by simpa using h)
theorem fr_eq_zero_iff {f : MRing ι R} : fr P f = 0 ↔ f ∈ P := by
  refine ⟨fun h => by_contra fun hf => fr_ne_zero hf h, fun h => ?_⟩
  simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]
theorem frac_mem {b : K → ℕ} {f g : MRing ι R} (hf : IsMultiHomog f b) (hg : IsMultiHomog g b)
    (hgW : g ∉ W) : fr P f / fr P g ∈ homLocRing P W :=
  Subring.subset_closure ⟨b, f, g, hf, hg, hgW, rfl⟩
theorem isMultiHomog_mul {f g : MRing ι R} {b c : K → ℕ} (hf : IsMultiHomog f b)
    (hg : IsMultiHomog g c) : IsMultiHomog (f * g) (b + c) :=
  IsWeightedHomogeneous.mul hf hg
end Fractions
section Laurent
variable [Fintype K] (P W : Ideal (MRing ι R)) [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
def tpow (n : K → ℕ) : MRing ι R := ∏ k, X ⟨k, T k⟩ ^ n k
theorem isMultiHomog_tpow (n : K → ℕ) : IsMultiHomog (tpow T n : MRing ι R) n := by
  have := IsWeightedHomogeneous.prod (w := blockWeight ι) Finset.univ
    (fun k => (X ⟨k, T k⟩ : MRing ι R) ^ n k) (fun k => n k • Pi.single k 1)
    (fun k _ => (isWeightedHomogeneous_X R (blockWeight ι) ⟨k, T k⟩).pow (n k))
  have h : (∑ k, n k • Pi.single k 1 : K → ℕ) = n := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [h] at this
  exact this
theorem tpow_single (k : K) : (tpow T (Pi.single k 1) : MRing ι R) = X ⟨k, T k⟩ := by
  rw [tpow, Finset.prod_eq_single k]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp
variable {W} in
theorem tpow_not_mem (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W) (n : K → ℕ) :
    (tpow T n : MRing ι R) ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hT k (Ideal.IsPrime.mem_of_pow_mem ‹_› _ hk)
abbrev nz : (K → ℕ) →+ (K → ℤ) := (Nat.castAddMonoidHom ℤ).compLeft K
variable {P W} (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hPW hT in
theorem frX_ne_zero (k : K) : fr P (X ⟨k, T k⟩ : MRing ι R) ≠ 0 :=
  fr_ne_zero fun h => hT k (hPW h)
def chi : Multiplicative (K → ℤ) →* FractionRing (MRing ι R ⧸ P) where
  toFun d := ∏ k, fr P (X ⟨k, T k⟩ : MRing ι R) ^ (Multiplicative.toAdd d k)
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => zpow_add₀ (frX_ne_zero T hPW hT k) _ _
theorem chi_apply (d : K → ℤ) :
    chi T hPW hT (Multiplicative.ofAdd d) = ∏ k, fr P (X ⟨k, T k⟩ : MRing ι R) ^ d k := rfl
theorem chi_nz (n : K → ℕ) :
    chi T hPW hT (Multiplicative.ofAdd (nz n)) = fr P (tpow T n : MRing ι R) := by
  rw [chi_apply, tpow, map_prod]
  simp [map_pow]
abbrev Lau (P W : Ideal (MRing ι R)) [P.IsPrime] := AddMonoidAlgebra (homLocRing P W) (K → ℤ)
def ev : Lau P W →+* FractionRing (MRing ι R ⧸ P) :=
  AddMonoidAlgebra.liftNCRingHom (homLocRing P W).subtype (chi T hPW hT) (fun _ _ => Commute.all _ _)
theorem ev_single (d : K → ℤ) (a : homLocRing P W) :
    ev T hPW hT (AddMonoidAlgebra.single d a) = a * chi T hPW hT (Multiplicative.ofAdd d) := by
  simp [ev, AddMonoidAlgebra.liftNCRingHom_single]
theorem one_not_mem_alt (W : Ideal (MRing ι R)) [W.IsPrime] : (1 : MRing ι R) ∉ W :=
  (Ideal.ne_top_iff_one W).mp Ideal.IsPrime.ne_top'
def constHom (P W : Ideal (MRing ι R)) [P.IsPrime] [W.IsPrime] : R →+* homLocRing P W :=
  RingHom.codRestrict ((fr P).comp (C : R →+* MRing ι R)) (homLocRing P W) fun r => by
    simpa using frac_mem (P := P) (W := W) (isWeightedHomogeneous_C (blockWeight ι) r)
      (isWeightedHomogeneous_one R (blockWeight ι)) (one_not_mem_alt W)
def uu (v : Σ k, ι k) : homLocRing P W :=
  ⟨fr P (X v) / fr P (X ⟨v.1, T v.1⟩),
    frac_mem (isWeightedHomogeneous_X R (blockWeight ι) v)
      (isWeightedHomogeneous_X R (blockWeight ι) ⟨v.1, T v.1⟩) (hT v.1)⟩
def psi : MRing ι R →+* Lau P W :=
  eval₂Hom (AddMonoidAlgebra.singleZeroRingHom.comp (constHom P W))
    (fun v => AddMonoidAlgebra.single (nz (blockWeight ι v)) (uu T hT v))
theorem ev_comp_psi : (ev T hPW hT).comp (psi T hT) = fr P := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [psi, ev_single, constHom]
  · intro v
    simp only [psi, RingHom.comp_apply, coe_eval₂Hom, eval₂_X, ev_single]
    rw [chi_nz, show blockWeight ι v = Pi.single v.1 1 from rfl, tpow_single]
    exact div_mul_cancel₀ _ (frX_ne_zero T hPW hT v.1)
theorem psi_monomial (s : (Σ k, ι k) →₀ ℕ) (c : R) :
    psi T hT (monomial s c) = AddMonoidAlgebra.single (nz (Finsupp.weight (blockWeight ι) s))
      (constHom P W c * s.prod fun v n => uu T hT v ^ n) := by
  simp only [psi, coe_eval₂Hom, eval₂_monomial, RingHom.comp_apply,
    AddMonoidAlgebra.singleZeroRingHom_apply, Finsupp.prod, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.prod_single, AddMonoidAlgebra.single_mul_single, zero_add, Finsupp.weight_apply,
    Finsupp.sum, map_sum, map_nsmul]
  change AddMonoidAlgebra.single 0 _ * _ = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]
end Laurent
section Localization
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime] (T : ∀ k, ι k)
  (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
theorem psi_homog_exists {f : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b) :
    ∃ a, psi (P := P) T hT f = AddMonoidAlgebra.single (nz b) a := by
  refine ⟨∑ s ∈ f.support, constHom P W (coeff s f) * s.prod fun v n => uu T hT v ^ n, ?_⟩
  conv_lhs => rw [f.as_sum]
  rw [map_sum, ← AddMonoidAlgebra.singleAddHom_apply, map_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [psi_monomial, AddMonoidAlgebra.singleAddHom_apply]
  congr 2
  exact hf (mem_support_iff.mp hs)
include hPW in
theorem psi_homog {f : MRing ι R} {b : K → ℕ} (hf : IsMultiHomog f b) :
    psi (P := P) T hT f = AddMonoidAlgebra.single (nz b)
      (⟨fr P f / fr P (tpow T b), frac_mem hf (isMultiHomog_tpow T b) (tpow_not_mem T hT b)⟩ :
        homLocRing P W) := by
  obtain ⟨a, ha⟩ := psi_homog_exists (P := P) T hT hf
  rw [ha]
  congr 1
  apply Subtype.ext
  have h := congrArg (ev T hPW hT) ha
  rw [← RingHom.comp_apply, ev_comp_psi, ev_single, chi_nz] at h
  change (a : FractionRing (MRing ι R ⧸ P)) = fr P f / fr P (tpow T b)
  rw [h, mul_div_cancel_right₀ _ (fr_ne_zero fun h' => tpow_not_mem T hT b (hPW h'))]
include hPW in
theorem psi_eq_zero (hPh : IsMultiHomogIdeal P) {f : MRing ι R} (hf : f ∈ P) :
    psi (P := P) T hT f = 0 := by
  conv_lhs => rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) f]
  refine finsum_induction (fun q => psi (P := P) T hT q = 0) (map_zero _)
    (fun x y hx hy => by rw [map_add, hx, hy, add_zero]) fun b => ?_
  rw [psi_homog T hPW hT (weightedHomogeneousComponent_isWeightedHomogeneous b f)]
  have h0 : fr P (weightedHomogeneousComponent (blockWeight ι) b f) = 0 :=
    fr_eq_zero_iff.mpr (hPh f hf b)
  have : (⟨fr P (weightedHomogeneousComponent (blockWeight ι) b f) / fr P (tpow T b), frac_mem
      (weightedHomogeneousComponent_isWeightedHomogeneous b f) (isMultiHomog_tpow T b)
      (tpow_not_mem T hT b)⟩ : homLocRing P W) = 0 := Subtype.ext (by simp [h0])
  rw [this, AddMonoidAlgebra.single_zero]
def psiQ (hPh : IsMultiHomogIdeal P) : (MRing ι R ⧸ P) →+* Lau P W :=
  Ideal.Quotient.lift P (psi T hT) fun _ hf => psi_eq_zero T hPW hT hPh hf
def homSub (P W : Ideal (MRing ι R)) [W.IsPrime] : Submonoid (MRing ι R ⧸ P) where
  carrier := {r | ∃ (b : K → ℕ) (f : MRing ι R), IsMultiHomog f b ∧ f ∉ W ∧ Ideal.Quotient.mk P f = r}
  mul_mem' := by
    rintro _ _ ⟨b, f, hf, hfW, rfl⟩ ⟨b', f', hf', hfW', rfl⟩
    exact ⟨b + b', f * f', isMultiHomog_mul hf hf',
      fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hfW hfW', map_mul _ _ _⟩
  one_mem' := ⟨0, 1, isWeightedHomogeneous_one _ _, one_not_mem_alt W, map_one _⟩
end Localization
section Local
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
theorem wbar_isPrime (hPW : P ≤ W) : (W.map (Ideal.Quotient.mk P)).IsPrime :=
  Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hPW)
def locC (hPW : P ≤ W) : Subring (FractionRing (MRing ι R ⧸ P)) :=
  haveI := wbar_isPrime hPW
  (Localization.subalgebra.ofField (FractionRing (MRing ι R ⧸ P))
    (W.map (Ideal.Quotient.mk P)).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)).toSubring
def algQC (hPW : P ≤ W) : (MRing ι R ⧸ P) →+* locC hPW :=
  haveI := wbar_isPrime hPW
  (algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P))).codRestrict (locC hPW)
    fun r => ⟨r, 1, Submonoid.one_mem _, by simp⟩
theorem locC_isLocalization (hPW : P ≤ W) :
    letI := (algQC hPW).toAlgebra
    haveI := wbar_isPrime hPW
    IsLocalization.AtPrime (locC hPW) (W.map (Ideal.Quotient.mk P)) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  have hnz : ∀ s ∈ (W.map (Ideal.Quotient.mk P)).primeCompl,
      algebraMap (MRing ι R ⧸ P) (FractionRing (MRing ι R ⧸ P)) s ≠ 0 := by
    intro s hs h
    apply hs
    rw [IsFractionRing.injective _ (FractionRing (MRing ι R ⧸ P)) (h.trans (map_zero _).symm)]
    exact zero_mem _
  show IsLocalization _ _
  rw [isLocalization_iff]
  refine ⟨fun ⟨s, hs⟩ => ?_, fun ⟨z, hz⟩ => ?_, fun {x y} h => ?_⟩
  · refine IsUnit.of_mul_eq_one (⟨(algebraMap _ (FractionRing (MRing ι R ⧸ P)) s)⁻¹,
      ⟨1, s, hs, by simp⟩⟩ : locC hPW) (Subtype.ext ?_)
    exact mul_inv_cancel₀ (hnz s hs)
  · obtain ⟨a, s, hs, rfl⟩ := hz
    refine ⟨(a, ⟨s, hs⟩), Subtype.ext ?_⟩
    change _ * algebraMap _ (FractionRing (MRing ι R ⧸ P)) s = algebraMap _ _ a
    rw [mul_assoc, inv_mul_cancel₀ (hnz s hs), mul_one]
  · refine ⟨1, ?_⟩
    have := congrArg Subtype.val h
    rw [IsFractionRing.injective _ (FractionRing (MRing ι R ⧸ P)) this]
theorem mem_locC (hPW : P ≤ W) {y : FractionRing (MRing ι R ⧸ P)} (a s : MRing ι R) (hs : s ∉ W)
    (hy : y = fr P a * (fr P s)⁻¹) : y ∈ locC hPW := by
  haveI := wbar_isPrime hPW
  exact ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P s,
    fun h => hs ((Ideal.mem_quotient_iff_mem hPW).mp h), hy⟩
theorem homLocRing_le_locC (hPW : P ≤ W) : homLocRing P W ≤ locC hPW := by
  unfold homLocRing
  rw [Subring.closure_le]
  rintro _ ⟨b, f, g, -, -, hgW, rfl⟩
  exact mem_locC hPW f g hgW (div_eq_mul_inv _ _)
theorem zpow_mem_locC (hPW : P ≤ W) {x : FractionRing (MRing ι R ⧸ P)} (hx : x ∈ locC hPW)
    (hx' : x⁻¹ ∈ locC hPW) (n : ℤ) : x ^ n ∈ locC hPW := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx m
  | negSucc m => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hx' _
def incAC (hPW : P ≤ W) : homLocRing P W →+* locC hPW :=
  (homLocRing P W).subtype.codRestrict (locC hPW) fun a => homLocRing_le_locC hPW a.2
variable (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
theorem ev_mem_locC (p : Lau P W) : ev T hPW hT p ∈ locC hPW := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => rw [map_zero]; exact zero_mem _
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | single d a =>
    rw [ev_single, chi_apply]
    refine mul_mem (homLocRing_le_locC hPW a.2) (prod_mem fun k _ => zpow_mem_locC hPW ?_ ?_ _)
    · exact mem_locC hPW (X ⟨k, T k⟩) 1 (one_not_mem_alt W) (by simp)
    · exact mem_locC hPW 1 (X ⟨k, T k⟩) (hT k) (by simp)
def evC : Lau P W →+* locC hPW := (ev T hPW hT).codRestrict (locC hPW) (ev_mem_locC T hPW hT)
end Local
section Length
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
  (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
end Length
end HomLocLaurent
end
end GroundTheory.Heights₂.Heights.NumbersDVR


