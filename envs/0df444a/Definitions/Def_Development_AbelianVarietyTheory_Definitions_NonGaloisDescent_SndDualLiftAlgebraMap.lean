-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_SndDualLiftAlgebraMap
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:53:10.738069+00:00
-- url     : https://prove2.me/theorems/b52389cf-3950-42d1-ba46-a1248bfc018c
-- title:
--   Snd Dual Lift Algebra Map
-- statement:
--   Definitions and structural lemmas for Snd Dual Lift Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/SndDualLiftAlgebraMap.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_NormPowLeNormFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow
import Theorems.Thm_GlobalTheory_BK_A_le_R
import Theorems.Thm_GlobalTheory_BK_R_mono
import Theorems.Thm_GlobalTheory_BK_S_le_R
import Theorems.Thm_GlobalTheory_BK_derivative_mem_A
import Theorems.Thm_GlobalTheory_BK_derivative_mem_away
import Theorems.Thm_GlobalTheory_BK_invL_le
import Theorems.Thm_GlobalTheory_BK_mem_R
import Theorems.Thm_GlobalTheory_BK_rad_pos
import Theorems.Thm_GlobalTheory_BK_rad_pow
import Theorems.Thm_GlobalTheory_DerivationPowerIdeal_derivation_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BK
open PowerSeries Filter Topology
section General
variable {A' B : Type} [CommRing A'] [CommRing B] (ι : A' →+* B) (s : A')
structure SameJets : Prop where
  div : ∀ (m : ℕ) (x : B), ∃ g h, x = ι g + ι s ^ m * h
  dvd : ∀ (m : ℕ) (g : A') (h : B), ι g = ι s ^ m * h → s ^ m ∣ g
def jetMap (m : ℕ) : A' ⧸ Ideal.span {s} ^ m →+* B ⧸ Ideal.span {ι s ^ m} :=
  Ideal.quotientMap _ ι (by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_pow]
    exact Ideal.mem_span_singleton_self _)
variable {ι s}
theorem SameJets.bijective (H : SameJets ι s) (m : ℕ) : Function.Bijective (jetMap ι s m) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨h, hh⟩ := hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact H.dvd m g h hh
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨g, h, rfl⟩ := H.div m x
    refine ⟨Ideal.Quotient.mk _ g, ?_⟩
    rw [jetMap, Ideal.quotientMap_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact ⟨-h, by ring⟩
def SameJets.jet (H : SameJets ι s) (m : ℕ) : B →+* A' ⧸ Ideal.span {s} ^ m :=
  (RingEquiv.ofBijective _ (H.bijective m)).symm.toRingHom.comp (Ideal.Quotient.mk _)
theorem SameJets.jet_eq_iff (H : SameJets ι s) (m : ℕ) (x : B) (g : A') :
    H.jet m x = Ideal.Quotient.mk _ g ↔ ι s ^ m ∣ x - ι g := by
  rw [SameJets.jet, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_eq, RingEquiv.coe_ofBijective, jetMap, Ideal.quotientMap_mk,
    Ideal.Quotient.eq, Ideal.mem_span_singleton]
theorem SameJets.jet_compat (H : SameJets ι s) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {s}) hle).comp (H.jet n) = H.jet m := by
  ext x
  obtain ⟨g, h, hx⟩ := H.div n x
  have h1 : ι s ^ n ∣ x - ι g := ⟨h, by rw [hx]; ring⟩
  rw [RingHom.comp_apply, (H.jet_eq_iff n x g).2 h1,
    (H.jet_eq_iff m x g).2 ((pow_dvd_pow _ hle).trans h1)]
  rfl
def SameJets.toCompl (H : SameJets ι s) : B →+* AdicCompletion (Ideal.span {s}) A' :=
  AdicCompletion.liftRingHom _ H.jet H.jet_compat
theorem SameJets.evalₐ_toCompl_eq_iff (H : SameJets ι s) (m : ℕ) (x : B) (g : A') :
    AdicCompletion.evalₐ _ m (H.toCompl x) = Ideal.Quotient.mk _ g ↔ ι s ^ m ∣ x - ι g := by
  rw [SameJets.toCompl, AdicCompletion.evalₐ_liftRingHom, H.jet_eq_iff]
theorem SameJets.toCompl_ι (H : SameJets ι s) (g : A') :
    H.toCompl (ι g) = algebraMap A' _ g := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  rw [(H.evalₐ_toCompl_eq_iff m _ g).2 (by simp), AlgHom.commutes]
  rfl
variable {k : Type} [CommRing k] [Algebra k A'] (I : Ideal A') (D : Derivation k A' A')
theorem derivation_mem_pow (n : ℕ) {x : A'} (hx : x ∈ I ^ (n + 1)) : D x ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow
  | exact _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow
  | (apply _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivationPowerIdeal.derivation_mem_pow ..)
theorem evalₐ_of_succ {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n x = Ideal.Quotient.mk _ r := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I A' x
  rw [AdicCompletion.evalₐ_mk] at h ⊢
  rw [← AdicCompletion.Ideal.mk_eq_mk I n.le_succ c]
  rw [Ideal.Quotient.eq] at h ⊢
  exact Ideal.pow_le_pow_right n.le_succ h
def cauchyDer (c : AdicCompletion.AdicCauchySequence I A') :
    AdicCompletion.AdicCauchySequence I A' :=
  ⟨fun n => D (c.val (n + 1)), fun {m n} hmn => by
    have h := AdicCompletion.Ideal.mk_eq_mk I (Nat.succ_le_succ hmn) c
    rw [Ideal.Quotient.eq] at h
    rw [SModEq.sub_mem, ← map_sub]
    have := derivation_mem_pow I D m ((Ideal.neg_mem_iff _).2 h)
    simpa using this⟩
def complDerFun (x : AdicCompletion I A') : AdicCompletion I A' :=
  AdicCompletion.mk I A' (cauchyDer I D (AdicCompletion.mk_surjective I A' x).choose)
theorem evalₐ_complDerFun {x : AdicCompletion I A'} {n : ℕ} {r : A'}
    (h : AdicCompletion.evalₐ I (n + 1) x = Ideal.Quotient.mk _ r) :
    AdicCompletion.evalₐ I n (complDerFun I D x) = Ideal.Quotient.mk _ (D r) := by
  rw [← (AdicCompletion.mk_surjective I A' x).choose_spec, AdicCompletion.evalₐ_mk,
    Ideal.Quotient.eq] at h
  rw [complDerFun, AdicCompletion.evalₐ_mk, Ideal.Quotient.eq]
  exact map_sub D _ _ ▸ derivation_mem_pow I D n h
theorem complDerFun_mul (x y : AdicCompletion I A') :
    complDerFun I D (x * y) = x * complDerFun I D y + y * complDerFun I D x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
  rw [evalₐ_complDerFun I D (r := r * t) (by rw [map_mul, map_mul, hr, ht]), map_add,
    map_mul (AdicCompletion.evalₐ I n), map_mul (AdicCompletion.evalₐ I n),
    evalₐ_complDerFun I D hr.symm, evalₐ_complDerFun I D ht.symm,
    evalₐ_of_succ I hr.symm, evalₐ_of_succ I ht.symm, D.leibniz]
  simp
theorem complDerFun_algebraMap (r : A') :
    complDerFun I D (algebraMap A' _ r) = algebraMap A' _ (D r) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [evalₐ_complDerFun I D (r := r) (AlgHom.commutes _ r), AlgHom.commutes]
  rfl
def complDer : Derivation k (AdicCompletion I A') (AdicCompletion I A') :=
  Derivation.mk'
    { toFun := complDerFun I D
      map_add' := fun x y => by
        refine AdicCompletion.ext_evalₐ fun n => ?_
        obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) x)
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) y)
        rw [evalₐ_complDerFun I D (r := r + t) (by rw [map_add, map_add, hr, ht]), map_add,
          map_add, map_add, evalₐ_complDerFun I D hr.symm, evalₐ_complDerFun I D ht.symm]
      map_smul' := fun c x => by
        have h : algebraMap k (AdicCompletion I A') c = algebraMap A' _ (algebraMap k A' c) := rfl
        rw [Algebra.smul_def, complDerFun_mul, RingHom.id_apply, Algebra.smul_def, h,
          complDerFun_algebraMap, D.map_algebraMap, map_zero, mul_zero, add_zero] }
    (complDerFun_mul I D)
def dualHom (s : A') : A' →+* TrivSqZeroExt (Localization.Away s) (Localization.Away s) where
  toFun r := TrivSqZeroExt.inl (algebraMap A' _ r) + TrivSqZeroExt.inr (algebraMap A' _ (D r))
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext
    · simp
    · simp [D.leibniz, mul_comm, -DualNumber.inr_eq_smul_eps]
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp [-DualNumber.inr_eq_smul_eps]
theorem isUnit_dualHom (s : A') : IsUnit (dualHom D s s) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [dualHom] using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away s) s)
def dualLift (s : A') :
    Localization.Away s →+* TrivSqZeroExt (Localization.Away s) (Localization.Away s) :=
  IsLocalization.Away.lift s (isUnit_dualHom D s)
theorem fst_dualLift (s : A') (x : Localization.Away s) : (dualLift D s x).fst = x := by
  have : (TrivSqZeroExt.fstHom (Localization.Away s) _ _).toRingHom.comp (dualLift D s) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun r => ?_)
    simp [dualLift, dualHom]
  exact congr($this x)
theorem snd_dualLift_mul (s : A') (x y : Localization.Away s) :
    (dualLift D s (x * y)).snd = x * (dualLift D s y).snd + y * (dualLift D s x).snd := by
  rw [map_mul, TrivSqZeroExt.snd_mul, fst_dualLift, fst_dualLift]
  simp [mul_comm]
theorem snd_dualLift_algebraMap (s r : A') :
    (dualLift D s (algebraMap A' _ r)).snd = algebraMap A' _ (D r) := by
  simp [dualLift, dualHom, -DualNumber.inr_eq_smul_eps]
def awayDer (s : A') : Derivation k (Localization.Away s) (Localization.Away s) :=
  Derivation.mk'
    { toFun := fun x => (dualLift D s x).snd
      map_add' := fun x y => by rw [map_add, TrivSqZeroExt.snd_add]
      map_smul' := fun c x => by
        rw [Algebra.smul_def, snd_dualLift_mul, RingHom.id_apply, Algebra.smul_def,
          IsScalarTower.algebraMap_apply k A' (Localization.Away s), snd_dualLift_algebraMap,
          D.map_algebraMap, map_zero, mul_zero, add_zero] }
    (snd_dualLift_mul D s)
end General
section Division
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]
theorem mem_invL_A_iff {f : K⟦X⟧} : f ∈ invL l (A O K) ↔ ∃ b : ℝ, ∀ n, ‖coeff n f‖ ≤ b := by
  have h2 : (((l : A O K) : K⟦X⟧)) = C (l : K) := by simp
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨(‖(l : K)‖ ^ m)⁻¹, fun n => ?_⟩
    have := hm n
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow] at this
    rw [← one_div, le_div_iff₀ (pow_pos hl m), mul_comm]
    exact this
  · rintro ⟨b, hb⟩
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
      (norm_l_lt_one (K := K) l)).mul_const b
    rw [zero_mul] at h
    obtain ⟨m, hm⟩ := (h.eventually (gt_mem_nhds zero_lt_one)).exists
    refine ⟨m, fun n => ?_⟩
    rw [h2, ← map_pow, coeff_C_mul, norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_left (hb n) (pow_pos hl m).le).trans hm.le
variable (O K) in

abbrev Rpi : Subalgebra O K⟦X⟧ := R O K l (1 / e)
theorem A_le_Rpi : A O K ≤ Rpi O K l e :=
  A_le_R l (by have := NeZero.pos e; positivity)
theorem invL_A_le_Rpi : invL l (A O K) ≤ Rpi O K l e := invL_le l (A_le_Rpi l e)
theorem invL_S_le_Rpi : invL l (S O K e) ≤ Rpi O K l e := invL_le l (S_le_R l e)
omit [IsUltrametricDist K] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] in
theorem coeff_E_mul (g : K⟦X⟧) (n : ℕ) :
    coeff (n + e) (E K l e * g) = coeff n g + l * coeff (n + e) g := by
  rw [E, add_mul, map_add, coeff_X_pow_mul, ← map_natCast (C : K →+* K⟦X⟧), coeff_C_mul]
theorem tendsto_add_mul (n : ℕ) : Tendsto (fun j : ℕ => n + j * e) atTop atTop :=
  tendsto_atTop_mono (fun j => (Nat.le_mul_of_pos_right j (NeZero.pos e)).trans
    (Nat.le_add_left _ _)) tendsto_id
theorem norm_term_eq (f : K⟦X⟧) (n j : ℕ) : ‖coeff (n + j * e) f * (-(l : K)) ^ j‖ * rad l (1 / e) ^ n =
    ‖coeff (n + j * e) f‖ * rad l (1 / e) ^ (n + j * e) := by
  rw [norm_mul, norm_pow, norm_neg, ← rad_pow l e, ← pow_mul, pow_add, mul_comm e j]
  ring
theorem eq_zero_of_E_mul {g : K⟦X⟧} (hg : g ∈ Rpi O K l e)
    (h : ∀ n, coeff (n + e) (E K l e * g) = 0) : g = 0 := by
  ext n
  have key : ∀ j, coeff n g = coeff (n + j * e) g * (-(l : K)) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      have := h (n + j * e)
      rw [coeff_E_mul] at this
      rw [ih, show n + (j + 1) * e = n + j * e + e by ring]
      linear_combination (-(l : K)) ^ j * this
  have h1 := (mem_R.1 hg).comp (tendsto_add_mul e n)
  have h2 : ‖coeff n g‖ * rad l (1 / e) ^ n = 0 := by
    refine tendsto_nhds_unique tendsto_const_nhds (h1.congr fun j => ?_)
    simp only [Function.comp]
    rw [← norm_term_eq (K := K) l e, ← key]
  simpa [(rad_pos l _).ne'] using h2
def tail (f : K⟦X⟧) (n : ℕ) : K := ∑' j : ℕ, coeff (n + j * e) f * (-(l : K)) ^ j
def quotE (f : K⟦X⟧) : K⟦X⟧ := PowerSeries.mk fun n => tail l e f (n + e)
variable [CompleteSpace K]
theorem tail_rec {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) (n : ℕ) :
    tail l e f n = coeff n f - l * tail l e f (n + e) := by
  have hs : Summable fun j : ℕ => coeff (n + j * e) f * (-(l : K)) ^ j := by
    refine NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_
    rw [Nat.cofinite_eq_atTop, tendsto_zero_iff_norm_tendsto_zero]
    have h1 := ((mem_R.1 hf).comp (tendsto_add_mul e n)).mul_const (rad l (1 / e) ^ n)⁻¹
    rw [zero_mul] at h1
    refine h1.congr fun j => ?_
    simp only [Function.comp]
    rw [← norm_term_eq (K := K) l e, mul_inv_cancel_right₀ (pow_pos (rad_pos l _) n).ne']
  rw [tail, hs.tsum_eq_zero_add, tail, ← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
  congr 1
  · simp
  · refine tsum_congr fun j => ?_
    rw [show n + (j + 1) * e = n + e + j * e by ring]
    ring
theorem coeff_sub_E_mul_quotE {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) (n : ℕ) :
    coeff (n + e) (f - E K l e * quotE l e f) = 0 := by
  rw [map_sub, coeff_E_mul, quotE, coeff_mk, coeff_mk, tail_rec l e hf (n + e)]
  ring
omit [CompleteSpace K] in
theorem quotE_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : quotE l e f ∈ Rpi O K l e := by
  have hρ := rad_pos l (1 / e)
  have h1 : Tendsto (fun n => ‖tail l e f n‖ * rad l (1 / e) ^ n) atTop (𝓝 0) := by
    have := mem_R.1 hf
    rw [Metric.tendsto_atTop] at this ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := this (ε / 2) (half_pos hε)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    refine lt_of_le_of_lt ?_ (half_lt_self hε)
    rw [← le_div_iff₀ (pow_pos hρ n)]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
    rw [le_div_iff₀ (pow_pos hρ n), norm_term_eq]
    have := hN (n + j * e) (by omega)
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  have h2 := (h1.comp (tendsto_add_atTop_nat e)).mul_const (rad l (1 / e) ^ e)⁻¹
  rw [zero_mul] at h2
  refine mem_R.2 (h2.congr fun n => ?_)
  simp only [Function.comp, quotE, coeff_mk]
  rw [pow_add]
  field_simp
omit [CompleteSpace K] [NeZero e] in
theorem quotE_mem_invL_A {f : K⟦X⟧} (hf : f ∈ invL l (A O K)) : quotE l e f ∈ invL l (A O K) := by
  obtain ⟨b, hb⟩ := (mem_invL_A_iff l).1 hf
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  refine (mem_invL_A_iff l).2 ⟨b, fun n => ?_⟩
  rw [quotE, coeff_mk]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hb0 fun j => ?_
  rw [norm_mul, norm_pow, norm_neg]
  exact (mul_le_of_le_one_right (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_l_lt_one l).le)).trans (hb _)
theorem sub_E_mul_quotE_mem {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    f - E K l e * quotE l e f ∈ invL l (A O K) := by
  have : Tendsto (fun n => ‖coeff n (f - E K l e * quotE l e f)‖) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop e] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [coeff_sub_E_mul_quotE l e hf, norm_zero]
  obtain ⟨b, hb⟩ := this.bddAbove_range
  exact (mem_invL_A_iff l).2 ⟨b, fun n => hb ⟨n, rfl⟩⟩
theorem mem_invL_A_of_E_mul {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e * h ∈ invL l (A O K)) : h ∈ invL l (A O K) := by
  have hR := invL_A_le_Rpi l e hE
  have : h - quotE l e (E K l e * h) = 0 :=
    eq_zero_of_E_mul l e (Subalgebra.sub_mem _ hh (quotE_mem_Rpi l e hR)) fun n => by
      rw [mul_sub]; exact coeff_sub_E_mul_quotE l e hR n
  rw [sub_eq_zero.1 this]
  exact quotE_mem_invL_A l e hE
theorem mem_invL_A_of_E_pow_mul (m : ℕ) {h : K⟦X⟧} (hh : h ∈ Rpi O K l e)
    (hE : E K l e ^ m * h ∈ invL l (A O K)) : h ∈ invL l (A O K) := by
  induction m with
  | zero => simpa using hE
  | succ m ih =>
    refine ih (mem_invL_A_of_E_mul l e
      (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (E_mem l e _) m) hh) ?_)
    rwa [← mul_assoc, ← pow_succ']
theorem exists_div_E_pow (m : ℕ) {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) :
    ∃ g ∈ invL l (A O K), ∃ h ∈ Rpi O K l e, f = g + E K l e ^ m * h := by
  induction m with
  | zero => exact ⟨0, zero_mem _, f, hf, by simp⟩
  | succ m ih =>
    obtain ⟨g, hg, h, hh, rfl⟩ := ih
    exact ⟨g + E K l e ^ m * (h - E K l e * quotE l e h),
      add_mem hg (mul_mem (pow_mem (E_mem l e _) m) (sub_E_mul_quotE_mem l e hh)),
      quotE l e h, quotE_mem_Rpi l e hh, by ring⟩
variable (O K) in

theorem sameJets : SameJets
    (Subalgebra.inclusion (invL_A_le_Rpi (O := O) (K := K) l e)).toRingHom
    (EIn l e (invL l (A O K))) where
  div m x := by
    obtain ⟨g, hg, h, hh, hx⟩ := exists_div_E_pow l e m x.2
    exact ⟨⟨g, hg⟩, ⟨h, hh⟩, Subtype.ext hx⟩
  dvd m g h hx := by
    have hx' : (g : K⟦X⟧) = E K l e ^ m * h := congrArg Subtype.val hx
    exact ⟨⟨h, mem_invL_A_of_E_pow_mul l e m h.2 (hx' ▸ g.2)⟩, Subtype.ext hx'⟩
end Division
section Hat
variable (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l e : ℕ)
abbrev idE : Ideal (invL l (A O K)) := Ideal.span {EIn l e (invL l (A O K))}
abbrev Ahat : Type := AdicCompletion (idE O K l e) (invL l (A O K))
abbrev ofAl : invL l (A O K) →+* Ahat O K l e := algebraMap _ _
def ofA : A O K →+* Ahat O K l e := (ofAl O K l e).comp (algebraMap (A O K) (invL l (A O K)))
def Ehat : Ahat O K l e := ofAl O K l e (EIn l e _)
def uhat : Ahat O K l e := ofAl O K l e (uIn _)
abbrev AhatE : Type := Localization.Away (Ehat O K l e)
variable [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
def derAl : Derivation K (invL l (A O K)) (invL l (A O K)) :=
  Derivation.mk'
    { toFun := fun f => ⟨PowerSeries.derivative K f,
        derivative_mem_away _ (fun _ => derivative_mem_A) f.2⟩
      map_add' := fun f g => Subtype.ext (map_add (PowerSeries.derivative K) _ _)
      map_smul' := fun c f => Subtype.ext (by
        change PowerSeries.derivative K (C c * (f : K⟦X⟧)) = C c * PowerSeries.derivative K f
        simp) }
    fun f g => Subtype.ext ((PowerSeries.derivative K).leibniz f g)
@[simp] theorem coe_derAl (f : invL l (A O K)) :
    (derAl O K l f : K⟦X⟧) = PowerSeries.derivative K f := rfl
def dHat : Derivation K (Ahat O K l e) (Ahat O K l e) := complDer _ (derAl O K l)
def dHatE : Derivation K (AhatE O K l e) (AhatE O K l e) := awayDer (dHat O K l e) _
def NHat : Derivation K (Ahat O K l e) (Ahat O K l e) := uhat O K l e • dHat O K l e
def NHatE : Derivation K (AhatE O K l e) (AhatE O K l e) :=
  algebraMap (Ahat O K l e) (AhatE O K l e) (uhat O K l e) • dHatE O K l e
variable [NeZero e] [CompleteSpace K]
def toHat : Rpi O K l e →+* Ahat O K l e := (sameJets O K l e).toCompl
variable {O K} in
theorem toHat_eq_ofAl {f : Rpi O K l e} {g : invL l (A O K)} (h : (f : K⟦X⟧) = g) :
    toHat O K l e f = ofAl O K l e g := by
  rw [← (sameJets O K l e).toCompl_ι g]
  exact congrArg _ (Subtype.ext h)
variable {O K} in

def toHatOf {B : Subalgebra O K⟦X⟧} (h : B ≤ Rpi O K l e) : B →+* Ahat O K l e :=
  (toHat O K l e).comp (Subalgebra.inclusion h).toRingHom
def toHatS : invL l (S O K e) →+* Ahat O K l e := toHatOf l e (invL_S_le_Rpi l e)
variable {e} in

def toHatR {k : ℝ} (hk : k ≤ 1 / e) : R O K l k →+* Ahat O K l e := toHatOf l e (R_mono l hk)
abbrev RpiE : Subalgebra O K⟦X⟧ := invE l e (Rpi O K l e)
theorem toHat_E : toHat O K l e (EIn l e _) = Ehat O K l e := toHat_eq_ofAl l e rfl
def toHatE : RpiE O K l e →+* AhatE O K l e :=
  IsLocalization.Away.lift (EIn l e (Rpi O K l e))
    (g := (algebraMap (Ahat O K l e) (AhatE O K l e)).comp (toHat O K l e))
    (by rw [RingHom.comp_apply, toHat_E]; exact IsLocalization.Away.algebraMap_isUnit _)
end Hat
end GlobalTheory.BK


