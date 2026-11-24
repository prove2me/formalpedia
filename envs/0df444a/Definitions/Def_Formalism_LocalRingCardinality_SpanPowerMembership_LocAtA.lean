-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T19:31:50.63663+00:00
-- url     : https://prove2.me/theorems/e0ad099c-a49d-43b0-adf1-61bd10f51951
-- title:
--   Loc At A
-- statement:
--   Definitions and structural lemmas for Loc At A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/LocAtA.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LocF
open NumberField IsDedekindDomain HeightOneSpectrum WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
@[reducible] def vrel : ValuativeRel (v.adicCompletion F) :=
  .ofValuation (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)
section Ql
variable (l : ℕ) [hl : Fact l.Prime] (hv : (l : 𝓞 F) ∈ v.asIdeal)
theorem not_dvd_den (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have hu := PadicInt.isUnit_den q h
  rw [PadicInt.isUnit_iff] at hu
  have : ‖((q.den : ℤ) : ℤ_[l])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (Int.natCast_dvd_natCast.mpr hd)
  rw [Int.cast_natCast] at this
  exact absurd hu this.ne
theorem norm_nat (n : ℕ) : ‖(n : v.adicCompletion F)‖ =
    ‖FinitePlace.embedding v (algebraMap (𝓞 F) F (n : 𝓞 F))‖ := by
  rw [map_natCast, map_natCast]
theorem norm_int_le (n : ℤ) : ‖(n : v.adicCompletion F)‖ ≤ 1 := by
  have := FinitePlace.norm_le_one (K := F) v (n : 𝓞 F)
  rwa [map_intCast, map_intCast] at this
include hv in
theorem norm_l_lt : ‖(l : v.adicCompletion F)‖ < 1 := by
  rw [norm_nat]; exact (FinitePlace.norm_lt_one_iff_mem F v _).mpr hv
include hv in
theorem norm_nat_eq_one (n : ℕ) (h : ¬ l ∣ n) : ‖(n : v.adicCompletion F)‖ = 1 := by
  rw [norm_nat]
  refine (FinitePlace.norm_eq_one_iff_notMem F v _).mpr (fun hn => v.isPrime.ne_top ?_)
  have hc : IsCoprime (l : 𝓞 F) (n : 𝓞 F) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hl.out).mpr h)
  obtain ⟨a, b, hab⟩ := hc
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hn)
instance : CharZero (v.adicCompletion F) := algebraRat.charZero _
include hv in
theorem norm_rat_le (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ‖(q : v.adicCompletion F)‖ ≤ 1 := by
  rw [Rat.cast_def, norm_div, norm_nat_eq_one v l hv _ (not_dvd_den l q h), div_one]
  exact norm_int_le v _
def QL (_l : ℕ) : Type := ℚ
instance : Field (QL l) := inferInstanceAs (Field ℚ)
def iQ : QL l →+* ℚ_[l] := Rat.castHom ℚ_[l]
instance : PseudoMetricSpace (QL l) := PseudoMetricSpace.induced (iQ l) inferInstance
def fQ : QL l →+* v.adicCompletion F := Rat.castHom _
theorem iQ_ind : IsUniformInducing (iQ l) := ⟨rfl⟩
theorem iQ_dense : DenseRange (iQ l) := Padic.denseRange_ratCast l
include hv in
theorem fQ_uc : UniformContinuous (fQ v l) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (norm_l_lt v l hv)
  have hl0 : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hlp : (0 : ℝ) < ‖(l : ℚ_[l])‖ ^ n :=
    pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n
  refine ⟨‖(l : ℚ_[l])‖ ^ n, hlp, fun {a b} hab => ?_⟩
  let q : ℚ := (show ℚ from a) - (show ℚ from b)
  have h1 : ‖(q : ℚ_[l])‖ < ‖(l : ℚ_[l])‖ ^ n := by
    have : dist a b = ‖iQ l a - iQ l b‖ := dist_eq_norm (iQ l a) (iQ l b)
    rw [this, ← map_sub] at hab
    exact hab
  have h2 : ‖((q / (l : ℚ) ^ n : ℚ) : ℚ_[l])‖ ≤ 1 := by
    push_cast
    rw [norm_div, norm_pow, div_le_one hlp]
    exact h1.le
  have h3 := norm_rat_le v l hv _ h2
  have hlv : (0 : ℝ) < ‖(l : v.adicCompletion F)‖ ^ n :=
    pow_pos (norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.out.ne_zero)) n
  push_cast at h3
  rw [norm_div, norm_pow, div_le_one hlv] at h3
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt h3 hn
def emb : ℚ_[l] →+* v.adicCompletion F :=
  IsDenseInducing.extendRingHom (iQ_ind l) (iQ_dense l) (fQ_uc v l hv)
theorem exists_frac (x : ℚ_[l]) : ∃ a : ℚ, (∃ n : ℕ, a.den = l ^ n) ∧ ‖x - (a : ℚ_[l])‖ ≤ 1 := by
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < (‖x‖ + 1)⁻¹ by positivity) hl1
  have hz : ‖(l : ℚ_[l]) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    have h1 : ‖(l : ℚ_[l])‖ ^ n * (‖x‖ + 1) ≤ 1 := by
      rw [← le_div_iff₀ (by positivity), one_div]; exact hn.le
    nlinarith [pow_nonneg (norm_nonneg (l : ℚ_[l])) n]
  let z : ℤ_[l] := ⟨_, hz⟩
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec n z)
  refine ⟨(z.appr n : ℚ) / (l : ℚ) ^ n, ?_, ?_⟩
  · have : ((z.appr n : ℚ) / (l : ℚ) ^ n).den ∣ l ^ n := by
      have h := Rat.den_dvd (z.appr n : ℤ) ((l ^ n : ℕ) : ℤ)
      rw [Rat.divInt_eq_div] at h
      push_cast at h
      exact_mod_cast h
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).mp this
    exact ⟨k, hk⟩
  · have h := congrArg (fun t : ℤ_[l] => (t : ℚ_[l])) he
    have hzc : (z : ℚ_[l]) = (l : ℚ_[l]) ^ n * x := rfl
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast, hzc] at h
    push_cast
    have : x - (z.appr n : ℚ_[l]) / (l : ℚ_[l]) ^ n = (e : ℚ_[l]) := by
      field_simp
      linear_combination h
    rw [this]
    exact e.2
theorem int_of_frac (b : ℚ) (n : ℕ) (hd : b.den ∣ l ^ n) (h : ‖(b : ℚ_[l])‖ ≤ 1) : ∃ z : ℤ, b = z := by
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).mp hd
  have hnd := not_dvd_den l b h
  have : k = 0 := by
    by_contra hk0
    exact hnd (hk ▸ dvd_pow_self l hk0)
  rw [this, pow_zero] at hk
  exact ⟨b.num, (Rat.coe_int_num_of_den_eq_one hk).symm⟩
def frac (x : ℚ_[l]) : ℚ := (exists_frac l x).choose
theorem exp_eq_of_int (a b : ℚ) (z : ℤ) (h : a - b = z) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * (b : ℂ)) := by
  have : (a : ℂ) = b + z := by
    have h' : a = b + z := by linarith
    rw [h']; push_cast; ring
  rw [this, mul_add, Complex.exp_add, mul_comm _ (z : ℂ), Complex.exp_int_mul_two_pi_mul_I, mul_one]
def psi0 : AddChar ℚ_[l] ℂ where
  toFun x := Complex.exp (2 * Real.pi * Complex.I * (frac l x : ℂ))
  map_zero_eq_one' := by
    obtain ⟨⟨n, hn⟩, h⟩ := (exists_frac l 0).choose_spec
    obtain ⟨z, hz⟩ := int_of_frac l (frac l 0) n (hn ▸ dvd_rfl) (by simpa [frac] using h)
    rw [exp_eq_of_int (frac l 0) 0 z (by simpa using hz)]
    simp
  map_add_eq_mul' x y := by
    obtain ⟨⟨n, hn⟩, h⟩ := (exists_frac l x).choose_spec
    obtain ⟨⟨m, hm⟩, h'⟩ := (exists_frac l y).choose_spec
    obtain ⟨⟨k, hk⟩, h''⟩ := (exists_frac l (x + y)).choose_spec
    have hd : (frac l (x + y) - (frac l x + frac l y)).den ∣ l ^ (k + (n + m)) := by
      refine (Rat.sub_den_dvd _ _).trans ?_
      rw [pow_add, pow_add]
      refine mul_dvd_mul (hk ▸ dvd_rfl) ((Rat.add_den_dvd _ _).trans ?_)
      exact mul_dvd_mul (hn ▸ dvd_rfl) (hm ▸ dvd_rfl)
    have hn1 : ‖((frac l (x + y) - (frac l x + frac l y) : ℚ) : ℚ_[l])‖ ≤ 1 := by
      have e : ((frac l (x + y) - (frac l x + frac l y) : ℚ) : ℚ_[l]) =
          ((x - frac l x) + (y - frac l y)) + -((x + y) - frac l (x + y)) := by push_cast; ring
      rw [e]
      refine (Padic.nonarchimedean _ _).trans (max_le ((Padic.nonarchimedean _ _).trans (max_le h h')) ?_)
      rw [norm_neg]; exact h''
    obtain ⟨z, hz⟩ := int_of_frac l _ _ hd hn1
    rw [exp_eq_of_int _ _ z hz, ← Complex.exp_add]
    congr 1
    push_cast; ring
end Ql
end Formalism.BasicNotions.Examples₂.LocF


