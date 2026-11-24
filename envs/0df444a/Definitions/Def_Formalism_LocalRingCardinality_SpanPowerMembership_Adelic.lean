-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_Adelic
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:13.490181+00:00
-- url     : https://prove2.me/theorems/23f1c91f-8aa3-485e-9fe2-eea8e5b950a9
-- title:
--   Adelic
-- statement:
--   Definitions and structural lemmas for Adelic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/Adelic.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_conjE_apply
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HC_HostAx_conjE_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_unimodUnramUnique_quad
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
open IsDedekindDomain HeightOneSpectrum IsLocalRing WithZero NumberField Filter Topology
noncomputable section
namespace Formalism.BasicNotions.Examples₂
section Local
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
theorem wz_lt_one_iff (γ : ℤᵐ⁰) : γ < 1 ↔ γ ≤ exp (-1 : ℤ) := by
  rcases eq_or_ne γ 0 with rfl | hγ
  · first
    | exact iff_of_true zero_lt_one zero_le'
    | simp
  · first
    | (rw [← WithZero.exp_log hγ, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]; omega)
    | (obtain ⟨a, rfl⟩ := WithZero.ne_zero_iff_exists.mp hγ
       rw [← WithZero.coe_one, WithZero.exp, WithZero.coe_lt_coe, WithZero.coe_le_coe,
         ← ofAdd_toAdd a, ← ofAdd_zero, Multiplicative.ofAdd_lt, Multiplicative.ofAdd_le]
       omega)
theorem adicInt_integers :
    Valuation.Integers (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (v.adicCompletionIntegers K) := by
  first
  | exact Valuation.integer.integers _
  | exact ⟨Subtype.val_injective, fun x => x.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  | (refine ⟨Subtype.val_injective, fun x => ?_, fun r hr => ⟨⟨r, ?_⟩, rfl⟩⟩
     · exact (mem_adicCompletionIntegers R K v).mp x.2
     · exact (mem_adicCompletionIntegers R K v).mpr hr)
theorem adicInt_exists_unif :
    ∃ π : v.adicCompletionIntegers K, Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ : ∃ π : K, v.valuation K π = exp (-1 : ℤ) := by
    first
    | exact valuation_exists_uniformizer K v
    | exact v.valuation_exists_uniformizer K
    | exact valuation_exists_uniformizer (K := K) v
  have hv : Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
    rw [← hπ]
    first
    | exact valuedAdicCompletion_eq_valuation' (v := v) π
    | exact valuedAdicCompletion_eq_valuation' v π
    | exact valuedAdicCompletion_eq_valuation' K v π
    | exact valuedAdicCompletion_eq_valuation (v := v) π
    | exact Valued.valuedCompletion_apply π
    | simp
  have hle : Valued.v (π : v.adicCompletion K) ≤ 1 := by
    rw [hv]; exact ((wz_lt_one_iff _).mpr le_rfl).le
  refine ⟨⟨(π : v.adicCompletion K), ?_⟩, hv⟩
  first
  | exact hle
  | exact (mem_adicCompletionIntegers R K v).mpr hle
  | simpa [mem_adicCompletionIntegers] using hle
theorem adicInt_mem_max_iff (x : v.adicCompletionIntegers K) :
    x ∈ maximalIdeal (v.adicCompletionIntegers K) ↔ Valued.v (x : v.adicCompletion K) < 1 := by
  have hI := adicInt_integers (K := K) v
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hI.isUnit_iff_valuation_eq_one]
  exact (hI.map_le_one x).lt_iff_ne.symm
end Local
section Local2
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
local notation "Ov" => v.adicCompletionIntegers K
local notation "Kv" => v.adicCompletion K
theorem adicInt_dvd_iff (x y : Ov) :
    x ∣ y ↔ Valued.v (y : Kv) ≤ Valued.v (x : Kv) := by
  first
  | exact (adicInt_integers (K := K) v).dvd_iff_le
  | exact Valuation.Integers.dvd_iff_le (adicInt_integers (K := K) v)
theorem adicInt_max_eq_span (π : Ov) (hπ : Valued.v (π : Kv) = exp (-1 : ℤ)) :
    maximalIdeal Ov = Ideal.span {π} := by
  ext x
  rw [adicInt_mem_max_iff v x, Ideal.mem_span_singleton, adicInt_dvd_iff v π x, hπ, wz_lt_one_iff]
theorem adicInt_mem_pow_iff (n : ℕ) (x : Ov) :
    x ∈ (maximalIdeal Ov) ^ n ↔ Valued.v (x : Kv) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := adicInt_exists_unif (K := K) v
  have h1 : ((π ^ n : Ov) : Kv) = (π : Kv) ^ n := by
    first
    | rfl
    | push_cast; rfl
    | simp
  have hpow : Valued.v ((π ^ n : Ov) : Kv) = exp (-(n : ℤ)) := by
    rw [h1, map_pow, hπ]
    first
    | (rw [← WithZero.exp_nsmul]; congr 1; simp)
    | (rw [← WithZero.exp_nsmul]; simp)
    | simp [WithZero.exp, ← ofAdd_nsmul]
  rw [adicInt_max_eq_span v π hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    adicInt_dvd_iff v, hpow]
theorem wz_exists_nat_lt (γ : ℤᵐ⁰) (h : γ ≠ 0) : ∃ N : ℕ, exp (-(N : ℤ)) < γ := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, exp m = γ := ⟨_, WithZero.exp_log h⟩
  exact ⟨m.natAbs + 1, by rw [WithZero.exp_lt_exp]; omega⟩
theorem adicInt_eq_zero_of_forall (x : Kv) (h : ∀ n : ℕ, Valued.v x ≤ exp (-(n : ℤ))) : x = 0 := by
  by_contra hx
  have h0 : Valued.v x ≠ 0 := by
    first
    | exact (Valuation.ne_zero_iff _).mpr hx
    | exact (map_ne_zero _).mpr hx
    | simpa using hx
  obtain ⟨N, hN⟩ := wz_exists_nat_lt (Valued.v x) h0
  exact absurd (h N) (not_le.mpr hN)
theorem adicCompl_isClosed_le (r : ℤᵐ⁰) : IsClosed {x : Kv | Valued.v x ≤ r} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' : r < Valued.v x := not_le.mp hx
  have hx0 : Valued.v x ≠ 0 := (lt_of_le_of_lt zero_le' hx').ne'
  have hmem : {y : Kv | Valued.v y = Valued.v x} ∈ 𝓝 x := by
    first
    | exact Valuation.loc_const hx0
    | exact Valued.locally_const hx0
    | exact (Valued.isOpen_sphere Kv hx0).mem_nhds rfl
    | exact (Valued.isClopen_sphere Kv hx0).isOpen.mem_nhds rfl
    | exact (Valued.isOpen_sphere (R := Kv) hx0).mem_nhds rfl
  filter_upwards [hmem] with y hy
  show ¬ Valued.v y ≤ r
  rw [show Valued.v y = Valued.v x from hy]
  exact not_le.mpr hx'
theorem adicInt_isAdicComplete : IsAdicComplete (maximalIdeal Ov) Ov := by
  have key : ∀ (n : ℕ) (x y : Ov), x ≡ y [SMOD (maximalIdeal Ov ^ n • ⊤ : Submodule Ov Ov)] ↔
      Valued.v ((x : Kv) - y) ≤ exp (-(n : ℤ)) := by
    intro n x y
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, adicInt_mem_pow_iff]
    rfl
  have h1 : IsHausdorff (maximalIdeal Ov) Ov := by
    refine ⟨fun x hx => ?_⟩
    have h0 : (x : Kv) = 0 := adicInt_eq_zero_of_forall v _ (fun n => by
      simpa using (key n x 0).1 (hx n))
    exact Subtype.ext h0
  have h2 : IsPrecomplete (maximalIdeal Ov) Ov := by
    refine ⟨fun f hf => ?_⟩
    set g : ℕ → Kv := fun n => (f n : Kv)
    have hg : ∀ m n, m ≤ n → Valued.v (g n - g m) ≤ exp (-(m : ℤ)) := by
      intro m n hmn
      have := (key m (f m) (f n)).1 (hf hmn)
      rwa [← Valuation.map_neg, neg_sub] at this
    have hc : CauchySeq g := by
      rw [(Valued.hasBasis_uniformity Kv ℤᵐ⁰).cauchySeq_iff]
      intro γ _
      have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := fun h =>
        γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
      obtain ⟨N, hN⟩ := wz_exists_nat_lt _ hne
      refine ⟨N, fun m hm n hn => ?_⟩
      simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding]
      have hle : ∀ a b, N ≤ a → a ≤ b →
          Valued.v (g b - g a) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := fun a b ha hab =>
        lt_of_le_of_lt ((hg a b hab).trans (exp_le_exp.2 (by omega))) hN
      rcases le_total m n with h | h
      · exact hle m n hm h
      · rw [← Valuation.map_neg, neg_sub]; exact hle n m hn h
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hLmem : L ∈ Ov := by
      refine (Valued.isClosed_valuationSubring Kv).mem_of_tendsto hL (Eventually.of_forall ?_)
      intro n; exact (f n).2
    refine ⟨⟨L, hLmem⟩, fun n => ?_⟩
    rw [key]
    have hcl : IsClosed {y : Kv | Valued.v (g n - y) ≤ exp (-(n : ℤ))} :=
      (adicCompl_isClosed_le v _).preimage (continuous_const.sub continuous_id)
    refine hcl.mem_of_tendsto hL ?_
    filter_upwards [eventually_ge_atTop n] with k hk
    show Valued.v (g n - g k) ≤ _
    rw [← Valuation.map_neg, neg_sub]; exact hg n k hk
  exact { toIsHausdorff := h1, toIsPrecomplete := h2 }
instance adicInt_henselian : HenselianLocalRing Ov := by
  have := adicInt_isAdicComplete (K := K) v
  have : HenselianRing Ov (maximalIdeal Ov) := inferInstance
  refine ⟨fun f hf a₀ h₁ h₂ => ?_⟩
  refine HenselianRing.is_henselian f hf a₀ h₁ ?_
  exact h₂.map _
end Local2
section Residue
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)
local notation "Ov" => v.adicCompletionIntegers K
local notation "Kv" => v.adicCompletion K
theorem adicCompl_val_algebraMap (y : K) : Valued.v (algebraMap K Kv y) = v.valuation K y := by
  first
  | exact valuedAdicCompletion_eq_valuation' (v := v) y
  | exact valuedAdicCompletion_eq_valuation' v y
  | exact valuedAdicCompletion_eq_valuation' K v y
  | exact valuedAdicCompletion_eq_valuation (v := v) y
  | exact Valued.valuedCompletion_apply y
  | simp
theorem adicInt_residue_surj : Function.Surjective ((residue Ov).comp (algebraMap R Ov)) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  have hn : {z : Kv | Valued.v (z - x) < 1} ∈ 𝓝 (x : Kv) := by
    rw [Valued.mem_nhds]
    refine ⟨1, fun z hz => ?_⟩
    simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_one,
      map_one] at hz ⊢
    exact hz
  obtain ⟨_, hz, ⟨k, rfl⟩⟩ := mem_closure_iff_nhds.1
    (denseRange_algebraMap (R := R) (K := K) (v := v) (x : Kv)) _ hn
  have hz' : Valued.v (algebraMap K Kv k - x) < 1 := hz
  have hk : v.valuation K k ≤ 1 := by
    rw [← adicCompl_val_algebraMap]
    have e : algebraMap K Kv k = (algebraMap K Kv k - x) + x := by ring
    rw [e]
    exact Valuation.map_add_le _ hz'.le x.2
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer (K := K) v hk 1
  refine ⟨a, ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  apply (Ideal.Quotient.eq).2
  rw [adicInt_mem_max_iff]
  have e1 : ((algebraMap R Ov a : Ov) : Kv) = algebraMap K Kv (algebraMap R K a) := rfl
  have e2 : ((algebraMap R Ov a - x : Ov) : Kv) =
      algebraMap K Kv (algebraMap R K a - k) + (algebraMap K Kv k - x) := by
    rw [map_sub, AddSubgroupClass.coe_sub, e1]
    ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ hz'
  rw [adicCompl_val_algebraMap]
  simpa using ha
theorem adicInt_residue_finite [Finite (R ⧸ v.asIdeal)] : Finite (ResidueField Ov) := by
  have hf : ∀ a ∈ v.asIdeal, ((residue Ov).comp (algebraMap R Ov)) a = 0 := by
    intro a ha
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, adicInt_mem_max_iff]
    have h1 : ((algebraMap R Ov a : Ov) : Kv) = algebraMap K Kv (algebraMap R K a) := by
      first
      | rfl
      | simp
    rw [h1, adicCompl_val_algebraMap, valuation_of_algebraMap]
    first
    | exact (v.intValuation_lt_one_iff_dvd a).mpr (Ideal.dvd_span_singleton.mpr ha)
    | exact (intValuation_lt_one_iff_mem v a).mpr ha
  exact Finite.of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective v.asIdeal hf (adicInt_residue_surj v))
theorem adicInt_isUnit_of_not_mem (r : R) (hr : r ∉ v.asIdeal) : IsUnit (algebraMap R Ov r) := by
  rw [(adicInt_integers (K := K) v).isUnit_iff_valuation_eq_one]
  have h1 : algebraMap Ov Kv (algebraMap R Ov r) = algebraMap K Kv (algebraMap R K r) := by
    first
    | rfl
    | simp
  rw [h1, adicCompl_val_algebraMap, valuation_of_algebraMap]
  first
  | exact (intValuation_eq_one_iff v r).mpr hr
  | exact v.intValuation_eq_one_iff.mpr hr
  | (refine le_antisymm (v.intValuation_le_one r) (not_lt.mp fun h => hr ?_)
     exact Ideal.dvd_span_singleton.mp ((v.intValuation_lt_one_iff_dvd r).mp h))
theorem adicInt_exists_norm [Finite (R ⧸ v.asIdeal)] (T N : ℤ)
    (hD : ((T ^ 2 - 4 * N : ℤ) : R) ∉ v.asIdeal) :
    ∃ s t : Ov, s ^ 2 + (T : Ov) * s * t + (N : Ov) * t ^ 2 = -1 := by
  have := adicInt_residue_finite (K := K) v
  have hDu : IsUnit ((T : Ov) ^ 2 - 4 * (N : Ov)) := by
    have e : ((T : Ov) ^ 2 - 4 * (N : Ov)) = algebraMap R Ov ((T ^ 2 - 4 * N : ℤ) : R) := by
      rw [map_intCast]; push_cast; ring
    rw [e]; exact adicInt_isUnit_of_not_mem v _ hD
  exact Formalism.HermitianLatticesTheory.unimodUnramUnique_quad (T : Ov) (N : Ov) (-1) hDu isUnit_one.neg
end Residue
section Global
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
theorem adel_conj_aE : H.conj (H.sqq) = - H.sqq := by
  rw [H.gal_sqq]
  have hc : (((H.gal H.conj).1.1 : ℤˣ) : ℤ) = -1 := by
    first
    | (simp only [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]; rfl)
    | (simp only [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]; decide)
    | (rw [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]; rfl)
    | simp [Formalism.HC.HostRaw.conj, Formalism.HC.Frame.cc]
  rw [hc]; simp
theorem adel_conj_bE : H.conj (H.sqd) = - H.sqd := by
  rw [H.gal_sqd]
  have hc : (((H.gal H.conj).1.2 : ℤˣ) : ℤ) = -1 := by
    first
    | (simp only [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]; rfl)
    | (simp only [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]; decide)
    | (rw [Formalism.HC.HostRaw.conj, MulEquiv.apply_symm_apply]; rfl)
    | simp [Formalism.HC.HostRaw.conj, Formalism.HC.Frame.cc]
  rw [hc]; simp
theorem adel_mem_F (x : H.E) (hx : H.conj x = x) : x ∈ H.F := by
  have key : ∀ φ : H.E →+* ℂ, starRingEnd ℂ (φ x) = φ x := fun φ => by
    have h1 := Formalism.HC.HostAx.conjE_apply (H := H.toHostAx) φ x
    rw [hx] at h1
    exact h1.symm
  first
  | exact (NumberField.mem_maximalRealSubfield_iff x).mpr key
  | exact (mem_maximalRealSubfield_iff x).mpr key
  | exact fun φ => key φ
  | (intro φ; exact key φ)
  | (show ∀ φ : H.E →+* ℂ, star (φ x) = φ x
     exact key)
end Global
section Main
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
def adelBeta : H.F :=
  ⟨H.sqq / H.sqd, adel_mem_F H _ (by
    rw [map_div₀, adel_conj_aE, adel_conj_bE, neg_div_neg_eq])⟩
def adelAlpha : H.F := (1 - adelBeta H) / 2
def adelTheta : H.E := (1 + H.sqd) / 2
def adelNd : ℤ := ((H.d : ℤ) + 1) / 4
def adelNq : ℤ := ((H.q : ℤ) + 1) / 4
theorem adelNd_spec : 4 * adelNd H = (H.d : ℤ) + 1 := by
  obtain ⟨-, -, -, hd, -⟩ := H.hyp
  unfold adelNd
  have h : (4 : ℤ) ∣ (H.d : ℤ) + 1 := by omega
  exact Int.mul_ediv_cancel' h
theorem adelNq_spec : 4 * adelNq H = (H.q : ℤ) + 1 := by
  obtain ⟨-, -, hq, -, -⟩ := H.hyp
  unfold adelNq
  have h : (4 : ℤ) ∣ (H.q : ℤ) + 1 := by omega
  exact Int.mul_ediv_cancel' h
theorem adelic_alpha_beta_linear : 2 * adelAlpha H + adelBeta H = 1 := by
  unfold adelAlpha
  ring
theorem adelic_alpha_beta_norm : adelAlpha H ^ 2 + adelAlpha H * adelBeta H + ((adelNd H : ℤ) : H.F) * adelBeta H ^ 2 =
    ((adelNq H : ℤ) : H.F) := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  have hd0 : (H.d : H.E) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne_zero
  have key : adelBeta H ^ 2 * (H.d : H.F) = (H.q : H.F) := by
    apply Subtype.ext
    have hb : ((adelBeta H : H.F) : H.E) = H.sqq / H.sqd := rfl
    push_cast [hb]
    rw [div_pow, H.sqq_sq, H.sqd_sq, neg_div_neg_eq, div_mul_cancel₀ _ hd0]
  have h4d := congrArg (Int.cast : ℤ → H.F) (adelNd_spec H)
  have h4q := congrArg (Int.cast : ℤ → H.F) (adelNq_spec H)
  push_cast at h4d h4q
  unfold adelAlpha
  linear_combination (1/4 : H.F) * key + (adelBeta H ^ 2 / 4) * h4d - (1/4 : H.F) * h4q
end Main
section Final
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
theorem adel_not_both (v : HeightOneSpectrum (𝓞 H.F)) :
    ¬ (((H.d : ℤ) : 𝓞 H.F) ∈ v.asIdeal ∧ ((H.q : ℤ) : 𝓞 H.F) ∈ v.asIdeal) := by
  rintro ⟨hdv, hqv⟩
  obtain ⟨hq, hd, hq8, hd16, -⟩ := H.hyp
  have hne : H.d ≠ H.q := by omega
  have hcop : IsCoprime (H.d : ℤ) (H.q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hd hq).mpr hne)
  obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 H.F))
  simp only [eq_intCast] at hab
  have h1 : (1 : 𝓞 H.F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hdv) (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
theorem adel_local (v : HeightOneSpectrum (𝓞 H.F)) :
    ∃ S T : v.adicCompletion H.F,
      (((H.d : ℤ) : 𝓞 H.F) ∉ v.asIdeal →
        S ∈ v.adicCompletionIntegers H.F ∧ T ∈ v.adicCompletionIntegers H.F) ∧
      S * S + S * T + ((adelNd H : ℤ) : v.adicCompletion H.F) * (T * T) = -1 := by
  haveI : Finite (𝓞 H.F ⧸ v.asIdeal) := by
    first
    | exact Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    | infer_instance
    | exact (Ideal.fintypeQuotientOfFreeOfNeBot v.asIdeal v.ne_bot).finite
  have hI3 : 2 * algebraMap H.F (v.adicCompletion H.F) (adelAlpha H)
      + algebraMap H.F (v.adicCompletion H.F) (adelBeta H) = 1 := by
    have h := congrArg (algebraMap H.F (v.adicCompletion H.F)) (adelic_alpha_beta_linear H)
    first
    | (rw [map_add, map_mul, map_ofNat, map_one] at h; exact h)
    | simpa using h
  have hI4 : algebraMap H.F (v.adicCompletion H.F) (adelAlpha H) ^ 2
      + algebraMap H.F (v.adicCompletion H.F) (adelAlpha H)
        * algebraMap H.F (v.adicCompletion H.F) (adelBeta H)
      + ((adelNd H : ℤ) : v.adicCompletion H.F) * algebraMap H.F (v.adicCompletion H.F) (adelBeta H) ^ 2
      = ((adelNq H : ℤ) : v.adicCompletion H.F) := by
    have h := congrArg (algebraMap H.F (v.adicCompletion H.F)) (adelic_alpha_beta_norm H)
    first
    | (rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_intCast, map_intCast] at h; exact h)
    | simpa using h
  by_cases hdv : ((H.d : ℤ) : 𝓞 H.F) ∈ v.asIdeal
  · have hqv : ((H.q : ℤ) : 𝓞 H.F) ∉ v.asIdeal := fun h => adel_not_both H v ⟨hdv, h⟩
    have hc : (1 : ℤ) ^ 2 - 4 * adelNq H = -(H.q : ℤ) := by
      have := adelNq_spec H
      linarith
    obtain ⟨s, t, hst⟩ := adicInt_exists_norm (K := H.F) v 1 (adelNq H) (by rw [hc]; simpa using hqv)
    have hst' : (s : v.adicCompletion H.F) ^ 2 + (s : v.adicCompletion H.F) * (t : v.adicCompletion H.F)
        + ((adelNq H : ℤ) : v.adicCompletion H.F) * (t : v.adicCompletion H.F) ^ 2 = -1 := by
      have h := congrArg (fun z : v.adicCompletionIntegers H.F => (z : v.adicCompletion H.F)) hst
      first
      | (push_cast at h; linear_combination h)
      | (simp at h; linear_combination h)
    refine ⟨(s : v.adicCompletion H.F)
        + algebraMap H.F (v.adicCompletion H.F) (adelAlpha H) * (t : v.adicCompletion H.F),
      algebraMap H.F (v.adicCompletion H.F) (adelBeta H) * (t : v.adicCompletion H.F),
      fun h => absurd hdv h, ?_⟩
    linear_combination hst' + ((s : v.adicCompletion H.F) * (t : v.adicCompletion H.F)) * hI3
      + (t : v.adicCompletion H.F) ^ 2 * hI4
  · have hc : (1 : ℤ) ^ 2 - 4 * adelNd H = -(H.d : ℤ) := by
      have := adelNd_spec H
      linarith
    obtain ⟨s, t, hst⟩ := adicInt_exists_norm (K := H.F) v 1 (adelNd H) (by rw [hc]; simpa using hdv)
    have hst' : (s : v.adicCompletion H.F) ^ 2 + (s : v.adicCompletion H.F) * (t : v.adicCompletion H.F)
        + ((adelNd H : ℤ) : v.adicCompletion H.F) * (t : v.adicCompletion H.F) ^ 2 = -1 := by
      have h := congrArg (fun z : v.adicCompletionIntegers H.F => (z : v.adicCompletion H.F)) hst
      first
      | (push_cast at h; linear_combination h)
      | (simp at h; linear_combination h)
    refine ⟨(s : v.adicCompletion H.F), (t : v.adicCompletion H.F), fun _ => ⟨s.2, t.2⟩, ?_⟩
    linear_combination hst'
end Final
section Adele
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped TensorProduct
variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)
theorem adel_finite_d :
    {v : HeightOneSpectrum (𝓞 H.F) | ((H.d : ℤ) : 𝓞 H.F) ∈ v.asIdeal}.Finite := by
  obtain ⟨-, hd, -, -, -⟩ := H.hyp
  have h0 : ((H.d : ℤ) : 𝓞 H.F) ≠ 0 := Int.cast_ne_zero.mpr (by exact_mod_cast hd.ne_zero)
  refine (Ideal.finite_factors (I := Ideal.span {((H.d : ℤ) : 𝓞 H.F)}) ?_).subset ?_
  · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  · intro v hv
    rw [Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
def adelSv (v : HeightOneSpectrum (𝓞 H.F)) : v.adicCompletion H.F := (adel_local H v).choose
def adelTv (v : HeightOneSpectrum (𝓞 H.F)) : v.adicCompletion H.F :=
  (adel_local H v).choose_spec.choose
theorem adelSTv_spec (v : HeightOneSpectrum (𝓞 H.F)) :
    (((H.d : ℤ) : 𝓞 H.F) ∉ v.asIdeal →
        adelSv H v ∈ v.adicCompletionIntegers H.F ∧ adelTv H v ∈ v.adicCompletionIntegers H.F) ∧
      adelSv H v * adelSv H v + adelSv H v * adelTv H v +
        ((adelNd H : ℤ) : v.adicCompletion H.F) * (adelTv H v * adelTv H v) = -1 := (adel_local H v).choose_spec.choose_spec
def adelS : FiniteAdeleRing (𝓞 H.F) H.F :=
  ⟨fun v => adelSv H v, Filter.eventually_cofinite.2 ((adel_finite_d H).subset (fun v hv => by
    by_contra h
    exact hv ((adelSTv_spec H v).1 h).1))⟩
def adelT : FiniteAdeleRing (𝓞 H.F) H.F :=
  ⟨fun v => adelTv H v, Filter.eventually_cofinite.2 ((adel_finite_d H).subset (fun v hv => by
    by_contra h
    exact hv ((adelSTv_spec H v).1 h).2))⟩
end Adele
end Formalism.BasicNotions.Examples₂


