-- Prove2me | Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
-- name    : GroundTheory_LocalFields_PrincipalUnitsModule
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:26:35.058052+00:00
-- url     : https://prove2.me/theorems/71391626-b64e-49bf-b11d-94ea559c2b67
-- title:
--   Principal Units Module
-- statement:
--   Definitions and structural lemmas for Principal Units Module, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsModule.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicExp
import Theorems.Thm_GroundTheory_LocalField_hasBasis_nhds_one_unitFiltrationUnits
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_normalizedValuation_eq_exp_ord
import Theorems.Thm_GroundTheory_LocalField_pow_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_summable_of_tendsto_zero
import Theorems.Thm_GroundTheory_LocalField_tendsto_zero_iff_valBall
import Theorems.Thm_GroundTheory_LocalField_tsum_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_unitFiltrationUnits_antitone
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


set_option autoImplicit false
namespace GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
section Filtration
variable (K) in

noncomputable def principalFiltration (k : ℕ) : AddSubgroup (Additive (unitFiltrationUnits K 1)) :=
  Subgroup.toAddSubgroup ((unitFiltrationUnits K (k + 1)).comap (unitFiltrationUnits K 1).subtype)
theorem mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)} :
    u ∈ principalFiltration K k ↔
      ((((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ) : K) - 1) ∈ valBall K (k + 1) := by
  have := mem_unitFiltrationUnits_iff_valBall (K := K) (n := k + 1) (by omega)
    (x := ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ))
  push_cast at this
  exact this
theorem principalFiltration_zero : principalFiltration K 0 = ⊤ := by
  ext u
  simp only [AddSubgroup.mem_top, iff_true, mem_principalFiltration]
  simpa using sub_one_mem_valBall_one (Additive.toMul u)
theorem normalizedValuation_eq_one_of_sub_one_mem {y : K} (hy : y - 1 ∈ valBall K 1) :
    normalizedValuation K y = 1 := by
  have h : normalizedValuation K (y - 1) < 1 := by
    refine lt_of_le_of_lt hy ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have := Valuation.map_one_add_of_lt (normalizedValuation K) h
  simpa using this
theorem mem_valBall_zero_of_sub_one_mem {y : K} (hy : y - 1 ∈ valBall K 1) : y ∈ valBall K 0 := by
  rw [mem_valBall, normalizedValuation_eq_one_of_sub_one_mem hy]; simp
theorem eq_zero_of_forall_mem_principalFiltration {w : Additive (unitFiltrationUnits K 1)}
    (h : ∀ k, w ∈ principalFiltration K k) : w = 0 := by
  set y : K := (((Additive.toMul w : unitFiltrationUnits K 1) : Kˣ) : K) - 1
  have hy : y = 0 := by
    by_contra hy0
    have hk := mem_principalFiltration.mp (h (ord y).toNat)
    rw [mem_valBall, normalizedValuation_eq_exp_ord hy0, WithZero.exp_le_exp] at hk
    have := Int.self_le_toNat (ord y)
    omega
  apply Additive.toMul.injective
  ext
  simpa [y, sub_eq_zero] using hy
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]
omit hp in
theorem natCast_prime_mem_valBall_one : (p : K) ∈ valBall K 1 := by
  have h : ((p : 𝒪[K]) : 𝒪[K]) ∈ 𝓂[K] ^ 1 := by
    rw [pow_one, ← residue_eq_zero_iff, map_natCast, CharP.cast_eq_zero]
  have := mem_maximalIdeal_pow_iff_valBall.mp h
  simpa using this
theorem pow_prime_sub_one_mem {k : ℤ} (hk : 1 ≤ k) {y : K} (hy : y - 1 ∈ valBall K k) :
    y ^ p - 1 ∈ valBall K (k + 1) := by
  set x := y - 1
  have hyx : y = x + 1 := by ring
  rw [hyx, add_pow, Finset.sum_range_succ']
  simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rcases Nat.lt_or_ge (i + 1) p with hlt | hge
  · obtain ⟨c, hc⟩ := hp.out.dvd_choose_self (Nat.succ_ne_zero i) hlt
    rw [hc, Nat.cast_mul]
    have h1 : (p : K) * (c : K) ∈ valBall K (1 + 0) :=
      mul_mem_valBall (natCast_prime_mem_valBall_one p)
        (by simpa using intCast_mem_valBall_zero (K := K) (c : ℤ))
    have h2 := mul_mem_valBall (pow_mem_valBall hy (i + 1)) h1
    refine valBall_antitone ?_ h2
    push_cast; nlinarith
  · have hi' : i + 1 = p := by omega
    rw [hi', Nat.choose_self, Nat.cast_one, mul_one]
    refine valBall_antitone ?_ (pow_mem_valBall hy p)
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    nlinarith
theorem nsmul_prime_mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) : p • u ∈ principalFiltration K (k + 1) := by
  rw [mem_principalFiltration] at hu ⊢
  have := pow_prime_sub_one_mem p (by omega) hu
  simpa using this
theorem nsmul_prime_pow_mem_principalFiltration {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) (j : ℕ) : p ^ j • u ∈ principalFiltration K (k + j) := by
  induction j with
  | zero => simpa using hu
  | succ j ih =>
    rw [show p ^ (j + 1) • u = p • (p ^ j • u) by rw [smul_smul, ← pow_succ'], ← add_assoc]
    exact nsmul_prime_mem_principalFiltration p ih
theorem zsmul_mem_principalFiltration_of_dvd {k : ℕ} {c : ℤ} (hc : (p ^ k : ℤ) ∣ c)
    (u : Additive (unitFiltrationUnits K 1)) : c • u ∈ principalFiltration K k := by
  obtain ⟨d, rfl⟩ := hc
  rw [mul_comm, mul_zsmul]
  refine zsmul_mem ?_ d
  have := nsmul_prime_pow_mem_principalFiltration p
    (by rw [principalFiltration_zero]; trivial : u ∈ principalFiltration K 0) k
  rw [zero_add] at this
  exact_mod_cast this
end Filtration
section Complete
theorem exists_forall_sub_mem_principalFiltration {s : ℕ → Additive (unitFiltrationUnits K 1)}
    (hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k) :
    ∃ l, ∀ k, l - s k ∈ principalFiltration K k := by
  set σ : ℕ → K := fun k ↦ (((Additive.toMul (s k) : unitFiltrationUnits K 1) : Kˣ) : K)
  have hσ1 : ∀ k, σ k - 1 ∈ valBall K 1 := fun k ↦ sub_one_mem_valBall_one (Additive.toMul (s k))
  have hσ0 : ∀ k, σ k ≠ 0 := fun k ↦ Units.ne_zero _
  have hquot : ∀ k : ℕ, σ (k + 1) / σ k - 1 ∈ valBall K (k + 1) := by
    intro k
    have := mem_principalFiltration.mp (hs k)
    simpa [σ, toMul_sub, div_eq_mul_inv] using this
  set f : ℕ → K := fun j ↦ σ (j + 1) - σ j
  have hf : ∀ j : ℕ, f j ∈ valBall K (j + 1) := by
    intro j
    have h : f j = σ j * (σ (j + 1) / σ j - 1) := by
      simp only [f]; field_simp [hσ0 j]
    rw [h]
    simpa using mul_mem_valBall (mem_valBall_zero_of_sub_one_mem (hσ1 j)) (hquot j)
  have hsum : Summable f := by
    refine summable_of_tendsto_zero (tendsto_zero_iff_valBall.mpr fun N ↦ ?_)
    rw [eventually_atTop]
    exact ⟨N.toNat, fun j hj ↦ valBall_antitone (by have := Int.self_le_toNat N; omega) (hf j)⟩
  set L := σ 0 + ∑' j, f j
  have hL : ∀ k : ℕ, L - σ k = ∑' j, f (j + k) := by
    intro k
    have h1 := hsum.sum_add_tsum_nat_add k
    have h2 : ∑ i ∈ Finset.range k, f i = σ k - σ 0 := Finset.sum_range_sub σ k
    simp only [L]
    rw [← h1, h2]
    ring
  have hLk : ∀ k : ℕ, L - σ k ∈ valBall K (k + 1) := by
    intro k
    rw [hL k]
    exact tsum_mem_valBall fun j ↦ valBall_antitone (by omega) (hf (j + k))
  have hL1 : L - 1 ∈ valBall K 1 := by
    have := add_mem (hLk 0) (hσ1 0)
    simpa using this
  have hL0 : L ≠ 0 := by
    intro h
    have := normalizedValuation_eq_one_of_sub_one_mem hL1
    rw [h, map_zero] at this
    exact zero_ne_one this
  refine ⟨Additive.ofMul ⟨Units.mk0 L hL0,
    (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩, fun k ↦ ?_⟩
  rw [mem_principalFiltration]
  have heq : (((Additive.toMul (Additive.ofMul ⟨Units.mk0 L hL0,
      (mem_unitFiltrationUnits_iff_valBall le_rfl).mpr (by simpa using hL1)⟩ - s k) :
        unitFiltrationUnits K 1) : Kˣ) : K) - 1 = (L - σ k) * (σ k)⁻¹ := by
    simp only [toMul_sub, toMul_ofMul]
    simp [σ, div_eq_mul_inv]
    field_simp [hσ0 k]
  rw [heq]
  have hinv : (σ k)⁻¹ ∈ valBall K 0 := by
    rw [mem_valBall, map_inv₀, normalizedValuation_eq_one_of_sub_one_mem (hσ1 k)]; simp
  simpa using mul_mem_valBall (hLk k) hinv
end Complete
section Module
variable (p : ℕ) [hp : Fact p.Prime]
theorem padicInt_dvd_intCast_iff {k : ℕ} {c : ℤ} :
    (p : ℤ_[p]) ^ k ∣ (c : ℤ_[p]) ↔ ((p : ℤ) ^ k) ∣ c := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow,
    PadicInt.norm_int_le_pow_iff_dvd]
theorem intCast_dvd_sub_of_dvd_sub {k : ℕ} {a : ℤ_[p]} {c c' : ℤ} (h : (p : ℤ_[p]) ^ k ∣ a - c)
    (h' : (p : ℤ_[p]) ^ k ∣ a - c') : ((p : ℤ) ^ k) ∣ c' - c := by
  rw [← padicInt_dvd_intCast_iff]
  have := dvd_sub h h'
  push_cast
  convert this using 1
  ring
theorem dvd_sub_appr (k : ℕ) (a : ℤ_[p]) : (p : ℤ_[p]) ^ k ∣ a - ((a.appr k : ℕ) : ℤ) := by
  rw [← Ideal.mem_span_singleton]
  simpa using PadicInt.appr_spec k a
variable [CharP 𝓀[K] p]
theorem exists_padicInt_pow (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    ∃ l : Additive (unitFiltrationUnits K 1), ∀ (k : ℕ) (c : ℤ), (p : ℤ_[p]) ^ k ∣ a - c →
      l - c • u ∈ principalFiltration K k := by
  set s : ℕ → Additive (unitFiltrationUnits K 1) := fun k ↦ ((a.appr k : ℕ) : ℤ) • u
  have hs : ∀ k, s (k + 1) - s k ∈ principalFiltration K k := by
    intro k
    simp only [s]
    rw [show ((a.appr (k + 1) : ℕ) : ℤ) • u - ((a.appr k : ℕ) : ℤ) • u =
      (((a.appr (k + 1) : ℕ) : ℤ) - ((a.appr k : ℕ) : ℤ)) • u by rw [sub_zsmul]; abel]
    refine zsmul_mem_principalFiltration_of_dvd p ?_ u
    have h1 := dvd_sub_appr p (k + 1) a
    have h1' : (p : ℤ_[p]) ^ k ∣ a - ((a.appr (k + 1) : ℕ) : ℤ) :=
      (pow_dvd_pow _ (Nat.le_succ k)).trans h1
    have := intCast_dvd_sub_of_dvd_sub p (dvd_sub_appr p k a) h1'
    exact_mod_cast this
  obtain ⟨l, hl⟩ := exists_forall_sub_mem_principalFiltration hs
  refine ⟨l, fun k c hc ↦ ?_⟩
  have h := intCast_dvd_sub_of_dvd_sub p hc (dvd_sub_appr p k a)
  have : l - c • u = (l - s k) + (((a.appr k : ℕ) : ℤ) - c) • u := by
    simp only [s, sub_zsmul]; abel
  rw [this]
  exact add_mem (hl k) (zsmul_mem_principalFiltration_of_dvd p h u)
noncomputable def padicIntSMul (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) :
    Additive (unitFiltrationUnits K 1) :=
  Classical.choose (exists_padicInt_pow p a u)
theorem padicIntSMul_spec (a : ℤ_[p]) (u : Additive (unitFiltrationUnits K 1)) {k : ℕ} {c : ℤ}
    (hc : (p : ℤ_[p]) ^ k ∣ a - c) : padicIntSMul p a u - c • u ∈ principalFiltration K k :=
  Classical.choose_spec (exists_padicInt_pow p a u) k c hc
theorem padicIntSMul_eq_of {a : ℤ_[p]} {u l : Additive (unitFiltrationUnits K 1)}
    (h : ∀ k : ℕ, ∃ c : ℤ, (p : ℤ_[p]) ^ k ∣ a - c ∧ l - c • u ∈ principalFiltration K k) :
    padicIntSMul p a u = l := by
  refine (sub_eq_zero.mp (eq_zero_of_forall_mem_principalFiltration fun k ↦ ?_))
  obtain ⟨c, hc, hl⟩ := h k
  have := sub_mem (padicIntSMul_spec p a u hc) hl
  simpa using this
noncomputable instance instModulePadicInt : Module ℤ_[p] (Additive (unitFiltrationUnits K 1)) where
  smul := padicIntSMul p
  one_smul u := padicIntSMul_eq_of p fun k ↦ ⟨1, by simp, by simp⟩
  mul_smul a b u := by
    show padicIntSMul p (a * b) u = padicIntSMul p a (padicIntSMul p b u)
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ), ?_, ?_⟩
    · have ha := dvd_sub_appr p k a
      have hb := dvd_sub_appr p k b
      have : a * b - (((((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ) : ℤ)) : ℤ_[p]) =
          a * (b - ((b.appr k : ℕ) : ℤ)) + ((b.appr k : ℕ) : ℤ) * (a - ((a.appr k : ℕ) : ℤ)) := by
        push_cast; ring
      rw [this]
      exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_right ha _)
    · have h1 := padicIntSMul_spec p a (padicIntSMul p b u) (dvd_sub_appr p k a)
      have h2 := padicIntSMul_spec p b u (dvd_sub_appr p k b)
      have : padicIntSMul p a (padicIntSMul p b u) -
          (((a.appr k : ℕ) : ℤ) * ((b.appr k : ℕ) : ℤ)) • u =
          (padicIntSMul p a (padicIntSMul p b u) - ((a.appr k : ℕ) : ℤ) • padicIntSMul p b u) +
            ((a.appr k : ℕ) : ℤ) • (padicIntSMul p b u - ((b.appr k : ℕ) : ℤ) • u) := by
        rw [mul_zsmul, zsmul_sub]; abel
      rw [this]
      exact add_mem h1 (zsmul_mem h2 _)
  smul_zero a := padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ), dvd_sub_appr p k a, by simp⟩
  smul_add a u v := by
    show padicIntSMul p a (u + v) = padicIntSMul p a u + padicIntSMul p a v
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ), dvd_sub_appr p k a, ?_⟩
    have h1 := padicIntSMul_spec p a u (dvd_sub_appr p k a)
    have h2 := padicIntSMul_spec p a v (dvd_sub_appr p k a)
    have : padicIntSMul p a u + padicIntSMul p a v - ((a.appr k : ℕ) : ℤ) • (u + v) =
        (padicIntSMul p a u - ((a.appr k : ℕ) : ℤ) • u) +
          (padicIntSMul p a v - ((a.appr k : ℕ) : ℤ) • v) := by
      rw [zsmul_add]; abel
    rw [this]
    exact add_mem h1 h2
  add_smul a b u := by
    show padicIntSMul p (a + b) u = padicIntSMul p a u + padicIntSMul p b u
    refine padicIntSMul_eq_of p fun k ↦ ⟨((a.appr k : ℕ) : ℤ) + ((b.appr k : ℕ) : ℤ), ?_, ?_⟩
    · have := dvd_add (dvd_sub_appr p k a) (dvd_sub_appr p k b)
      convert this using 1
      push_cast; ring
    · have h1 := padicIntSMul_spec p a u (dvd_sub_appr p k a)
      have h2 := padicIntSMul_spec p b u (dvd_sub_appr p k b)
      have : padicIntSMul p a u + padicIntSMul p b u -
          (((a.appr k : ℕ) : ℤ) + ((b.appr k : ℕ) : ℤ)) • u =
          (padicIntSMul p a u - ((a.appr k : ℕ) : ℤ) • u) +
            (padicIntSMul p b u - ((b.appr k : ℕ) : ℤ) • u) := by
        rw [add_zsmul]; abel
      rw [this]
      exact add_mem h1 h2
  zero_smul u := padicIntSMul_eq_of p fun k ↦ ⟨0, by simp, by simp⟩
end Module
section ModuleProps
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p]
theorem smul_sub_intCast_smul_mem {a : ℤ_[p]} {k : ℕ} {c : ℤ} (hc : (p : ℤ_[p]) ^ k ∣ a - c)
    (u : Additive (unitFiltrationUnits K 1)) : a • u - c • u ∈ principalFiltration K k :=
  padicIntSMul_spec p a u hc
theorem smul_mem_of_dvd {a : ℤ_[p]} {k : ℕ} (ha : (p : ℤ_[p]) ^ k ∣ a)
    (u : Additive (unitFiltrationUnits K 1)) : a • u ∈ principalFiltration K k := by
  have := smul_sub_intCast_smul_mem p (c := 0) (by simpa using ha) u
  simpa using this
theorem smul_mem_principalFiltration (a : ℤ_[p]) {k : ℕ} {u : Additive (unitFiltrationUnits K 1)}
    (hu : u ∈ principalFiltration K k) : a • u ∈ principalFiltration K k := by
  have h1 := smul_sub_intCast_smul_mem p (dvd_sub_appr p k a) u
  have h2 : ((a.appr k : ℕ) : ℤ) • u ∈ principalFiltration K k := zsmul_mem hu _
  simpa using add_mem h1 h2
theorem hasBasis_nhds_zero_principalFiltration :
    (𝓝 (0 : Additive (unitFiltrationUnits K 1))).HasBasis (fun _ ↦ True)
      (fun k ↦ (principalFiltration K k : Set (Additive (unitFiltrationUnits K 1)))) := by
  have h1 : 𝓝 (0 : Additive (unitFiltrationUnits K 1)) =
      Filter.comap (fun u : Additive (unitFiltrationUnits K 1) ↦
        ((Additive.toMul u : unitFiltrationUnits K 1) : Kˣ)) (𝓝 1) :=
    nhds_subtype _ (1 : unitFiltrationUnits K 1)
  rw [h1]
  refine (hasBasis_nhds_one_unitFiltrationUnits.comap _).to_hasBasis
    (fun n _ ↦ ⟨n, trivial, fun u hu ↦ unitFiltrationUnits_antitone (Nat.le_succ n) hu⟩)
    (fun k _ ↦ ⟨k + 1, trivial, fun u hu ↦ hu⟩)
theorem principalFiltration_mem_nhds (k : ℕ) :
    (principalFiltration K k : Set (Additive (unitFiltrationUnits K 1))) ∈ 𝓝 0 :=
  hasBasis_nhds_zero_principalFiltration.mem_of_mem trivial
instance continuousSMul_padicInt_principalUnits : ContinuousSMul ℤ_[p] (Additive (unitFiltrationUnits K 1)) := by
  refine ⟨continuous_iff_continuousAt.mpr fun x ↦ ?_⟩
  obtain ⟨a0, u0⟩ := x
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
    hasBasis_nhds_zero_principalFiltration.tendsto_right_iff]
  intro k _
  have h1 : {a : ℤ_[p] | (p : ℤ_[p]) ^ k ∣ a - a0} ∈ 𝓝 a0 := by
    have hr : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) := by
      have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
      positivity
    refine Filter.mem_of_superset (Metric.closedBall_mem_nhds a0 hr) fun a ha ↦ ?_
    rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
      Ideal.mem_span_singleton] at ha
    exact ha
  have h2 : {u : Additive (unitFiltrationUnits K 1) | u - u0 ∈ principalFiltration K k} ∈ 𝓝 u0 := by
    have ht : Tendsto (fun u : Additive (unitFiltrationUnits K 1) ↦ u - u0) (𝓝 u0) (𝓝 0) := by
      have : Tendsto (fun u : Additive (unitFiltrationUnits K 1) ↦ u - u0) (𝓝 u0) (𝓝 (u0 - u0)) :=
        tendsto_id.sub tendsto_const_nhds
      rwa [sub_self] at this
    exact ht (principalFiltration_mem_nhds k)
  filter_upwards [prod_mem_nhds h1 h2] with x hx
  obtain ⟨a, u⟩ := x
  obtain ⟨ha, hu⟩ := hx
  have : a • u - a0 • u0 = (a - a0) • u + a0 • (u - u0) := by rw [sub_smul, smul_sub]; abel
  show a • u - a0 • u0 ∈ principalFiltration K k
  rw [this]
  exact add_mem (smul_mem_of_dvd p ha u) (smul_mem_principalFiltration p a0 hu)
end ModuleProps
end GroundTheory.LocalField


