-- Prove2me | Definitions.Def_DetDLP_W4_M5Parameters
-- name    : DetDLP_W4_M5Parameters
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T20:31:22.563403+00:00
-- url     : https://prove2.me/theorems/f2287f80-af6c-4e8e-b911-f62ca2a75a04
-- title:
--   Dyadic parameters for the two-layer multiplication gadget
-- statement:
--   Constructs the limb width, transform dimensions and Fermat-ring parameters as functions of the bit length, proving simultaneous size and principal-root bounds.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.3, Lemma 2.3 (pp. 8–9)

import Theorems.Thm_DetDLP_schonhage_strassen_fermat_dft_and_carry

set_option autoImplicit false

namespace DetDLP.w4_MulParams

/-- The least exponent for which `(2^j)^2 ≥ 64(d+1)`. -/
def j (d : ℕ) : ℕ := Nat.clog 4 (64 * (d + 1))

def J (d : ℕ) : ℕ := 2 ^ j d

def k (d : ℕ) : ℕ := J d / 4

/-- Ceiling division by the limb width. -/
def n0 (d : ℕ) : ℕ := (d + k d - 1) / k d

def μ (d : ℕ) : ℕ := Nat.clog 2 (2 * n0 d)

def L (d : ℕ) : ℕ := 2 ^ μ d

def L1 (d : ℕ) : ℕ := 2 ^ (μ d / 2)

def L2 (d : ℕ) : ℕ := 2 ^ ((μ d + 1) / 2)

lemma two_pow_sq (a : ℕ) : (2 ^ a) ^ 2 = (4 : ℕ) ^ a := by
  rw [← pow_mul, Nat.mul_comm a 2, pow_mul]
  norm_num

lemma j_ge_four {d : ℕ} (hd : 1 ≤ d) : 4 ≤ j d := by
  have h : 3 < Nat.clog 4 (64 * (d + 1)) :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num; omega)
  exact h

lemma J_minimal (d e : ℕ) : 64 * (d + 1) ≤ (2 ^ e) ^ 2 ↔ j d ≤ e := by
  rw [two_pow_sq, j, Nat.clog_le_iff_le_pow (by norm_num)]

lemma J_lower (d : ℕ) : 64 * (d + 1) ≤ (J d) ^ 2 := by
  exact (J_minimal d (j d)).mpr le_rfl

lemma J_ge_sixteen {d : ℕ} (hd : 1 ≤ d) : 16 ≤ J d := by
  exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (j_ge_four hd)

lemma J_upper {d : ℕ} (hd : 1 ≤ d) : (J d) ^ 2 < 256 * (d + 1) := by
  have hpred : (4 : ℕ) ^ (j d - 1) < 64 * (d + 1) := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num)).mp
    change j d - 1 < j d
    have := j_ge_four hd
    omega
  have hj : 4 ^ j d = 4 * 4 ^ (j d - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (by have := j_ge_four hd; omega)]
  rw [J, two_pow_sq, hj]
  omega

lemma sixteen_dvd_J {d : ℕ} (hd : 1 ≤ d) : 16 ∣ J d := by
  exact pow_dvd_pow 2 (j_ge_four hd)

lemma four_mul_k {d : ℕ} (hd : 1 ≤ d) : 4 * k d = J d := by
  apply Nat.mul_div_cancel'
  exact dvd_trans (by norm_num : 4 ∣ 16) (sixteen_dvd_J hd)

lemma k_ge_four {d : ℕ} (hd : 1 ≤ d) : 4 ≤ k d := by
  have hJ := J_ge_sixteen hd
  dsimp [k]
  omega

lemma n0_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ n0 d := by
  have hk := k_ge_four hd
  dsimp [n0]
  apply (Nat.le_div_iff_mul_le (by omega)).mpr
  omega

lemma n0_covers {d : ℕ} (hd : 1 ≤ d) : d ≤ k d * n0 d := by
  have hk := k_ge_four hd
  have hlt := Nat.lt_mul_div_succ (d + k d - 1) (by omega : 0 < k d)
  rw [Nat.mul_add, Nat.mul_one] at hlt
  dsimp [n0]
  omega

lemma n0_minimal {d : ℕ} (hd : 1 ≤ d) : k d * (n0 d - 1) < d := by
  have hk := k_ge_four hd
  have hn := n0_pos hd
  have hle := Nat.mul_div_le (d + k d - 1) (k d)
  change k d * n0 d ≤ d + k d - 1 at hle
  have heq : k d * (n0 d - 1) = k d * n0 d - k d := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [heq]
  omega

lemma n0_upper {d : ℕ} (hd : 1 ≤ d) : n0 d < J d / 16 + 1 := by
  have hJ := J_lower d
  have hk := k_ge_four hd
  have hkJ := four_mul_k hd
  have hdiv : 16 * (J d / 16) = J d := Nat.mul_div_cancel' (sixteen_dvd_J hd)
  have hcover : d ≤ k d * (J d / 16) := by
    nlinarith
  have hdiv_le : (d + k d - 1) / k d ≤ J d / 16 := by
    apply (Nat.div_le_iff_le_mul_add_pred (by omega)).mpr
    omega
  exact Nat.lt_succ_of_le hdiv_le

lemma L_lower {d : ℕ} (_hd : 1 ≤ d) : 2 * n0 d ≤ L d := by
  exact Nat.le_pow_clog (by norm_num) _

lemma mu_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ μ d := by
  have hn := n0_pos hd
  exact Nat.clog_pos (by norm_num) (by omega)

lemma L_upper {d : ℕ} (hd : 1 ≤ d) : L d < 4 * n0 d := by
  have hp : 2 ^ (μ d - 1) < 2 * n0 d := by
    apply (Nat.lt_clog_iff_pow_lt (by norm_num)).mp
    change μ d - 1 < μ d
    have := mu_pos hd
    omega
  have heq : L d = 2 * 2 ^ (μ d - 1) := by
    unfold L
    rw [← pow_succ', Nat.sub_add_cancel (mu_pos hd)]
  rw [heq]
  omega

lemma L_le_half_J {d : ℕ} (hd : 1 ≤ d) : L d ≤ J d / 2 := by
  have hn := n0_upper hd
  have hL := L_upper hd
  omega

lemma L1_le_L2 (d : ℕ) : L1 d ≤ L2 d := by
  exact Nat.pow_le_pow_right (by decide) (by omega)

lemma L1_mul_L2 (d : ℕ) : L1 d * L2 d = L d := by
  unfold L1 L2 L
  rw [← pow_add]
  congr 1
  omega

lemma L2_sq_le_twice_L (d : ℕ) : (L2 d) ^ 2 ≤ 2 * L d := by
  unfold L2 L
  rw [← pow_mul, ← pow_succ']
  exact Nat.pow_le_pow_right (by decide) (by omega)

lemma L2_sq_le_J {d : ℕ} (hd : 1 ≤ d) : (L2 d) ^ 2 ≤ J d := by
  have hL := L_le_half_J hd
  have hsq := L2_sq_le_twice_L d
  omega

/-- The exact hypotheses consumed by the previously proved numerical bound theorem. -/
theorem core_bounds {d : ℕ} (hd : 1 ≤ d) :
    16 ≤ J d ∧ 64 * (d + 1) ≤ (J d) ^ 2 ∧ (J d) ^ 2 < 256 * (d + 1) ∧
    1 ≤ n0 d ∧ n0 d < J d / 16 + 1 ∧
    2 * n0 d ≤ L d ∧ L d < 4 * n0 d ∧
    L1 d ≤ L2 d ∧ (L2 d) ^ 2 ≤ 2 * L d :=
  ⟨J_ge_sixteen hd, J_lower d, J_upper hd, n0_pos hd, n0_upper hd,
    L_lower hd, L_upper hd, L1_le_L2 d, L2_sq_le_twice_L d⟩

lemma L_minimal (d e : ℕ) : 2 * n0 d ≤ 2 ^ e ↔ μ d ≤ e := by
  rw [μ, Nat.clog_le_iff_le_pow (by norm_num)]

lemma half_J {d : ℕ} (hd : 1 ≤ d) : J d / 2 = 2 ^ (j d - 1) := by
  have hJ : J d = 2 * 2 ^ (j d - 1) := by
    unfold J
    rw [← pow_succ', Nat.sub_add_cancel (by have := j_ge_four hd; omega)]
  rw [hJ, Nat.mul_div_right _ (by norm_num)]

lemma mu_le_j_sub_one {d : ℕ} (hd : 1 ≤ d) : μ d ≤ j d - 1 := by
  have h := L_le_half_J hd
  rw [half_J hd] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp h

lemma mu_le_J {d : ℕ} (hd : 1 ≤ d) : μ d ≤ J d := by
  have hμ := mu_le_j_sub_one hd
  have hj : j d ≤ 2 ^ j d := Nat.le_of_lt Nat.lt_two_pow_self
  exact le_trans (le_trans hμ (Nat.sub_le _ _)) hj

lemma L_dvd_J {d : ℕ} (hd : 1 ≤ d) : L d ∣ J d := by
  exact pow_dvd_pow 2 ((mu_le_j_sub_one hd).trans (Nat.sub_le _ _))

lemma L_dvd_two_J {d : ℕ} (hd : 1 ≤ d) : L d ∣ 2 * J d :=
  dvd_mul_of_dvd_right (L_dvd_J hd) 2

lemma two_dvd_L {d : ℕ} (hd : 1 ≤ d) : 2 ∣ L d := by
  exact pow_dvd_pow 2 (mu_pos hd)

lemma half_L {d : ℕ} (hd : 1 ≤ d) : L d / 2 = 2 ^ (μ d - 1) := by
  have hL : L d = 2 * 2 ^ (μ d - 1) := by
    unfold L
    rw [← pow_succ', Nat.sub_add_cancel (mu_pos hd)]
  rw [hL, Nat.mul_div_right _ (by norm_num)]

/-- The exponent used for the principal `L`-th root of unity. -/
def rootStep (d : ℕ) : ℕ := 2 * J d / L d

lemma rootStep_pos {d : ℕ} (hd : 1 ≤ d) : 1 ≤ rootStep d := by
  have hJ := J_ge_sixteen hd
  have hL := L_le_half_J hd
  have hLp : 0 < L d := by unfold L; positivity
  apply (Nat.le_div_iff_mul_le hLp).mpr
  omega

lemma L_mul_rootStep {d : ℕ} (hd : 1 ≤ d) : L d * rootStep d = 2 * J d :=
  Nat.mul_div_cancel' (L_dvd_two_J hd)

lemma half_L_mul_rootStep {d : ℕ} (hd : 1 ≤ d) :
    (L d / 2) * rootStep d = J d := by
  have heq : 2 * (L d / 2) = L d := Nat.mul_div_cancel' (two_dvd_L hd)
  have hroot := L_mul_rootStep hd
  nlinarith

lemma rootStep_eq_pow {d : ℕ} (hd : 1 ≤ d) :
    rootStep d = 2 ^ (j d + 1 - μ d) := by
  have hμ : μ d ≤ j d + 1 := by have := mu_le_j_sub_one hd; omega
  have hfact : 2 * J d = L d * 2 ^ (j d + 1 - μ d) := by
    unfold L J
    rw [← pow_succ', ← pow_add, Nat.add_sub_of_le hμ]
  unfold rootStep
  rw [hfact, Nat.mul_div_right _ (by unfold L; positivity)]

lemma n0_le_k {d : ℕ} (hd : 1 ≤ d) : n0 d ≤ k d := by
  have hn := n0_upper hd
  have hk := four_mul_k hd
  omega

lemma n0_lt_two_pow_k {d : ℕ} (hd : 1 ≤ d) : n0 d < 2 ^ k d :=
  (n0_le_k hd).trans_lt Nat.lt_two_pow_self

/-- A direct no-wrap bound for the convolution coefficient envelope. -/
lemma coefficient_envelope_lt_modulus {d : ℕ} (hd : 1 ≤ d) :
    n0 d * 2 ^ (2 * k d) < 2 ^ J d := by
  have hfirst : n0 d * 2 ^ (2 * k d) < 2 ^ k d * 2 ^ (2 * k d) :=
    Nat.mul_lt_mul_of_pos_right (n0_lt_two_pow_k hd) (by positivity)
  have heq : 2 ^ k d * 2 ^ (2 * k d) = (2 : ℕ) ^ (3 * k d) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow : (2 : ℕ) ^ (3 * k d) ≤ 2 ^ J d := by
    apply Nat.pow_le_pow_right (by norm_num)
    have := four_mul_k hd
    omega
  exact (heq ▸ hfirst).trans_le hpow

lemma k_eq_pow {d : ℕ} (hd : 1 ≤ d) : k d = 2 ^ (j d - 2) := by
  have hJ : J d = 4 * 2 ^ (j d - 2) := by
    change 2 ^ j d = 2 ^ 2 * 2 ^ (j d - 2)
    rw [← pow_add, Nat.add_sub_of_le (by have := j_ge_four hd; omega)]
  unfold k
  rw [hJ, Nat.mul_div_right _ (by norm_num)]

lemma n0_covers_tightly {d : ℕ} (hd : 1 ≤ d) :
    d ≤ k d * n0 d ∧ k d * n0 d < d + k d := by
  refine ⟨n0_covers hd, ?_⟩
  have h := Nat.mul_div_le (d + k d - 1) (k d)
  change k d * n0 d ≤ d + k d - 1 at h
  have := k_ge_four hd
  omega

lemma L_ge_two {d : ℕ} (hd : 1 ≤ d) : 2 ≤ L d := by
  have hn := n0_pos hd
  have hL := L_lower hd
  omega

lemma L1_pos (d : ℕ) : 0 < L1 d := by unfold L1; positivity

lemma L2_pos (d : ℕ) : 0 < L2 d := by unfold L2; positivity

lemma L1_dvd_L (d : ℕ) : L1 d ∣ L d := by
  rw [← L1_mul_L2]
  exact dvd_mul_right _ _

lemma L2_dvd_L (d : ℕ) : L2 d ∣ L d := by
  rw [← L1_mul_L2]
  exact dvd_mul_left _ _

lemma root_parameters {d : ℕ} (hd : 1 ≤ d) :
    1 ≤ μ d ∧ μ d - 1 ≤ J d ∧
    J d = 2 ^ (μ d - 1) * rootStep d ∧
    L d = 2 ^ ((μ d - 1) + 1) := by
  refine ⟨mu_pos hd, (Nat.sub_le _ _).trans (mu_le_J hd), ?_, ?_⟩
  · rw [← half_L hd]
    exact (half_L_mul_rootStep hd).symm
  · rw [Nat.sub_add_cancel (mu_pos hd)]
    rfl

/-- All parameters are explicit, and all hypotheses of the numerical gadget bounds hold. -/
theorem parameters_exist (d : ℕ) (hd : 1 ≤ d) :
    ∃ (j J k n0 μ L L1 L2 : ℕ),
      J = 2 ^ j ∧ k = J / 4 ∧ n0 = (d + k - 1) / k ∧
      μ = Nat.clog 2 (2 * n0) ∧ L = 2 ^ μ ∧
      L1 = 2 ^ (μ / 2) ∧ L2 = 2 ^ ((μ + 1) / 2) ∧
      16 ≤ J ∧ 64 * (d + 1) ≤ J ^ 2 ∧ J ^ 2 < 256 * (d + 1) ∧
      0 < k ∧ d ≤ k * n0 ∧ 1 ≤ n0 ∧ n0 < J / 16 + 1 ∧
      2 * n0 ≤ L ∧ L < 4 * n0 ∧ L = L1 * L2 ∧
      L1 ≤ L2 ∧ L2 ^ 2 ≤ 2 * L ∧ L ≤ J / 2 ∧
      L ∣ 2 * J ∧ μ ≤ J ∧ n0 * 2 ^ (2 * k) < 2 ^ J := by
  refine ⟨j d, J d, k d, n0 d, μ d, L d, L1 d, L2 d,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    J_ge_sixteen hd, J_lower d, J_upper hd, ?_, n0_covers hd,
    n0_pos hd, n0_upper hd, L_lower hd, L_upper hd, (L1_mul_L2 d).symm,
    L1_le_L2 d, L2_sq_le_twice_L d, L_le_half_J hd, L_dvd_two_J hd,
    mu_le_J hd, coefficient_envelope_lt_modulus hd⟩
  have := k_ge_four hd
  omega

/-- Instantiate the existing proved arithmetic theorem; no numerical bound is reproved here. -/
theorem size_bounds {d : ℕ} (hd : 1 ≤ d) :
    L d ≤ J d / 2 ∧ (L2 d) ^ 2 ≤ J d ∧
    4 * d + 4 * J d * (J d + 1) < 1100 * (d + 1) ∧
    (2 * max (L1 d) (L2 d) * (J d + 1) : ℝ) <
      136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) :=
  DetDLP.schonhage_strassen_fermat_dft_and_carry.1
    d (J d) (n0 d) (L d) (L1 d) (L2 d) hd
    (J_ge_sixteen hd) (J_lower d) (J_upper hd) (n0_pos hd) (n0_upper hd)
    (L_lower hd) (L_upper hd) (L1_le_L2 d) (L2_sq_le_twice_L d)

lemma J_lt_linear {d : ℕ} (hd : 1 ≤ d) : J d < 16 * (d + 1) := by
  have hl := J_ge_sixteen hd
  have hu := J_upper hd
  have hlin : 16 * J d ≤ (J d) ^ 2 := by nlinarith
  omega

lemma L1_le_L (d : ℕ) : L1 d ≤ L d := by
  exact Nat.le_of_dvd (by unfold L; positivity) (L1_dvd_L d)

lemma L2_le_L (d : ℕ) : L2 d ≤ L d := by
  exact Nat.le_of_dvd (by unfold L; positivity) (L2_dvd_L d)

/-- A concise existential interface for the network's edge, degree, and vertex-count arguments. -/
theorem parameters_with_size_exist (d : ℕ) (hd : 1 ≤ d) :
    ∃ (J k n0 μ L L1 L2 : ℕ),
      J = 2 ^ j d ∧ k = J / 4 ∧ n0 = (d + k - 1) / k ∧
      L = 2 ^ μ ∧ L1 = 2 ^ (μ / 2) ∧ L2 = 2 ^ ((μ + 1) / 2) ∧
      0 < k ∧ d ≤ k * n0 ∧ 1 ≤ n0 ∧ 2 * n0 ≤ L ∧
      L = L1 * L2 ∧ L ∣ 2 * J ∧ μ ≤ J ∧
      n0 * 2 ^ (2 * k) < 2 ^ J ∧
      J < 16 * (d + 1) ∧ L ≤ J / 2 ∧ L1 ≤ L2 ∧ L2 ≤ L ∧
      4 * d + 4 * J * (J + 1) < 1100 * (d + 1) ∧
      (2 * max L1 L2 * (J + 1) : ℝ) <
        136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) := by
  obtain ⟨hLJ, _, hedge, hdeg⟩ := size_bounds hd
  refine ⟨J d, k d, n0 d, μ d, L d, L1 d, L2 d,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_, n0_covers hd, n0_pos hd,
    L_lower hd, (L1_mul_L2 d).symm, L_dvd_two_J hd, mu_le_J hd,
    coefficient_envelope_lt_modulus hd, J_lt_linear hd,
    hLJ, L1_le_L2 d, L2_le_L d, hedge, hdeg⟩
  have := k_ge_four hd
  omega

/-- The Fermat ring used for the actual transform.  The modulus need not be prime. -/
abbrev FermatRing (d : ℕ) := ZMod (2 ^ J d + 1)

/-- The principal-root candidate; its orthogonality is proved in the convolution module. -/
def omega (d : ℕ) : FermatRing d := (2 : FermatRing d) ^ rootStep d

/-- An explicit inverse for the transform length in the Fermat ring. -/
def inverseL (d : ℕ) : FermatRing d := -(2 : FermatRing d) ^ (J d - μ d)

lemma modulus_odd {d : ℕ} (hd : 1 ≤ d) : Odd (2 ^ J d + 1) := by
  apply Even.add_one
  exact (even_two : Even (2 : ℕ)).pow_of_ne_zero (by have := J_ge_sixteen hd; omega)

lemma two_isUnit {d : ℕ} (hd : 1 ≤ d) : IsUnit (2 : FermatRing d) :=
  ZMod.isUnit_prime_of_not_dvd Nat.prime_two (modulus_odd hd).not_two_dvd_nat

lemma L_isUnit {d : ℕ} (hd : 1 ≤ d) : IsUnit (L d : FermatRing d) := by
  simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using (two_isUnit hd).pow (μ d)

lemma L_coprime_modulus {d : ℕ} (hd : 1 ≤ d) :
    Nat.Coprime (L d) (2 ^ J d + 1) :=
  (ZMod.isUnit_iff_coprime _ _).mp (L_isUnit hd)

lemma two_pow_J {d : ℕ} (hd : 1 ≤ d) : (2 : FermatRing d) ^ J d = -1 := by
  obtain ⟨_, hm, hJ, _⟩ := root_parameters hd
  exact (DetDLP.schonhage_strassen_fermat_dft_and_carry.2.1.1
    (J d) (μ d - 1) (rootStep d) hm hJ).1

lemma omega_half {d : ℕ} (hd : 1 ≤ d) : omega d ^ (L d / 2) = -1 := by
  obtain ⟨_, hm, hJ, _⟩ := root_parameters hd
  rw [half_L hd]
  exact (DetDLP.schonhage_strassen_fermat_dft_and_carry.2.1.1
    (J d) (μ d - 1) (rootStep d) hm hJ).2.1

lemma omega_full {d : ℕ} (hd : 1 ≤ d) : omega d ^ L d = 1 := by
  obtain ⟨_, hm, hJ, hL⟩ := root_parameters hd
  rw [hL]
  exact (DetDLP.schonhage_strassen_fermat_dft_and_carry.2.1.1
    (J d) (μ d - 1) (rootStep d) hm hJ).2.2.1

lemma inverseL_mul_L {d : ℕ} (hd : 1 ≤ d) :
    inverseL d * (L d : FermatRing d) = 1 := by
  have hJ : J d = 2 ^ μ d * (J d / L d) :=
    (Nat.mul_div_cancel' (L_dvd_J hd)).symm
  simpa only [inverseL, L, Nat.cast_pow, Nat.cast_ofNat] using
    (DetDLP.schonhage_strassen_fermat_dft_and_carry.2.1.1
      (J d) (μ d) (J d / L d) (mu_le_J hd) hJ).2.2.2

lemma L_mul_inverseL {d : ℕ} (hd : 1 ≤ d) :
    (L d : FermatRing d) * inverseL d = 1 := by
  rw [mul_comm, inverseL_mul_L hd]

lemma omega_isUnit {d : ℕ} (hd : 1 ≤ d) : IsUnit (omega d) :=
  (two_isUnit hd).pow (rootStep d)

lemma neg_one_ne_one {d : ℕ} (hd : 1 ≤ d) : (-1 : FermatRing d) ≠ 1 := by
  intro heq
  have hzero : (2 : FermatRing d) = 0 := by
    calc (2 : FermatRing d) = 1 + 1 := by norm_num
      _ = -1 + 1 := by rw [heq]
      _ = 0 := by simp
  have hdiv : 2 ^ J d + 1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 _).mp hzero
  have hbound := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) hdiv
  have hJ := J_ge_sixteen hd
  have hpow : 16 ≤ (2 : ℕ) ^ J d := by
    change (2 : ℕ) ^ 4 ≤ 2 ^ J d
    apply Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ))
    omega
  omega

/-- Exact multiplicative order of the actual transform root; no field assumption is used. -/
lemma omega_isPrimitiveRoot {d : ℕ} (hd : 1 ≤ d) :
    IsPrimitiveRoot (omega d) (L d) := by
  have horder : orderOf (omega d) = L d := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by have := L_ge_two hd; omega) (omega_full hd)
    intro p hp hpd
    have hp2 : p = 2 := Nat.prime_eq_prime_of_dvd_pow hp Nat.prime_two hpd
    rw [hp2, omega_half hd]
    exact neg_one_ne_one hd
  rw [← horder]
  exact IsPrimitiveRoot.orderOf (omega d)

/-- Parameter-to-ring interface for the separate DFT orthogonality/convolution proof. -/
theorem fermat_ring_parameters {d : ℕ} (hd : 1 ≤ d) :
    Odd (2 ^ J d + 1) ∧ Nat.Coprime (L d) (2 ^ J d + 1) ∧
    IsUnit (2 : FermatRing d) ∧ IsUnit (L d : FermatRing d) ∧
    inverseL d * (L d : FermatRing d) = 1 ∧
    (L d : FermatRing d) * inverseL d = 1 ∧
    omega d ^ (L d / 2) = -1 ∧ omega d ^ L d = 1 ∧
    IsPrimitiveRoot (omega d) (L d) :=
  ⟨modulus_odd hd, L_coprime_modulus hd, two_isUnit hd, L_isUnit hd,
    inverseL_mul_L hd, L_mul_inverseL hd, omega_half hd, omega_full hd,
    omega_isPrimitiveRoot hd⟩

end DetDLP.w4_MulParams


