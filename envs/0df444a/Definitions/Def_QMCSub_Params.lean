-- Prove2me | Definitions.Def_QMCSub_Params
-- name    : QMCSub_Params
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:21:36.949213+00:00
-- url     : https://prove2.me/theorems/55682af7-4396-44f7-8ef6-d652ca9228ce
-- title:
--   Parameters of the subgradient method and an admissible choice of constants
-- statement:
--   The parameters as functions of the number of vertices $n$: $T=c_Tn^3$ iterations, step $\eta=c_Hn^3$, shift $\sigma=c_Tc_Hn^7$, weight scale $\Omega=c_\Omega n^5$ and exponent $2K=c_Kn^5$. The structure `Good` lists the inequalities the analysis and the size guards need. They hold for every $n\ge1$ with $c_T=c_H=10^{16}$, $c_\Omega=c_K=2\cdot10^{20}$, $c_\theta=4\cdot10^4$ and guard constants $200$, taking $\delta=1/(10^{18}n^4)$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_Core

/-!
The numeric parameters of the method as functions of the number of vertices, the list of
inequalities the analysis needs from them, and a concrete admissible choice of constants.
-/

namespace QMCSub

/-- Number of outer iterations, `cT n^3`. -/
def Tn (c : Consts) (n : ℕ) : ℕ := n * (n * (n * c.cT))

/-- The matrix power exponent `2K = cK n^5`. -/
def Kn2 (c : Consts) (n : ℕ) : ℕ := n * (n * (n * (n * (n * c.cK))))

/-- Step size `η = cH n^3`. -/
def etaZ (c : Consts) (n : ℕ) : ℤ := (c.cH : ℤ) * ((n : ℤ) * n * n)

/-- Shift `σ = cT cH n^7`. -/
def sigZ (c : Consts) (n : ℕ) : ℤ :=
  (c.cT : ℤ) * (c.cH : ℤ) * ((n : ℤ) * n * n * n * n * n * n)

/-- Weight scale `Ω = cOm n^5`. -/
def OmN (c : Consts) (n : ℕ) : ℕ := c.cOm * (n * n * n * n * n)

/-- Everything the analysis needs from the constants at a given number of vertices. -/
structure Good (c : Consts) (n : ℕ) : Prop where
  hK : ∃ K : ℕ, Kn2 c n = 2 * K
  hη : 0 < etaZ c n
  hT : 0 < Tn c n
  hσ : (Tn c n : ℤ) * (etaZ c n * n) ≤ sigZ c n
  hcθ : 0 < c.cth
  hηθ : 2 * (c.cth : ℤ) ≤ etaZ c n
  hOm : n ^ 2 ≤ OmN c n
  hδ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ (n : ℝ) * (1 - δ) ^ (Kn2 c n) ≤ δ ∧
      8 * (c.cth : ℝ) ^ 2 * (2 * n * ((OmN c n : ℤ) : ℝ) +
          errE n (etaZ c n) (sigZ c n) (OmN c n : ℤ) (Tn c n) δ) ≤
        (etaZ c n : ℝ) * (Tn c n : ℝ) ∧
      (4 * ((OmN c n : ℤ) : ℝ) / (c.cth : ℝ) + 1 +
          errE n (etaZ c n) (sigZ c n) (OmN c n : ℤ) (Tn c n) δ + 2 * (n : ℝ) ^ 2) /
        (4 * ((OmN c n : ℤ) : ℝ)) ≤ 1 / 10000
  hG1 : n * (2 * OmN c n + 2 * (sigZ c n).natAbs) ≤ 2 ^ (c.cbI + n * 8)
  hG2 : (sigZ c n).natAbs < 2 ^ (c.cbO + 1 + n * 9)
  hG3 : Tn c n * (n * (2 * OmN c n)) < 2 ^ (c.cbO + 1 + n * 9)

/-- A concrete admissible choice of constants. -/
def c0 : Consts where
  cT := 10 ^ 16
  cH := 10 ^ 16
  cOm := 2 * 10 ^ 20
  cK := 2 * 10 ^ 20
  cth := 4 * 10 ^ 4
  cbI := 200
  cbO := 200

private lemma Tn_c0 (n : ℕ) : Tn c0 n = 10 ^ 16 * n ^ 3 := by
  simp only [Tn, c0]; ring

private lemma Kn2_c0 (n : ℕ) : Kn2 c0 n = 2 * 10 ^ 20 * n ^ 5 := by
  simp only [Kn2, c0]; ring

private lemma etaZ_c0 (n : ℕ) : etaZ c0 n = 10 ^ 16 * (n : ℤ) ^ 3 := by
  simp only [etaZ, c0]; push_cast; ring

private lemma sigZ_c0 (n : ℕ) : sigZ c0 n = 10 ^ 32 * (n : ℤ) ^ 7 := by
  simp only [sigZ, c0]; push_cast; ring

private lemma sigZ_natAbs_c0 (n : ℕ) : (sigZ c0 n).natAbs = 10 ^ 32 * n ^ 7 := by
  rw [sigZ_c0]
  have h : (10 ^ 32 * (n : ℤ) ^ 7) = ((10 ^ 32 * n ^ 7 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.natAbs_natCast]

private lemma OmN_c0 (n : ℕ) : OmN c0 n = 2 * 10 ^ 20 * n ^ 5 := by
  simp only [OmN, c0]; ring

private lemma c0_cth : c0.cth = 4 * 10 ^ 4 := rfl
private lemma c0_cbI : c0.cbI = 200 := rfl
private lemma c0_cbO : c0.cbO = 200 := rfl

private lemma pow_le_two_pow (n k : ℕ) : n ^ k ≤ 2 ^ (n * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := n)).le k

private lemma errE_c0 (n : ℕ) (δ : ℝ) :
    errE n (etaZ c0 n) (sigZ c0 n) (OmN c0 n : ℤ) (Tn c0 n) δ =
      2 * 10 ^ 16 * (n : ℝ) ^ 5 +
        4 * δ * (4 * 10 ^ 20 * (n : ℝ) ^ 6 + 2 * 10 ^ 32 * (n : ℝ) ^ 9) := by
  rw [errE, etaZ_c0, sigZ_c0, OmN_c0, Tn_c0]
  push_cast
  ring

private lemma errE_c0_delta (n : ℕ) (hn : 1 ≤ n) :
    errE n (etaZ c0 n) (sigZ c0 n) (OmN c0 n : ℤ) (Tn c0 n) (1 / (10 ^ 18 * (n : ℝ) ^ 4)) =
      2 * 10 ^ 16 * (n : ℝ) ^ 5 + 1600 * (n : ℝ) ^ 2 + 8 * 10 ^ 14 * (n : ℝ) ^ 5 := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have hx' : (n : ℝ) ≠ 0 := hx.ne'
  rw [errE_c0]
  field_simp
  ring

private lemma pow_cond (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (1 - 1 / (10 ^ 18 * (n : ℝ) ^ 4)) ^ (2 * 10 ^ 20 * n ^ 5) ≤
      1 / (10 ^ 18 * (n : ℝ) ^ 4) := by
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 10 ^ 18 * n ^ 4 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = 60 + 5 * n := ⟨_, rfl⟩
  have hn0 : 0 < n := hn
  have hapos : 0 < a := by rw [ha]; positivity
  have haR : (0 : ℝ) < a := by exact_mod_cast hapos
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hapos
  have hδ : (1 : ℝ) / (10 ^ 18 * (n : ℝ) ^ 4) = 1 / (a : ℝ) := by rw [ha]; push_cast; norm_num
  rw [hδ]
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (a : ℝ) := ⟨_, rfl⟩
  rw [← hδdef]
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδle : δ ≤ 1 := by
    rw [hδdef, div_le_one haR]; exact ha1
  have h0 : 0 ≤ 1 - δ := by linarith
  have h1 : 1 - δ ≤ 1 := by linarith
  have hbern : 1 + (a : ℝ) * δ ≤ (1 + δ) ^ a := one_add_mul_le_pow (by linarith) a
  have haδ : (a : ℝ) * δ = 1 := by rw [hδdef]; field_simp
  have h2 : (2 : ℝ) ≤ (1 + δ) ^ a := by linarith
  have hprod : (1 - δ) ^ a * (1 + δ) ^ a ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  have hhalf : (1 - δ) ^ a ≤ 1 / 2 := by
    have hpos : 0 ≤ (1 - δ) ^ a := pow_nonneg h0 a
    nlinarith
  have hab : a * b ≤ 2 * 10 ^ 20 * n ^ 5 := by
    have h45 : n ^ 4 ≤ n ^ 5 := Nat.pow_le_pow_right hn (by norm_num)
    rw [ha, hb]
    calc 10 ^ 18 * n ^ 4 * (60 + 5 * n)
        = 60 * 10 ^ 18 * n ^ 4 + 5 * 10 ^ 18 * n ^ 5 := by ring
      _ ≤ 60 * 10 ^ 18 * n ^ 5 + 5 * 10 ^ 18 * n ^ 5 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ h45) _
      _ = 65 * 10 ^ 18 * n ^ 5 := by ring
      _ ≤ 2 * 10 ^ 20 * n ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
  have hmono : (1 - δ) ^ (2 * 10 ^ 20 * n ^ 5) ≤ (1 - δ) ^ (a * b) :=
    pow_le_pow_of_le_one h0 h1 hab
  have hpowb : (1 - δ) ^ (a * b) ≤ (1 / 2) ^ b := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg h0 a) hhalf b
  have hnat : n * a ≤ 2 ^ b := by
    rw [ha, hb, pow_add]
    have h5 : n ^ 5 ≤ 2 ^ (5 * n) := by rw [mul_comm]; exact pow_le_two_pow n 5
    calc n * (10 ^ 18 * n ^ 4) = 10 ^ 18 * n ^ 5 := by ring
      _ ≤ 2 ^ 60 * 2 ^ (5 * n) := Nat.mul_le_mul (by norm_num) h5
  have hreal : (n : ℝ) * (a : ℝ) ≤ 2 ^ b := by exact_mod_cast hnat
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * (1 - δ) ^ (2 * 10 ^ 20 * n ^ 5) ≤ (n : ℝ) * (1 / 2) ^ b :=
        mul_le_mul_of_nonneg_left (hmono.trans hpowb) hnR
    _ ≤ δ := by
        rw [hδdef, one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) haR]
        linarith

theorem good_c0 (n : ℕ) (hn : 1 ≤ n) : Good c0 n := by
  have hn0 : 0 < n := hn
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hz : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hz0 : (0 : ℤ) < n := by linarith
  refine
    { hK := ⟨10 ^ 20 * n ^ 5, by rw [Kn2_c0]; ring⟩
      hη := by rw [etaZ_c0]; positivity
      hT := by rw [Tn_c0]; positivity
      hσ := by rw [Tn_c0, etaZ_c0, sigZ_c0]; push_cast; apply le_of_eq; ring
      hcθ := by rw [c0_cth]; norm_num
      hηθ := ?_
      hOm := ?_
      hδ := ?_
      hG1 := ?_
      hG2 := ?_
      hG3 := ?_ }
  · rw [etaZ_c0, c0_cth]
    have h3 : (1 : ℤ) ≤ (n : ℤ) ^ 3 := one_le_pow₀ hz
    push_cast
    linarith
  · rw [OmN_c0]
    calc n ^ 2 ≤ n ^ 5 := Nat.pow_le_pow_right hn (by norm_num)
      _ = 1 * n ^ 5 := (one_mul _).symm
      _ ≤ 2 * 10 ^ 20 * n ^ 5 := Nat.mul_le_mul_right _ (by norm_num)
  · refine ⟨1 / (10 ^ 18 * (n : ℝ) ^ 4), by positivity, ?_, ?_, ?_, ?_⟩
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hx
      linarith
    · rw [Kn2_c0]; exact pow_cond n hn
    · rw [errE_c0_delta n hn, OmN_c0, etaZ_c0, Tn_c0, c0_cth]
      push_cast
      have h56 : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hx (by norm_num)
      have h26 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hx (by norm_num)
      nlinarith [h56, h26]
    · rw [errE_c0_delta n hn, OmN_c0, c0_cth]
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have h25 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 5 := pow_le_pow_right₀ hx (by norm_num)
      have h05 : (1 : ℝ) ≤ (n : ℝ) ^ 5 := one_le_pow₀ hx
      linarith
  · rw [OmN_c0, sigZ_natAbs_c0, c0_cbI]
    have h8 : n ^ 8 ≤ 2 ^ (n * 8) := pow_le_two_pow n 8
    have h68 : n ^ 6 ≤ n ^ 8 := Nat.pow_le_pow_right hn (by norm_num)
    calc n * (2 * (2 * 10 ^ 20 * n ^ 5) + 2 * (10 ^ 32 * n ^ 7))
        = 4 * 10 ^ 20 * n ^ 6 + 2 * 10 ^ 32 * n ^ 8 := by ring
      _ ≤ 4 * 10 ^ 20 * n ^ 8 + 2 * 10 ^ 32 * n ^ 8 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ h68) _
      _ = (4 * 10 ^ 20 + 2 * 10 ^ 32) * n ^ 8 := by ring
      _ ≤ 2 ^ 200 * 2 ^ (n * 8) := Nat.mul_le_mul (by norm_num) h8
      _ = 2 ^ (200 + n * 8) := by rw [pow_add]
  · rw [sigZ_natAbs_c0, c0_cbO]
    have h9 : n ^ 9 ≤ 2 ^ (n * 9) := pow_le_two_pow n 9
    have h79 : n ^ 7 ≤ n ^ 9 := Nat.pow_le_pow_right hn (by norm_num)
    calc 10 ^ 32 * n ^ 7 ≤ 10 ^ 32 * 2 ^ (n * 9) := Nat.mul_le_mul_left _ (h79.trans h9)
      _ < 2 ^ 201 * 2 ^ (n * 9) := mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ = 2 ^ (200 + 1 + n * 9) := by rw [← pow_add]
  · rw [Tn_c0, OmN_c0, c0_cbO]
    have h9 : n ^ 9 ≤ 2 ^ (n * 9) := pow_le_two_pow n 9
    calc 10 ^ 16 * n ^ 3 * (n * (2 * (2 * 10 ^ 20 * n ^ 5)))
        = 4 * 10 ^ 36 * n ^ 9 := by ring
      _ ≤ 4 * 10 ^ 36 * 2 ^ (n * 9) := Nat.mul_le_mul_left _ h9
      _ < 2 ^ 201 * 2 ^ (n * 9) := mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ = 2 ^ (200 + 1 + n * 9) := by rw [← pow_add]

end QMCSub


