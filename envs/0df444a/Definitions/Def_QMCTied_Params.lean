-- Prove2me | Definitions.Def_QMCTied_Params
-- name    : QMCTied_Params
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T10:18:00.389796+00:00
-- url     : https://prove2.me/theorems/88899d7f-6528-4e57-95ce-71766312f90b
-- title:
--   Parameters of the tied-entry iteration
-- statement:
--   For $N$ rows and accuracy $1/E$: grid $D=4096E^2N^8$, step $\eta=16EN^2$, $\delta=1/(48EN^2)$, exponent $K=48EN^2(48E+3N)$, $T=1024E^2N^8$ iterations and output resolution $8E$. For $E\ge1$, $N\ge2$ these satisfy the power condition $N(1-\delta)^{2K}\le\delta$, make the total error at most $5/(8E)$, and fit the size guards.
-- source:
--   Supporting library for QuantumMaxCutEnergy.PauliSDP.uniform_value_lower_approximation_compiler (Prove2me Quantum Max-Cut campaign; level-k Pauli moment relaxation as in Gribling, Sinjorgo and Sotirov, arXiv:2504.11120, Section 2). Method: integer penalty supergradient iteration with matrix-power certificates.

import Mathlib
import Definitions.Def_QMCTied_Defs
import Definitions.Def_QMCTied_Core

/-!
The parameters of the tied-entry SDP iteration as functions of the number of rows `N` and the
accuracy parameter `E` (accuracy `1 / E`), and the inequalities the analysis needs from them.
-/

namespace QMCTied

/-- Parameters for `N` rows and accuracy `1 / E`. -/
def parOf (E N : ℕ) : Par where
  D := 4096 * (E : ℤ) * E * (N : ℤ) ^ 8
  eta := 16 * (E : ℚ) * (N : ℚ) ^ 2
  K := 48 * E * N ^ 2 * (48 * E + 3 * N)
  dN := 48 * E * N ^ 2
  D2 := 8 * E

/-- Number of outer iterations. -/
def TOf (E N : ℕ) : ℕ := 1024 * E * E * N ^ 8

/-- Everything the analysis and the size guards need from the parameters. -/
structure PGood (E N : ℕ) : Prop where
  hD : 0 < (parOf E N).D
  heta : 0 < (parOf E N).eta
  hdN : 2 ≤ (parOf E N).dN
  hD2 : 0 < (parOf E N).D2
  hT : 0 < TOf E N
  hK : (N : ℝ) * (1 - 1 / ((parOf E N).dN : ℝ)) ^ (2 * (parOf E N).K) ≤
    1 / ((parOf E N).dN : ℝ)
  herr : 1 / ((parOf E N).D2 : ℝ) + 6 * (N : ℝ) ^ 2 / ((parOf E N).dN : ℝ) +
    convErr N (parOf E N) (TOf E N) ≤ 5 / (8 * (E : ℝ))
  hG1 : N * (N * (parOf E N).D.natAbs + (parOf E N).D.natAbs) ≤ 2 ^ (8192 * E * E + N * 10)
  hG2 : (parOf E N).D.natAbs < 2 ^ (4096 * E * E + 1 + N * 8)
  hG3 : 2 * (parOf E N).D2 < 2 ^ (4096 * E * E + 1 + N * 8)

private lemma par_D (E N : ℕ) : (parOf E N).D = 4096 * (E : ℤ) * E * (N : ℤ) ^ 8 := rfl
private lemma par_eta (E N : ℕ) : (parOf E N).eta = 16 * (E : ℚ) * (N : ℚ) ^ 2 := rfl
private lemma par_K (E N : ℕ) : (parOf E N).K = 48 * E * N ^ 2 * (48 * E + 3 * N) := rfl
private lemma par_dN (E N : ℕ) : (parOf E N).dN = 48 * E * N ^ 2 := rfl
private lemma par_D2 (E N : ℕ) : (parOf E N).D2 = 8 * E := rfl

private lemma par_D_natAbs (E N : ℕ) : (parOf E N).D.natAbs = 4096 * E * E * N ^ 8 := by
  rw [par_D]
  have h : (4096 * (E : ℤ) * E * (N : ℤ) ^ 8) = ((4096 * E * E * N ^ 8 : ℕ) : ℤ) := by
    push_cast; ring
  rw [h, Int.natAbs_natCast]

private lemma par_D_real (E N : ℕ) :
    ((parOf E N).D : ℝ) = 4096 * (E : ℝ) ^ 2 * (N : ℝ) ^ 8 := by
  rw [par_D]; push_cast; ring

private lemma par_eta_real (E N : ℕ) :
    ((parOf E N).eta : ℝ) = 16 * (E : ℝ) * (N : ℝ) ^ 2 := by
  rw [par_eta]; push_cast; ring

private lemma par_dN_real (E N : ℕ) :
    ((parOf E N).dN : ℝ) = 48 * (E : ℝ) * (N : ℝ) ^ 2 := by
  rw [par_dN]; push_cast; ring

private lemma par_D2_real (E N : ℕ) : ((parOf E N).D2 : ℝ) = 8 * (E : ℝ) := by
  rw [par_D2]; push_cast; ring

private lemma TOf_real (E N : ℕ) :
    ((TOf E N : ℕ) : ℝ) = 1024 * (E : ℝ) ^ 2 * (N : ℝ) ^ 8 := by
  simp only [TOf]; push_cast; ring

private lemma pow_le_two_pow (n k : ℕ) : n ^ k ≤ 2 ^ (n * k) := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := n)).le k

private lemma pow_cond (E N : ℕ) (hE : 1 ≤ E) (hN : 2 ≤ N) :
    (N : ℝ) * (1 - 1 / ((parOf E N).dN : ℝ)) ^ (2 * (parOf E N).K) ≤
      1 / ((parOf E N).dN : ℝ) := by
  have hE0 : 0 < E := hE
  have hN0 : 0 < N := by omega
  rw [par_dN, par_K]
  obtain ⟨a, ha⟩ : ∃ a : ℕ, a = 48 * E * N ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = 48 * E + 3 * N := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hapos : 0 < a := by
    rw [ha]; exact Nat.mul_pos (Nat.mul_pos (by norm_num) hE0) (pow_pos hN0 2)
  have haR : (0 : ℝ) < a := by exact_mod_cast hapos
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast hapos
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
  have hab : a * b ≤ 2 * (a * b) := by
    have := Nat.zero_le (a * b)
    linarith
  have hmono : (1 - δ) ^ (2 * (a * b)) ≤ (1 - δ) ^ (a * b) :=
    pow_le_pow_of_le_one h0 h1 hab
  have hpowb : (1 - δ) ^ (a * b) ≤ (1 / 2) ^ b := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg h0 a) hhalf b
  have hnat : N * a ≤ 2 ^ b := by
    rw [ha, hb, pow_add]
    have h3 : N ^ 3 ≤ 2 ^ (3 * N) := by rw [mul_comm]; exact pow_le_two_pow N 3
    calc N * (48 * E * N ^ 2) = 48 * E * N ^ 3 := by ring
      _ ≤ 2 ^ (48 * E) * 2 ^ (3 * N) :=
          Nat.mul_le_mul (Nat.lt_two_pow_self (n := 48 * E)).le h3
  have hreal : (N : ℝ) * (a : ℝ) ≤ 2 ^ b := by exact_mod_cast hnat
  have hnR : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc (N : ℝ) * (1 - δ) ^ (2 * (a * b)) ≤ (N : ℝ) * (1 / 2) ^ b :=
        mul_le_mul_of_nonneg_left (hmono.trans hpowb) hnR
    _ ≤ δ := by
        rw [hδdef, one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) haR]
        linarith

private lemma err_real (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) :
    1 / (8 * x) + 6 * y ^ 2 / (48 * x * y ^ 2) +
      (y ^ 2 * (4096 * x ^ 2 * y ^ 8) / (2 * (16 * x * y ^ 2) * (1024 * x ^ 2 * y ^ 8)) +
        2 * y ^ 2 / (16 * x * y ^ 2) +
        y ^ 2 * (16 * x * y ^ 2 * (4 * y ^ 2) + 1) ^ 2 /
          (2 * (16 * x * y ^ 2) * (4096 * x ^ 2 * y ^ 8))) ≤ 5 / (8 * x) := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have t2 : 6 * y ^ 2 / (48 * x * y ^ 2) = 1 / (8 * x) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have t3 : y ^ 2 * (4096 * x ^ 2 * y ^ 8) / (2 * (16 * x * y ^ 2) * (1024 * x ^ 2 * y ^ 8)) =
      1 / (8 * x) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have t4 : 2 * y ^ 2 / (16 * x * y ^ 2) = 1 / (8 * x) := by
    rw [div_eq_div_iff (by positivity) (by positivity)]; ring
  have t5 : y ^ 2 * (16 * x * y ^ 2 * (4 * y ^ 2) + 1) ^ 2 /
      (2 * (16 * x * y ^ 2) * (4096 * x ^ 2 * y ^ 8)) ≤ 1 / (8 * x) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hy4 : 1 ≤ y ^ 4 := one_le_pow₀ hy
    have hxy : 1 ≤ x * y ^ 4 := by nlinarith
    have h65 : 16 * x * y ^ 2 * (4 * y ^ 2) + 1 ≤ 65 * (x * y ^ 4) := by
      have e : 16 * x * y ^ 2 * (4 * y ^ 2) = 64 * (x * y ^ 4) := by ring
      rw [e]; linarith
    have hsq : (16 * x * y ^ 2 * (4 * y ^ 2) + 1) ^ 2 ≤ (65 * (x * y ^ 4)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h65 2
    have hp : 0 ≤ x ^ 3 * y ^ 10 := by positivity
    calc y ^ 2 * (16 * x * y ^ 2 * (4 * y ^ 2) + 1) ^ 2 * (8 * x)
        ≤ y ^ 2 * (65 * (x * y ^ 4)) ^ 2 * (8 * x) := by gcongr
      _ = 33800 * (x ^ 3 * y ^ 10) := by ring
      _ ≤ 131072 * (x ^ 3 * y ^ 10) := by linarith
      _ = 1 * (2 * (16 * x * y ^ 2) * (4096 * x ^ 2 * y ^ 8)) := by ring
  have e5 : 5 / (8 * x) = 1 / (8 * x) + 1 / (8 * x) + (1 / (8 * x) + 1 / (8 * x) + 1 / (8 * x)) := by
    ring
  rw [t2, t3, t4, e5]
  linarith

private lemma err_cond (E N : ℕ) (hE : 1 ≤ E) (hN : 2 ≤ N) :
    1 / ((parOf E N).D2 : ℝ) + 6 * (N : ℝ) ^ 2 / ((parOf E N).dN : ℝ) +
      convErr N (parOf E N) (TOf E N) ≤ 5 / (8 * (E : ℝ)) := by
  have hx : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hy : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  rw [convErr, par_D_real, par_eta_real, par_dN_real, par_D2_real, TOf_real]
  exact err_real _ _ hx hy

theorem pgood (E N : ℕ) (hE : 1 ≤ E) (hN : 2 ≤ N) : PGood E N := by
  have hE0 : 0 < E := hE
  have hN0 : 0 < N := by omega
  have hEz : (0 : ℤ) < E := by exact_mod_cast hE0
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN0
  have hEq : (0 : ℚ) < E := by exact_mod_cast hE0
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN0
  refine
    { hD := ?_
      heta := ?_
      hdN := ?_
      hD2 := ?_
      hT := ?_
      hK := pow_cond E N hE hN
      herr := err_cond E N hE hN
      hG1 := ?_
      hG2 := ?_
      hG3 := ?_ }
  · rw [par_D]
    exact mul_pos (mul_pos (mul_pos (by norm_num) hEz) hEz) (pow_pos hNz 8)
  · rw [par_eta]
    exact mul_pos (mul_pos (by norm_num) hEq) (pow_pos hNq 2)
  · rw [par_dN]
    have h2 : 1 ≤ N ^ 2 := Nat.one_le_pow _ _ hN0
    have h3 : 1 * 1 ≤ E * N ^ 2 := Nat.mul_le_mul hE h2
    nlinarith
  · rw [par_D2]; omega
  · unfold TOf
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hE0) hE0) (pow_pos hN0 8)
  · rw [par_D_natAbs]
    calc N * (N * (4096 * E * E * N ^ 8) + 4096 * E * E * N ^ 8)
        ≤ N * (N * (4096 * E * E * N ^ 8) + N * (4096 * E * E * N ^ 8)) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hN0) _)
      _ = 8192 * E * E * N ^ 10 := by ring
      _ ≤ 2 ^ (8192 * E * E) * 2 ^ (N * 10) :=
          Nat.mul_le_mul (Nat.lt_two_pow_self (n := 8192 * E * E)).le (pow_le_two_pow N 10)
      _ = 2 ^ (8192 * E * E + N * 10) := by rw [pow_add]
  · rw [par_D_natAbs]
    calc 4096 * E * E * N ^ 8
        ≤ 2 ^ (4096 * E * E) * 2 ^ (N * 8) :=
          Nat.mul_le_mul (Nat.lt_two_pow_self (n := 4096 * E * E)).le (pow_le_two_pow N 8)
      _ < 2 ^ (4096 * E * E + 1) * 2 ^ (N * 8) :=
          mul_lt_mul_of_pos_right
            (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)) (by positivity)
      _ = 2 ^ (4096 * E * E + 1 + N * 8) := by rw [← pow_add]
  · rw [par_D2]
    calc 2 * (8 * E) ≤ 4096 * E * E := by nlinarith
      _ < 2 ^ (4096 * E * E) := Nat.lt_two_pow_self
      _ ≤ 2 ^ (4096 * E * E + 1 + N * 8) :=
          Nat.pow_le_pow_right (by norm_num)
            ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))

end QMCTied


