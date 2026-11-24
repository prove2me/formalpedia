-- Prove2me | Definitions.Def_HodgeComputerSSR_LocalInfCore
-- name    : HodgeComputerSSR_LocalInfCore
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T18:22:48.176528+00:00
-- url     : https://prove2.me/theorems/f1daaa40-687a-4d8b-a8ca-546371a58072
-- title:
--   Infinity expansion $\psi_\infty$, branches `br1_inf`/`br2_inf`, and `LocalInfWeightsSpec`
-- statement:
--   Proves $L_K \neq 0$, constructs the $U = \infty$ expansion $\psi_\infty = \psi_0 \circ \operatorname{reciprocal}$ and branch homomorphisms `br1_inf`, `br2_inf`, proves `P1_d0_sub_P0_d1_split` and `interp4_p4_mul`, and states `LocalInfWeightsSpec`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueInf.lean#L1-L328

import Definitions.Def_HodgeComputerSSR_BranchHelpers
import Definitions.Def_HodgeComputerSSR_LocalInfAlgDefs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
namespace SymmetricSexticResidual.LocalResidueInf
open Polynomial
open scoped LaurentSeries PowerSeries
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  SymmetricSexticResidual.LocalResidueU0 SymmetricSexticResidual.LocalResidueInfAlg
  QuadraticCovers

lemma L_K_ne_zero : L_K ≠ 0 := by
  have hL : L_K = poly4ToK5 (77 * MvPolynomial.X 0 - 210 * MvPolynomial.X 1 + 45) := by
    simp only [map_add, map_sub, map_mul, map_ofNat]; rfl
  rw [hL]
  apply poly4ToK5_ne_zero
  intro h0
  have hv := congrArg (MvPolynomial.eval (0 : Fin 4 → ℂ)) h0
  simp only [map_add, map_sub, map_mul, map_ofNat, map_zero, MvPolynomial.eval_X, Pi.zero_apply, mul_zero, sub_zero, zero_add] at hv
  exact (by norm_num : (45 : ℂ) ≠ 0) hv

lemma coeff_quadU {R : Type*} [CommRing R] (a0 a1 a2 : R) (n : ℕ) :
    (CoverParams.quadU a0 a1 a2).coeff n =
      match n with | 0 => a0 | 1 => a1 | 2 => a2 | _ => 0 := by
  unfold CoverParams.quadU
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · simp


noncomputable def ψinf : RatFunc K5 →+* LaurentSeries K5 :=
  ψ0.comp CrossedRationalResidue.reciprocal.toRingHom

lemma ψinf_C (c : K5) : ψinf (RatFunc.C c) = HahnSeries.C c := by
  change ψ0 (CrossedRationalResidue.reciprocal (RatFunc.C c)) = HahnSeries.C c
  rw [CrossedRationalResidue.reciprocal_C, ψ0_C]

lemma ψinf_X : ψinf (RatFunc.X : RatFunc K5) = HahnSeries.single (-1 : ℤ) (1 : K5) := by
  change ψ0 (CrossedRationalResidue.reciprocal (RatFunc.X : RatFunc K5)) = HahnSeries.single (-1 : ℤ) (1 : K5)
  rw [CrossedRationalResidue.reciprocal_X, map_inv₀, ψ0_X]
  have h : HahnSeries.single (1 : ℤ) (1 : K5) * HahnSeries.single (-1 : ℤ) (1 : K5) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  exact inv_eq_of_mul_eq_one_right h

lemma ψinf_toRat (P : K5[X]) : ψinf (toRat P) = evalInvT P := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow]
    simp only [toRat, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      ψinf_C, ψinf_X, map_mul, map_pow, evalInvT_C, evalInvT_X]

lemma ValLead.of_ofNat (n : ℕ) [n.AtLeastTwo] :
    ValLead 0 (no_index (OfNat.ofNat n) : LaurentSeries K5) (no_index (OfNat.ofNat n) : K5) := by
  simpa only [map_ofNat] using ValLead.of_C (OfNat.ofNat n : K5)

lemma HasValGe.of_ofNat (n : ℕ) [n.AtLeastTwo] :
    HasValGe 0 (no_index (OfNat.ofNat n) : LaurentSeries K5) := by
  simpa only [map_ofNat] using HasValGe.of_C (OfNat.ofNat n : K5)

lemma ValDual.of_ofNat (n : ℕ) [n.AtLeastTwo] :
    ValDual 0 (no_index (OfNat.ofNat n) : LaurentSeries K5) (Dual.C (OfNat.ofNat n : K5)) := by
  simpa only [map_ofNat] using ValDual.of_C (OfNat.ofNat n : K5)

lemma valLead_eq_fc {k : ℤ} {f g : LaurentSeries K5} {a b : K5}
    (hf : ValLead k f a) (hfg : f = g) (hab : a = b) : ValLead k g b := hfg ▸ hab ▸ hf

lemma valDual_eq_fd {k : ℤ} {f g : LaurentSeries K5} {a b : Dual K5}
    (hf : ValDual k f a) (hfg : f = g) (hab : a = b) : ValDual k g b := hfg ▸ hab ▸ hf

lemma hasValGe_eq_f {k : ℤ} {f g : LaurentSeries K5}
    (hf : HasValGe k f) (hfg : f = g) : HasValGe k g := hfg ▸ hf


lemma infinityCoefficient_eq_coeff_one (f : RatFunc K5) :
    CrossedRationalResidue.infinityCoefficient f = (ψinf f).coeff 1 := by
  change CrossedRationalResidue.residue 0 ((RatFunc.X ^ 2)⁻¹ * CrossedRationalResidue.reciprocal f) =
    (ψ0 (CrossedRationalResidue.reciprocal f)).coeff 1
  change (ψ0 ((RatFunc.X ^ 2)⁻¹ * CrossedRationalResidue.reciprocal f)).coeff (-1) =
    (ψ0 (CrossedRationalResidue.reciprocal f)).coeff 1
  rw [map_mul, map_inv₀, map_pow, ψ0_X]
  have hinv : (HahnSeries.single (1 : ℤ) (1 : K5) ^ 2)⁻¹ = HahnSeries.single (-2 : ℤ) (1 : K5) := by
    apply inv_eq_of_mul_eq_one_right
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single]; simp
  rw [hinv, HahnSeries.coeff_single_mul]
  simp

lemma W1_inf_eq_ψinf :
    W1_inf ^ 2 + ψinf (toRat k5Params.bW) * W1_inf + ψinf (toRat k5Params.cW) = 0 := by
  rw [ψinf_toRat, ψinf_toRat]; exact W1_inf_eq

lemma W2_inf_eq_ψinf :
    W2_inf ^ 2 + ψinf (toRat k5Params.bW) * W2_inf + ψinf (toRat k5Params.cW) = 0 := by
  rw [ψinf_toRat, ψinf_toRat]; exact W2_inf_eq

lemma W1_W2_inf_sum_ψinf : W1_inf + W2_inf = -ψinf (toRat k5Params.bW) := by
  rw [ψinf_toRat]; exact W1_W2_inf_sum

noncomputable def br1_inf : A_C →+* LaurentSeries K5 :=
  branchHom ψinf W1_inf W1_inf_eq_ψinf

noncomputable def br2_inf : A_C →+* LaurentSeries K5 :=
  branchHom ψinf W2_inf W2_inf_eq_ψinf

/-! ### Section 3: `W1_inf` Dual Expansion, Weights, and `res_z_W2_inf_val_ne` -/


lemma evalInvT_toUW_valLead_W1 (v0 v1 v2 : K5) :
    ValLead (-2) (PairAlg.evalAt W1_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2))) v0 := by
  have heq : PairAlg.evalAt W1_inf (PairAlg.map evalInvT (k5Params.toUW v0 v1 v2)) =
      HahnSeries.C v0 * HahnSeries.single (-2) 1 +
      (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W1_inf + HahnSeries.C v2 * W1_inf ^ 2) := by
    simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
      evalInvT_C, evalInvT_X, HahnSeries.single_pow]
    have h2p : (2 : ℕ) • (-1 : ℤ) = -2 := by decide
    simp only [one_pow, h2p]
    linear_combination -HahnSeries.C v2 * W1_inf_eq
  rw [heq]
  have h0 : ValLead (-2) (HahnSeries.C v0 * HahnSeries.single (-2) 1) v0 :=
    ((ValLead.of_C v0).mul (ValLead.of_single (-2) 1)).eq_k (by omega) |>.eq_c (mul_one v0)
  have h1 : HasValGe (-1) (HahnSeries.C v1 * HahnSeries.single (-1) 1 * W1_inf + HahnSeries.C v2 * W1_inf ^ 2) :=
    ((((HasValGe.of_C v1).mul (HasValGe.single (-1) 1)).mul HasValGe_W1_inf).mono (by omega)).add
      (((HasValGe.of_C v2).mul (HasValGe_W1_inf.pow 2)).mono (by omega))
  exact h0.add_high h1

lemma natDegree_quadU_le {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).natDegree ≤ 2 := by
  unfold CoverParams.quadU
  exact (Polynomial.natDegree_add_le _ _).trans (max_le
    ((Polynomial.natDegree_add_le _ _).trans (max_le (by simp)
      ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans (by omega)))))
    ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le 2)))

lemma deg2_q11 : k5Params.q11.natDegree ≤ 2 := natDegree_quadU_le _ _ _
lemma deg2_q02 : k5Params.q02.natDegree ≤ 2 := natDegree_quadU_le _ _ _
lemma deg2_c21 : k5Params.c21.natDegree ≤ 2 := natDegree_quadU_le _ _ _
lemma deg2_c12 : k5Params.c12.natDegree ≤ 2 := natDegree_quadU_le _ _ _
lemma deg2_c03 : k5Params.c03.natDegree ≤ 2 := natDegree_quadU_le _ _ _
lemma deg2_ca : k5Params.ca_h.natDegree ≤ 2 := natDegree_quadU_le _ _ _
lemma deg2_cb : k5Params.cb_h.natDegree ≤ 2 := natDegree_quadU_le _ _ _

lemma coeff_mul_top2 (a b : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) :
    (a * b).coeff 4 = a.coeff 2 * b.coeff 2 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.coeff i * b.coeff j),
    Finset.sum_eq_single 2]
  · intro i _ hi2; by_cases hgt : 2 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < 4 - i), mul_zero]
  · intro h; simp at h

lemma coeff_mul_top3 (a b c : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2) :
    (a * b * c).coeff 6 = a.coeff 2 * b.coeff 2 * c.coeff 2 := by
  have hbc : (b * c).natDegree ≤ 4 := (Polynomial.natDegree_mul_le).trans (by omega)
  rw [mul_assoc, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.coeff i * (b * c).coeff j),
    Finset.sum_eq_single 2]
  · rw [show 6 - 2 = 4 by rfl, coeff_mul_top2 b c hb hc]; ring
  · intro i _ hi2; by_cases hgt : 2 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < i), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : (b * c).natDegree < 6 - i), mul_zero]
  · intro h; simp at h

lemma natDegree_mul3_le (a b c : K5[X]) (ha : a.natDegree ≤ 2) (hb : b.natDegree ≤ 2) (hc : c.natDegree ≤ 2) :
    (a * b * c).natDegree ≤ 6 :=
  (Polynomial.natDegree_mul_le).trans (by have := Polynomial.natDegree_mul_le (p := a) (q := b); omega)

lemma k5Params_p21_natDegree_le :
    (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).natDegree ≤ 3 := by
  have hle4 : (-k5Params.q11 * k5Params.cb_h + 2 * k5Params.q02 * k5Params.ca_h).natDegree ≤ 4 := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_neg]; linarith [deg2_q11, deg2_cb])
    · rw [mul_assoc, show (2 : K5[X]) = C 2 from (map_ofNat C 2).symm]
      exact (Polynomial.natDegree_C_mul_le 2 _).trans (Polynomial.natDegree_mul_le.trans (by linarith [deg2_q02, deg2_ca]))
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h4 : n = 4
  · subst h4
    rw [Polynomial.coeff_add, neg_mul, Polynomial.coeff_neg, mul_assoc,
      show (2 : K5[X]) * (k5Params.q02 * k5Params.ca_h) = C 2 * (k5Params.q02 * k5Params.ca_h) by rw [map_ofNat],
      Polynomial.coeff_C_mul, coeff_mul_top2 _ _ deg2_q11 deg2_cb, coeff_mul_top2 _ _ deg2_q02 deg2_ca]
    simp only [CoverParams.q11, CoverParams.q02, CoverParams.ca_h, CoverParams.cb_h, coeff_quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3]; ring
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma k5Params_p31_natDegree_le :
    (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).natDegree ≤ 3 := by
  have hle4 : (k5Params.c12 * k5Params.cb_h - 3 * k5Params.c03 * k5Params.ca_h).natDegree ≤ 4 := by
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by linarith [deg2_c12, deg2_cb])
    · rw [mul_assoc, show (3 : K5[X]) = C 3 from (map_ofNat C 3).symm]
      exact (Polynomial.natDegree_C_mul_le 3 _).trans (Polynomial.natDegree_mul_le.trans (by linarith [deg2_c03, deg2_ca]))
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h4 : n = 4
  · subst h4
    rw [Polynomial.coeff_sub, mul_assoc,
      show (3 : K5[X]) * (k5Params.c03 * k5Params.ca_h) = C 3 * (k5Params.c03 * k5Params.ca_h) by rw [map_ofNat],
      Polynomial.coeff_C_mul, coeff_mul_top2 _ _ deg2_c12 deg2_cb, coeff_mul_top2 _ _ deg2_c03 deg2_ca]
    simp only [CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h, coeff_quadU,
      CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3]; ring
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

lemma k5Params_p32_natDegree_le :
    (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 5 := by
  have hle6 : (-k5Params.c21 * k5Params.cb_h ^ 2 + 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h -
      3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
    have h1 : (-k5Params.c21 * k5Params.cb_h ^ 2).natDegree ≤ 6 := by
      rw [show -k5Params.c21 * k5Params.cb_h ^ 2 = -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) by ring,
        Polynomial.natDegree_neg]
      exact natDegree_mul3_le _ _ _ deg2_c21 deg2_cb deg2_cb
    have h2 : (2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h).natDegree ≤ 6 := by
      rw [show 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h = C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) by rw [map_ofNat]; ring]
      exact (Polynomial.natDegree_C_mul_le 2 _).trans (natDegree_mul3_le _ _ _ deg2_c12 deg2_ca deg2_cb)
    have h3 : (3 * k5Params.c03 * k5Params.ca_h ^ 2).natDegree ≤ 6 := by
      rw [show 3 * k5Params.c03 * k5Params.ca_h ^ 2 = C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) by rw [map_ofNat]; ring]
      exact (Polynomial.natDegree_C_mul_le 3 _).trans (natDegree_mul3_le _ _ _ deg2_c03 deg2_ca deg2_ca)
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le h1 h2)) h3)
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  by_cases h6 : n = 6
  · subst h6
    rw [Polynomial.coeff_sub, Polynomial.coeff_add,
      show -k5Params.c21 * k5Params.cb_h ^ 2 = -(k5Params.c21 * k5Params.cb_h * k5Params.cb_h) by ring,
      show 2 * k5Params.c12 * k5Params.ca_h * k5Params.cb_h = C 2 * (k5Params.c12 * k5Params.ca_h * k5Params.cb_h) by rw [map_ofNat]; ring,
      show 3 * k5Params.c03 * k5Params.ca_h ^ 2 = C 3 * (k5Params.c03 * k5Params.ca_h * k5Params.ca_h) by rw [map_ofNat]; ring,
      Polynomial.coeff_neg, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      coeff_mul_top3 _ _ _ deg2_c21 deg2_cb deg2_cb,
      coeff_mul_top3 _ _ _ deg2_c12 deg2_ca deg2_cb,
      coeff_mul_top3 _ _ _ deg2_c03 deg2_ca deg2_ca]
    simp only [CoverParams.c21, CoverParams.c12, CoverParams.c03, CoverParams.ca_h, CoverParams.cb_h,
      coeff_quadU, CoverParams.inv9, CoverParams.inv27, CoverParams.inv81, k5Params_inv3]; ring
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

-- Exact decomposition of `remDeg4_P1 * d0 - remDeg4_P0 * d1` as a linear combination of `p4..p0`:
lemma P1_d0_sub_P0_d1_split {R : Type*} [CommRing R] (q2 q1 q0 d1 d0 p4 p3 p2 p1 p0 : R) :
    remDeg4_P1 q2 q1 q0 p4 p3 p2 p1 * d0 - remDeg4_P0 q2 q1 q0 p4 p3 p2 p0 * d1 =
      ((-q1 ^ 3 + 2 * q2 * q1 * q0) * d0 - (-q1 ^ 2 * q0 + q2 * q0 ^ 2) * d1) * p4 +
      ((q2 * (q1 ^ 2 - q2 * q0)) * d0 - (q2 * q1 * q0) * d1) * p3 +
      ((-q2 ^ 2 * q1) * d0 - (-q2 ^ 2 * q0) * d1) * p2 +
      (q2 ^ 3 * d0) * p1 +
      (-q2 ^ 3 * d1) * p0 := by
  simp only [remDeg4_P1, remDeg4_P0]; ring

-- Bundle of `W1_inf` dual weights `A4[3], A4[4], A3[4], A2[4]`, `HasValGe 5 A1, A0`, and `res_z` valuation!

lemma interp4_add_p4 {R : Type*} [Field R] [CharZero R] (f g : R → R) :
    (interp4 (fun z => f z + g z)).1 = (interp4 f).1 + (interp4 g).1 := by
  unfold interp4; ring

lemma interp4_p4_mul {R : Type*} [Field R] [CharZero R] {f h : R → R}
    (hf : IsPolyDeg 3 f) (hh : IsPolyDeg 1 h) :
    (interp4 (fun z => f z * h z)).1 = ((f 2 - 3 * f 1 + 3 * f 0 - f (-1)) / 6) * (h 1 - h 0) := by
  rcases hf with ⟨P, hP, heP⟩
  rcases hh with ⟨Q, hQ, heQ⟩
  have hfeq (z : R) : f z = P.coeff 0 + P.coeff 1 * z + P.coeff 2 * z ^ 2 + P.coeff 3 * z ^ 3 := by
    rw [heP z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]; ring
  have hheq (z : R) : h z = Q.coeff 0 + Q.coeff 1 * z := by
    rw [heQ z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQ)]
    rw [Finset.sum_range_succ, Finset.sum_range_one]; ring
  unfold interp4
  simp only [hfeq, hheq]; ring


/-- Bundled `W1_inf`/`W2_inf` Laurent weight, resultant, and `numM_Uk` jet bounds. -/
structure LocalInfWeightsSpec : Prop where
  W1_valDual : ValDual 0 W1_inf ⟨-(k5Params.Cv0 / k5Params.Bv2), k5Params.Cv0 * k5Params.Bv1 / k5Params.Bv2 ^ 2⟩
  W1_weights :
    let d2_2 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_2)
    let d2_1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_1)
    let d2_0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d2_0)
    let d1 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d1_z)
    let d0 := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.d0_z)
    let res := PairAlg.evalAt W1_inf (PairAlg.map evalInvT k5Params.res_z)
    let pref := -(HahnSeries.single (-1 : ℤ) (1 : K5) ^ 3 * W1_inf * evalInvT k5Params.cb_h ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W1_inf + evalInvT k5Params.bW) * evalInvT k5Params.Q5_z ^ 3 * res)
    let A4 := pref * ((-d2_1 ^ 3 + 2 * d2_2 * d2_1 * d2_0) * d0 - (-d2_1 ^ 2 * d2_0 + d2_2 * d2_0 ^ 2) * d1)
    let A3 := pref * ((d2_2 * (d2_1 ^ 2 - d2_2 * d2_0)) * d0 - (d2_2 * d2_1 * d2_0) * d1)
    let A2 := pref * ((-d2_2 ^ 2 * d2_1) * d0 - (-d2_2 ^ 2 * d2_0) * d1)
    let A1 := pref * (d2_2 ^ 3 * d0)
    let A0 := pref * (-d2_2 ^ 3 * d1)
    let S3Q := S_K - 3 * Q_K; let T59 := 5 * T_K - 9
    ValDual 3 A4
      ⟨-(279006525 / 64 : K5) * T_K * T59 ^ 2 / (S3Q ^ 8 * L_K),
       (13286025 / 12544 : K5) * T_K * T59 ^ 2 * P44_fn S_K Q_K T_K / (S3Q ^ 11 * L_K ^ 2)⟩ ∧
    ValLead 4 A3 ((531441 / 448 : K5) * T_K * T59 * (35 * S_K * T_K + 133 * S_K - 420 * Q_K + 225 * T_K - 45) / S3Q ^ 8) ∧
    ValLead 4 A2 (-(177147 / 400 : K5) * T_K / S3Q ^ 5) ∧
    HasValGe 5 A1 ∧ HasValGe 5 A0 ∧ HasValGe (-32) res ∧ res.coeff (-32) ≠ 0
  res_W2_val_ne :
    HasValGe (-41) (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)) ∧
    (PairAlg.evalAt W2_inf (PairAlg.map evalInvT k5Params.res_z)).coeff (-41) ≠ 0
  numM_Uk_valLead : ∀ (k : Fin 4) (mi : Fin 10)
    {a_s b_s ξS_s ξQ_s : LaurentSeries K5} {a0 b0 ξS0 ξQ0 : K5},
    ValLead 0 a_s a0 → ValLead 0 b_s b0 → ValLead 0 ξS_s ξS0 → ValLead 0 ξQ_s ξQ0 →
    ValLead 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s) (numM_Uk k mi a0 b0 ξS0 ξQ0)
  numM_Uk_hasValGe : ∀ (k : Fin 4) (mi : Fin 10) {a_s b_s ξS_s ξQ_s : LaurentSeries K5},
    HasValGe 0 a_s → HasValGe 0 b_s → HasValGe 0 ξS_s → HasValGe 0 ξQ_s →
    HasValGe 0 (numM_Uk k mi a_s b_s ξS_s ξQ_s)

end SymmetricSexticResidual.LocalResidueInf


