-- Prove2me | Definitions.Def_HodgeComputerSSR_BranchHelpers
-- name    : HodgeComputerSSR_BranchHelpers
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T10:21:32.996491+00:00
-- url     : https://prove2.me/theorems/dcfaff43-4d44-4d0e-adb3-7705493a8179
-- title:
--   Laurent branch homomorphisms `branchHom`, `br1_0`/`br2_0`, `P18_of_HahnC_eq`, and `BranchJetHelpersSpec`
-- statement:
--   Constructs the universal Laurent-series branch homomorphism `branchHom` (with `branchHom_eta_AC_of_eq`), the $U=0$ branches `br1_0`/`br2_0`, `W2_0_valDual`, `P18_of_HahnC_eq`, and the bundled jet-transport specification `BranchJetHelpersSpec`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L151-L393

import Definitions.Def_HodgeComputerFormal_CoverResidues
import Definitions.Def_HodgeComputerSSR_SheetCalculus
import Definitions.Def_HodgeComputerSSR_CoverParams
import Definitions.Def_HodgeComputerSSR_CoverFactors
import Definitions.Def_HodgeComputerSSR_CoverResidueDefs
import Definitions.Def_HodgeComputerSSR_BivEval

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field SymmetricSexticResidual.SheetCalculus
  SymmetricSexticResidual.CoverAlgebra SymmetricSexticResidual.CoverResidue
  PolynomialEncoding.KroneckerCheck QuadraticCovers CrossedRationalResidue Polynomial
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions
open scoped BigOperators LaurentSeries PowerSeries

abbrev ψ0 : RatFunc K5 →+* LaurentSeries K5 := CrossedRationalResidue.expansion (0 : K5)

lemma ψ0_C (c : K5) : ψ0 (RatFunc.C c) = HahnSeries.C c :=
  CrossedRationalResidue.expansion_C 0 c

lemma ψ0_X : ψ0 (RatFunc.X : RatFunc K5) = HahnSeries.single (1 : ℤ) (1 : K5) := by
  rw [← CrossedRationalResidue.uniformizer_zero]
  exact CrossedRationalResidue.expansion_uniformizer 0

lemma ψ0_toRat (P : K5[X]) : ψ0 (toRat P) = evalT P := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X, ψ0_C, ψ0_X,
      evalT_C, evalT_X]

/-- Total ring homomorphism `A_C →+* LaurentSeries K5` specializing `(U, W)` to a Laurent branch. -/
def branchHom (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) :
    A_C →+* LaurentSeries K5 :=
  AdjoinRoot.lift ψ W (by
    simp only [E0_poly, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    exact hW)

lemma branchHom_ιC_rat (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (f : RatFunc K5) :
    branchHom ψ W hW (ιC_rat f) = ψ f :=
  AdjoinRoot.lift_of _

lemma branchHom_W_C (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) :
    branchHom ψ W hW W_C = W :=
  AdjoinRoot.lift_root _

lemma branchHom_polyC (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (P : K5[X]) :
    branchHom ψ W hW (polyC P) = ψ (toRat P) :=
  branchHom_ιC_rat ψ W hW (toRat P)

lemma branchHom_pairC (ψ : RatFunc K5 →+* LaurentSeries K5) (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (x : PairAlg K5[X]) :
    branchHom ψ W hW (pairC x) = PairAlg.evalAt W (PairAlg.map (ψ.comp toRat) x) := by
  simp only [pairC, evalAC, PairAlg.evalAt, PairAlg.map, map_add, map_mul,
    branchHom_ιC_rat, branchHom_W_C, RingHom.comp_apply]

lemma branchHom_ιC_K5 (ψ : RatFunc K5 →+* LaurentSeries K5)
    (hψC : ∀ c : K5, ψ (RatFunc.C c) = HahnSeries.C c)
    (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) (c : K5) :
    branchHom ψ W hW (ιC_K5 c) = HahnSeries.C c := by
  change branchHom ψ W hW (ιC_rat (RatFunc.C c)) = HahnSeries.C c
  rw [branchHom_ιC_rat, hψC]

/-- Universal two-branch trace splitting into `LaurentSeries K5`. -/
lemma map_trace_AC_eq_sum_branches (ψ : RatFunc K5 →+* LaurentSeries K5)
    (W1 W2 : LaurentSeries K5)
    (hW1 : W1 ^ 2 + ψ (toRat k5Params.bW) * W1 + ψ (toRat k5Params.cW) = 0)
    (hW2 : W2 ^ 2 + ψ (toRat k5Params.bW) * W2 + ψ (toRat k5Params.cW) = 0)
    (hsum : W1 + W2 = -ψ (toRat k5Params.bW)) (x : A_C) :
    ψ (Algebra.trace (RatFunc K5) A_C x) =
      branchHom ψ W1 hW1 x + branchHom ψ W2 hW2 x := by
  rw [← evalAC_coordsAC x, trace_AC_evalAC]
  simp only [evalAC, map_add, map_sub, map_mul, map_ofNat, branchHom_ιC_rat, branchHom_W_C]
  linear_combination -ψ (coordsAC x).c1 * hsum

/-- Transport `eta_AC` across `branchHom` directly into `LaurentSeries K5`. -/
lemma branchHom_eta_AC (ψ : RatFunc K5 →+* LaurentSeries K5)
    (hψC : ∀ c : K5, ψ (RatFunc.C c) = HahnSeries.C c)
    (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0) :
    let U := ψ RatFunc.X
    let V := W / U
    let fP := ψ.comp toRat
    let ca := fP k5Params.ca_h
    let cb := fP k5Params.cb_h
    let c0W := PairAlg.evalAt W (PairAlg.map fP k5Params.c0W)
    let d2_2 := PairAlg.evalAt W (PairAlg.map fP k5Params.d2_2)
    let d2_1 := PairAlg.evalAt W (PairAlg.map fP k5Params.d2_1)
    let d2_0 := PairAlg.evalAt W (PairAlg.map fP k5Params.d2_0)
    let d1 := PairAlg.evalAt W (PairAlg.map fP k5Params.d1_z)
    let d0 := PairAlg.evalAt W (PairAlg.map fP k5Params.d0_z)
    let res := PairAlg.evalAt W (PairAlg.map fP k5Params.res_z)
    let g : LaurentSeries K5 → LaurentSeries K5 := fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K)
        (z / W) (-(ca * z + c0W) / (W * cb)) U V
    let p := interp4 g
    let P1 := remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1
    let P0 := remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2
    branchHom ψ W hW eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W + fP k5Params.bW) * fP k5Params.Q5_z ^ 3 * res) := by
  intro U V fP ca cb c0W d2_2 d2_1 d2_0 d1 d0 res g p P1 P0
  let br := branchHom ψ W hW
  have hbr_K5 : ∀ c : K5, br (ιC_K5 c) = HahnSeries.C c := branchHom_ιC_K5 ψ hψC W hW
  have hbr_U : br U_C = U := branchHom_ιC_rat ψ W hW RatFunc.X
  have hbr_W : br W_C = W := branchHom_W_C ψ W hW
  have hbr_V : br V_C = V := by simp only [V_C, map_div₀, hbr_W, hbr_U, V]
  have hbr_poly : ∀ P : K5[X], br (polyC P) = fP P := branchHom_polyC ψ W hW
  have hbr_pair : ∀ x : PairAlg K5[X], br (pairC x) = PairAlg.evalAt W (PairAlg.map fP x) :=
    branchHom_pairC ψ W hW
  have hbr_P18 : ∀ z : A_C, br (P18_z_AC z) = g (br z) := by
    intro z
    simp only [P18_z_AC, g, P18_of, A_0U, A_0V, A_Y, A_X, numM, q1_a2, q1_a1, q1_a0,
      q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ, H0_of, A1_of, B1_of, cA1_of, dA1_fn, dH0_fn,
      dot_ab, QY_num, QX_num, Omega_F, dDX2_F, dDY2_F, F_contract, dF5_fn, dDX2_fn, dDY2_fn,
      DX2_of, DY2_of, u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, EB_of,
      W2_of, u_of, v_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat,
      map_one, map_zero, hbr_K5, hbr_U, hbr_W, hbr_V, hbr_poly, hbr_pair, ca, cb, c0W]
  have hint : (br (interp4 P18_z_AC).1, br (interp4 P18_z_AC).2.1,
      br (interp4 P18_z_AC).2.2.1, br (interp4 P18_z_AC).2.2.2.1,
      br (interp4 P18_z_AC).2.2.2.2) = p :=
    map_interp4 br P18_z_AC g hbr_P18
  have hp4 : br (interp4 P18_z_AC).1 = p.1 := congrArg Prod.fst hint
  have hp3 : br (interp4 P18_z_AC).2.1 = p.2.1 := congrArg (fun t => t.2.1) hint
  have hp2 : br (interp4 P18_z_AC).2.2.1 = p.2.2.1 := congrArg (fun t => t.2.2.1) hint
  have hp1 : br (interp4 P18_z_AC).2.2.2.1 = p.2.2.2.1 := congrArg (fun t => t.2.2.2.1) hint
  have hp0 : br (interp4 P18_z_AC).2.2.2.2 = p.2.2.2.2 := congrArg (fun t => t.2.2.2.2) hint
  change br eta_AC = _
  simp only [eta_AC, eta_AC_num, remDeg4_P1, remDeg4_P0, map_div₀, map_mul, map_sub, map_add,
    map_neg, map_pow, map_ofNat, hbr_K5, hbr_U, hbr_W, hbr_poly, hbr_pair,
    hp4, hp3, hp2, hp1, hp0]
  rfl

lemma branchHom_eta_AC_of_eq (ψ : RatFunc K5 →+* LaurentSeries K5)
    (hψC : ∀ c : K5, ψ (RatFunc.C c) = HahnSeries.C c)
    (W : LaurentSeries K5)
    (hW : W ^ 2 + ψ (toRat k5Params.bW) * W + ψ (toRat k5Params.cW) = 0)
    (U : LaurentSeries K5) (hU : ψ RatFunc.X = U)
    (fP : K5[X] →+* LaurentSeries K5) (hfP : ψ.comp toRat = fP)
    (V ca cb c0W d2_2 d2_1 d2_0 d1 d0 res : LaurentSeries K5)
    (g : LaurentSeries K5 → LaurentSeries K5)
    (p : LaurentSeries K5 × LaurentSeries K5 × LaurentSeries K5 × LaurentSeries K5 × LaurentSeries K5)
    (P1 P0 : LaurentSeries K5)
    (hV : V = W / U) (hca : ca = fP k5Params.ca_h) (hcb : cb = fP k5Params.cb_h)
    (hc0W : c0W = PairAlg.evalAt W (PairAlg.map fP k5Params.c0W))
    (hd2_2 : d2_2 = PairAlg.evalAt W (PairAlg.map fP k5Params.d2_2))
    (hd2_1 : d2_1 = PairAlg.evalAt W (PairAlg.map fP k5Params.d2_1))
    (hd2_0 : d2_0 = PairAlg.evalAt W (PairAlg.map fP k5Params.d2_0))
    (hd1 : d1 = PairAlg.evalAt W (PairAlg.map fP k5Params.d1_z))
    (hd0 : d0 = PairAlg.evalAt W (PairAlg.map fP k5Params.d0_z))
    (hres : res = PairAlg.evalAt W (PairAlg.map fP k5Params.res_z))
    (hg : g = fun z =>
      P18_of (HahnSeries.C S_K) (HahnSeries.C Q_K) (HahnSeries.C T_K)
        (HahnSeries.C x_K) (HahnSeries.C y_K)
        (z / W) (-(ca * z + c0W) / (W * cb)) U V)
    (hp : p = interp4 g)
    (hP1 : P1 = remDeg4_P1 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.1)
    (hP0 : P0 = remDeg4_P0 d2_2 d2_1 d2_0 p.1 p.2.1 p.2.2.1 p.2.2.2.2) :
    branchHom ψ W hW eta_AC =
      (-(P1 * d0 - P0 * d1) * U ^ 3 * W * cb ^ 4) /
      (81 * HahnSeries.C k5Params.Av0 * (2 * W + fP k5Params.bW) * fP k5Params.Q5_z ^ 3 * res) := by
  let br := branchHom ψ W hW
  have hbr_K5 : ∀ c : K5, br (ιC_K5 c) = HahnSeries.C c := branchHom_ιC_K5 ψ hψC W hW
  have hbr_U : br U_C = U := (branchHom_ιC_rat ψ W hW RatFunc.X).trans hU
  have hbr_W : br W_C = W := branchHom_W_C ψ W hW
  have hbr_V : br V_C = V := by simp only [V_C, map_div₀, hbr_W, hbr_U, hV]
  have hbr_poly : ∀ P : K5[X], br (polyC P) = fP P := fun P =>
    (branchHom_polyC ψ W hW P).trans (congrArg (fun φ : K5[X] →+* LaurentSeries K5 => φ P) hfP)
  have hbr_pair : ∀ x : PairAlg K5[X], br (pairC x) = PairAlg.evalAt W (PairAlg.map fP x) := fun x => by
    rw [branchHom_pairC ψ W hW x, hfP]
  have hbr_P18 : ∀ z : A_C, br (P18_z_AC z) = g (br z) := by
    intro z
    rw [hg]
    simp only [P18_z_AC, P18_of, A_0U, A_0V, A_Y, A_X, numM, q1_a2, q1_a1, q1_a0,
      q2_b2, q2_b1, q2_b0, dH_dS, dH_dQ, H0_of, A1_of, B1_of, cA1_of, dA1_fn, dH0_fn,
      dot_ab, QY_num, QX_num, Omega_F, dDX2_F, dDY2_F, F_contract, dF5_fn, dDX2_fn, dDY2_fn,
      DX2_of, DY2_of, u3_of, v3_of, om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, EB_of,
      W2_of, u_of, v_of, map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat,
      map_one, map_zero, hbr_K5, hbr_U, hbr_W, hbr_V, hbr_poly, hbr_pair, hca, hcb, hc0W]
  have hint : (br (interp4 P18_z_AC).1, br (interp4 P18_z_AC).2.1,
      br (interp4 P18_z_AC).2.2.1, br (interp4 P18_z_AC).2.2.2.1,
      br (interp4 P18_z_AC).2.2.2.2) = p :=
    (map_interp4 br P18_z_AC g hbr_P18).trans hp.symm
  have hp4 : br (interp4 P18_z_AC).1 = p.1 := congrArg Prod.fst hint
  have hp3 : br (interp4 P18_z_AC).2.1 = p.2.1 := congrArg (fun t => t.2.1) hint
  have hp2 : br (interp4 P18_z_AC).2.2.1 = p.2.2.1 := congrArg (fun t => t.2.2.1) hint
  have hp1 : br (interp4 P18_z_AC).2.2.2.1 = p.2.2.2.1 := congrArg (fun t => t.2.2.2.1) hint
  have hp0 : br (interp4 P18_z_AC).2.2.2.2 = p.2.2.2.2 := congrArg (fun t => t.2.2.2.2) hint
  have hbr_P1 : br (remDeg4_P1 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
      (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1 (interp4 P18_z_AC).2.2.2.1) = P1 := by
    rw [hP1]
    simp only [remDeg4_P1, map_sub, map_mul, map_pow,
      hbr_pair, hp4, hp3, hp2, hp1, hd2_2, hd2_1, hd2_0]
  have hbr_P0 : br (remDeg4_P0 (pairC k5Params.d2_2) (pairC k5Params.d2_1) (pairC k5Params.d2_0)
      (interp4 P18_z_AC).1 (interp4 P18_z_AC).2.1 (interp4 P18_z_AC).2.2.1 (interp4 P18_z_AC).2.2.2.2) = P0 := by
    rw [hP0]
    simp only [remDeg4_P0, map_sub, map_mul, map_pow,
      hbr_pair, hp4, hp3, hp2, hp0, hd2_2, hd2_1, hd2_0]
  change br eta_AC = _
  simp only [eta_AC, eta_AC_num, map_div₀, map_mul, map_sub, map_add,
    map_neg, map_pow, map_ofNat, hbr_K5, hbr_U, hbr_W, hbr_poly, hbr_pair,
    hbr_P1, hbr_P0, hcb, hd1, hd0, hres]


lemma quadU_coeff_zero {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).coeff 0 = a0 := by simp [CoverParams.quadU]

lemma quadU_coeff_one {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).coeff 1 = a1 := by simp [CoverParams.quadU]

lemma quadU_coeff_two {R : Type*} [CommRing R] (a0 a1 a2 : R) :
    (CoverParams.quadU a0 a1 a2).coeff 2 = a2 := by simp [CoverParams.quadU]

/-! ### Section 2: Exact `Dual K5` Analysis of `W2_0` and `res_z` Nonvanishing on Both Branches -/

lemma W1_0_eq_ψ0 : W1_0 ^ 2 + ψ0 (toRat k5Params.bW) * W1_0 + ψ0 (toRat k5Params.cW) = 0 := by
  rw [ψ0_toRat, ψ0_toRat]; exact W1_0_eq

lemma W2_0_eq_ψ0 : W2_0 ^ 2 + ψ0 (toRat k5Params.bW) * W2_0 + ψ0 (toRat k5Params.cW) = 0 := by
  rw [ψ0_toRat, ψ0_toRat]; exact W2_0_eq

lemma W1_W2_0_sum_ψ0 : W1_0 + W2_0 = -ψ0 (toRat k5Params.bW) := by
  rw [ψ0_toRat]; exact W1_W2_0_sum

abbrev br1_0 : A_C →+* LaurentSeries K5 := branchHom ψ0 W1_0 W1_0_eq_ψ0
abbrev br2_0 : A_C →+* LaurentSeries K5 := branchHom ψ0 W2_0 W2_0_eq_ψ0

lemma W2_0_coeff1 : W2_0.coeff 1 = -(k5Params.Bv1 * k5Params.Av0_inv) := by
  rw [W2_0, HahnSeries.coeff_sub, HahnSeries.coeff_neg, HasValGe_W1_0 1 (by omega), sub_zero,
    evalT_bW_eq]
  change -(HahnSeries.ofPowerSeries ℤ K5 b0PS).coeff (1 : ℕ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  simp only [b0PS, map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X,
    PowerSeries.coeff_X_pow, mul_assoc]
  norm_num

lemma W2_0_valDual :
    ValDual 0 W2_0 ⟨-(k5Params.Bv0 * k5Params.Av0_inv), -(k5Params.Bv1 * k5Params.Av0_inv)⟩ :=
  ⟨HasValGe_W2_0, W2_0_coeff0, W2_0_coeff1⟩

lemma evalT_toUW_valDual_W2 (v0 v1 v2 : K5) :
    let w0 := -(k5Params.Bv0 * k5Params.Av0_inv)
    let w1 := -(k5Params.Bv1 * k5Params.Av0_inv)
    ValDual 0 (PairAlg.evalAt W2_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2)))
      (Dual.C v2 * (⟨w0, w1⟩ : Dual K5) ^ 2 + Dual.C v1 * ⟨0, 1⟩ * ⟨w0, w1⟩) := by
  intro w0 w1
  have heq : PairAlg.evalAt W2_0 (PairAlg.map evalT (k5Params.toUW v0 v1 v2)) =
      HahnSeries.C v2 * W2_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0 +
      HahnSeries.C v0 * HahnSeries.single 2 1 := by
    simp only [PairAlg.evalAt, PairAlg.map, CoverParams.toUW, map_sub, map_mul, map_pow,
      evalT_C, evalT_X, HahnSeries.single_pow]
    have h2p : (2 : ℕ) • (1 : ℤ) = 2 := by decide
    simp only [one_pow, h2p]
    linear_combination -HahnSeries.C v2 * W2_0_eq
  rw [heq]
  have h1 : ValDual 0 (HahnSeries.C v2 * W2_0 ^ 2) (Dual.C v2 * (⟨w0, w1⟩ : Dual K5) ^ 2) := by
    simpa only [zero_add, mul_zero] using (ValDual.of_C v2).mul (W2_0_valDual.pow 2)
  have h2 : ValLead 1 (HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0) (v1 * w0) := by
    have ha := ((ValLead.of_C v1).mul (ValLead.of_single 1 1)).mul W2_0_valDual.toValLead
    simpa only [zero_add, add_zero, mul_one] using ha
  have h3 : HasValGe 2 (HahnSeries.C v0 * HahnSeries.single 2 1) := by
    simpa only [zero_add] using (HasValGe.of_C v0).mul (HasValGe.single 2 (1 : K5))
  have h12 : ValDual 0 (HahnSeries.C v2 * W2_0 ^ 2 + HahnSeries.C v1 * HahnSeries.single 1 1 * W2_0)
      (Dual.C v2 * (⟨w0, w1⟩ : Dual K5) ^ 2 + Dual.C v1 * ⟨0, 1⟩ * ⟨w0, w1⟩) := by
    refine (h1.add_shift1 h2).eq_d ?_
    ext <;> simp [Dual.C]
  exact h12.add_high h3

-- Exact `U = 0` scalar polynomial `ValDual 0` helpers
lemma quadU_valDual (a0 a1 a2 : K5) :
    ValDual 0 (evalT (CoverParams.quadU a0 a1 a2)) ⟨a0, a1⟩ := by
  simpa only [quadU_coeff_zero, quadU_coeff_one] using ValDual.of_evalT (CoverParams.quadU a0 a1 a2)


lemma hasValGe_div_nat_mul {k : ℤ} {f : LaurentSeries K5} (p q : ℕ) (hf : HasValGe k f) :
    HasValGe k (((p : LaurentSeries K5) / (q : LaurentSeries K5)) * f) := by
  rw [show ((p : LaurentSeries K5) / (q : LaurentSeries K5)) = HahnSeries.C ((p : K5) / (q : K5)) by
    simp only [map_div₀, map_natCast]]
  exact ((HasValGe.of_C _).mul hf).mono (by omega)

lemma hasValGe_neg_div_nat_mul {k : ℤ} {f : LaurentSeries K5} (p q : ℕ) (hf : HasValGe k f) :
    HasValGe k (-((p : LaurentSeries K5) / (q : LaurentSeries K5)) * f) := by
  rw [show -((p : LaurentSeries K5) / (q : LaurentSeries K5)) = HahnSeries.C (-((p : K5) / (q : K5))) by
    simp only [map_div₀, map_neg, map_natCast]]
  exact ((HasValGe.of_C _).mul hf).mono (by omega)


lemma map_EB_of {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (S Q T x y U V : R) :
    EB_of (f S) (f Q) (f T) (f x) (f y) (f U) (f V) = f (EB_of S Q T x y U V) := by
  simp only [EB_of, W2_of, DX2_of, DY2_of, dF5_fn, br_fn, LX_of, LY_of,
    dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
    map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat, map_one, map_zero]

lemma map_QY_num {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (S Q T x y U V : R) (i : Fin 3) :
    QY_num (f S) (f Q) (f T) (f x) (f y) (f U) (f V) i = f (QY_num S Q T x y U V i) := by
  fin_cases i <;>
    simp only [QY_num, Omega_F, dDX2_F, F_contract, dF5_fn, dH0_fn, dDX2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]

lemma map_QX_num {R R' : Type*} [Field R] [Field R'] (f : R →+* R')
    (S Q T x y U V : R) (i : Fin 3) :
    QX_num (f S) (f Q) (f T) (f x) (f y) (f U) (f V) i = f (QX_num S Q T x y U V i) := by
  fin_cases i <;>
    simp only [QX_num, Omega_F, dDY2_F, F_contract, dF5_fn, dH0_fn, dDY2_fn, DX2_of, DY2_of,
      om_fn, br_fn, LX_of, LY_of, dLX_fn, dLY_fn, u3_of, v3_of, u_of, v_of,
      map_add, map_sub, map_mul, map_div₀, map_neg, map_pow, map_ofNat, map_zero, map_one]

lemma EB_of_zero_zero {F : Type*} [Field F] [CharZero F] (S Q T x y : F) :
    EB_of S Q T x y 0 0 = 0 := by
  simp only [EB_of, br_fn, dLX_fn, dLY_fn]; ring


def dHS_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (s q : R) : Dual R :=
  ⟨ι (-(25 / 243 : K5)) * (5 * s - 9 * q) * (15 * s - 9 * q),
   ι (143 / 81 : K5) * s ^ 2 - ι (184 / 27 : K5) * s * q + ι (52 / 9 : K5) * q ^ 2⟩

def dHQ_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (s q : R) (v0 : K5) : Dual R :=
  ⟨ι (50 / 27 : K5) * s * (5 * s - 9 * q),
   ι (-(92 / 27 : K5)) * s ^ 2 + ι (104 / 9 : K5) * s * q - ι (22 / 3 : K5) * q ^ 2 +
     ι ((10 / 7 : K5) * v0) * q + ι ((10 / 7 : K5) * v0 ^ 2)⟩

def numM_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (mi : Fin 10) (a b : R) : R :=
  let ξS := ι S_K - a * ι T_K
  let ξQ := ι Q_K - b * ι T_K
  let a2 := dHS_12_of ι a b; let a0 := dHS_12_of ι ξS ξQ
  let a1 := dHS_12_of ι (a + ξS) (b + ξQ) - a2 - a0
  let b2 := dHQ_12_of ι a b 0; let b0 := dHQ_12_of ι ξS ξQ 1
  let b1 := dHQ_12_of ι (a + ξS) (b + ξQ) 0 - b2 - dHQ_12_of ι ξS ξQ 0 + ⟨0, ι (10 / 7 : K5) * b⟩
  let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
  let (m2, m1, m0) : R × R × R := match mi with
    | 0 => (a ^ 2, 2 * a * ξS, ξS ^ 2)
    | 1 => (a * b, a * ξQ + b * ξS, ξS * ξQ)
    | 2 => (b ^ 2, 2 * b * ξQ, ξQ ^ 2)
    | 3 => (a, ξS, 0)
    | 4 => (0, a, ξS)
    | 5 => (b, ξQ, 0)
    | 6 => (0, b, ξQ)
    | 7 => (1, 0, 0)
    | 8 => (0, 1, 0)
    | 9 => (0, 0, 1)
  ι (1 / 16 : K5) * (m2 * d10.eps - m1 * d20.eps + m0 * d21.eps)

def A0U_12_of {R : Type*} [CommRing R] (ι : K5 →+* R) (a b : R) : R :=
  let m := fun i => numM_12_of ι i a b
  ι (-(19708 / 1257375 : K5)) * (5 * m 0 - 9 * m 1) +
  ι (1472 / 1257375 : K5) * (5 * m 1 - 9 * m 2) -
  ι (16 / 729 : K5) * (5 * m 3 - 9 * m 5) +
  ι (188 / 2025 : K5) * (5 * m 4 - 9 * m 6)

lemma map_numM_12_of {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') (ι : K5 →+* R) (mi : Fin 10) (a b : R) :
    f (numM_12_of ι mi a b) = numM_12_of (f.comp ι) mi (f a) (f b) := by
  fin_cases mi <;>
    simp only [numM_12_of, dHS_12_of, dHQ_12_of, Dual.add_val, Dual.add_eps, Dual.sub_val, Dual.sub_eps,
      Dual.mul_eps, map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero, map_one,
      RingHom.comp_apply]

lemma map_A0U_12_of {R R' : Type*} [CommRing R] [CommRing R']
    (f : R →+* R') (ι : K5 →+* R) (a b : R) :
    f (A0U_12_of ι a b) = A0U_12_of (f.comp ι) (f a) (f b) := by
  simp only [A0U_12_of, map_add, map_sub, map_mul, map_ofNat, RingHom.comp_apply, map_numM_12_of]


lemma P18_of_HahnC_eq (S Q T x y : K5) (a b U V : LaurentSeries K5) :
    P18_of (R := LaurentSeries K5) (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) (HahnSeries.C x) (HahnSeries.C y) a b U V =
    (A_0U a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V / U +
     A_0V a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V / V) *
      (H0_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) *
        A1_of (HahnSeries.C S) (HahnSeries.C Q) U V *
        (dot_ab (QY_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
          (HahnSeries.C x) (HahnSeries.C y) U V) a b / v_of V) +
       H0_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) *
        B1_of (HahnSeries.C T) U V *
        (dot_ab (QX_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
          (HahnSeries.C x) (HahnSeries.C y) U V) a b / u_of U) +
       (cA1_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) a b U V / v_of V) *
        EB_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
          (HahnSeries.C x) (HahnSeries.C y) U V) +
    (A_Y a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V *
      (dot_ab (QY_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
        (HahnSeries.C x) (HahnSeries.C y) U V) a b / v_of V) +
     A_X a b (HahnSeries.C S - a * HahnSeries.C T) (HahnSeries.C Q - b * HahnSeries.C T) U V *
      (dot_ab (QX_num (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T)
        (HahnSeries.C x) (HahnSeries.C y) U V) a b / u_of U)) *
    H0_of (HahnSeries.C S) (HahnSeries.C Q) (HahnSeries.C T) ^ 2 := by
  unfold P18_of
  congr 1


/-- Bundled `ValLead`/`ValDual`/bilinear sheet-numerator jet helpers shared across local residue branches. -/
structure BranchJetHelpersSpec : Prop where
  numM_ValLead : ∀ {k1 : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {a0 b0 ξS0 ξQ0 a2_0 a1_0 a0_0 b2_0 b1_0 b0_0 : K5},
    ValLead 0 a_s a0 → ValLead 0 b_s b0 →
    ValLead 0 ξS_s ξS0 → ValLead 0 ξQ_s ξQ0 →
    ValLead k1 (q1_a2 a_s b_s U V) a2_0 →
    ValLead k1 (q1_a1 a_s b_s ξS_s ξQ_s U V) a1_0 →
    ValLead k1 (q1_a0 ξS_s ξQ_s U V) a0_0 →
    ValLead k1 (q2_b2 a_s b_s U V) b2_0 →
    ValLead k1 (q2_b1 a_s b_s ξS_s ξQ_s U V) b1_0 →
    ValLead k1 (q2_b0 ξS_s ξQ_s U V) b0_0 → ∀ mi : Fin 10,
    ValLead (2 * k1) (numM mi a_s b_s ξS_s ξQ_s U V)
      (let (c2, c1, c0) : K5 × K5 × K5 := match mi with
        | 0 => (a0 ^ 2, 2 * a0 * ξS0, ξS0 ^ 2)
        | 1 => (a0 * b0, a0 * ξQ0 + b0 * ξS0, ξS0 * ξQ0)
        | 2 => (b0 ^ 2, 2 * b0 * ξQ0, ξQ0 ^ 2)
        | 3 => (a0, ξS0, 0) | 4 => (0, a0, ξS0)
        | 5 => (b0, ξQ0, 0) | 6 => (0, b0, ξQ0)
        | 7 => (1, 0, 0) | 8 => (0, 1, 0) | 9 => (0, 0, 1)
       (1 / 16 : K5) * (c2 * (a1_0 * b0_0 - a0_0 * b1_0) -
         c1 * (a2_0 * b0_0 - a0_0 * b2_0) + c0 * (a2_0 * b1_0 - a1_0 * b2_0)))
  numM_ValDual : ∀ {k1 : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5}
    {aD bD ξSD ξQD a2D a1D a0D b2D b1D b0D : Dual K5},
    ValDual 0 a_s aD → ValDual 0 b_s bD →
    ValDual 0 ξS_s ξSD → ValDual 0 ξQ_s ξQD →
    ValDual k1 (q1_a2 a_s b_s U V) a2D →
    ValDual k1 (q1_a1 a_s b_s ξS_s ξQ_s U V) a1D →
    ValDual k1 (q1_a0 ξS_s ξQ_s U V) a0D →
    ValDual k1 (q2_b2 a_s b_s U V) b2D →
    ValDual k1 (q2_b1 a_s b_s ξS_s ξQ_s U V) b1D →
    ValDual k1 (q2_b0 ξS_s ξQ_s U V) b0D → ∀ mi : Fin 10,
    ValDual (2 * k1) (numM mi a_s b_s ξS_s ξQ_s U V)
      (let (c2, c1, c0) : Dual K5 × Dual K5 × Dual K5 := match mi with
        | 0 => (aD ^ 2, 2 * aD * ξSD, ξSD ^ 2)
        | 1 => (aD * bD, aD * ξQD + bD * ξSD, ξSD * ξQD)
        | 2 => (bD ^ 2, 2 * bD * ξQD, ξQD ^ 2)
        | 3 => (aD, ξSD, 0) | 4 => (0, aD, ξSD)
        | 5 => (bD, ξQD, 0) | 6 => (0, bD, ξQD)
        | 7 => (1, 0, 0) | 8 => (0, 1, 0) | 9 => (0, 0, 1)
       Dual.C (1 / 16 : K5) * (c2 * (a1D * b0D - a0D * b1D) -
         c1 * (a2D * b0D - a0D * b2D) + c0 * (a2D * b1D - a1D * b2D)))
  A0U_ValLead : ∀ {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5} {c : Fin 10 → K5},
    (∀ i, ValLead k (numM i a_s b_s ξS_s ξQ_s U V) (c i)) →
    ValLead k (A_0U a_s b_s ξS_s ξQ_s U V)
      (-(19708 / 1257375 : K5) * (5 * c 0 - 9 * c 1) +
       (1472 / 1257375 : K5) * (5 * c 1 - 9 * c 2) -
       (16 / 729 : K5) * (5 * c 3 - 9 * c 5) +
       (188 / 2025 : K5) * (5 * c 4 - 9 * c 6))
  A0V_ValLead : ∀ {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5} {c : Fin 10 → K5},
    (∀ i, ValLead k (numM i a_s b_s ξS_s ξQ_s U V) (c i)) →
    ValLead k (A_0V a_s b_s ξS_s ξQ_s U V)
      (-(892 / 3645 : K5) * (5 * c 3 - 9 * c 4) +
       (40 / 81 : K5) * (5 * c 5 - 9 * c 6) -
       (112 / 2395 : K5) * (5 * c 7 - 9 * c 8) +
       (392 / 11975 : K5) * (5 * c 8 - 9 * c 9))
  A0U_ValDual : ∀ {k : ℤ} {a_s b_s ξS_s ξQ_s U V : LaurentSeries K5} {d : Fin 10 → Dual K5},
    (∀ i, ValDual k (numM i a_s b_s ξS_s ξQ_s U V) (d i)) →
    ValDual k (A_0U a_s b_s ξS_s ξQ_s U V)
      (Dual.C (-(19708 / 1257375 : K5)) * (5 * d 0 - 9 * d 1) +
       Dual.C (1472 / 1257375 : K5) * (5 * d 1 - 9 * d 2) -
       Dual.C (16 / 729 : K5) * (5 * d 3 - 9 * d 5) +
       Dual.C (188 / 2025 : K5) * (5 * d 4 - 9 * d 6))
  dual_minor_pair_const : ∀ {R : Type} [Field R]
    (aD bD xSD xQD wD u1 u0 : Dual R) (da2 da1 da0 db2 db1 db0 : R),
    let mk := fun (a b xS xQ w u1' u0' : Dual R) =>
      let dHS0 := fun s q : Dual R => Dual.C (-(25 / 243 : R)) * (5 * s - 9 * q) * (15 * s - 9 * q) * w
      let dHQ0 := fun s q : Dual R => Dual.C (50 / 27 : R) * s * (5 * s - 9 * q) * w
      let A2 := dHS0 a b; let A0 := dHS0 xS xQ; let A1 := dHS0 (a + xS) (b + xQ) - A2 - A0
      let B2 := dHQ0 a b; let B0 := dHQ0 xS xQ; let B1 := dHQ0 (a + xS) (b + xQ) - B2 - B0
      let a2 := A2 + ⟨0, da2⟩; let a1 := A1 + ⟨0, da1⟩; let a0 := A0 + ⟨0, da0⟩
      let b2 := B2 + ⟨0, db2⟩; let b1 := B1 + ⟨0, db1⟩; let b0 := B0 + ⟨0, db0⟩
      let d20 := a2 * b0 - a0 * b2; let d21 := a2 * b1 - a1 * b2; let d10 := a1 * b0 - a0 * b1
      let m2 := u1' * (5 * a - 9 * b)
      let m1 := u1' * (5 * xS - 9 * xQ) + u0' * (5 * a - 9 * b)
      let m0 := u0' * (5 * xS - 9 * xQ)
      m2 * d10 - m1 * d20 + m0 * d21
    mk aD bD xSD xQD wD u1 u0 =
      ⟨0, (mk (Dual.C aD.val) (Dual.C bD.val) (Dual.C xSD.val) (Dual.C xQD.val)
        (Dual.C wD.val) (Dual.C u1.val) (Dual.C u0.val)).eps⟩
  EB_bilinear : ∀ {R : Type} [Field R] [CharZero R] (S Q T x y U V : R),
    EB_of S Q T x y U V = EB_of S Q T x y 0 0 +
      (EB_of S Q T x y 0 1 - EB_of S Q T x y 0 0) * V +
      (EB_of S Q T x y 1 0 - EB_of S Q T x y 0 0) * U +
      (EB_of S Q T x y 1 1 - EB_of S Q T x y 1 0 - EB_of S Q T x y 0 1 + EB_of S Q T x y 0 0) * U * V
  QY_bilinear : ∀ {R : Type} [Field R] [CharZero R] (S Q T x y U V : R) (i : Fin 3),
    QY_num S Q T x y U V i = QY_num S Q T x y 0 0 i +
      (QY_num S Q T x y 0 1 i - QY_num S Q T x y 0 0 i) * V +
      (QY_num S Q T x y 1 0 i - QY_num S Q T x y 0 0 i) * U +
      (QY_num S Q T x y 1 1 i - QY_num S Q T x y 1 0 i - QY_num S Q T x y 0 1 i + QY_num S Q T x y 0 0 i) * U * V
  QX_bilinear : ∀ {R : Type} [Field R] [CharZero R] (S Q T x y U V : R) (i : Fin 3),
    QX_num S Q T x y U V i = QX_num S Q T x y 0 0 i +
      (QX_num S Q T x y 0 1 i - QX_num S Q T x y 0 0 i) * V +
      (QX_num S Q T x y 1 0 i - QX_num S Q T x y 0 0 i) * U +
      (QX_num S Q T x y 1 1 i - QX_num S Q T x y 1 0 i - QX_num S Q T x y 0 1 i + QX_num S Q T x y 0 0 i) * U * V
  QX_num_01_sub_00 : ∀ {R : Type} [Field R] [CharZero R] (S Q T x y a b : R),
    (T - 3) * ((QX_num S Q T x y 0 1 0 - QX_num S Q T x y 0 0 0) * a +
      (QX_num S Q T x y 0 1 1 - QX_num S Q T x y 0 0 1) * b +
      (QX_num S Q T x y 0 1 2 - QX_num S Q T x y 0 0 2)) =
    (80 / 81 : R) * x * T ^ 2 * S ^ 2 * (T - 3) ^ 3 *
      (23 * S ^ 3 - 82 * S ^ 2 * Q + 71 * S * Q ^ 2 + 4 * Q ^ 3 -
        50 * S ^ 2 * x + 90 * S * Q * x + 27 * S * x ^ 2) *
      ((T - 3) * (-(5 * S - 3 * Q) * a + 6 * S * b) + S * (5 * S - 9 * Q))

end SymmetricSexticResidual.LocalResidueU0


