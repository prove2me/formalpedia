-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateOrder13_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_TateOrder13_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:48:34.578974+00:00
-- url     : https://prove2.me/theorems/d94d2ae6-cd48-40c6-8183-af21144d2cac
-- title:
--   FLT.Assumptions.MazurProof.TateOrder13 source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.TateOrder13

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.TateOrder13
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNFDivision_p0
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_TateNormalFormBridge_p0
import Definitions.Def_MazurN13_KeystoneInterface

set_option autoImplicit false




/-!
# The concrete order-13 Tate-normal-form condition

Parallels `TateOrder11`: connects the Tate-normal-form bridge, the
division-polynomial recurrence, and the explicit identity
`ψ₁₃(0,0) = -b⁵⁶ F₁₃(b,c)`.

A rational point of exact order 13 yields concrete Tate parameters
with `b ≠ 0` and `F13 b c = 0`.
-/

open Polynomial
open scoped WeierstrassCurve.Affine

namespace MazurProof.TateOrder13

open Scratch.TateZ2xZ10Reduction

noncomputable section

 abbrev W (b c : ℚ) : WeierstrassCurve ℚ :=
  tateNormalFormCurve b c

 theorem psi_ne_zero_rat (W : WeierstrassCurve ℚ) :
    ∀ m : ℤ, m ≠ 0 → W.ψ m ≠ 0 := by
  have hψ₂_ne : W.ψ₂ ≠ 0 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact ne_of_apply_ne Polynomial.natDegree (by
      rw [Polynomial.natDegree_linear
        (Polynomial.C_ne_zero.mpr (two_ne_zero (α := ℚ))),
        Polynomial.natDegree_zero]
      omega)
  have hψ₂_deg : W.ψ₂.natDegree ≤ 1 := by
    rw [WeierstrassCurve.ψ₂, WeierstrassCurve.Affine.polynomialY]
    exact Polynomial.natDegree_linear_le
  have hPsi_ne : ∀ n : ℕ, n ≠ 0 → W.Ψ (n : ℤ) ≠ 0 := by
    intro n hn
    rw [WeierstrassCurve.Ψ_ofNat]
    have hC : Polynomial.C (W.preΨ' n) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (W.preΨ'_ne_zero (Nat.cast_ne_zero.mpr hn))
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      exact mul_ne_zero hC hψ₂_ne
    · simp only [heven, ↓reduceIte, mul_one]
      exact hC
  have hPsi_deg : ∀ n : ℕ, n ≠ 0 →
      (W.Ψ (n : ℤ)).natDegree < W.toAffine.polynomial.natDegree := by
    intro n _
    rw [WeierstrassCurve.Affine.natDegree_polynomial,
      WeierstrassCurve.Ψ_ofNat]
    by_cases heven : Even n
    · simp only [heven, ↓reduceIte]
      calc
        (Polynomial.C (W.preΨ' n) * W.ψ₂).natDegree
            ≤ 0 + 1 := Polynomial.natDegree_mul_le |>.trans
              (Nat.add_le_add (Polynomial.natDegree_C _).le hψ₂_deg)
        _ < 2 := by omega
    · simp only [heven, ↓reduceIte, mul_one]
      have hdeg : (Polynomial.C (W.preΨ' n)).natDegree = 0 :=
        Polynomial.natDegree_C _
      omega
  intro m hm hpsi
  suffices hPsi :
      WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine (W.Ψ m) ≠ 0 by
    exact hPsi (by
      rw [← WeierstrassCurve.Affine.CoordinateRing.mk_ψ, hpsi, map_zero])
  rcases m with n | n
  · exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne n (by intro h; exact hm (by simp [h])))
      (hPsi_deg n (by intro h; exact hm (by simp [h])))
  · rw [show (Int.negSucc n : ℤ) = -(↑(n + 1) : ℤ) by
        simp [Int.negSucc_eq],
      WeierstrassCurve.Ψ_neg, map_neg, neg_ne_zero]
    exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      WeierstrassCurve.Affine.monic_polynomial
      (hPsi_ne _ (Nat.succ_ne_zero n))
      (hPsi_deg _ (Nat.succ_ne_zero n))

 theorem nsmul_eq_zero_iff_PsiSq_eval
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    {n : ℕ} {x y : ℚ} (h : (W⁄ℚ).Nonsingular x y) :
    n • (WeierstrassCurve.Affine.Point.some x y h : (W⁄ℚ).Point) = 0 ↔
      (W.ΨSq (n : ℤ)).eval x = 0 := by
  have h4 : (4 : ℚ) ≠ 0 := by norm_num
  have hc3 : W.Ψ₃ ≠ 0 :=
    WeierstrassCurve.Ψ₃_ne_zero W (by norm_num)
  have key := KeystoneLadder.nsmul_eq_zero_iff_ΨSq_eval
    W h4 (psi_ne_zero_rat W) hc3 (n := n) h
  convert key using 3
  congr
  exact Subsingleton.elim _ _

 lemma eval_prePsi_five (b c : ℚ) :
    ((W b c).preΨ' 5).eval 0 =
      ((W b c).preΨ₄).eval 0 * ((W b c).Ψ₂Sq.eval 0) ^ 2 -
        ((W b c).Ψ₃.eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 0)
  simpa using h

 lemma eval_prePsi_six (b c : ℚ) :
    ((W b c).preΨ' 6).eval 0 =
      ((W b c).preΨ' 3).eval 0 * ((W b c).preΨ' 5).eval 0 -
        ((W b c).preΨ' 3).eval 0 * (((W b c).preΨ' 4).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 0)
  simpa using h

 lemma eval_prePsi_seven (b c : ℚ) :
    ((W b c).preΨ' 7).eval 0 =
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 3).eval 0) ^ 3 -
        ((W b c).preΨ' 4).eval 0 ^ 3 * ((W b c).Ψ₂Sq.eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 1)
  simpa using h

 lemma eval_prePsi_eight (b c : ℚ) :
    ((W b c).preΨ' 8).eval 0 =
      (((W b c).preΨ' 3).eval 0) ^ 2 * ((W b c).preΨ' 4).eval 0 *
        ((W b c).preΨ' 6).eval 0 -
      ((W b c).preΨ' 4).eval 0 * (((W b c).preΨ' 5).eval 0) ^ 2 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_even 1)
  simpa using h

 lemma eval_prePsi_thirteen (b c : ℚ) :
    ((W b c).preΨ' 13).eval 0 =
      ((W b c).preΨ' 8).eval 0 * (((W b c).preΨ' 6).eval 0) ^ 3 *
        ((W b c).Ψ₂Sq.eval 0) ^ 2 -
      ((W b c).preΨ' 5).eval 0 * (((W b c).preΨ' 7).eval 0) ^ 3 := by
  have h := congrArg (fun p : ℚ[X] ↦ p.eval 0) ((W b c).preΨ'_odd 4)
  simpa [show Even (4 : ℕ) by decide] using h

set_option maxHeartbeats 800000 in
theorem prePsi_thirteen_eval_tate_origin (b c : ℚ) :
    ((W b c).preΨ' 13).eval 0 =
      -(b ^ 56 * TateNFDivision.F13 b c) := by
  rw [eval_prePsi_thirteen, eval_prePsi_eight, eval_prePsi_seven,
    eval_prePsi_six, eval_prePsi_five]
  simp [W, tateNormalFormCurve, WeierstrassCurve.preΨ'_three,
    WeierstrassCurve.preΨ'_four, WeierstrassCurve.Ψ₂Sq,
    WeierstrassCurve.Ψ₃, WeierstrassCurve.preΨ₄,
    WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, TateNFDivision.F13, TateNFDivision.F8]
  ring

 lemma tate_origin_nonsingular
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Nonsingular (W b c) 0 0 := by
  apply WeierstrassCurve.Affine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [W]

def tateOrigin (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    WeierstrassCurve.Affine.Point (W b c) :=
  WeierstrassCurve.Affine.Point.some 0 0 (tate_origin_nonsingular b c)

 lemma tateOrigin_eq_normalized_origin
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)] :
    tateOrigin b c = TateNormalFormBridge.tateOrigin b c := by
  change WeierstrassCurve.Affine.Point.some 0 0 _ =
    WeierstrassCurve.Affine.Point.some 0 0 _
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

theorem F13_eq_zero_of_tateOrigin_order_thirteen
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (hb : b ≠ 0) (hord : addOrderOf (tateOrigin b c) = 13) :
    TateNFDivision.F13 b c = 0 := by
  have h13 : (13 : ℕ) • tateOrigin b c = 0 := by
    simpa [hord] using addOrderOf_nsmul_eq_zero (tateOrigin b c)
  have hPsiSq : ((W b c).ΨSq (13 : ℤ)).eval 0 = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mp h13
  have hpre : ((W b c).preΨ' 13).eval 0 = 0 := by
    change ((W b c).ΨSq (13 : ℕ)).eval 0 = 0 at hPsiSq
    rw [(W b c).ΨSq_ofNat 13] at hPsiSq
    simpa [show ¬ Even (13 : ℕ) by decide] using hPsiSq
  rw [prePsi_thirteen_eval_tate_origin] at hpre
  have hpre' : b ^ 56 * TateNFDivision.F13 b c = 0 := neg_eq_zero.mp hpre
  exact (mul_eq_zero.mp hpre').resolve_left (pow_ne_zero 56 hb)

theorem tateOrigin_order_thirteen_of_F13_eq_zero
    (b c : ℚ) [WeierstrassCurve.IsElliptic (W b c)]
    (_hb : b ≠ 0) (hF13 : TateNFDivision.F13 b c = 0) :
    addOrderOf (tateOrigin b c) = 13 := by
  have hpre : ((W b c).preΨ' 13).eval 0 = 0 := by
    rw [prePsi_thirteen_eval_tate_origin, hF13, mul_zero, neg_zero]
  have hPsiSq : ((W b c).ΨSq (13 : ℤ)).eval 0 = 0 := by
    change ((W b c).ΨSq (13 : ℕ)).eval 0 = 0
    rw [(W b c).ΨSq_ofNat 13]
    simp [show ¬ Even (13 : ℕ) by decide, hpre]
  have h13 : (13 : ℕ) • tateOrigin b c = 0 :=
    (nsmul_eq_zero_iff_PsiSq_eval (W b c)
      (tate_origin_nonsingular b c)).mpr hPsiSq
  have hne : tateOrigin b c ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero _
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  exact addOrderOf_eq_prime h13 hne


end
end MazurProof.TateOrder13


