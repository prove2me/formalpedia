-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
-- name    : GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PXiMetric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:22.178581+00:00
-- url     : https://prove2.me/theorems/56db1df7-9277-45a4-a10b-e7fce88bddae
-- title:
--   PXi Metric
-- statement:
--   Definitions and structural lemmas for PXi Metric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PXiMetric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open scoped ComplexOrder
set_option linter.unusedSectionVars false
noncomputable section
namespace XiMetricSmoothness
section Tens
variable {κ : Type} [Fintype κ]
def tensQ (G : Matrix κ κ ℂ) (u : κ × κ → ℂ) : ℝ :=
  (star u ⬝ᵥ (Matrix.kronecker G G *ᵥ u)).re
theorem tensQ_smul (G : Matrix κ κ ℂ) (c : ℂ) (u : κ × κ → ℂ) :
    tensQ G (c • u) = ‖c‖ ^ 2 * tensQ G u := by
  unfold tensQ
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]
  have : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
theorem tensQ_pos {G : Matrix κ κ ℂ} (hG : G.PosDef) {u : κ × κ → ℂ} (hu : u ≠ 0) : 0 < tensQ G u :=
  (Complex.pos_iff.1 ((hG.kronecker hG).dotProduct_mulVec_pos hu)).1
theorem tensQ_nonneg {G : Matrix κ κ ℂ} (hG : G.PosDef) (u : κ × κ → ℂ) : 0 ≤ tensQ G u := by
  by_cases hu : u = 0
  · subst hu
    simp [tensQ]
  · exact (tensQ_pos hG hu).le
end Tens
section Form
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {n : WithTop ℕ∞}
end Form
section Poly
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
def evC (f : MRing ι) (w : (Σ k, ι k) → ℂ) : ℂ :=
  eval w (map (Int.castRingHom ℂ) f)
theorem evC_smul {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (c : K → ℂ) (w : (Σ k, ι k) → ℂ) :
    evC f (fun p => c p.1 * w p) = (∏ k, c k ^ a k) * evC f w := by
  unfold evC
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring
end Poly
section Line
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
abbrev YPt (ι ν κ : Type) := (Σ k, T.yyIdx ι ν κ k) → ℂ
def ynorm (w : YPt ι ν κ) : ℝ := ∑ i : ι, ‖w ⟨.base, i⟩‖ ^ 2
def dnorm (w : YPt ι ν κ) : ℝ := ∑ l : ν, ‖w ⟨.det, l⟩‖ ^ 2
def ypow (N : ℕ) (w : YPt ι ν κ) : ℝ := ∑ i : ι, (‖w ⟨.base, i⟩‖ ^ 2) ^ N
def lineV (w : YPt ι ν κ) : κ → ℂ := fun k => w ⟨.line, k⟩
def hv (G : YPt ι ν κ → Matrix κ κ ℂ) (w : YPt ι ν κ) : ℝ := (hermG (G w) (lineV w) (lineV w)).re
def numF (G : YPt ι ν κ → Matrix κ κ ℂ) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) (w : YPt ι ν κ) : ℝ :=
  ∑ i, ∑ l, tensQ (G w) (fun p => evC (F i l p.1 p.2) w)
def remR (N : ℕ) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) : ℝ :=
  ynorm w ^ (N + 3) * ∑ j, ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det)
def ratio (G : YPt ι ν κ → Matrix κ κ ℂ) (N : ℕ) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) {q : ℕ}
    (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) : ℝ :=
  (numF G F w + remR N r b w) / (2 * (ypow N w * dnorm w))
def xiH (G : YPt ι ν κ → Matrix κ κ ℂ) (N : ℕ) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) {q : ℕ}
    (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) : ℝ :=
  Real.sqrt (ratio G N F r b w) / hv G w
theorem prodY {M : Type*} [CommMonoid M] (f : T.YBlk → M) : ∏ k, f k = f .base * (f .det * f .line) := by
  rw [show (Finset.univ : Finset T.YBlk) = {.base, .det, .line} from rfl]
  simp
section Pos
variable {w : YPt ι ν κ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
include hw
theorem ynorm_pos : 0 < ynorm w := by
  obtain ⟨i, hi⟩ := hw .base
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
theorem dnorm_pos : 0 < dnorm w := by
  obtain ⟨i, hi⟩ := hw .det
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩
theorem ypow_pos (N : ℕ) : 0 < ypow N w := by
  obtain ⟨i, hi⟩ := hw .base
  exact Finset.sum_pos' (fun j _ => pow_nonneg (sq_nonneg _) _)
    ⟨i, Finset.mem_univ _, pow_pos (pow_pos (norm_pos_iff.2 hi) 2) N⟩
theorem lineV_ne : lineV w ≠ 0 := by
  obtain ⟨i, hi⟩ := hw .line
  intro h0
  exact hi (congrFun h0 i)
theorem hv_pos {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : ∀ w, (G w).PosDef) : 0 < hv G w :=
  (Complex.pos_iff.1 ((hG w).dotProduct_mulVec_pos (lineV_ne hw))).1
end Pos
theorem remR_nonneg (N : ℕ) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ) (w : YPt ι ν κ) :
    0 ≤ remR N r b w := by
  have hy : 0 ≤ ynorm w := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hd : 0 ≤ dnorm w := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact mul_nonneg (pow_nonneg hy _) (Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hy _) (pow_nonneg hd _)))
theorem numF_nonneg {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : ∀ w, (G w).PosDef) (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ))
    (w : YPt ι ν κ) : 0 ≤ numF G F w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => tensQ_nonneg (hG w) _
theorem num_add_rem_pos {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : ∀ w, (G w).PosDef) (N : ℕ)
    (F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)) {q : ℕ} (r : Fin q → MRing (T.yyIdx ι ν κ)) (b : Fin q → T.YBlk → ℕ)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0)
    {w : YPt ι ν κ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 < numF G F w + remR N r b w := by
  by_cases hr : ∀ j, evC (r j) w = 0
  · obtain ⟨i, l, k, m, hF⟩ := hcov w hw hr
    have hu : (fun p : κ × κ => evC (F i l p.1 p.2) w) ≠ 0 := fun h0 => hF (congrFun h0 (k, m))
    have hpos : 0 < numF G F w := by
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun i => ∑ l, tensQ (G w) (fun p => evC (F i l p.1 p.2) w))
        (fun _ _ => Finset.sum_nonneg fun _ _ => tensQ_nonneg (hG w) _) (Finset.mem_univ i))
      exact lt_of_lt_of_le (tensQ_pos (hG w) hu) (Finset.single_le_sum
        (f := fun l => tensQ (G w) (fun p => evC (F i l p.1 p.2) w))
        (fun l _ => tensQ_nonneg (hG w) _) (Finset.mem_univ l))
    linarith [remR_nonneg N r b w]
  · obtain ⟨j, hj⟩ := not_forall.1 hr
    have hy := ynorm_pos hw
    have hd := dnorm_pos hw
    have hterm : 0 < ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det) :=
      div_pos (pow_pos (norm_pos_iff.2 hj) 2) (mul_pos (pow_pos hy _) (pow_pos hd _))
    have hsum : 0 < ∑ j, ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det) :=
      lt_of_lt_of_le hterm (Finset.single_le_sum
        (f := fun j => ‖evC (r j) w‖ ^ 2 / (ynorm w ^ b j .base * dnorm w ^ b j .det))
        (fun j _ => div_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hy.le _) (pow_nonneg hd.le _)))
        (Finset.mem_univ j))
    have hrem : 0 < remR N r b w := mul_pos (pow_pos hy _) hsum
    linarith [numF_nonneg hG F w]
end Line
section Scale
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] (c : T.YBlk → ℂ) (w : YPt ι ν κ)
theorem ynorm_smul : ynorm (fun p => c p.1 * w p) = ‖c .base‖ ^ 2 * ynorm w := by
  simp only [ynorm, Finset.mul_sum, norm_mul, mul_pow]
theorem dnorm_smul : dnorm (fun p => c p.1 * w p) = ‖c .det‖ ^ 2 * dnorm w := by
  simp only [dnorm, Finset.mul_sum, norm_mul, mul_pow]
theorem ypow_smul (N : ℕ) : ypow N (fun p => c p.1 * w p) = (‖c .base‖ ^ 2) ^ N * ypow N w := by
  simp only [ypow, Finset.mul_sum, norm_mul, mul_pow]
theorem hermG_smul (G : Matrix κ κ ℂ) (a : ℂ) (v : κ → ℂ) :
    (hermG G (a • v) (a • v)).re = ‖a‖ ^ 2 * (hermG G v v).re := by
  unfold hermG
  rw [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul]
  have : star a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
theorem hv_smul {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) :
    hv G (fun p => c p.1 * w p) = ‖c .line‖ ^ 2 * hv G w := by
  unfold hv
  rw [hG]
  exact hermG_smul (G w) (c .line) (lineV w)
theorem prod_single_base (n : ℕ) : ∏ k, c k ^ (Pi.single T.YBlk.base n : T.YBlk → ℕ) k = c .base ^ n := by
  rw [prodY]
  simp
theorem numF_smul {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) (N : ℕ)
    {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)}
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3))) :
    numF G F (fun p => c p.1 * w p) = (‖c .base‖ ^ 2) ^ (N + 3) * numF G F w := by
  unfold numF
  rw [hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have e : (fun p : κ × κ => evC (F i l p.1 p.2) (fun p => c p.1 * w p)) =
      c .base ^ (N + 3) • fun p : κ × κ => evC (F i l p.1 p.2) w := by
    funext p
    rw [evC_smul (hF i l p.1 p.2), prod_single_base]
    rfl
  rw [e, tensQ_smul, norm_pow, ← pow_mul, ← pow_mul, mul_comm 2]
theorem normSq_evC_smul {f : MRing (T.yyIdx ι ν κ)} {a : T.YBlk → ℕ} (hf : IsMultiHomog f a) (ha : a .line = 0) :
    ‖evC f (fun p => c p.1 * w p)‖ ^ 2 =
      (‖c .base‖ ^ 2) ^ a .base * (‖c .det‖ ^ 2) ^ a .det * ‖evC f w‖ ^ 2 := by
  rw [evC_smul hf, prodY, ha, pow_zero, mul_one, norm_mul, norm_mul, norm_pow, norm_pow]
  ring
theorem remR_smul (hc : ∀ k, c k ≠ 0) (N : ℕ) {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0) :
    remR N r b (fun p => c p.1 * w p) = (‖c .base‖ ^ 2) ^ (N + 3) * remR N r b w := by
  unfold remR
  rw [ynorm_smul, dnorm_smul, mul_pow, mul_assoc]
  refine congrArg _ (congrArg _ (Finset.sum_congr rfl fun j _ => ?_))
  have hA : (‖c .base‖ ^ 2) ^ b j .base * (‖c .det‖ ^ 2) ^ b j .det ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc _))))
      (pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc _))))
  rw [normSq_evC_smul c w (hr j) (hrl j), mul_pow, mul_pow,
    show (‖c .base‖ ^ 2) ^ b j .base * ynorm w ^ b j .base * ((‖c .det‖ ^ 2) ^ b j .det * dnorm w ^ b j .det) =
      ((‖c .base‖ ^ 2) ^ b j .base * (‖c .det‖ ^ 2) ^ b j .det) * (ynorm w ^ b j .base * dnorm w ^ b j .det) by ring,
    mul_div_mul_left _ _ hA]
theorem ratio_smul (hc : ∀ k, c k ≠ 0) {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) (N : ℕ)
    {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)}
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0) :
    ratio G N F r b (fun p => c p.1 * w p) = (‖c .base‖ ^ 3 / ‖c .det‖) ^ 2 * ratio G N F r b w := by
  unfold ratio
  rw [numF_smul c w hG N hF, remR_smul c w hc N hr hrl, ypow_smul, dnorm_smul, ← mul_add]
  have hAN : (‖c .base‖ ^ 2) ^ N ≠ 0 := pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.2 (hc _)))
  rw [show (‖c .base‖ ^ 2) ^ (N + 3) * (numF G F w + remR N r b w) =
      (‖c .base‖ ^ 2) ^ N * ((‖c .base‖ ^ 3) ^ 2 * (numF G F w + remR N r b w)) by ring,
    show 2 * ((‖c .base‖ ^ 2) ^ N * ypow N w * (‖c .det‖ ^ 2 * dnorm w)) =
      (‖c .base‖ ^ 2) ^ N * (‖c .det‖ ^ 2 * (2 * (ypow N w * dnorm w))) by ring,
    mul_div_mul_left _ _ hAN, mul_div_mul_comm, div_pow]
theorem xiH_smul (hc : ∀ k, c k ≠ 0) {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : G (fun p => c p.1 * w p) = G w) (N : ℕ)
    {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)}
    (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0) :
    xiH G N F r b (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ T.twoXiDegY k) * xiH G N F r b w := by
  unfold xiH
  have hK : 0 ≤ ‖c .base‖ ^ 3 / ‖c .det‖ := by positivity
  rw [ratio_smul c w hc hG N hF hr hrl, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK, hv_smul c w hG,
    mul_div_mul_comm, prodY]
  simp only [T.twoXiDegY, _root_.zpow_neg, zpow_ofNat]
  ring
end Scale
section Smooth
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ]
abbrev goodY (ι ν κ : Type) : Set (YPt ι ν κ) := {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0}
variable {G : YPt ι ν κ → Matrix κ κ ℂ} (hG : IsEEMetric G)
include hG
end Smooth
section Herm
variable {ι ν κ : Type} [Fintype ι] [Fintype ν] [Fintype κ] {G : YPt ι ν κ → Matrix κ κ ℂ} {N : ℕ}
  {F : ι → ν → κ → κ → MRing (T.yyIdx ι ν κ)} {q : ℕ} {r : Fin q → MRing (T.yyIdx ι ν κ)} {b : Fin q → T.YBlk → ℕ}
theorem ratio_pos (hG : IsEEMetric G)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0)
    {w : YPt ι ν κ} (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : 0 < ratio G N F r b w :=
  div_pos (num_add_rem_pos hG.1 N F r b hcov hw)
    (mul_pos two_pos (mul_pos (ypow_pos hw N) (dnorm_pos hw)))
def xiLine (hG : IsEEMetric G) (hF : ∀ i l k m, IsMultiHomog (F i l k m) (Pi.single T.YBlk.base (N + 3)))
    (hr : ∀ j, IsMultiHomog (r j) (b j)) (hrl : ∀ j, b j .line = 0)
    (hcov : ∀ w : YPt ι ν κ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ j, evC (r j) w = 0) → ∃ i l k m, evC (F i l k m) w ≠ 0) :
    HermLine (T.yyIdx ι ν κ) where
  a := T.twoXiDegY
  h := xiH G N F r b
  pos _ hz := div_pos (Real.sqrt_pos.2 (ratio_pos hG hcov hz)) (hv_pos hz hG.1)
  smul c z hc := xiH_smul c z hc (hG.2.2.1 c z hc) N hF hr hrl
end Herm
section Identity
variable {D : ℕ} (S : ProjectiveLineBundle D) {N : ℕ} {F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx} {q : ℕ}
  {r : Fin q → MRing S.YIdx} {b : Fin q → T.YBlk → ℕ}
end Identity
end XiMetricSmoothness
end
end GroundTheory.Heights₂.Heights.Inter


