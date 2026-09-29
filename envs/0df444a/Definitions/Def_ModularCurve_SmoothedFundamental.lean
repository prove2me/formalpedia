-- Prove2me | Definitions.Def_ModularCurve_SmoothedFundamental
-- name    : ModularCurve_SmoothedFundamental
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/2cc47659-7026-5761-9f66-2f6f01a8300a
-- title:
--   Smoothed fundamental-domain cut-off functions on the upper half-plane
-- statement:
--   Fix a real number $T$. The module builds, out of Mathlib's smooth transition function $\mathrm{st} =$ `Real.smoothTransition` (which vanishes on $(-\infty,0]$, equals $1$ on $[1,\infty)$ and takes values in $[0,1]$), an explicit non-negative function on $\mathbb{C}$ attached to a subgroup of $SL_2(\mathbb{Z})$. The Möbius map is taken in the unrestricted form `mob γ z = num γ z / denom γ z`, i.e. $(az+b)/(cz+d)$ for $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}$, acting on all of $\mathbb{C}$; `coe_smul` identifies it with the Mathlib action of $SL(2,\mathbb{Z})$ on $\mathbb{H}$, and `mob_mob`, `mob_one_apply` record that it is a (left) action. The profiles are `pOne x = st(x+1) - st(x)`, which is $[0,1]$-valued, vanishes for $x \le -1$ and for $x \ge 1$, and satisfies `pOne (u-1) + pOne u = 1` for $u \in [0,1]$; and `pTwo T y` $= \mathrm{st}(8y-5)\cdot \mathrm{st}(T+4-y)$, which is $[0,1]$-valued, equals $1$ on $[3/4, T+3]$ and vanishes for $y \le 5/8$ and for $y \ge T+4$. Their product `bump T z = pOne (Re z) · pTwo T (Im z)` is $[0,1]$-valued with support, hence closed support, inside the compact box `box T = [-1,1] ×ℂ [5/8, T+4]`; in particular $\mathrm{Im}\,z>0$ wherever the bump is non-zero. Next, `cover T z` is the unordered sum $\sum_{\gamma \in SL(2,\mathbb{Z})} \mathrm{bump}_T(\mathrm{mob}\,\gamma\, z)$ (a `finsum`), `recip t = st(4t-1)/t` is a regularised reciprocal satisfying $t\cdot\mathrm{recip}\,t = 1$ for $t \ge 1/2$ and $t\cdot\mathrm{recip}\,t \le 1$ always, and `pu T = bump T · recip (cover T)` is the resulting normalised bump. A cusp cut-off `gcut T z = 1 - st(Im z - T)` is $[0,1]$-valued, equals $1$ when $\mathrm{Im}\,z \le T$ and $0$ when $\mathrm{Im}\,z \ge T+1$, and `puCut T = pu T · gcut T` is bounded by `pu T`, supported in `box T`, and equal to `pu T` below height $T$. Finally, for a subgroup $\Gamma \le SL_2(\mathbb{Z})$, [`ModularCurve.smoothedFundamental Γ T z`](../def/ModularCurve_SmoothedFundamental.html#L170) is the unordered sum of $\mathrm{puCut}_T(\mathrm{mob}\,\sigma_q\,z)$ over the cosets $q \in SL(2,\mathbb{Z})/\Gamma$, where $\sigma_q =$ `Quotient.out q` is the chosen coset representative; it is non-negative, and reduces to an ordinary finite sum when the coset space is finite.
--
--   **Relation to Mathlib.** All the profiles are assembled from Mathlib's `Real.smoothTransition`, and `mob` is a $\mathbb{C}$-valued form of the Möbius action identified with Mathlib's action of $SL(2,\mathbb{Z})$ on `ℍ`; Mathlib has no smoothed fundamental-domain function of this kind, so the construction is the project's own.
--
--   **Where it is used.** These functions serve as smooth, compactly supported substitutes for the characteristic function of a fundamental domain for $\Gamma \backslash \mathbb{H}$, whose $\Gamma$-translates add up to the level-one partition of unity cut off above height $T$. They are used in the analytic work on modular curves — integration identities of Stokes type, residue and period computations — which feeds the modular-forms side of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SmoothedFundamental.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane Set
open scoped MatrixGroups Topology

noncomputable section

namespace ModularCurve.SmoothedFundamental

def mob (γ : SL(2, ℤ)) (z : ℂ) : ℂ := num γ z / denom γ z

theorem coe_smul (γ : SL(2, ℤ)) (τ : ℍ) : ((γ • τ : ℍ) : ℂ) = mob γ τ := by
  rw [ModularGroup.sl_moeb, coe_smul_of_det_pos (by simp)]; rfl

theorem mob_mob (γ γ' : SL(2, ℤ)) (τ : ℍ) : mob γ (mob γ' τ) = mob (γ * γ') τ := by
  rw [← coe_smul, ← coe_smul, ← coe_smul, mul_smul]

theorem mob_one_apply (z : ℂ) : mob 1 z = z := by
  simp [mob, num, denom]

def pOne (x : ℝ) : ℝ := Real.smoothTransition (x + 1) - Real.smoothTransition x

theorem pOne_nonneg (x : ℝ) : 0 ≤ pOne x :=
  sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

theorem pOne_le_one (x : ℝ) : pOne x ≤ 1 := by
  have := Real.smoothTransition.le_one (x + 1)
  have := Real.smoothTransition.nonneg x
  unfold pOne; linarith

theorem pOne_eq_zero_of_le {x : ℝ} (hx : x ≤ -1) : pOne x = 0 := by
  simp [pOne, Real.smoothTransition.zero_of_nonpos (show x + 1 ≤ 0 by linarith),
    Real.smoothTransition.zero_of_nonpos (show x ≤ 0 by linarith)]

theorem pOne_eq_zero_of_ge {x : ℝ} (hx : 1 ≤ x) : pOne x = 0 := by
  simp [pOne, Real.smoothTransition.one_of_one_le (show 1 ≤ x + 1 by linarith),
    Real.smoothTransition.one_of_one_le hx]

theorem mem_Ioo_of_pOne_ne_zero {x : ℝ} (hx : pOne x ≠ 0) : -1 < x ∧ x < 1 := by
  by_contra h
  rcases not_and_or.1 h with h | h <;> push Not at h
  exacts [hx (pOne_eq_zero_of_le h), hx (pOne_eq_zero_of_ge h)]

theorem pOne_sub_one_add {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : pOne (u - 1) + pOne u = 1 := by
  unfold pOne
  rw [sub_add_cancel, Real.smoothTransition.zero_of_nonpos (by linarith : u - 1 ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ u + 1)]
  ring

def pTwo (T y : ℝ) : ℝ := Real.smoothTransition (8 * y - 5) * Real.smoothTransition (T + 4 - y)

theorem pTwo_nonneg (T y : ℝ) : 0 ≤ pTwo T y :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem pTwo_le_one (T y : ℝ) : pTwo T y ≤ 1 :=
  mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.le_one _)

theorem pTwo_eq_zero_of_le {T y : ℝ} (hy : y ≤ 5 / 8) : pTwo T y = 0 := by
  simp [pTwo, Real.smoothTransition.zero_of_nonpos (show 8 * y - 5 ≤ 0 by linarith)]

theorem pTwo_eq_zero_of_ge {T y : ℝ} (hy : T + 4 ≤ y) : pTwo T y = 0 := by
  simp [pTwo, Real.smoothTransition.zero_of_nonpos (show T + 4 - y ≤ 0 by linarith)]

theorem pTwo_eq_one {T y : ℝ} (h1 : 3 / 4 ≤ y) (h2 : y ≤ T + 3) : pTwo T y = 1 := by
  simp [pTwo, Real.smoothTransition.one_of_one_le (show 1 ≤ 8 * y - 5 by linarith),
    Real.smoothTransition.one_of_one_le (show 1 ≤ T + 4 - y by linarith)]

theorem mem_Ioo_of_pTwo_ne_zero {T y : ℝ} (h : pTwo T y ≠ 0) : 5 / 8 < y ∧ y < T + 4 := by
  by_contra h'
  rcases not_and_or.1 h' with h' | h' <;> push Not at h'
  exacts [h (pTwo_eq_zero_of_le h'), h (pTwo_eq_zero_of_ge h')]

def bump (T : ℝ) (z : ℂ) : ℝ := pOne z.re * pTwo T z.im

theorem bump_nonneg (T : ℝ) (z : ℂ) : 0 ≤ bump T z := mul_nonneg (pOne_nonneg _) (pTwo_nonneg _ _)

theorem bump_le_one (T : ℝ) (z : ℂ) : bump T z ≤ 1 :=
  mul_le_one₀ (pOne_le_one _) (pTwo_nonneg _ _) (pTwo_le_one _ _)

theorem mem_of_bump_ne_zero {T : ℝ} {z : ℂ} (h : bump T z ≠ 0) :
    (-1 < z.re ∧ z.re < 1) ∧ (5 / 8 < z.im ∧ z.im < T + 4) :=
  ⟨mem_Ioo_of_pOne_ne_zero (left_ne_zero_of_mul h),
    mem_Ioo_of_pTwo_ne_zero (right_ne_zero_of_mul h)⟩

theorem im_pos_of_bump_ne_zero {T : ℝ} {z : ℂ} (h : bump T z ≠ 0) : 0 < z.im := by
  have := (mem_of_bump_ne_zero h).2.1; linarith

def box (T : ℝ) : Set ℂ := Icc (-1 : ℝ) 1 ×ℂ Icc (5 / 8 : ℝ) (T + 4)

theorem isCompact_box (T : ℝ) : IsCompact (box T) := isCompact_Icc.reProdIm isCompact_Icc

theorem isClosed_box (T : ℝ) : IsClosed (box T) := isClosed_Icc.reProdIm isClosed_Icc

theorem im_pos_of_mem_box {T : ℝ} {z : ℂ} (hz : z ∈ box T) : 0 < z.im := by
  have := (Complex.mem_reProdIm.1 hz).2.1; linarith

theorem support_bump_subset (T : ℝ) : Function.support (bump T) ⊆ box T := by
  intro z hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := mem_of_bump_ne_zero hz
  exact Complex.mem_reProdIm.2 ⟨⟨h1.le, h2.le⟩, h3.le, h4.le⟩

theorem tsupport_bump_subset (T : ℝ) : tsupport (bump T) ⊆ box T :=
  closure_minimal (support_bump_subset T) (isClosed_box T)

def recip (t : ℝ) : ℝ := Real.smoothTransition (4 * t - 1) / t

theorem recip_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ recip t :=
  div_nonneg (Real.smoothTransition.nonneg _) ht

theorem mul_recip_of_half_le {t : ℝ} (ht : 1 / 2 ≤ t) : t * recip t = 1 := by
  unfold recip
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  field_simp

theorem mul_recip_le_one (t : ℝ) : t * recip t ≤ 1 := by
  unfold recip
  by_cases ht : t = 0
  · simp [ht]
  · rw [mul_div_cancel₀ _ ht]; exact Real.smoothTransition.le_one _

def gcut (T : ℝ) (z : ℂ) : ℝ := 1 - Real.smoothTransition (z.im - T)

theorem gcut_eq_one {T : ℝ} {z : ℂ} (h : z.im ≤ T) : gcut T z = 1 := by
  simp [gcut, Real.smoothTransition.zero_of_nonpos (show z.im - T ≤ 0 by linarith)]

theorem gcut_eq_zero {T : ℝ} {z : ℂ} (h : T + 1 ≤ z.im) : gcut T z = 0 := by
  simp [gcut, Real.smoothTransition.one_of_one_le (show 1 ≤ z.im - T by linarith)]

theorem gcut_nonneg (T : ℝ) (z : ℂ) : 0 ≤ gcut T z :=
  sub_nonneg.2 (Real.smoothTransition.le_one _)

theorem gcut_le_one (T : ℝ) (z : ℂ) : gcut T z ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

def cover (T : ℝ) (z : ℂ) : ℝ := ∑ᶠ γ : SL(2, ℤ), bump T (mob γ z)

theorem cover_nonneg (T : ℝ) (z : ℂ) : 0 ≤ cover T z := finsum_nonneg fun _ => bump_nonneg _ _

def pu (T : ℝ) (z : ℂ) : ℝ := bump T z * recip (cover T z)

theorem pu_nonneg (T : ℝ) (z : ℂ) : 0 ≤ pu T z :=
  mul_nonneg (bump_nonneg _ _) (recip_nonneg (cover_nonneg _ _))

theorem support_pu_subset (T : ℝ) : Function.support (pu T) ⊆ Function.support (bump T) :=
  fun _ hz => left_ne_zero_of_mul hz

theorem tsupport_pu_subset (T : ℝ) : tsupport (pu T) ⊆ box T :=
  (closure_mono (support_pu_subset T)).trans (tsupport_bump_subset T)

def puCut (T : ℝ) (z : ℂ) : ℝ := pu T z * gcut T z

theorem puCut_nonneg (T : ℝ) (z : ℂ) : 0 ≤ puCut T z :=
  mul_nonneg (pu_nonneg _ _) (gcut_nonneg _ _)

theorem puCut_le_pu (T : ℝ) (z : ℂ) : puCut T z ≤ pu T z :=
  mul_le_of_le_one_right (pu_nonneg _ _) (gcut_le_one _ _)

theorem support_puCut_subset (T : ℝ) : Function.support (puCut T) ⊆ box T :=
  fun _ hz => support_bump_subset T (support_pu_subset T (left_ne_zero_of_mul hz))

theorem tsupport_puCut_subset (T : ℝ) : tsupport (puCut T) ⊆ box T :=
  closure_minimal (support_puCut_subset T) (isClosed_box T)

theorem puCut_eq_pu_of_im_le {T : ℝ} {z : ℂ} (h : z.im ≤ T) : puCut T z = pu T z := by
  rw [puCut, gcut_eq_one h, mul_one]

end ModularCurve.SmoothedFundamental

def ModularCurve.smoothedFundamental (Γ : Subgroup SL(2, ℤ)) (T : ℝ) (z : ℂ) : ℝ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    ModularCurve.SmoothedFundamental.puCut T (ModularCurve.SmoothedFundamental.mob (Quotient.out q) z)

namespace ModularCurve.SmoothedFundamental

theorem smoothedFundamental_nonneg (Γ : Subgroup SL(2, ℤ)) (T : ℝ) (z : ℂ) :
    0 ≤ ModularCurve.smoothedFundamental Γ T z :=
  finsum_nonneg fun _ => puCut_nonneg _ _

theorem smoothedFundamental_eq_sum (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)] (T : ℝ)
    (z : ℂ) : ModularCurve.smoothedFundamental Γ T z =
      ∑ q : SL(2, ℤ) ⧸ Γ, puCut T (mob (Quotient.out q) z) :=
  finsum_eq_sum_of_fintype _

end ModularCurve.SmoothedFundamental

end


