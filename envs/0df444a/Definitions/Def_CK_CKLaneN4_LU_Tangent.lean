-- Prove2me | Definitions.Def_CK_CKLaneN4_LU_Tangent
-- name    : CK_CKLaneN4_LU_Tangent
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:42:05.124377+00:00
-- url     : https://prove2.me/theorems/5ecfd67f-44d5-4eea-896a-f4472f0380fe
-- title:
--   Courtade–Kumar proof module `CKLaneN4.LU.Tangent` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.LU.Tangent` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.LU.Tangent` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.LU.Tangent (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/LU/Tangent.lean)

import Definitions.Def_CK_CKLaneN4_LU_Convex

-- ===== source module CKLaneN4.LU.Tangent =====
section
/-
Lane N4b — tangent plane of the convex part `Cfun` at an interior centre.

  Cfun p ≥ Cfun c + gA c · (p₁ - c₁) + gB c · (p₂ - c₂)      (c interior, p ∈ CDom)

`gA`, `gB` are the explicit partial derivatives (corpus `hasDerivAt_J`, `Comparison.hasDerivAt_H`,
`hasDerivAt_F_curve` with the perspective slope).  Proof: the line restriction is convex on `[0,1]`
(`C_seg`), differentiable at `0`, and `ConvexOn.deriv_le_slope`.
-/

set_option autoImplicit false

namespace CKLaneN4.LU

open GeneralCK Set

noncomputable def Jd (x : ℝ) : ℝ := -1 / (Real.log 2 * x * (1 - x))
noncomputable def rc (c1 c2 : ℝ) : ℝ := (1 / 2 - c1) / hAvg c1 c2
noncomputable def Phi (r : ℝ) : ℝ := F r 1
noncomputable def PhiD (r : ℝ) : ℝ := deriv (fun r => F r 1) r

noncomputable def gA (c1 c2 : ℝ) : ℝ :=
  (-(J c1 - J c2) + (c2 - c1) * Jd c1) / 2 +
    2 * (-PhiD (rc c1 c2) + (J c1 / 2) * (Phi (rc c1 c2) - rc c1 c2 * PhiD (rc c1 c2)))

noncomputable def gB (c1 c2 : ℝ) : ℝ :=
  ((J c1 - J c2) - (c2 - c1) * Jd c2) / 2 +
    2 * ((J c2 / 2) * (Phi (rc c1 c2) - rc c1 c2 * PhiD (rc c1 c2))) +
    (-2 * J c2 + (1 - 2 * c2) * Jd c2) / 2

theorem hasDerivAt_lin (c d : ℝ) : HasDerivAt (fun s : ℝ => c + s * d) d 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c

theorem hasDerivAt_affine_comp {f : ℝ → ℝ} {f' c : ℝ} (d : ℝ) (hf : HasDerivAt f f' c) :
    HasDerivAt (fun s => f (c + s * d)) (f' * d) 0 := by
  have hf' : HasDerivAt f f' (c + 0 * d) := by simpa using hf
  exact hf'.comp 0 (hasDerivAt_lin c d)

theorem hasDerivAt_kfun {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    HasDerivAt kfun (-2 * J b + (1 - 2 * b) * Jd b) b := by
  have h := (((hasDerivAt_id b).const_mul 2).const_sub 1).mul (hasDerivAt_J hb hb1)
  have e : kfun = fun x => (1 - 2 * id x) * J x := by
    funext x; simp [kfun]
  rw [e]
  refine h.congr_deriv ?_
  simp only [Jd, id]
  ring

theorem hasDerivAt_Cline {c1 c2 : ℝ} (d1 d2 : ℝ) (h1 : 0 < c1) (h12 : c1 < c2) (h2 : c2 < 1 / 2) :
    HasDerivAt (fun s => Cfun (c1 + s * d1) (c2 + s * d2)) (gA c1 c2 * d1 + gB c1 c2 * d2) 0 := by
  have hc1 : c1 < 1 := by linarith
  have hc2p : 0 < c2 := by linarith
  have hc2 : c2 < 1 := by linarith
  have hA := hasDerivAt_lin c1 d1
  have hB := hasDerivAt_lin c2 d2
  have hJ1 := hasDerivAt_affine_comp d1 (hasDerivAt_J h1 hc1)
  have hJ2 := hasDerivAt_affine_comp d2 (hasDerivAt_J hc2p hc2)
  have hH1 := hasDerivAt_affine_comp d1 (Comparison.hasDerivAt_H h1 hc1)
  have hH2 := hasDerivAt_affine_comp d2 (Comparison.hasDerivAt_H hc2p hc2)
  have hK := hasDerivAt_affine_comp d2 (hasDerivAt_kfun hc2p hc2)
  -- interior cost
  have hIC := ((hB.sub hA).mul (hJ1.sub hJ2)).div_const 2
  -- average entropy and the radial term
  have hE := (hH1.add hH2).div_const 2
  have hS := hA.const_sub (1 / 2)
  have hE0 : 0 < (fun s => (H (c1 + s * d1) + H (c2 + s * d2)) / 2) 0 := by
    have := hAvg_pos (CDom.vdom ⟨h1, h12.le, h2.le, by linarith⟩)
    simpa [hAvg] using this
  have hS0 : 0 < (fun s => 1 / 2 - (c1 + s * d1)) 0 := by simp; linarith
  have hF := hasDerivAt_F_curve hS hE hS0 hE0
  have hsum := (hIC.add (hF.const_mul 2)).add (hK.div_const 2)
  have efun : (fun s => Cfun (c1 + s * d1) (c2 + s * d2)) =
      (fun s => ((c2 + s * d2) - (c1 + s * d1)) * (J (c1 + s * d1) - J (c2 + s * d2)) / 2 +
        2 * F (1 / 2 - (c1 + s * d1)) ((H (c1 + s * d1) + H (c2 + s * d2)) / 2) +
        kfun (c2 + s * d2) / 2) := by
    funext s
    simp only [Cfun, interiorCost, hAvg]
  rw [efun]
  refine hsum.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, zero_mul, add_zero, gA, gB, rc, Phi, PhiD,
    perspectiveSlope, hAvg, Jd]
  ring

theorem C_tangent {c1 c2 p1 p2 : ℝ} (h1 : 0 < c1) (h12 : c1 < c2) (h2 : c2 < 1 / 2)
    (hp : CDom p1 p2) :
    Cfun c1 c2 + gA c1 c2 * (p1 - c1) + gB c1 c2 * (p2 - c2) ≤ Cfun p1 p2 := by
  have hcd : CDom c1 c2 := ⟨h1, h12.le, h2.le, by linarith⟩
  have hline : ∀ s : ℝ, (1 - s) * c1 + s * p1 = c1 + s * (p1 - c1) ∧
      (1 - s) * c2 + s * p2 = c2 + s * (p2 - c2) := fun s => ⟨by ring, by ring⟩
  have hdom : ∀ s ∈ Icc (0 : ℝ) 1, CDom (c1 + s * (p1 - c1)) (c2 + s * (p2 - c2)) := by
    intro s hs
    have := CDom_seg hcd hp hs.1 hs.2
    rwa [(hline s).1, (hline s).2] at this
  have hconv : ConvexOn ℝ (Icc 0 1) (fun s => Cfun (c1 + s * (p1 - c1)) (c2 + s * (p2 - c2))) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy α β hα hβ hαβ
    have key := C_seg (hdom x hx) (hdom y hy) hβ (by linarith)
    have hα' : α = 1 - β := by linarith
    subst hα'
    simp only [smul_eq_mul]
    have e1 : c1 + ((1 - β) * x + β * y) * (p1 - c1) =
        (1 - β) * (c1 + x * (p1 - c1)) + β * (c1 + y * (p1 - c1)) := by ring
    have e2 : c2 + ((1 - β) * x + β * y) * (p2 - c2) =
        (1 - β) * (c2 + x * (p2 - c2)) + β * (c2 + y * (p2 - c2)) := by ring
    rw [e1, e2]
    exact key
  have hd := hasDerivAt_Cline (p1 - c1) (p2 - c2) h1 h12 h2
  have hsl := hconv.deriv_le_slope (x := 0) (y := 1) (by simp) (by simp) one_pos
    hd.differentiableAt
  rw [hd.deriv, slope_def_field] at hsl
  simp only [zero_mul, add_zero, one_mul, sub_zero, div_one] at hsl
  have e1 : c1 + (p1 - c1) = p1 := by ring
  have e2 : c2 + (p2 - c2) = p2 := by ring
  rw [e1, e2] at hsl
  linarith

/-! ### The comparison function on a cell -/

/-- Tangent plane of `C` at `c` plus the concave part. -/
noncomputable def Wfun (c1 c2 a b : ℝ) : ℝ :=
  Cfun c1 c2 + gA c1 c2 * (a - c1) + gB c1 c2 * (b - c2) + Vfun a b

theorem W_seg (c1 c2 : ℝ) {a0 b0 a1 b1 μ : ℝ} (h0 : VDom a0 b0) (h1 : VDom a1 b1)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    min (Wfun c1 c2 a0 b0) (Wfun c1 c2 a1 b1) ≤
      Wfun c1 c2 ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) := by
  have hv := V_seg h0 h1 hμ0 hμ1
  have hm : min (Wfun c1 c2 a0 b0) (Wfun c1 c2 a1 b1) ≤
      (1 - μ) * Wfun c1 c2 a0 b0 + μ * Wfun c1 c2 a1 b1 := by
    rcases le_total (Wfun c1 c2 a0 b0) (Wfun c1 c2 a1 b1) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hlin : Wfun c1 c2 ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) -
      Vfun ((1 - μ) * a0 + μ * a1) ((1 - μ) * b0 + μ * b1) =
      (1 - μ) * (Wfun c1 c2 a0 b0 - Vfun a0 b0) + μ * (Wfun c1 c2 a1 b1 - Vfun a1 b1) := by
    unfold Wfun; ring
  nlinarith

/-- The `(a,t)` chart: `b = a + t (1/2 - a)`. -/
noncomputable def bAt (a t : ℝ) : ℝ := a + t * (1 / 2 - a)

theorem cell_bound {A0 A1 T0 T1 c1 c2 a t : ℝ} (hA : A0 < A1) (hT : T0 < T1)
    (hv00 : VDom A0 (bAt A0 T0)) (hv10 : VDom A1 (bAt A1 T0))
    (hv01 : VDom A0 (bAt A0 T1)) (hv11 : VDom A1 (bAt A1 T1))
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1 / 2)
    (ha : A0 ≤ a) (ha' : a ≤ A1) (ht : T0 ≤ t) (ht' : t ≤ T1) (hapos : 0 < a)
    (hT0 : 0 ≤ T0) (hT1 : T1 ≤ 1)
    (w00 : 0 ≤ Wfun c1 c2 A0 (bAt A0 T0)) (w10 : 0 ≤ Wfun c1 c2 A1 (bAt A1 T0))
    (w01 : 0 ≤ Wfun c1 c2 A0 (bAt A0 T1)) (w11 : 0 ≤ Wfun c1 c2 A1 (bAt A1 T1)) :
    0 ≤ Gexpr a (bAt a t) := by
  set ν := (a - A0) / (A1 - A0) with hν
  set μ := (t - T0) / (T1 - T0) with hμ
  have hAp : 0 < A1 - A0 := sub_pos.2 hA
  have hTp : 0 < T1 - T0 := sub_pos.2 hT
  have hν0 : 0 ≤ ν := div_nonneg (by linarith) hAp.le
  have hν1 : ν ≤ 1 := (div_le_one hAp).2 (by linarith)
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hTp.le
  have hμ1 : μ ≤ 1 := (div_le_one hTp).2 (by linarith)
  have ea : (1 - ν) * A0 + ν * A1 = a := by
    rw [hν]; field_simp; ring
  have et : (1 - μ) * T0 + μ * T1 = t := by
    rw [hμ]; field_simp; ring
  -- q0 = (a, bAt a T0), q1 = (a, bAt a T1)
  have eq0 : (1 - ν) * bAt A0 T0 + ν * bAt A1 T0 = bAt a T0 := by
    rw [← ea]; unfold bAt; ring
  have eq1 : (1 - ν) * bAt A0 T1 + ν * bAt A1 T1 = bAt a T1 := by
    rw [← ea]; unfold bAt; ring
  have ep : (1 - μ) * bAt a T0 + μ * bAt a T1 = bAt a t := by
    rw [← et]; unfold bAt; ring
  have hq0 : VDom a (bAt a T0) := by
    have := VDom_seg hv00 hv10 hν0 hν1
    rwa [ea, eq0] at this
  have hq1 : VDom a (bAt a T1) := by
    have := VDom_seg hv01 hv11 hν0 hν1
    rwa [ea, eq1] at this
  have wq0 : min (Wfun c1 c2 A0 (bAt A0 T0)) (Wfun c1 c2 A1 (bAt A1 T0)) ≤
      Wfun c1 c2 a (bAt a T0) := by
    have := W_seg c1 c2 hv00 hv10 hν0 hν1
    rwa [ea, eq0] at this
  have wq1 : min (Wfun c1 c2 A0 (bAt A0 T1)) (Wfun c1 c2 A1 (bAt A1 T1)) ≤
      Wfun c1 c2 a (bAt a T1) := by
    have := W_seg c1 c2 hv01 hv11 hν0 hν1
    rwa [ea, eq1] at this
  have wp : min (Wfun c1 c2 a (bAt a T0)) (Wfun c1 c2 a (bAt a T1)) ≤ Wfun c1 c2 a (bAt a t) := by
    have := W_seg c1 c2 hq0 hq1 hμ0 hμ1
    have ea' : (1 - μ) * a + μ * a = a := by ring
    rwa [ea', ep] at this
  have hW : 0 ≤ Wfun c1 c2 a (bAt a t) := by
    have m0 : 0 ≤ min (Wfun c1 c2 A0 (bAt A0 T0)) (Wfun c1 c2 A1 (bAt A1 T0)) := le_min w00 w10
    have m1 : 0 ≤ min (Wfun c1 c2 A0 (bAt A0 T1)) (Wfun c1 c2 A1 (bAt A1 T1)) := le_min w01 w11
    have := le_min (m0.trans wq0) (m1.trans wq1)
    exact this.trans wp
  -- p ∈ CDom
  have hah : a < 1 / 2 := lt_of_le_of_lt ha' hv10.2.2.2.1
  have hpd : CDom a (bAt a t) := by
    refine ⟨hapos, ?_, ?_, hah⟩
    · unfold bAt; nlinarith
    · unfold bAt; nlinarith
  have htan := C_tangent hc1 hc12 hc2 hpd
  unfold Gexpr
  unfold Wfun at hW
  linarith

end CKLaneN4.LU

end


