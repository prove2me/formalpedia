-- Prove2me | Definitions.Def_CK_CKLaneP_LeftFiber
-- name    : CK_CKLaneP_LeftFiber
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T02:11:58.548831+00:00
-- url     : https://prove2.me/theorems/0a5d91ab-c051-40bc-95d2-6d51d95b3cf3
-- title:
--   Courtade–Kumar proof module `CKLaneP.LeftFiber` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.LeftFiber` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.LeftFiber` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.LeftFiber (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/LeftFiber.lean)

import Definitions.Def_CK_CKLaneP_ThetaBounds
import Definitions.Def_CK_GeneralCK_PureGapMeanStationarity
import Definitions.Def_CK_GeneralCK_PureGapCompactMean

-- ===== source module CKLaneP.LeftFiber =====
section
/-
Lane P — the left cap fiber `y ↦ canonicalPureGap a y e f`: derivative in `e8Theta` form and
elementary mean-value consequences.

  L'(c) = Θ((c−a)/(e+f)) − Θ((1−a−c)/(e+f)) + Θ((1−2c)/(2f)),   a < c < 1/2, a + c < 1.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set

/-- The left-fiber derivative (derivative in the second mean `c`) in `e8Theta` form. -/
noncomputable def leftFiberDeriv (a c e f : ℝ) : ℝ :=
  e8Theta ((c - a) / (e + f)) - e8Theta ((1 - a - c) / (e + f)) + e8Theta ((1 - 2 * c) / (2 * f))

theorem hasDerivAt_leftFiber {a c e f : ℝ} (hac : a < c) (hsum : a + c < 1) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    HasDerivAt (fun y => canonicalPureGap a y e f) (leftFiberDeriv a c e f) c := by
  have hef : 0 < (e + f) / 2 := by linarith
  have hFd := (hasDerivAt_F_radius (sub_pos.mpr hac) hef).differentiableAt.hasDerivAt
  have hFc := (hasDerivAt_F_radius (show 0 < 1 - a - c by linarith) hef).differentiableAt.hasDerivAt
  have hFr := (hasDerivAt_F_radius (show 0 < 1 - 2 * c by linarith) hf).differentiableAt.hasDerivAt
  have hdiff := hFd.comp c ((hasDerivAt_id c).sub_const a)
  have hcenter := hFc.comp c ((hasDerivAt_const c (1 - a)).sub (hasDerivAt_id c))
  have hright := hFr.comp c (((hasDerivAt_id c).const_mul 2).const_sub 1)
  have hd1 := deriv_F_radius_eq_e8Theta (sub_pos.mpr hac) hef
  have hd2 := deriv_F_radius_eq_e8Theta (show 0 < 1 - a - c by linarith) hef
  have hd3 := deriv_F_radius_eq_e8Theta (show 0 < 1 - 2 * c by linarith) hf
  have e1 : (c - a) / (2 * ((e + f) / 2)) = (c - a) / (e + f) := by ring_nf
  have e2 : (1 - a - c) / (2 * ((e + f) / 2)) = (1 - a - c) / (e + f) := by ring_nf
  rw [e1] at hd1
  rw [e2] at hd2
  have hdiff' : HasDerivAt (fun t => F (t - a) ((e + f) / 2))
      (deriv (fun r => F r ((e + f) / 2)) (c - a) * 1) c := hdiff
  have hcenter' : HasDerivAt (fun t => F (1 - a - t) ((e + f) / 2))
      (deriv (fun r => F r ((e + f) / 2)) (1 - a - c) * (0 - 1)) c := hcenter
  have hright' : HasDerivAt (fun t => F (1 - 2 * t) f)
      (deriv (fun r => F r f) (1 - 2 * c) * -(2 * 1)) c := hright
  have hsum :=
    ((hdiff'.add (hasDerivAt_const c (entropyCorrection e f))).sub
      ((hasDerivAt_const c (eta ((e + f) / 2))).sub hcenter')).add
      ((((hasDerivAt_const c (radialPhi (1 - 2 * a) e)).add
        ((hasDerivAt_const c (eta f)).sub hright')).div_const 2))
  have hev : (fun t => canonicalPureGap a t e f) =ᶠ[nhds c]
      (fun t => F (t - a) ((e + f) / 2) + entropyCorrection e f -
        (eta ((e + f) / 2) - F (1 - a - t) ((e + f) / 2)) +
        (radialPhi (1 - 2 * a) e + (eta f - F (1 - 2 * t) f)) / 2) :=
    Filter.Eventually.of_forall (fun t => by
      simp only [canonicalPureGap, radialPhi]
      try ring_nf)
  refine (hsum.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hd1, hd2, hd3]
  unfold leftFiberDeriv
  ring

/-- Mean-value lower bound on the left fiber: a derivative lower bound `ℓ` on `[t1, t2]`
(inside `(a, 1/2)`) gives `L(t2) ≥ L(t1) + ℓ (t2 - t1)`. -/
theorem leftFiber_mvt {a e f t1 t2 ℓ : ℝ} (he : 0 < e) (hf : 0 < f)
    (ha1 : a < t1) (h12 : t1 ≤ t2) (h2 : t2 < 1 / 2)
    (hd : ∀ t ∈ Icc t1 t2, ℓ ≤ leftFiberDeriv a t e f) :
    canonicalPureGap a t1 e f + ℓ * (t2 - t1) ≤ canonicalPureGap a t2 e f := by
  have hdiff : ∀ t ∈ Icc t1 t2, HasDerivAt (fun y => canonicalPureGap a y e f - ℓ * y)
      (leftFiberDeriv a t e f - ℓ) t := by
    intro t ht
    have hat : a < t := lt_of_lt_of_le ha1 ht.1
    have ht2 : t < 1 / 2 := lt_of_le_of_lt ht.2 h2
    have h := hasDerivAt_leftFiber hat (by linarith) ht2 he hf
    exact (h.sub ((hasDerivAt_id t).const_mul ℓ)).congr_deriv (by rw [mul_one])
  have hcont : ContinuousOn (fun y => canonicalPureGap a y e f - ℓ * y) (Icc t1 t2) :=
    fun t ht => (hdiff t ht).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun y => canonicalPureGap a y e f - ℓ * y) (Icc t1 t2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t1 t2) hcont
    · intro t ht
      exact (hdiff t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hdiff t (interior_subset ht)).deriv]
      linarith [hd t (interior_subset ht)]
  have := hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12
  simp only at this
  linarith

/-- Monotone special case. -/
theorem leftFiber_mono_of_deriv_nonneg {a e f t1 t2 : ℝ} (he : 0 < e) (hf : 0 < f)
    (ha1 : a < t1) (h12 : t1 ≤ t2) (h2 : t2 < 1 / 2)
    (hd : ∀ t ∈ Icc t1 t2, 0 ≤ leftFiberDeriv a t e f) :
    canonicalPureGap a t1 e f ≤ canonicalPureGap a t2 e f := by
  have := leftFiber_mvt (ℓ := 0) he hf ha1 h12 h2 hd
  linarith

/-- The stationarity hypothesis of `leftStationary` in `leftFiberDeriv` form. -/
theorem leftFiber_deriv_eq {a c e f : ℝ} (hac : a < c) (hsum : a + c < 1) (hc : c < 1 / 2)
    (he : 0 < e) (hf : 0 < f) :
    deriv (fun y => canonicalPureGap a y e f) c = leftFiberDeriv a c e f :=
  (hasDerivAt_leftFiber hac hsum hc he hf).deriv

end CKLaneP

end


