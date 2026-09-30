-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TauInverseContraction
-- name    : CK_GeneralCK_Certificates_E8TauInverseContraction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:08:49.150202+00:00
-- url     : https://prove2.me/theorems/3a185670-3591-4603-b1ca-3785e1f73198
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TauInverseContraction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TauInverseContraction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TauInverseContraction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TauInverseContraction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TauInverseContraction.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8QuantitativeBranchBridge
import Mathlib.Topology.MetricSpace.Contracting

-- ===== source module GeneralCK.Certificates.E8TauInverseContraction =====
section

/-!
# Quantitative contraction for the remaining E8 scalar inversion

For `F(tau) = 4*tau + R(tau)`, solving `F(tau)=y` is equivalent to finding a
fixed point of `(y - R(tau))/4`.  The rational radii below leave enough room
for the Cauchy estimate and make all self-map/contraction arithmetic exact.
-/

namespace GeneralCK.Certificates.E8TauInverseContraction

open Metric Set Function
open GeneralCK.E8AnalyticGerm
open GeneralCK.Reflection.ComplexGlobalAnalytic

noncomputable def tauRadius : ℝ := 2 / 5
noncomputable def supportedYRadius : ℝ := 6 / 5

private abbrev tauDisc : Set ℂ := closedBall 0 tauRadius

noncomputable def inverseMap (R : ℂ → ℂ) (y tau : ℂ) : ℂ :=
  (y - R tau) / 4

/-- The concrete map that remains to be inverted after passing from contact
bias `c` to the contraction parameter `tau`. -/
noncomputable def thetaOfTau (tau : ℂ) : ℂ :=
  thetaParam (fixedPointOnDisc tau)

/-- Its nonlinear part after removing the exact derivative `4` at zero. -/
noncomputable def thetaTauRemainder (tau : ℂ) : ℂ :=
  thetaOfTau tau - 4 * tau

theorem fixedPointOnDisc_zero : fixedPointOnDisc 0 = 0 := by
  have h := fixedPointOnDisc_fixed (tau := (0 : ℂ)) (by norm_num)
  simpa using h

@[simp] theorem thetaOfTau_zero : thetaOfTau 0 = 0 := by
  simp [thetaOfTau, fixedPointOnDisc_zero]

@[simp] theorem thetaTauRemainder_zero : thetaTauRemainder 0 = 0 := by
  simp [thetaTauRemainder]

/-- A unit-Lipschitz nonlinear remainder fixing zero makes the inverse map
a self-map of the `2/5` disc for every `‖y‖ ≤ 6/5`. -/
theorem inverseMap_mapsTo
    {R : ℂ → ℂ} (hR0 : R 0 = 0)
    (hRlip : LipschitzOnWith (1 : NNReal) R tauDisc)
    {y : ℂ} (hy : ‖y‖ ≤ supportedYRadius) :
    MapsTo (inverseMap R y) tauDisc tauDisc := by
  intro tau htau
  have hzero : (0 : ℂ) ∈ tauDisc := by
    simp [tauDisc, tauRadius]
    norm_num
  have hR : ‖R tau‖ ≤ ‖tau‖ := by
    have h := hRlip.dist_le_mul tau htau 0 hzero
    simpa [hR0, dist_eq_norm] using h
  have htauNorm : ‖tau‖ ≤ tauRadius := by
    simpa [tauDisc, mem_closedBall, dist_zero_right] using htau
  have hnorm : ‖inverseMap R y tau‖ ≤ tauRadius := by
    rw [inverseMap, norm_div]
    have hfour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
    rw [hfour]
    calc
      ‖y - R tau‖ / 4 ≤ (‖y‖ + ‖R tau‖) / 4 := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ (supportedYRadius + tauRadius) / 4 := by
        gcongr
        exact hR.trans htauNorm
      _ = tauRadius := by norm_num [supportedYRadius, tauRadius]
  simpa [tauDisc, mem_closedBall, dist_zero_right] using hnorm

/-- The same remainder hypothesis makes the restricted inverse map a strict
`1/4` contraction. -/
theorem inverseMap_contracting
    {R : ℂ → ℂ} (hR0 : R 0 = 0)
    (hRlip : LipschitzOnWith (1 : NNReal) R tauDisc)
    {y : ℂ} (hy : ‖y‖ ≤ supportedYRadius) :
    ContractingWith (1 / 4 : NNReal)
      ((inverseMap_mapsTo hR0 hRlip hy).restrict (inverseMap R y) tauDisc tauDisc) := by
  refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
  intro a b
  have hR := hRlip.dist_le_mul a a.property b b.property
  change dist (inverseMap R y a) (inverseMap R y b) ≤
    ((1 / 4 : NNReal) : ℝ) * dist a b
  rw [dist_eq_norm, inverseMap]
  change ‖(y - R a) / 4 - (y - R b) / 4‖ ≤
    ((1 / 4 : NNReal) : ℝ) * dist a b
  have hid : (y - R a) / 4 - (y - R b) / 4 = (R b - R a) / 4 := by ring
  rw [hid, norm_div]
  have hfour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  rw [hfour]
  norm_num at hR ⊢
  rw [dist_eq_norm] at hR
  rw [norm_sub_rev] at hR
  calc
    ‖R b - R a‖ / 4 ≤ dist (a : ℂ) (b : ℂ) / 4 :=
      div_le_div_of_nonneg_right hR (by norm_num)
    _ = (1 / 4 : ℝ) * dist a b := by
      rw [Subtype.dist_eq]
      ring

/-- Banach's theorem now gives an inverse value for every point of the
closed `6/5` `y` disc.  This is the existence/uniqueness part of the desired
quantitative branch; analyticity follows once the actual remainder is shown
holomorphic with this Lipschitz bound. -/
theorem exists_unique_inverse
    {R : ℂ → ℂ} (hR0 : R 0 = 0)
    (hRlip : LipschitzOnWith (1 : NNReal) R tauDisc)
    {y : ℂ} (hy : ‖y‖ ≤ supportedYRadius) :
    ∃! tau : ℂ, tau ∈ tauDisc ∧ inverseMap R y tau = tau := by
  let hmaps := inverseMap_mapsTo hR0 hRlip hy
  let hcontract := inverseMap_contracting hR0 hRlip hy
  have hcomplete : IsComplete tauDisc := isClosed_closedBall.isComplete
  have hzero : (0 : ℂ) ∈ tauDisc := by
    simp [tauDisc, tauRadius]
    norm_num
  have hfinite := edist_ne_top (0 : ℂ) (inverseMap R y 0)
  obtain ⟨tau, htau, hfixed, _⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hzero hfinite
  refine ⟨tau, ⟨htau, hfixed⟩, ?_⟩
  intro sigma hsigma
  have heq := hcontract.fixedPoint_unique'
    (x := ⟨sigma, hsigma.1⟩) (y := ⟨tau, htau⟩)
    (Subtype.ext hsigma.2) (Subtype.ext hfixed)
  exact congrArg Subtype.val heq

/-- For the concrete E8 map, existence and uniqueness on the full closed
`6/5` `y` disc now reduce to one explicit norm inequality: the nonlinear
remainder is unit-Lipschitz on `‖tau‖ ≤ 2/5`. -/
theorem exists_unique_thetaOfTau_inverse
    (hLip : LipschitzOnWith (1 : NNReal) thetaTauRemainder tauDisc)
    {y : ℂ} (hy : ‖y‖ ≤ supportedYRadius) :
    ∃! tau : ℂ, tau ∈ tauDisc ∧ thetaOfTau tau = y := by
  have h := exists_unique_inverse thetaTauRemainder_zero hLip hy
  have hiff (tau : ℂ) :
      (tau ∈ tauDisc ∧ inverseMap thetaTauRemainder y tau = tau) ↔
        (tau ∈ tauDisc ∧ thetaOfTau tau = y) := by
    constructor
    · rintro ⟨htau, hfix⟩
      refine ⟨htau, ?_⟩
      unfold inverseMap thetaTauRemainder at hfix
      have hmul := congrArg (fun z : ℂ => 4 * z) hfix
      linear_combination -hmul
    · rintro ⟨htau, heq⟩
      refine ⟨htau, ?_⟩
      unfold inverseMap thetaTauRemainder
      rw [heq]
      ring
  rcases h with ⟨tau, htau, hunique⟩
  refine ⟨tau, (hiff tau).mp htau, ?_⟩
  intro sigma hsigma
  exact hunique sigma ((hiff sigma).mpr hsigma)

end GeneralCK.Certificates.E8TauInverseContraction

end


