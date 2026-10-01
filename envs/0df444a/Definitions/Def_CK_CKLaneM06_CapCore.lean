-- Prove2me | Definitions.Def_CK_CKLaneM06_CapCore
-- name    : CK_CKLaneM06_CapCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T04:18:16.202769+00:00
-- url     : https://prove2.me/theorems/c0025392-0297-4b32-b0ad-e303bd49982b
-- title:
--   Courtade–Kumar proof module `CKLaneM06.CapCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM06.CapCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM06.CapCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM06.CapCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM06/CapCore.lean)

import Definitions.Def_CK_CKLaneM06_CapBonus
import Definitions.Def_CK_CKLaneM07_KappaLogSum
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGlobal
import Definitions.Def_CK_GeneralCK_ScalarGap
import Definitions.Def_CK_GeneralCK_DeterministicCap
import Definitions.Def_CK_GeneralCK_BellmanAssembly

-- ===== source module CKLaneM06.CapCore =====
section

/-!
# Lane M06: analytic core of the cap theorem (5)

For a finite interior law with `a < b`, mean deficit `s ≤ S` and `Δ + S < 1`:

* `psi_gap_le_cost_of_endpoint` : a law-level entropy slope `ζ ≥ j + λ s` and the endpoint inequality
  `G(S) = j + λS - P(Δ+S) + P(S) ≥ 0` give `ζ ≥ R_ψ` (`candidateGap psi ≤ cost`) for EVERY feasible split
  (corpus `Scalar.gap_endpoint_criterion` = concavity of `G`, corpus `deterministic_cap_bound` = `G(0) ≥ 0`,
  corpus `psi_gap_le_splitBound` = Jensen).
* `slope_kappa` : `ζ ≥ j + κ d²/(2 b (1-a)) · s` (M07 `kappa_cost_lower_bound`, `0 ≤ κ ≤ 2`).
* `slope_plane` : `ζ ≥ j + 2 l d² s` whenever `0 < l ≤ min(A0, D0)`, where `(d² A0, d² D0)` is the exact
  mean-contact plane at `(a,b)` (archive system (2)); corpus `supporting_plane_of_contact` (Theorem 3.10,
  arbitrary ordered contacts with positive coefficients) + `averaged_supporting_plane`.
* `psi_gap_le_cost_of_eq` : the equal-mean case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM06.Cap

open GeneralCK

section Core

variable {ι : Type*} [Fintype ι]

/-- Slope + endpoint criterion ⇒ `ζ ≥ R_ψ` for every feasible split with deficit `≤ S`. -/
theorem psi_gap_le_cost_of_endpoint (μ : InteriorLaw ι) {lam S : ℝ}
    (hslope : interiorCost μ.a μ.b + lam * μ.meanDeficit ≤ μ.cost)
    (hS : μ.meanDeficit ≤ S) (hI : μ.entropyDrop + S < 1)
    (hend : 0 ≤ Scalar.gap (interiorCost μ.a μ.b) lam μ.entropyDrop S) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have hΔ0 := μ.entropyDrop_nonneg
  have hs0 := μ.meanDeficit_mem.1
  have hS0 : 0 ≤ S := hs0.trans hS
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hzero : Scalar.P μ.entropyDrop ≤ interiorCost μ.a μ.b :=
    deterministic_cap_bound ha.1 ha.2 hb.1 hb.2
  have hcrit := Scalar.gap_endpoint_criterion hΔ0 hS0 hI hzero hend hs0 hS
  calc candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.splitBound := μ.psi_gap_le_splitBound
    _ = Scalar.P (μ.entropyDrop + μ.meanDeficit) - Scalar.P μ.meanDeficit := rfl
    _ ≤ interiorCost μ.a μ.b + lam * μ.meanDeficit := hcrit
    _ ≤ μ.cost := hslope

theorem meanDeficit_eq (μ : InteriorLaw ι) :
    μ.meanDeficit = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
  unfold InteriorLaw.meanDeficit InteriorLaw.meanEntropy
  ring

theorem entropyDrop_eq (μ : InteriorLaw ι) :
    μ.entropyDrop = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := rfl

/-- The kappa-enhanced log-sum slope (M07). -/
theorem slope_kappa (μ : InteriorLaw ι) (hab : μ.a < μ.b) {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ2 : κ ≤ 2)
    (c1 : κ * -Real.log (1 - μ.a) ≤ μ.a / (1 - μ.a)) (c2 : κ * -Real.log μ.a ≤ (1 - μ.a) / μ.a)
    (c3 : κ * -Real.log (1 - μ.b) ≤ μ.b / (1 - μ.b)) (c4 : κ * -Real.log μ.b ≤ (1 - μ.b) / μ.b) :
    interiorCost μ.a μ.b + κ * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) * μ.meanDeficit ≤ μ.cost := by
  have h := CKLaneM07.kappa_cost_lower_bound μ hκ0 hκ2 c1 c2 c3 c4
  have hV : LogSum.V μ.a μ.b = μ.b * (1 - μ.a) := by
    simp only [LogSum.V, max_eq_right hab.le, min_eq_left hab.le]
  rw [hV] at h
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hVpos : 0 < μ.b * (1 - μ.a) := mul_pos hb.1 (by linarith)
  have e : κ * ((μ.a - μ.b) ^ 2 / (4 * (μ.b * (1 - μ.a)))) * (H μ.a - μ.e + (H μ.b - μ.f)) =
      κ * (μ.b - μ.a) ^ 2 / (2 * (μ.b * (1 - μ.a))) * μ.meanDeficit := by
    unfold InteriorLaw.meanDeficit
    field_simp
    ring
  linarith

end Core

/-! ## The mean-contact plane at the means -/

/-- Determinant of the archive system (2) (natural logs). -/
noncomputable def pDet (a b : ℝ) : ℝ :=
  (-Real.log a) * (-Real.log (1 - b)) - (-Real.log b) * (-Real.log (1 - a))

/-- Normalized first coefficient `A/(b-a)²` of the mean-contact plane. -/
noncomputable def pA0 (a b : ℝ) : ℝ :=
  ((-Real.log (1 - b)) / (2 * a * b) - (-Real.log b) / (2 * (1 - a) * (1 - b))) / pDet a b

/-- Normalized second coefficient `D/(b-a)²` of the mean-contact plane. -/
noncomputable def pD0 (a b : ℝ) : ℝ :=
  ((-Real.log a) / (2 * (1 - a) * (1 - b)) - (-Real.log (1 - a)) / (2 * a * b)) / pDet a b

/-- Cramer's rule for the 2×2 contact system. -/
theorem cramer2 {m11 m12 m21 m22 r1 r2 : ℝ} (hdet : m11 * m22 - m12 * m21 ≠ 0) :
    (r1 * m22 - r2 * m12) / (m11 * m22 - m12 * m21) * m11 +
        (m11 * r2 - m21 * r1) / (m11 * m22 - m12 * m21) * m12 = r1 ∧
      (r1 * m22 - r2 * m12) / (m11 * m22 - m12 * m21) * m21 +
        (m11 * r2 - m21 * r1) / (m11 * m22 - m12 * m21) * m22 = r2 := by
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    ring

theorem pA0_eq (a b : ℝ) : pA0 a b =
    (1 / (2 * a * b) * (-Real.log (1 - b)) - 1 / (2 * (1 - a) * (1 - b)) * (-Real.log b)) /
      ((-Real.log a) * (-Real.log (1 - b)) - (-Real.log b) * (-Real.log (1 - a))) := by
  unfold pA0 pDet
  ring

theorem pD0_eq (a b : ℝ) : pD0 a b =
    ((-Real.log a) * (1 / (2 * (1 - a) * (1 - b))) - (-Real.log (1 - a)) * (1 / (2 * a * b))) /
      ((-Real.log a) * (-Real.log (1 - b)) - (-Real.log b) * (-Real.log (1 - a))) := by
  unfold pD0 pDet
  ring

theorem contact_eqs {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hdet : pDet a b ≠ 0) :
    PsiEndpointPlane.contactLevel1 ((b - a) ^ 2 * pA0 a b) ((b - a) ^ 2 * pD0 a b) a b = 0 ∧
      PsiEndpointPlane.contactLevel0 ((b - a) ^ 2 * pA0 a b) ((b - a) ^ 2 * pD0 a b) a b = 0 := by
  have hb0 : 0 < b := ha.trans hab
  have ha1 : 0 < 1 - a := by linarith
  have hb1 : 0 < 1 - b := by linarith
  unfold pDet at hdet
  obtain ⟨k1, k2⟩ := cramer2 (m11 := -Real.log a) (m12 := -Real.log b) (m21 := -Real.log (1 - a))
    (m22 := -Real.log (1 - b)) (r1 := 1 / (2 * a * b)) (r2 := 1 / (2 * (1 - a) * (1 - b))) hdet
  rw [← pA0_eq, ← pD0_eq] at k1 k2
  unfold PsiEndpointPlane.contactLevel1 PsiEndpointPlane.contactLevel0
  have e1 : (a - b) ^ 2 / (2 * a * b) = (b - a) ^ 2 * (1 / (2 * a * b)) := by ring
  have e2 : (a - b) ^ 2 / (2 * (1 - a) * (1 - b)) = (b - a) ^ 2 * (1 / (2 * (1 - a) * (1 - b))) := by
    ring
  rw [e1, e2]
  constructor
  · linear_combination (-(b - a) ^ 2) * k1
  · linear_combination (-(b - a) ^ 2) * k2

section Plane

variable {ι : Type*} [Fintype ι]

/-- The mean-contact supporting plane: `ζ ≥ j + 2 l d² s` for `0 < l ≤ min(A0, D0)`. -/
theorem slope_plane (μ : InteriorLaw ι) (hab : μ.a < μ.b) {l : ℝ} (hl : 0 < l)
    (hA : l ≤ pA0 μ.a μ.b) (hD : l ≤ pD0 μ.a μ.b) (hdet : pDet μ.a μ.b ≠ 0) :
    interiorCost μ.a μ.b + 2 * l * (μ.b - μ.a) ^ 2 * μ.meanDeficit ≤ μ.cost := by
  have ha := μ.a_interior
  have hb := μ.b_interior
  have hd : 0 < μ.b - μ.a := by linarith
  have hd2 : 0 < (μ.b - μ.a) ^ 2 := by positivity
  set A := (μ.b - μ.a) ^ 2 * pA0 μ.a μ.b with hAdef
  set B := (μ.b - μ.a) ^ 2 * pD0 μ.a μ.b with hBdef
  have hApos : 0 < A := mul_pos hd2 (lt_of_lt_of_le hl hA)
  have hBpos : 0 < B := mul_pos hd2 (lt_of_lt_of_le hl hD)
  have hxy : (μ.a, μ.b) ∈ PsiEndpointPlane.triangle := ⟨ha.1, hab, hb.2⟩
  obtain ⟨h1, h0⟩ := contact_eqs ha.1 hab hb.2 hdet
  have hplane := PsiEndpointPlane.supporting_plane_of_contact hApos hBpos hxy h1 h0
  have havg := PsiEndpointPlane.averaged_supporting_plane μ hplane
  have hq : PsiEndpointPlane.quotient A B μ.a μ.b * (μ.b - μ.a) =
      Real.log 2 * (interiorCost μ.a μ.b + A * H μ.a + B * H μ.b) := by
    unfold PsiEndpointPlane.quotient PsiEndpointPlane.naturalCost
    rw [PsiEndpointPlane.binEntropy_eq_log_two_mul_H, PsiEndpointPlane.binEntropy_eq_log_two_mul_H]
    field_simp
  rw [hq] at havg
  have hL := log_two_pos
  have hmain : interiorCost μ.a μ.b + A * (H μ.a - μ.e) + B * (H μ.b - μ.f) ≤ μ.cost := by
    have h' : Real.log 2 * (interiorCost μ.a μ.b + A * (H μ.a - μ.e) + B * (H μ.b - μ.f)) ≤
        Real.log 2 * μ.cost := by nlinarith
    exact le_of_mul_le_mul_left h' hL
  have hx := μ.left_deficit_mem.1
  have hy := μ.right_deficit_mem.1
  have hAl : (μ.b - μ.a) ^ 2 * l ≤ A := mul_le_mul_of_nonneg_left hA hd2.le
  have hBl : (μ.b - μ.a) ^ 2 * l ≤ B := mul_le_mul_of_nonneg_left hD hd2.le
  have e : 2 * l * (μ.b - μ.a) ^ 2 * μ.meanDeficit =
      (μ.b - μ.a) ^ 2 * l * (H μ.a - μ.e) + (μ.b - μ.a) ^ 2 * l * (H μ.b - μ.f) := by
    unfold InteriorLaw.meanDeficit
    ring
  have t1 := mul_le_mul_of_nonneg_right hAl hx
  have t2 := mul_le_mul_of_nonneg_right hBl hy
  linarith

/-- Equal means: `R_ψ ≤ 0 ≤ ζ`. -/
theorem psi_gap_le_cost_of_eq (μ : InteriorLaw ι) (hab : μ.a = μ.b) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have h := μ.psi_gap_le_splitBound
  have hΔ : μ.entropyDrop = 0 := by
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint
    rw [hab]
    ring_nf
  have hsb : μ.splitBound = 0 := by
    unfold InteriorLaw.splitBound
    rw [hΔ, zero_add, sub_self]
  have hc : 0 ≤ μ.cost := by
    have hl := LogSum.cost_lower_bound μ
    have hV := LogSum.V_pos μ.a_interior μ.b_interior
    have hx := μ.left_deficit_mem.1
    have hy := μ.right_deficit_mem.1
    have hj : interiorCost μ.a μ.b = 0 := by
      unfold interiorCost
      rw [hab]
      ring
    have hnn : 0 ≤ (μ.a - μ.b) ^ 2 / (4 * LogSum.V μ.a μ.b) * (H μ.a - μ.e + (H μ.b - μ.f)) := by
      apply mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (by linarith)
    linarith
  linarith

end Plane

end CKLaneM06.Cap

end


