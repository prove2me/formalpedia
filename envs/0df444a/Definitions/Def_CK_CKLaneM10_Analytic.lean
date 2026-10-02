-- Prove2me | Definitions.Def_CK_CKLaneM10_Analytic
-- name    : CK_CKLaneM10_Analytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T15:37:22.368408+00:00
-- url     : https://prove2.me/theorems/c6d0c7cf-f8c5-4853-8e6f-757b4e7a1f76
-- title:
--   Courtade–Kumar proof module `CKLaneM10.Analytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM10.Analytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM10.Analytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM10.Analytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM10/Analytic.lean)

import Definitions.Def_CK_CKLaneD_FleetBase
import Definitions.Def_CK_GeneralCK_PsiFeasibleImbalance

-- ===== source module CKLaneM10.Analytic =====
section

/-!
# Lane M10: analytic lemmas for the `global_feasible_split` kernel

* `law_gap_le_split`: the psi candidate gap is bounded by the cap-sensitive (feasible) split
  bound with RATIONAL cap enclosures, derived from the provider's
  `GeneralCK.Scalar.feasible_imbalance_lower` (manuscript eq. (108)) applied to the law's own
  deficits `H a - e ≤ H a ≤ cA`, `H b - f ≤ H b ≤ cB` (feasibility `e, f > 0`).
* `split_mono`: the feasible-split profile average is monotone in the mean deficit
  (from `GeneralCK.Scalar.P_increment_lower`).
* `plane_cost_lower_asym`: an explicit ASYMMETRIC supporting plane at any contact point
  `0 < x < y < 1` whose closed-form coefficients are positive, obtained from the provider's
  `supporting_plane_of_contact` + `averaged_supporting_plane` (no contact-existence premise).
-/

namespace CKLaneM10

open GeneralCK GeneralCK.PsiEndpointPlane Set

/-! ## The scalar profile -/

theorem P_mono {p q : ℝ} (hp : 0 ≤ p) (hq : q < 1) (hpq : p ≤ q) :
    Scalar.P p ≤ Scalar.P q := by
  have := Scalar.P_increment_lower hp hq hpq
  linarith

/-- The feasible-split profile sum is monotone in the mean deficit, for a fixed cap `c`. -/
theorem split_mono {sL s c : ℝ} (h0 : 0 ≤ sL) (hs : sL ≤ s)
    (h1 : s + max 0 (s - c) < 1) :
    Scalar.P (sL - max 0 (sL - c)) + Scalar.P (sL + max 0 (sL - c)) ≤
      Scalar.P (s - max 0 (s - c)) + Scalar.P (s + max 0 (s - c)) := by
  have hs1 : s < 1 := by
    have := le_max_left 0 (s - c)
    linarith
  rcases le_total s c with hsc | hcs
  · have hsLc : sL ≤ c := hs.trans hsc
    rw [max_eq_left (by linarith : sL - c ≤ 0), max_eq_left (by linarith : s - c ≤ 0)]
    simp only [sub_zero, add_zero]
    have := P_mono h0 hs1 hs
    linarith
  · rw [max_eq_right (by linarith : 0 ≤ s - c)] at h1 ⊢
    have e1 : s - (s - c) = c := by ring
    rw [e1]
    rcases le_total sL c with hsLc | hcsL
    · rw [max_eq_left (by linarith : sL - c ≤ 0)]
      simp only [sub_zero, add_zero]
      have hc1 : c < 1 := by linarith
      have h2 := P_mono h0 hc1 hsLc
      have h3 := P_mono h0 h1 (by linarith : sL ≤ s + (s - c))
      linarith
    · rw [max_eq_right (by linarith : 0 ≤ sL - c)]
      have e2 : sL - (sL - c) = c := by ring
      rw [e2]
      have h3 := P_mono (by linarith : 0 ≤ sL + (sL - c)) h1
        (by linarith : sL + (sL - c) ≤ s + (s - c))
      linarith

/-! ## The feasible (cap-sensitive) split bound with rational caps -/

theorem deficit_eq {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) :
    ((H μ.a - μ.e) + (H μ.b - μ.f)) / 2 = (H μ.a + H μ.b) / 2 - μ.meanEntropy := by
  unfold InteriorLaw.meanEntropy
  ring

/-- Law-level feasible split bound: `s = C - E` is the mean deficit, `cA ≥ H a`, `cB ≥ H b`. -/
theorem law_gap_le_split {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {cA cB : ℝ}
    (hA : H μ.a ≤ cA) (hB : H μ.b ≤ cB) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤
      Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) -
        (Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy -
            max 0 ((H μ.a + H μ.b) / 2 - μ.meanEntropy - min cA cB)) +
          Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy +
            max 0 ((H μ.a + H μ.b) / 2 - μ.meanEntropy - min cA cB))) / 2 := by
  have h := Scalar.feasible_imbalance_lower μ.left_deficit_mem μ.right_deficit_mem
    (by linarith [μ.e_pos] : H μ.a - μ.e ≤ cA) (by linarith [μ.f_pos] : H μ.b - μ.f ≤ cB)
  dsimp only at h
  rw [deficit_eq μ] at h
  have hg : candidateGap psi μ.a μ.b μ.e μ.f =
      Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) -
        (Scalar.P (H μ.a - μ.e) + Scalar.P (H μ.b - μ.f)) / 2 := by
    simp only [candidateGap, psi_eq_P]
    rfl
  rw [hg]
  linarith

theorem law_split_args {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {cA cB : ℝ}
    (hA : H μ.a ≤ cA) (hB : H μ.b ≤ cB) :
    (H μ.a + H μ.b) / 2 - μ.meanEntropy +
      max 0 ((H μ.a + H μ.b) / 2 - μ.meanEntropy - min cA cB) < 1 := by
  have h := Scalar.feasible_imbalance_args_mem μ.left_deficit_mem μ.right_deficit_mem
    (by linarith [μ.e_pos] : H μ.a - μ.e ≤ cA) (by linarith [μ.f_pos] : H μ.b - μ.f ≤ cB)
  dsimp only at h
  rw [deficit_eq μ] at h
  exact h.2.2

/-! ## Explicit asymmetric supporting plane -/

/-- Closed-form solution of the two linear contact equations
`A L1 + B L2 = r1`, `A M1 + B M2 = r2`. -/
noncomputable def solA (L1 L2 M1 M2 r1 r2 : ℝ) : ℝ := (r1 * M2 - r2 * L2) / (L1 * M2 - L2 * M1)
noncomputable def solB (L1 L2 M1 M2 r1 r2 : ℝ) : ℝ := (r2 * L1 - r1 * M1) / (L1 * M2 - L2 * M1)

theorem sol_spec {L1 L2 M1 M2 r1 r2 : ℝ} (hdet : L1 * M2 - L2 * M1 ≠ 0) :
    solA L1 L2 M1 M2 r1 r2 * L1 + solB L1 L2 M1 M2 r1 r2 * L2 = r1 ∧
      solA L1 L2 M1 M2 r1 r2 * M1 + solB L1 L2 M1 M2 r1 r2 * M2 = r2 := by
  unfold solA solB
  constructor
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hdet]
    ring

/-- Contact-equation data at `(x, y)`: `L1 = -log x`, `L2 = -log y`, `M1 = -log (1-x)`,
`M2 = -log (1-y)`, `r1 = (x-y)^2/(2xy)`, `r2 = (x-y)^2/(2(1-x)(1-y))`. -/
noncomputable def planeDet (x y : ℝ) : ℝ :=
  (-Real.log x) * (-Real.log (1 - y)) - (-Real.log y) * (-Real.log (1 - x))

noncomputable def planeA (x y : ℝ) : ℝ :=
  solA (-Real.log x) (-Real.log y) (-Real.log (1 - x)) (-Real.log (1 - y))
    ((x - y) ^ 2 / (2 * x * y)) ((x - y) ^ 2 / (2 * (1 - x) * (1 - y)))

noncomputable def planeB (x y : ℝ) : ℝ :=
  solB (-Real.log x) (-Real.log y) (-Real.log (1 - x)) (-Real.log (1 - y))
    ((x - y) ^ 2 / (2 * x * y)) ((x - y) ^ 2 / (2 * (1 - x) * (1 - y)))

/-- The plane's slope coefficient, in bit units. -/
noncomputable def planeC (x y : ℝ) : ℝ :=
  (interiorCost x y + planeA x y * H x + planeB x y * H y) / (y - x)

theorem plane_contact {x y : ℝ} (hdet : planeDet x y ≠ 0) :
    contactLevel1 (planeA x y) (planeB x y) x y = 0 ∧
      contactLevel0 (planeA x y) (planeB x y) x y = 0 := by
  obtain ⟨h1, h2⟩ := sol_spec (L1 := -Real.log x) (L2 := -Real.log y)
    (M1 := -Real.log (1 - x)) (M2 := -Real.log (1 - y))
    (r1 := (x - y) ^ 2 / (2 * x * y)) (r2 := (x - y) ^ 2 / (2 * (1 - x) * (1 - y))) hdet
  unfold contactLevel1 contactLevel0 planeA planeB
  constructor
  · linear_combination -h1
  · linear_combination -h2

/-- Asymmetric supporting-plane cost floor at a contact point with positive coefficients. -/
theorem plane_cost_lower_asym {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {x y : ℝ}
    (hx : 0 < x) (hxy : x < y) (hy : y < 1) (hdet : planeDet x y ≠ 0)
    (hA : 0 < planeA x y) (hB : 0 < planeB x y) :
    planeC x y * (μ.b - μ.a) - planeA x y * μ.e - planeB x y * μ.f ≤ μ.cost := by
  obtain ⟨h1, h0⟩ := plane_contact hdet
  have hplane := supporting_plane_of_contact hA hB ⟨hx, hxy, hy⟩ h1 h0
  have havg := averaged_supporting_plane μ hplane
  have hyx : y - x ≠ 0 := (sub_pos.mpr hxy).ne'
  have hq : quotient (planeA x y) (planeB x y) x y = Real.log 2 * planeC x y := by
    unfold quotient naturalCost planeC
    rw [binEntropy_eq_log_two_mul_H, binEntropy_eq_log_two_mul_H]
    field_simp
  rw [hq] at havg
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log 2 * (planeC x y * (μ.b - μ.a) - planeA x y * μ.e - planeB x y * μ.f) ≤
      Real.log 2 * μ.cost := by
    nlinarith [havg]
  exact le_of_mul_le_mul_left key hl2

/-! ## Small real-arithmetic helpers -/

theorem J_le_of_ge_half {b b0 : ℝ} (hb0 : 1 / 2 ≤ b0) (hbb : b0 ≤ b) (hb1 : b < 1) :
    J b ≤ J b0 := by
  have h := J_antitone (u := 1 - b) (v := 1 - b0) (by linarith) (by linarith) (by linarith)
  rw [J_complement, J_complement] at h
  linarith

end CKLaneM10

end


