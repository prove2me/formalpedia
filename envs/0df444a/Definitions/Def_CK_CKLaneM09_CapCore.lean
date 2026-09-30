-- Prove2me | Definitions.Def_CK_CKLaneM09_CapCore
-- name    : CK_CKLaneM09_CapCore
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:46:21.968986+00:00
-- url     : https://prove2.me/theorems/964cb35d-1a62-489f-88c3-b6ec7aca61b7
-- title:
--   Courtade–Kumar proof module `CKLaneM09.CapCore` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM09.CapCore` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM09.CapCore` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM09.CapCore (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM09/CapCore.lean)

import Definitions.Def_CK_CKLaneD_FleetBase
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_GeneralCK_PsiEndpointPlaneGlobal
import Definitions.Def_CK_GeneralCK_DeterministicCap

-- ===== source module CKLaneM09.CapCore =====
section

/-!
# Lane M09: analytic core of the archived `global_cap_slope` owner

* `cap_plane_cost`: the global supporting plane at the deterministic cap `(μ.a, μ.b)`
  (`GeneralCK.PsiEndpointPlane.supporting_plane_of_contact` with contact point `(a, b)`),
  averaged over the law: `j + A (H a - e) + B (H b - f) ≤ cost`, `j = interiorCost a b`.
* `capA`, `capB`, `capDet`: the explicit solution of the two contact equations at `(a, b)`
  (the archive's `A = (b-a)^2 A0`, `D = (b-a)^2 D0`), `cap_contact`.
* `cap_slope_bound`: slope comparison.  If `k ≤ A`, `k ≤ B`, `I = H(m) - E ≤ Y` and
  `P1 ≤ U` on `[0, Y]` with `U - 4 ≤ 2 k`, then `candidateGap psi ≤ cost`.
  Uses `CKLaneD.law_gap_le_P` (Jensen split), `GeneralCK.deterministic_cap_bound` (`P Δ ≤ j`),
  `GeneralCK.Scalar.P_increment_upper`, `GeneralCK.Scalar.four_mul_le_P`.
No numerical fact is assumed here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM09

open GeneralCK GeneralCK.PsiEndpointPlane

/-- The supporting plane at the deterministic cap, averaged over an arbitrary finite law. -/
theorem cap_plane_cost {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {A B : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hab : μ.a < μ.b)
    (h1 : contactLevel1 A B μ.a μ.b = 0) (h0 : contactLevel0 A B μ.a μ.b = 0) :
    interiorCost μ.a μ.b + A * (H μ.a - μ.e) + B * (H μ.b - μ.f) ≤ μ.cost := by
  have hxy : (μ.a, μ.b) ∈ triangle := ⟨μ.a_interior.1, hab, μ.b_interior.2⟩
  have hplane := supporting_plane_of_contact hA hB hxy h1 h0
  have havg := averaged_supporting_plane μ hplane
  have hq : quotient A B μ.a μ.b * (μ.b - μ.a) =
      Real.log 2 * (interiorCost μ.a μ.b + A * H μ.a + B * H μ.b) := by
    unfold quotient naturalCost
    rw [binEntropy_eq_log_two_mul_H, binEntropy_eq_log_two_mul_H]
    have hne : μ.b - μ.a ≠ 0 := (sub_pos.mpr hab).ne'
    rw [div_mul_cancel₀ _ hne]
    ring
  rw [hq] at havg
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : Real.log 2 * (interiorCost μ.a μ.b + A * (H μ.a - μ.e) + B * (H μ.b - μ.f)) ≤
      Real.log 2 * μ.cost := by
    have e1 : Real.log 2 * (interiorCost μ.a μ.b + A * (H μ.a - μ.e) + B * (H μ.b - μ.f)) =
        Real.log 2 * (interiorCost μ.a μ.b + A * H μ.a + B * H μ.b) -
          (A * (Real.log 2 * μ.e) + B * (Real.log 2 * μ.f)) := by ring
    rw [e1]
    linarith
  exact le_of_mul_le_mul_left key hl2

/-- Determinant of the contact system at `(a, b)`
(`= (-log a)(-log (1-b)) - (-log b)(-log (1-a))`). -/
noncomputable def capDet (a b : ℝ) : ℝ :=
  Real.log a * Real.log (1 - b) - Real.log b * Real.log (1 - a)

/-- First plane coefficient (entropy weight of the left child). -/
noncomputable def capA (a b : ℝ) : ℝ :=
  ((b - a) ^ 2 / (2 * (1 - a) * (1 - b)) * Real.log b -
    (b - a) ^ 2 / (2 * a * b) * Real.log (1 - b)) / capDet a b

/-- Second plane coefficient (entropy weight of the right child). -/
noncomputable def capB (a b : ℝ) : ℝ :=
  ((b - a) ^ 2 / (2 * a * b) * Real.log (1 - a) -
    (b - a) ^ 2 / (2 * (1 - a) * (1 - b)) * Real.log a) / capDet a b

theorem cap_contact {a b : ℝ} (ha : 0 < a) (hab : a < b) (_hb1 : b < 1) (hdet : capDet a b ≠ 0) :
    contactLevel1 (capA a b) (capB a b) a b = 0 ∧
      contactLevel0 (capA a b) (capB a b) a b = 0 := by
  have _hb : b ≠ 0 := (by linarith : (0 : ℝ) < b).ne'
  have _ha : a ≠ 0 := ha.ne'
  have key1 : capA a b * Real.log a + capB a b * Real.log b =
      -((b - a) ^ 2 / (2 * a * b)) := by
    have h : capA a b * Real.log a + capB a b * Real.log b =
        (((b - a) ^ 2 / (2 * (1 - a) * (1 - b)) * Real.log b -
            (b - a) ^ 2 / (2 * a * b) * Real.log (1 - b)) * Real.log a +
          ((b - a) ^ 2 / (2 * a * b) * Real.log (1 - a) -
            (b - a) ^ 2 / (2 * (1 - a) * (1 - b)) * Real.log a) * Real.log b) / capDet a b := by
      unfold capA capB; ring
    rw [h, div_eq_iff hdet]
    unfold capDet
    ring
  have key0 : capA a b * Real.log (1 - a) + capB a b * Real.log (1 - b) =
      -((b - a) ^ 2 / (2 * (1 - a) * (1 - b))) := by
    have h : capA a b * Real.log (1 - a) + capB a b * Real.log (1 - b) =
        (((b - a) ^ 2 / (2 * (1 - a) * (1 - b)) * Real.log b -
            (b - a) ^ 2 / (2 * a * b) * Real.log (1 - b)) * Real.log (1 - a) +
          ((b - a) ^ 2 / (2 * a * b) * Real.log (1 - a) -
            (b - a) ^ 2 / (2 * (1 - a) * (1 - b)) * Real.log a) * Real.log (1 - b)) /
          capDet a b := by
      unfold capA capB; ring
    rw [h, div_eq_iff hdet]
    unfold capDet
    ring
  have s1 : (a - b) ^ 2 / (2 * a * b) = (b - a) ^ 2 / (2 * a * b) := by ring
  have s0 : (a - b) ^ 2 / (2 * (1 - a) * (1 - b)) = (b - a) ^ 2 / (2 * (1 - a) * (1 - b)) := by
    ring
  constructor
  · unfold contactLevel1
    rw [s1]
    linarith
  · unfold contactLevel0
    rw [s0]
    linarith

/-- `capA` in the archive's interval form `(b-a)^2 (r1 m22 - r2 m12) / det`. -/
theorem capA_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    capA a b = (b - a) ^ 2 * ((1 / (2 * a * b)) * (-Real.log (1 - b)) -
      (1 / (2 * (1 - a) * (1 - b))) * (-Real.log b)) / capDet a b := by
  have hb0 : b ≠ 0 := (by linarith : (0 : ℝ) < b).ne'
  have ha1 : 1 - a ≠ 0 := (by linarith : (0 : ℝ) < 1 - a).ne'
  have hb1 : 1 - b ≠ 0 := (by linarith : (0 : ℝ) < 1 - b).ne'
  unfold capA
  congr 1
  field_simp
  ring

/-- `capB` in the archive's interval form `(b-a)^2 (m11 r2 - m21 r1) / det`. -/
theorem capB_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    capB a b = (b - a) ^ 2 * ((-Real.log a) * (1 / (2 * (1 - a) * (1 - b))) -
      (-Real.log (1 - a)) * (1 / (2 * a * b))) / capDet a b := by
  have hb0 : b ≠ 0 := (by linarith : (0 : ℝ) < b).ne'
  have ha1 : 1 - a ≠ 0 := (by linarith : (0 : ℝ) < 1 - a).ne'
  have hb1 : 1 - b ≠ 0 := (by linarith : (0 : ℝ) < 1 - b).ne'
  unfold capB
  congr 1
  field_simp
  ring

theorem capDet_eq (a b : ℝ) :
    capDet a b = (-Real.log a) * (-Real.log (1 - b)) - (-Real.log b) * (-Real.log (1 - a)) := by
  unfold capDet; ring

/-- Interval quotient lower bound: `dlo^2 (nlo / Dhi) ≤ d^2 n / D`. -/
theorem sq_quot_lower {d dlo n nlo D Dhi : ℝ} (hd : dlo ≤ d) (hdlo : 0 ≤ dlo) (hn : nlo ≤ n)
    (hnlo : 0 < nlo) (hD : 0 < D) (hDhi : D ≤ Dhi) :
    dlo ^ 2 * (nlo / Dhi) ≤ d ^ 2 * n / D := by
  have hDhi0 : 0 < Dhi := lt_of_lt_of_le hD hDhi
  have hsq : dlo ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hdlo hd 2
  have hq1 : nlo / Dhi ≤ nlo / D := div_le_div_of_nonneg_left hnlo.le hD hDhi
  have hq2 : nlo / D ≤ n / D := div_le_div_of_nonneg_right hn hD.le
  have hq : nlo / Dhi ≤ n / D := hq1.trans hq2
  have hq0 : 0 ≤ nlo / Dhi := div_nonneg hnlo.le hDhi0.le
  calc dlo ^ 2 * (nlo / Dhi) ≤ d ^ 2 * (n / D) :=
        mul_le_mul hsq hq hq0 (sq_nonneg d)
    _ = d ^ 2 * n / D := by ring

/-- The slope comparison at the deterministic cap. -/
theorem cap_slope_bound {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) {A B k Y U : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hab : μ.a < μ.b)
    (h1 : contactLevel1 A B μ.a μ.b = 0) (h0 : contactLevel0 A B μ.a μ.b = 0)
    (hkA : k ≤ A) (hkB : k ≤ B)
    (hI : H ((μ.a + μ.b) / 2) - μ.meanEntropy ≤ Y)
    (hP1 : ∀ x : ℝ, 0 ≤ x → x ≤ Y → Scalar.P1 x ≤ U)
    (hU : U - 4 ≤ 2 * k) :
    candidateGap psi μ.a μ.b μ.e μ.f ≤ μ.cost := by
  have hgap := CKLaneD.law_gap_le_P μ
  have hs := CKLaneD.law_deficit_mem μ
  have hplane := cap_plane_cost μ hA hB hab h1 h0
  have hcap := deterministic_cap_bound μ.a_interior.1 μ.a_interior.2
    μ.b_interior.1 μ.b_interior.2
  have hdrop := μ.entropyDrop_nonneg
  have hinfo := μ.information_mem
  have he := μ.e_le_cap
  have hf := μ.f_le_cap
  unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at hdrop
  unfold InteriorLaw.information InteriorLaw.midpoint at hinfo
  generalize hIdef : H ((μ.a + μ.b) / 2) - μ.meanEntropy = I at hgap hI hinfo
  generalize hsdef : (H μ.a + H μ.b) / 2 - μ.meanEntropy = s at hgap hs
  generalize hΔdef : H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 = Δ at hcap hdrop
  have hIΔ : I = Δ + s := by rw [← hIdef, ← hsdef, ← hΔdef]; ring
  have hsplit : 2 * s = (H μ.a - μ.e) + (H μ.b - μ.f) := by
    rw [← hsdef]; unfold InteriorLaw.meanEntropy; ring
  have e1 : k * (H μ.a - μ.e) ≤ A * (H μ.a - μ.e) :=
    mul_le_mul_of_nonneg_right hkA (by linarith)
  have e2 : k * (H μ.b - μ.f) ≤ B * (H μ.b - μ.f) :=
    mul_le_mul_of_nonneg_right hkB (by linarith)
  have hks : k * (2 * s) = k * (H μ.a - μ.e) + k * (H μ.b - μ.f) := by rw [hsplit]; ring
  have hplane2 : interiorCost μ.a μ.b + k * (2 * s) ≤ μ.cost := by linarith
  have h4 := Scalar.four_mul_le_P hs.1 hs.2
  rcases eq_or_lt_of_le hs.1 with hs0 | hspos
  · -- zero mean deficit: the deterministic cap itself
    subst hs0
    have hIeq : I = Δ := by linarith
    subst hIeq
    have hk0 : k * (2 * 0) = 0 := by ring
    linarith
  · have hIpos : 0 < I := by linarith
    have hinc := Scalar.P_increment_upper hdrop (by linarith : Δ ≤ I) hIpos hinfo.2
    rw [← Scalar.P1_eq_deriv hIpos, show I - Δ = s by linarith] at hinc
    have hP1I := hP1 I hIpos.le hI
    have hsU : s * Scalar.P1 I ≤ s * U := mul_le_mul_of_nonneg_left hP1I hs.1
    have hsk : s * (U - 4) ≤ s * (2 * k) := mul_le_mul_of_nonneg_left hU hs.1
    have hks' : k * (2 * s) = s * (2 * k) := by ring
    have hsU4 : s * (U - 4) = s * U - 4 * s := by ring
    linarith

end CKLaneM09

end


