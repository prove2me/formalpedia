-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Box
-- name    : CK_CKLaneA1_R5Box
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:35:26.91437+00:00
-- url     : https://prove2.me/theorems/f6cf634b-cabe-4241-bf65-547f8bcd13c7
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Box` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Box` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Box` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Box (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Box.lean)

import Definitions.Def_CK_CKLaneA1_R5Core
import Definitions.Def_CK_CKLaneP_EvalDy

-- ===== source module CKLaneA1.R5Box =====
section

/-!
# CKLaneA1.R5Box — the `(t, A)` cell checker for CE-stat row 5 and its soundness

Kernel-evaluated Boolean checks on rational data (Lane P's contact data `VD`, dyadic points
`N / 2^40`), proved sound once:
* `exclOK`  — Case-E exclusion data `κ` (Riemann or direct form), giving `λ < (1+κA)/2`;
* `brOK`    — contact brackets of an `x`-interval, giving `Θ(y) − Θ(x) ≤ PsiUB·(y − x)`;
* `thLoOK`, `thHiOK` — contact brackets for `Θ` value bounds.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP

/-- Contact data at the dyadic point `N / 2^40`. -/
def vd (N : ℕ) : VD := VD.ofDy 40 64 20 l2c N

/-- Admissible dyadic point: `1 ≤ N`, `2N ≤ 2^40`. -/
def okN (N : ℕ) : Bool := VD.okDy 40 N

theorem vd_sound {N : ℕ} (h : okN N = true) : (vd N).Sound := VD.ofDy_sound l2c_sound h

/-- The dyadic point `N / 2^40`. -/
def dyq (N : ℕ) : ℚ := (N : ℚ) / ((2 ^ 40 : ℕ) : ℚ)

theorem vd_v (N : ℕ) : (vd N).v = dyq N := rfl

theorem dyq_pos {N : ℕ} (h : okN N = true) : (0 : ℝ) < ((dyq N : ℚ) : ℝ) := by
  have hs := vd_sound h
  have := hs.1
  rw [vd_v] at this
  exact_mod_cast this

theorem dyq_le_half {N : ℕ} (h : okN N = true) : ((dyq N : ℚ) : ℝ) ≤ 1 / 2 := by
  have hs := vd_sound h
  have := hs.2.1
  rw [vd_v] at this
  exact VD.cast_le_half this

/-! ## Θ bounds -/

/-- Contact bracket for a `Θ` lower bound at any `x ≥ xq`. -/
def thLoOK (xq : ℚ) (N : ℕ) : Bool :=
  okN N && decide (0 < xq ∧ (vd N).v < 1 / 2 ∧ 1 - 2 * (vd N).v ≤ 2 * xq * (vd N).Hlo)

theorem thLoOK_sound {xq : ℚ} {N : ℕ} (h : thLoOK xq N = true) {x : ℝ} (hx : (xq : ℝ) ≤ x) :
    (((vd N).Slo : ℚ) : ℝ) ≤ e8Theta x := by
  unfold thLoOK at h
  have h1 := Bool.and_eq_true_iff.mp h
  obtain ⟨h0, hv, hc⟩ := of_decide_eq_true h1.2
  exact theta_ge_Slo (vd_sound h1.1) hv h0 hx hc

/-- Contact bracket for a `Θ` upper bound at any `0 < x ≤ xq`. -/
def thHiOK (xq : ℚ) (N : ℕ) : Bool :=
  okN N && decide ((vd N).v < 1 / 2 ∧ 0 < (vd N).a1 + (vd N).a2 ∧
    2 * xq * (vd N).Hhi ≤ 1 - 2 * (vd N).v)

theorem thHiOK_sound {xq : ℚ} {N : ℕ} (h : thHiOK xq N = true) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ (xq : ℝ)) : e8Theta x ≤ (((vd N).Shi : ℚ) : ℝ) := by
  unfold thHiOK at h
  have h1 := Bool.and_eq_true_iff.mp h
  obtain ⟨hv, hp, hc⟩ := of_decide_eq_true h1.2
  exact theta_le_Shi (vd_sound h1.1) hv hp hx0 hx hc

/-- Contact bracket of an `x`-interval `[x1, x2]` for mean-value bounds of `Θ`. -/
def brOK (x1 x2 : ℚ) (Na Nb : ℕ) : Bool :=
  okN Na && okN Nb && decide (0 < x1 ∧ x1 ≤ x2 ∧ (vd Na).v ≤ (vd Nb).v ∧
    2 * x2 * (vd Na).Hhi ≤ 1 - 2 * (vd Na).v ∧
    1 - 2 * (vd Nb).v ≤ 2 * x1 * (vd Nb).Hlo ∧ 0 < (vd Nb).kapLo)

theorem brOK_parts {x1 x2 : ℚ} {Na Nb : ℕ} (h : brOK x1 x2 Na Nb = true) :
    (vd Na).Sound ∧ (vd Nb).Sound ∧ 0 < x1 ∧ x1 ≤ x2 ∧ (vd Na).v ≤ (vd Nb).v ∧
      2 * x2 * (vd Na).Hhi ≤ 1 - 2 * (vd Na).v ∧
      1 - 2 * (vd Nb).v ≤ 2 * x1 * (vd Nb).Hlo ∧ 0 < (vd Nb).kapLo := by
  unfold brOK at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  obtain ⟨a, b, c, d, e, f⟩ := of_decide_eq_true h1.2
  exact ⟨vd_sound h2.1, vd_sound h2.2, a, b, c, d, e, f⟩

/-- Contacts of `x ∈ [x1, x2]` lie in the bracket. -/
theorem brOK_contact {x1 x2 : ℚ} {Na Nb : ℕ} (h : brOK x1 x2 Na Nb = true) {x : ℝ}
    (hx1 : (x1 : ℝ) ≤ x) (hx2 : x ≤ (x2 : ℝ)) :
    (((vd Na).v : ℚ) : ℝ) ≤ radialContact (2 * x) 1 ∧ radialContact (2 * x) 1 ≤ (((vd Nb).v : ℚ) : ℝ) := by
  obtain ⟨da, db, h0, -, -, hA, hB, -⟩ := brOK_parts h
  exact contact_mem_of_brackets da db h0 hA hB hx1 hx2

/-- Mean-value upper bound for `Θ` from a pointwise bound on `Θ'`. -/
theorem theta_sub_le_of_deriv {x y M : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hd : ∀ t ∈ Set.Icc x y, deriv e8Theta t ≤ M) : e8Theta y - e8Theta x ≤ M * (y - x) := by
  have hpos : ∀ t ∈ Set.Icc x y, 0 < t := fun t ht => lt_of_lt_of_le hx ht.1
  have hcont : ContinuousOn (fun t => M * t - e8Theta t) (Set.Icc x y) := by
    apply ContinuousOn.sub (continuousOn_const.mul continuousOn_id)
    exact continuousOn_e8Theta_pos.mono (fun t ht => hpos t ht)
  have hmono : MonotoneOn (fun t => M * t - e8Theta t) (Set.Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont
    · intro t ht
      have ht0 := hpos t (interior_subset ht)
      exact ((differentiableAt_id.const_mul M).sub
        (hasDerivAt_e8Theta ht0).differentiableAt).differentiableWithinAt
    · intro t ht
      have ht0 := hpos t (interior_subset ht)
      have hdd : HasDerivAt (fun t => M * t - e8Theta t) (M * 1 - deriv e8Theta t) t :=
        ((hasDerivAt_id t).const_mul M).sub (hasDerivAt_e8Theta ht0).differentiableAt.hasDerivAt
      rw [hdd.deriv]
      linarith [hd t (interior_subset ht)]
  have := hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  simp only at this
  linarith

theorem brOK_sound {x1 x2 : ℚ} {Na Nb : ℕ} (h : brOK x1 x2 Na Nb = true) {x y : ℝ}
    (hx : (x1 : ℝ) ≤ x) (hxy : x ≤ y) (hy : y ≤ (x2 : ℝ)) :
    e8Theta y - e8Theta x ≤ ((PsiUB (vd Na) (vd Nb) : ℚ) : ℝ) * (y - x) := by
  obtain ⟨da, db, hx1, -, -, hA, hB, hk⟩ := brOK_parts h
  exact theta_sub_le da db hk hx1 hA hB hx hxy hy

theorem PsiUB_pos_of_brOK {x1 x2 : ℚ} {Na Nb : ℕ} (h : brOK x1 x2 Na Nb = true) :
    (0 : ℝ) < ((PsiUB (vd Na) (vd Nb) : ℚ) : ℝ) := by
  obtain ⟨da, db, hx1, hx12, hab, hA, hB, hk⟩ := brOK_parts h
  have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1
  have hc := contact_mem_of_brackets da db hx1 hA hB (x := (x1 : ℝ)) le_rfl (by exact_mod_cast hx12)
  set v := radialContact (2 * (x1 : ℝ)) 1
  have hv0 : 0 < v := radialContact_pos (by positivity) one_pos
  have hvh : v < 1 / 2 := radialContact_lt_half (by positivity) one_pos
  have hle := Psi_le_PsiUB da db hk hc.1 hc.2
  have hp : 0 < Psi v := by
    unfold Psi
    have hH := H_pos hv0 (by linarith)
    have hn0 : 0 < hn v := by rw [hn_eq_H_mul_log]; exact mul_pos hH (Real.log_pos (by norm_num))
    have hk0 := kap_pos hv0 hvh
    have hK : 0 < 2 * kap v - (1 - 2 * v) ^ 2 := by
      have := GeneralCK.kap_ge_log_two hv0 (by linarith)
      have hl : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
      nlinarith
    have hl := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    have hq : 0 < 4 * v * (1 - v) := by nlinarith
    positivity
  linarith

#print axioms thLoOK_sound
#print axioms thHiOK_sound
#print axioms brOK_sound
#print axioms theta_sub_le_of_deriv

end CKLaneA1.R5

end


