-- Prove2me | Definitions.Def_CK_CKLaneN1_SRChecker
-- name    : CK_CKLaneN1_SRChecker
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T08:14:03.594987+00:00
-- url     : https://prove2.me/theorems/e9f1874c-307e-4938-8a99-6f790efdb75d
-- title:
--   Courtade–Kumar proof module `CKLaneN1.SRChecker` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.SRChecker` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.SRChecker` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.SRChecker (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/SRChecker.lean)

import Definitions.Def_CK_CKLaneN1_Analytic
import Definitions.Def_CK_CKLaneN1_Tree
import Definitions.Def_CK_CKLaneN1_SubRows
import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneD_Analytic

-- ===== source module CKLaneN1.SRChecker =====
section

/-!
# Lane N1: Boolean kernels for SMALL_RATIO Thm 4 (`normalized`) and Thm 1 (normalized collar)

Archive: `CK_SMALL_RATIO_EXTENSION.zip` (sha256 01d9dbba…dd9a), `CENTRAL_SMALL_RATIO.py` (`bound`, owner
`normalized`) and `NORMALIZED_COLLAR.py` (`upper`/`bound`).  The acceptance quantity is PROOF.md (12) / (7):

  `F(x⁺,1)/x⁺² − 2 A E − K A ρ ℓ₀(z) ≥ 0`,  `A = 1/(2L(1−u²))`, `K = (1+1/((1−v)log((1−v)/v)))/L`,
  `v = H⁻¹(E + C(u))`, `ρ = E/(E + C(q))` (collar: `ρ = 1`), `ℓ₀(z) = log(1+z)/z`.

The checker only needs `≥ 0` (in-row conclusion `μ.gap ≤ μ.cost`); every quantity is recomputed in exact ℚ
from the box and two dyadic witnesses, with `CKLaneE.FP` log/entropy enclosures.

Soundness (`checkN_sound`, `checkC_sound`): the only premises are `check = true` and membership of the law in
the exact archived box (plus the row's canonical/central hypotheses and strict psi-activity).
Entropy split `e, f` arbitrary; no stored margins.
-/

namespace CKLaneN1

open GeneralCK CKLaneE.FP Set

/-! ## Rational enclosures -/

/-- Upper bound of `C(r) = 1 − H((1−r)/2)` (valid when `ptOk ((1-r)/2)`). -/
def Cup (r : ℚ) : ℚ := 1 - Hlo ((1 - r) / 2)
/-- Lower bound of `C(r)`, clipped at `0`. -/
def Clo (r : ℚ) : ℚ := max 0 (1 - Hhi ((1 - r) / 2))
/-- Upper bound of `A = 1/(2L(1−u²))`. -/
def AupOf (u : ℚ) : ℚ := 1 / (2 * LqLo * (1 - u ^ 2))
/-- Upper bound of the slope constant `K` from an upper bracket `vh` of `H⁻¹(h⁺)`. -/
def KupOf (vh : ℚ) : ℚ := (1 + 1 / ((1 - vh) * lamLo vh)) / LqLo
/-- Lower bound of `J(vc)`. -/
def JloOf (vc : ℚ) : ℚ := lamLo vc / LqHi
/-- Upper bound of `ℓ₀(z) = log(1+z)/z` at a rational anchor `z ≥ 0`. -/
def ellOf (z : ℚ) : ℚ := if z = 0 then 1 else -(lLo (1 / (1 + z))) / z

/-- Common acceptance core. -/
def checkCore (e1 x1 u rhoUp zLo vh vc : ℚ) : Bool :=
  decide (0 ≤ u ∧ u < 1 ∧ 0 < x1 ∧ 0 ≤ zLo ∧ 0 ≤ rhoUp) &&
  ptOk ((1 - u) / 2) && decide (e1 + Cup u < 1) &&
  ptOk vh && decide (vh ≤ 1 / 2 ∧ e1 + Cup u ≤ Hlo vh ∧ 0 < lamLo vh) &&
  ptOk vc && decide (vc ≤ 1 / 2 ∧ 1 - 2 * vc ≤ x1 * Hlo vc ∧ 0 ≤ lamLo vc) &&
  (decide (zLo = 0) || ptOk (1 / (1 + zLo))) &&
  decide (2 * AupOf u * e1 + KupOf vh * AupOf u * rhoUp * ellOf zLo ≤ JloOf vc / x1)

/-! ## Soundness of the rational enclosures -/

theorem H_ge_Hlo {q : ℚ} (h : ptOk q = true) : ((Hlo q : ℚ) : ℝ) ≤ H (q : ℝ) := (H_bounds h).1
theorem H_le_Hhi {q : ℚ} (h : ptOk q = true) : H (q : ℝ) ≤ ((Hhi q : ℚ) : ℝ) := (H_bounds h).2

/-- `C(r) ≤ Cup r`. -/
theorem C_le_Cup {r : ℚ} (h : ptOk ((1 - r) / 2) = true) :
    1 - H ((1 - (r : ℝ)) / 2) ≤ ((Cup r : ℚ) : ℝ) := by
  have := H_ge_Hlo h
  simp only [Cup]
  push_cast at this ⊢
  linarith

/-- `Clo r ≤ C(r)`. -/
theorem Clo_le_C {r : ℚ} (h : ptOk ((1 - r) / 2) = true) :
    ((Clo r : ℚ) : ℝ) ≤ 1 - H ((1 - (r : ℝ)) / 2) := by
  have h1 := H_le_Hhi h
  have hH1 : H ((1 - (r : ℝ)) / 2) ≤ 1 := H_le_one _
  push_cast at h1
  unfold Clo
  rcases le_total 0 (1 - Hhi ((1 - r) / 2)) with hc | hc
  · rw [max_eq_right hc]
    push_cast
    linarith
  · rw [max_eq_left hc]
    push_cast
    linarith

theorem LqLo_le : ((LqLo : ℚ) : ℝ) ≤ Real.log 2 := log_two_mem.1
theorem LqHi_ge : Real.log 2 ≤ ((LqHi : ℚ) : ℝ) := log_two_mem.2

/-- `log(1+z) ≤ z * ellOf z` for rational `z ≥ 0` (with `ptOk (1/(1+z))` when `z > 0`). -/
theorem log_le_ell {z : ℚ} (hz : 0 ≤ z) (hpt : z = 0 ∨ ptOk (1 / (1 + z)) = true) :
    Real.log (1 + (z : ℝ)) ≤ (z : ℝ) * ((ellOf z : ℚ) : ℝ) ∧ 0 ≤ ((ellOf z : ℚ) : ℝ) := by
  by_cases h0 : z = 0
  · subst h0
    simp [ellOf]
  · have hpt' : ptOk (1 / (1 + z)) = true := hpt.resolve_left h0
    have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm h0)
    have hzR : (0 : ℝ) < z := by exact_mod_cast hzpos
    obtain ⟨hlo, -, -, -⟩ := ptOk_sound hpt'
    have hcast : (((1 / (1 + z) : ℚ)) : ℝ) = 1 / (1 + (z : ℝ)) := by push_cast; ring
    rw [hcast] at hlo
    have hlog : Real.log (1 / (1 + (z : ℝ))) = -Real.log (1 + (z : ℝ)) := by
      rw [one_div, Real.log_inv]
    rw [hlog] at hlo
    have hell : ((ellOf z : ℚ) : ℝ) = -((lLo (1 / (1 + z)) : ℚ) : ℝ) / (z : ℝ) := by
      simp only [ellOf, h0, if_false]
      push_cast
      ring
    rw [hell]
    have hlogpos : 0 < Real.log (1 + (z : ℝ)) := Real.log_pos (by linarith)
    constructor
    · rw [mul_div_assoc', le_div_iff₀ hzR]
      nlinarith
    · apply div_nonneg _ hzR.le
      linarith

/-! ## Small arithmetic helpers (kept out of the big proofs) -/

theorem one_sub_sq_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : 0 < 1 - u ^ 2 := by nlinarith

theorem Aup_pos {u : ℚ} (h0 : (0 : ℝ) ≤ (u : ℝ)) (h1 : (u : ℝ) < 1) : 0 < ((AupOf u : ℚ) : ℝ) := by
  have hd := one_sub_sq_pos h0 h1
  have hL := LqLo_pos
  simp only [AupOf]
  push_cast
  positivity

/-- Jensen gap bounded by the checker's `Aup`. -/
theorem drop_le_Aup {a b : ℝ} {u : ℚ} (ha : 0 < a) (hab : a < b) (hb : b < 1) (hsum : a + b ≤ 1)
    (hu : 1 - 2 * a ≤ (u : ℝ)) (hu1 : (u : ℝ) < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ ((AupOf u : ℚ) : ℝ) * (b - a) ^ 2 := by
  have hr0 : 0 ≤ 1 - 2 * a := by linarith
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := hr0.trans hu
  have hj := entropyDrop_le ha hab.le hb (lt_of_le_of_lt hu hu1)
    (by rw [abs_of_nonneg hr0]) (by rw [abs_le]; constructor <;> linarith)
  refine hj.trans ?_
  have hu2 := one_sub_sq_pos hu0 hu1
  have hr2 : (1 - 2 * a) ^ 2 ≤ (u : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hu 2
  have hL0 := LqLo_pos
  have hL0le := LqLo_le
  have hL := log_two_pos
  have hpos : 0 < 2 * ((LqLo : ℚ) : ℝ) * (1 - (u : ℝ) ^ 2) := by positivity
  have hprod : 2 * ((LqLo : ℚ) : ℝ) * (1 - (u : ℝ) ^ 2) ≤
      2 * Real.log 2 * (1 - (1 - 2 * a) ^ 2) := by
    have h1 : 1 - (u : ℝ) ^ 2 ≤ 1 - (1 - 2 * a) ^ 2 := by linarith
    have h3 := mul_le_mul hL0le h1 hu2.le hL.le
    linarith
  have hA1 : 1 / (2 * Real.log 2 * (1 - (1 - 2 * a) ^ 2)) ≤ ((AupOf u : ℚ) : ℝ) := by
    have hAeq : ((AupOf u : ℚ) : ℝ) = 1 / (2 * ((LqLo : ℚ) : ℝ) * (1 - (u : ℝ) ^ 2)) := by
      simp only [AupOf]; push_cast; ring
    rw [hAeq]
    exact one_div_le_one_div_of_le hpos hprod
  calc (b - a) ^ 2 / (2 * Real.log 2 * (1 - (1 - 2 * a) ^ 2))
      = (b - a) ^ 2 * (1 / (2 * Real.log 2 * (1 - (1 - 2 * a) ^ 2))) := by ring
    _ ≤ (b - a) ^ 2 * ((AupOf u : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hA1 (sq_nonneg _)
    _ = ((AupOf u : ℚ) : ℝ) * (b - a) ^ 2 := by ring

/-- Lower bound of the radial cost from an upper contact bracket at `x₁`. -/
theorem F_lower_of_bracket {d E x1 vc Jlo : ℝ} (hd : 0 < d) (hE : 0 < E) (hx1 : 0 < x1)
    (hdx : d / E ≤ x1) (hvc0 : 0 < vc) (hvc : vc ≤ 1 / 2) (hres : 1 - 2 * vc ≤ x1 * H vc)
    (hJ : Jlo ≤ J vc) :
    (d ^ 2 / E) * (Jlo / x1) ≤ F d E := by
  have hpersp : F d E = E * F (d / E) 1 := F_perspective hE.ne' d
  have hxpos : 0 < d / E := div_pos hd hE
  have hanti := antitoneOn_F_div_sq (h := 1) one_pos hxpos hx1 hdx
  simp only at hanti
  have hrc : radialContact x1 1 ≤ vc := by
    rw [radialContact_le_iff hx1 one_pos hvc0.le hvc]
    linarith
  have hrcpos := radialContact_pos hx1 one_pos
  have hJa := J_antitone hrcpos hvc hrc
  have hFx1 : x1 * Jlo ≤ F x1 1 := by
    have : F x1 1 = x1 * J (radialContact x1 1) := by simp [F, hx1.ne']
    rw [this]
    exact mul_le_mul_of_nonneg_left (hJ.trans hJa) hx1.le
  have h1 : Jlo / x1 ≤ F x1 1 / x1 ^ 2 := by
    rw [div_le_div_iff₀ hx1 (by positivity)]
    have := mul_le_mul_of_nonneg_left hFx1 hx1.le
    nlinarith [this]
  have h3 : F (d / E) 1 / (d / E) ^ 2 * (d ^ 2 / E) = E * F (d / E) 1 := by
    field_simp
  calc (d ^ 2 / E) * (Jlo / x1) ≤ (d ^ 2 / E) * (F (d / E) 1 / (d / E) ^ 2) :=
        mul_le_mul_of_nonneg_left (h1.trans hanti) (by positivity)
    _ = E * F (d / E) 1 := by rw [mul_comm]; exact h3
    _ = F d E := hpersp.symm

/-- The final rational comparison, normalized by `d²/E`. -/
theorem final_compare {E e1 d A K Z ell rho J x1 : ℝ} (hE : 0 < E) (hEe : E ≤ e1)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hell : 0 ≤ ell)
    (hZr : E * Z ≤ d ^ 2 * (A * rho))
    (hfin : 2 * A * e1 + K * A * rho * ell ≤ J / x1) :
    2 * (A * d ^ 2) + K * (Z * ell) ≤ (d ^ 2 / E) * (J / x1) := by
  have hd2 : 0 ≤ d ^ 2 := sq_nonneg d
  have h1 : E * (2 * (A * d ^ 2)) ≤ d ^ 2 * (2 * A * e1) := by
    have := mul_le_mul_of_nonneg_left hEe (show 0 ≤ 2 * A * d ^ 2 by positivity)
    linarith
  have h2 : E * (K * (Z * ell)) ≤ d ^ 2 * (K * A * rho * ell) := by
    have hKe : 0 ≤ K * ell := mul_nonneg hK hell
    have := mul_le_mul_of_nonneg_left hZr hKe
    linarith
  have h3 : d ^ 2 * (2 * A * e1 + K * A * rho * ell) ≤ d ^ 2 * (J / x1) :=
    mul_le_mul_of_nonneg_left hfin hd2
  rw [div_mul_eq_mul_div, le_div_iff₀ hE]
  linarith

/-! ## The core soundness lemma -/

set_option maxHeartbeats 1000000 in
/-- Core semantic lemma, stated for a law with `a < b`, `a + b ≤ 1`, non-strict psi-activity, and the
real-valued consequences of box membership. -/
theorem core_sound {k : ℕ} (μ : InteriorLaw (Fin k)) {e1 x1 u rhoUp zLo vh vc : ℚ}
    (hc : checkCore e1 x1 u rhoUp zLo vh vc = true)
    (hab : μ.a < μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hact : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy)
    (hE1 : μ.meanEntropy ≤ (e1 : ℝ))
    (hx1 : (μ.b - μ.a) / μ.meanEntropy ≤ (x1 : ℝ))
    (hu : 1 - 2 * μ.a ≤ (u : ℝ))
    {Z : ℝ}
    (hZy : ((AupOf u : ℚ) : ℝ) * (μ.b - μ.a) ^ 2 /
        (μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2))) ≤ Z)
    (hZz : (zLo : ℝ) ≤ Z)
    (hZr : μ.meanEntropy * Z ≤ (μ.b - μ.a) ^ 2 * (((AupOf u : ℚ) : ℝ) * (rhoUp : ℝ))) :
    μ.gap ≤ μ.cost := by
  -- unpack the Boolean check
  simp only [checkCore, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hu0, hu1, hx1pos, hz0, hrho0⟩, hptu⟩, hhup⟩, hptvh⟩, hvh⟩, hptvc⟩, hvc⟩, hptz⟩,
    hfinal⟩ := hc
  obtain ⟨hvh12, hvhH, hlamvh⟩ := hvh
  obtain ⟨hvc12, hvcH, hlamvc⟩ := hvc
  have haI := μ.a_interior
  have hbI := μ.b_interior
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  have hdpos : 0 < μ.b - μ.a := by linarith
  have hL := log_two_pos
  have hL0 : (0 : ℝ) < ((LqLo : ℚ) : ℝ) := LqLo_pos
  -- casts of the Boolean facts
  have hu0R : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0
  have hu1R : (u : ℝ) < 1 := by exact_mod_cast hu1
  have hx1R : (0 : ℝ) < (x1 : ℝ) := by exact_mod_cast hx1pos
  have hz0R : (0 : ℝ) ≤ (zLo : ℝ) := by exact_mod_cast hz0
  have hhupR : (e1 : ℝ) + ((Cup u : ℚ) : ℝ) < 1 := by exact_mod_cast hhup
  have hvh12R : ((vh : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hvh12
    push_cast at h
    linarith
  have hvhHR : (e1 : ℝ) + ((Cup u : ℚ) : ℝ) ≤ ((Hlo vh : ℚ) : ℝ) := by exact_mod_cast hvhH
  have hlamvhR : (0 : ℝ) < ((lamLo vh : ℚ) : ℝ) := by exact_mod_cast hlamvh
  have hvc12R : ((vc : ℚ) : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hvc12
    push_cast at h
    linarith
  have hvcHR : 1 - 2 * ((vc : ℚ) : ℝ) ≤ (x1 : ℝ) * ((Hlo vc : ℚ) : ℝ) := by exact_mod_cast hvcH
  have hlamvcR : (0 : ℝ) ≤ ((lamLo vc : ℚ) : ℝ) := by exact_mod_cast hlamvc
  have hfinalR : 2 * ((AupOf u : ℚ) : ℝ) * (e1 : ℝ) +
      ((KupOf vh : ℚ) : ℝ) * ((AupOf u : ℚ) : ℝ) * (rhoUp : ℝ) * ((ellOf zLo : ℚ) : ℝ) ≤
      ((JloOf vc : ℚ) : ℝ) / (x1 : ℝ) := by exact_mod_cast hfinal
  have hApos := Aup_pos hu0R hu1R
  -- Jensen gap
  have hdrop := drop_le_Aup haI.1 hab hbI.2 hsum hu hu1R
  -- psi split bound, in eta form
  have hpsi : candidateGap psi μ.a μ.b μ.e μ.f ≤
      Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) -
        Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) := CKLaneD.law_gap_le_P μ
  have hP : ∀ t, Scalar.P t = eta (1 - t) := fun t => rfl
  set y := 1 - (H ((μ.a + μ.b) / 2) - μ.meanEntropy) with hy_def
  set y' := 1 - ((H μ.a + H μ.b) / 2 - μ.meanEntropy) with hy'_def
  have hHm1 : H ((μ.a + μ.b) / 2) ≤ 1 := H_le_one _
  have hy0 : 0 < y := by rw [hy_def]; linarith
  have hyy : y ≤ y' := by
    have := μ.entropyDrop_nonneg
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint at this
    rw [hy_def, hy'_def]; linarith
  -- y' ≤ e1 + Cup u < 1
  have hHa_le : H μ.a ≤ (H μ.a + H μ.b) / 2 := by
    have : H μ.a ≤ H μ.b := by
      rcases le_total μ.b (1 / 2) with hb2 | hb2
      · exact CKLaneD.H_mono_left haI.1.le hab.le hb2
      · rw [← H_complement μ.b]
        exact CKLaneD.H_mono_left haI.1.le (by linarith) (by linarith)
    linarith
  have hCa : 1 - H μ.a ≤ ((Cup u : ℚ) : ℝ) := by
    have hr0 : 0 ≤ 1 - 2 * μ.a := by linarith
    have h1 : 1 - H ((1 - (1 - 2 * μ.a)) / 2) ≤ 1 - H ((1 - (u : ℝ)) / 2) :=
      C_mono hr0 hu hu1R.le
    have h2 := C_le_Cup hptu
    have h3 : (1 - (1 - 2 * μ.a)) / 2 = μ.a := by ring
    rw [h3] at h1
    linarith
  have hy'up : y' ≤ (e1 : ℝ) + ((Cup u : ℚ) : ℝ) := by rw [hy'_def]; linarith
  have hy'1 : y' < 1 := lt_of_le_of_lt hy'up hhupR
  -- slope constant
  obtain ⟨hvhlog, -⟩ := lam_bounds hptvh
  have hKup : ((KupOf vh : ℚ) : ℝ) = (1 + 1 / ((1 - ((vh : ℚ) : ℝ)) * ((lamLo vh : ℚ) : ℝ))) /
      ((LqLo : ℚ) : ℝ) := by
    simp only [KupOf]; push_cast; ring
  have hslope : ∀ h ∈ Icc y y', h * (-deriv eta h - 2) ≤ ((KupOf vh : ℚ) : ℝ) := by
    intro h hh
    have h0 : 0 < h := hy0.trans_le hh.1
    have h1 : h < 1 := lt_of_le_of_lt hh.2 hy'1
    have hHv : h ≤ H ((vh : ℚ) : ℝ) :=
      (hh.2.trans hy'up).trans (hvhHR.trans (H_ge_Hlo hptvh))
    rw [hKup]
    exact neg_deriv_eta_sub_two_le_bracket h0 h1 hvh12R hHv hlamvhR hvhlog hL0 LqLo_le
  have hdec := eta_decrement_le_of_slope hy0 hyy hy'1 hslope
  have hKpos : 0 < ((KupOf vh : ℚ) : ℝ) := by
    rw [hKup]
    have : 0 < 1 - ((vh : ℚ) : ℝ) := by linarith
    positivity
  -- Δ = y' - y, and y = E + C(q)
  have hΔ : y' - y = H ((μ.a + μ.b) / 2) - (H μ.a + H μ.b) / 2 := by
    rw [hy_def, hy'_def]; ring
  have hy_eq : y = μ.meanEntropy + (1 - H ((1 - (1 - μ.a - μ.b)) / 2)) := by
    rw [hy_def]
    have : (1 - (1 - μ.a - μ.b)) / 2 = (μ.a + μ.b) / 2 := by ring
    rw [this]
    ring
  -- log term
  have hlogq : Real.log y' - Real.log y = Real.log (1 + (y' - y) / y) := by
    rw [← Real.log_div (by linarith) hy0.ne']
    congr 1
    field_simp
    ring
  have hZ0 : 0 ≤ Z := hz0R.trans hZz
  have hlog1 : Real.log (1 + (y' - y) / y) ≤ Real.log (1 + Z) := by
    apply Real.log_le_log (by positivity)
    have : (y' - y) / y ≤ Z := by
      refine le_trans ?_ (hy_eq ▸ hZy)
      rw [hΔ]
      exact div_le_div_of_nonneg_right hdrop hy0.le
    linarith
  obtain ⟨hell, hell0⟩ := log_le_ell hz0 (by
    rcases hptz with h | h
    · left; exact h
    · right; exact h)
  have hlogZ : Real.log (1 + Z) ≤ Z * ((ellOf zLo : ℚ) : ℝ) := by
    rcases eq_or_lt_of_le hz0R with hz | hz
    · have hzq : zLo = 0 := by exact_mod_cast hz.symm
      have : ((ellOf zLo : ℚ) : ℝ) = 1 := by simp [ellOf, hzq]
      rw [this, mul_one]
      exact log_one_add_le_self hZ0
    · exact log_one_add_le_of_anchor hz hZz hell
  -- gap upper bound
  have hgap : μ.gap ≤ 2 * (((AupOf u : ℚ) : ℝ) * (μ.b - μ.a) ^ 2) +
      ((KupOf vh : ℚ) : ℝ) * (Z * ((ellOf zLo : ℚ) : ℝ)) := by
    have h1 : μ.gap ≤ candidateGap psi μ.a μ.b μ.e μ.f := hybrid_gap_le_psi hact
    have h2 : Scalar.P (H ((μ.a + μ.b) / 2) - μ.meanEntropy) -
        Scalar.P ((H μ.a + H μ.b) / 2 - μ.meanEntropy) = eta y - eta y' := by
      rw [hP, hP]
    have h3 := hdec
    rw [hΔ, hlogq] at h3
    have h4 : ((KupOf vh : ℚ) : ℝ) * Real.log (1 + (y' - y) / y) ≤
        ((KupOf vh : ℚ) : ℝ) * (Z * ((ellOf zLo : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hlog1.trans hlogZ) hKpos.le
    linarith
  -- cost lower bound
  have hvcpos := (ptOk_pos hptvc).1
  have hvcR : (0 : ℝ) < ((vc : ℚ) : ℝ) := by exact_mod_cast hvcpos
  obtain ⟨hvclog, -⟩ := lam_bounds hptvc
  have hJlo : ((JloOf vc : ℚ) : ℝ) ≤ J ((vc : ℚ) : ℝ) := by
    simp only [JloOf]
    push_cast
    unfold J
    calc ((lamLo vc : ℚ) : ℝ) / ((LqHi : ℚ) : ℝ) ≤ ((lamLo vc : ℚ) : ℝ) / Real.log 2 :=
          div_le_div_of_nonneg_left hlamvcR hL LqHi_ge
      _ ≤ Real.log ((1 - ((vc : ℚ) : ℝ)) / ((vc : ℚ) : ℝ)) / Real.log 2 :=
          div_le_div_of_nonneg_right hvclog hL.le
  have hJ0 : (0 : ℝ) ≤ ((JloOf vc : ℚ) : ℝ) := by
    simp only [JloOf]; push_cast
    exact div_nonneg hlamvcR (le_trans hL.le LqHi_ge)
  have hres : 1 - 2 * ((vc : ℚ) : ℝ) ≤ (x1 : ℝ) * H ((vc : ℚ) : ℝ) :=
    hvcHR.trans (mul_le_mul_of_nonneg_left (H_ge_Hlo hptvc) hx1R.le)
  have hcost : ((μ.b - μ.a) ^ 2 / μ.meanEntropy) * (((JloOf vc : ℚ) : ℝ) / (x1 : ℝ)) ≤ μ.cost :=
    (F_lower_of_bracket hdpos hEpos hx1R hx1 hvcR hvc12R hres hJlo).trans
      (PsiEndpointPlane.law_radial_lower μ hab)
  have hfin := final_compare hEpos hE1 hApos.le hKpos.le hell0 hZr hfinalR
  exact hgap.trans (hfin.trans hcost)

/-! ## Archived boxes, leaf checks and their soundness -/

/-- Witness of a normalized-collar leaf. -/
structure CWit where
  vh : ℚ
  vc : ℚ
  deriving Repr, DecidableEq

/-- Payload of a Thm 4 leaf (archived owner label + witness). -/
inductive SRLeaf where
  | normalized (vh vc : ℚ)
  | smallRatio
  deriving Repr, DecidableEq

/-- Thm 4 root `(E, x, q) ∈ [10^-6, 11/200] × [0, 4] × [0, 4/5]` (`CENTRAL_SMALL_RATIO.py` ROOT). -/
def centralRoot : B3 := ⟨1 / 1000000, 11 / 200, 0, 4, 0, 4 / 5⟩
/-- Thm 1 root `(E, x) ∈ [10^-6, 11/200] × [0, 4]` (`NORMALIZED_COLLAR.py` ROOT; degenerate third axis). -/
def collarRoot : B3 := ⟨1 / 1000000, 11 / 200, 0, 4, 0, 0⟩

/-- Thm 4 `normalized` acceptance on a box (E ∈ [a0,a1], x ∈ [b0,b1], q ∈ [c0,c1]). -/
def checkN (B : B3) (vh vc : ℚ) : Bool :=
  decide (0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ 0 ≤ B.b0 ∧ B.b0 ≤ B.b1 ∧ 0 ≤ B.c0 ∧ B.c0 ≤ B.c1 ∧ B.c1 < 1) &&
  ptOk ((1 - B.c0) / 2) && ptOk ((1 - B.c1) / 2) &&
  checkCore B.a1 B.b1 (min (B.c1 + B.b1 * B.a1) (4 / 5))
    (1 / (1 + Clo B.c0 / B.a1))
    (AupOf (min (B.c1 + B.b1 * B.a1) (4 / 5)) * B.b0 ^ 2 * B.a0 * (1 / (1 + Cup B.c1 / B.a0)))
    vh vc

/-- Thm 1 acceptance on a box (E ∈ [a0,a1], x ∈ [b0,b1]). -/
def checkC (B : B3) (vh vc : ℚ) : Bool :=
  decide (0 < B.a0 ∧ B.a0 ≤ B.a1 ∧ 0 ≤ B.b0 ∧ B.b0 ≤ B.b1) &&
  checkCore B.a1 B.b1 ((B.b1 + 1) * B.a1) 1 (AupOf ((B.b1 + 1) * B.a1) * B.b0 ^ 2 * B.a0) vh vc

/-- Law membership in a Thm 4 box: `E`, `x = (b-a)/E`, `q = 1-a-b`. -/
def InCentral (B : B3) {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  B.Mem μ.meanEntropy ((μ.b - μ.a) / μ.meanEntropy) (1 - μ.a - μ.b)

/-- Law membership in a Thm 1 box: `E`, `x = (b-a)/E`. -/
def InCollar (B : B3) {k : ℕ} (μ : InteriorLaw (Fin k)) : Prop :=
  B.Mem μ.meanEntropy ((μ.b - μ.a) / μ.meanEntropy) 0

theorem C_nonneg (p : ℝ) : 0 ≤ 1 - H p := by linarith [H_le_one p]

theorem Cup_nonneg {r : ℚ} (h : ptOk ((1 - r) / 2) = true) : (0 : ℝ) ≤ ((Cup r : ℚ) : ℝ) :=
  (C_nonneg _).trans (C_le_Cup h)

set_option maxHeartbeats 1000000 in
/-- Soundness of the Thm 4 `normalized` leaf check (in-row form). -/
theorem checkN_sound {B : B3} {vh vc : ℚ} (h : checkN B vh vc = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1)
    (ha : 1 / 10 ≤ μ.a) (hin : InCentral B μ) (hact : PsiActive μ) : μ.gap ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  simp only [checkN, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbox, hpt0⟩, hpt1⟩, hcore⟩ := h
  obtain ⟨ha0, ha01, hb0, hb01, hc0, hc01, hc1⟩ := hbox
  obtain ⟨hE0, hE1, hx0, hx1, hq0, hq1⟩ := hin
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  set E := μ.meanEntropy with hE_def
  set d := μ.b - μ.a with hd_def
  set q := 1 - μ.a - μ.b with hq_def
  have hdpos : 0 < d := by rw [hd_def]; linarith
  set x := d / E with hx_def
  have hxE : x * E = d := by rw [hx_def]; field_simp
  have hb0R : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast hb0
  have ha0R : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast ha0
  have hc0R : (0 : ℝ) ≤ (B.c0 : ℝ) := by exact_mod_cast hc0
  have hc1R : (B.c1 : ℝ) < 1 := by exact_mod_cast hc1
  have hx0' : 0 ≤ x := hb0R.trans hx0
  -- C values
  set Cq := 1 - H ((1 - q) / 2) with hCq_def
  have hCq0 : 0 ≤ Cq := C_nonneg _
  have hq0' : 0 ≤ q := hc0R.trans hq0
  have hCq_up : Cq ≤ ((Cup B.c1 : ℚ) : ℝ) := by
    have h1 : Cq ≤ 1 - H ((1 - (B.c1 : ℝ)) / 2) := C_mono hq0' hq1 hc1R.le
    have h2 := C_le_Cup hpt1
    linarith
  have hCq_lo : ((Clo B.c0 : ℚ) : ℝ) ≤ Cq := by
    have h1 : 1 - H ((1 - (B.c0 : ℝ)) / 2) ≤ Cq := C_mono hc0R hq0 (by linarith)
    have h2 := Clo_le_C hpt0
    linarith
  have hCup0 := Cup_nonneg hpt1
  have hClo0 : (0 : ℝ) ≤ ((Clo B.c0 : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ Clo B.c0 := le_max_left _ _
    exact_mod_cast this
  -- radial coordinate
  have hu : 1 - 2 * μ.a ≤ ((min (B.c1 + B.b1 * B.a1) (4 / 5) : ℚ) : ℝ) := by
    push_cast
    apply le_min
    · have hdle : d ≤ (B.b1 : ℝ) * (B.a1 : ℝ) := by
        rw [← hxE]
        exact mul_le_mul hx1 hE1 hEpos.le (hx0'.trans hx1)
      have : 1 - 2 * μ.a = q + d := by rw [hq_def, hd_def]; ring
      rw [this]
      linarith
    · linarith
  set u : ℚ := min (B.c1 + B.b1 * B.a1) (4 / 5) with hu_def
  -- apply the core with Z = Aup d² / (E + C(q))
  have hy : 0 < E + Cq := by linarith
  refine core_sound μ hcore hlt hsum hact.le hE1 hx1 hu (Z := ((AupOf u : ℚ) : ℝ) * d ^ 2 / (E + Cq))
    le_rfl ?_ ?_
  · -- zLo ≤ Z
    have hAup : (0 : ℝ) ≤ ((AupOf u : ℚ) : ℝ) := by
      have hu1 : (u : ℝ) < 1 := by
        rw [hu_def]; push_cast
        exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hu0 : (0 : ℝ) ≤ (u : ℝ) := by
        rw [hu_def]; push_cast
        apply le_min
        · have : (0 : ℝ) ≤ (B.b1 : ℝ) * (B.a1 : ℝ) := by
            have hb1 : (0 : ℝ) ≤ (B.b1 : ℝ) := hx0'.trans hx1
            have ha1 : (0 : ℝ) ≤ (B.a1 : ℝ) := by linarith
            positivity
          linarith
        · norm_num
      exact (Aup_pos hu0 hu1).le
    push_cast
    have hrho : 1 / (1 + ((Cup B.c1 : ℚ) : ℝ) / (B.a0 : ℝ)) ≤ E / (E + Cq) := by
      rw [div_le_div_iff₀ (by positivity) hy]
      have h1 : Cq * (B.a0 : ℝ) ≤ ((Cup B.c1 : ℚ) : ℝ) * E := by
        have := mul_le_mul hCq_up hE0 ha0R.le hCup0
        linarith
      have : E * (1 + ((Cup B.c1 : ℚ) : ℝ) / (B.a0 : ℝ)) =
          E + ((Cup B.c1 : ℚ) : ℝ) * E / (B.a0 : ℝ) := by ring
      rw [this]
      have h2 : Cq ≤ ((Cup B.c1 : ℚ) : ℝ) * E / (B.a0 : ℝ) := by
        rw [le_div_iff₀ ha0R]; linarith
      linarith
    have hx2 : (B.b0 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hb0R hx0 2
    have hZ : ((AupOf u : ℚ) : ℝ) * d ^ 2 / (E + Cq) =
        ((AupOf u : ℚ) : ℝ) * x ^ 2 * E * (E / (E + Cq)) := by
      rw [← hxE]; field_simp
    rw [hZ]
    have hrho0 : 0 ≤ 1 / (1 + ((Cup B.c1 : ℚ) : ℝ) / (B.a0 : ℝ)) := by positivity
    have h1 : ((AupOf u : ℚ) : ℝ) * (B.b0 : ℝ) ^ 2 * (B.a0 : ℝ) ≤ ((AupOf u : ℚ) : ℝ) * x ^ 2 * E := by
      have := mul_le_mul hx2 hE0 ha0R.le (sq_nonneg x)
      have := mul_le_mul_of_nonneg_left this hAup
      linarith [mul_assoc ((AupOf u : ℚ) : ℝ) ((B.b0 : ℝ) ^ 2) (B.a0 : ℝ),
        mul_assoc ((AupOf u : ℚ) : ℝ) (x ^ 2) E]
    have h1' : (0 : ℝ) ≤ ((AupOf u : ℚ) : ℝ) * (B.b0 : ℝ) ^ 2 * (B.a0 : ℝ) := by positivity
    exact mul_le_mul h1 hrho hrho0 (by positivity)
  · -- E * Z ≤ d² * (Aup * rhoUp)
    push_cast
    have hrho : E / (E + Cq) ≤ 1 / (1 + ((Clo B.c0 : ℚ) : ℝ) / (B.a1 : ℝ)) := by
      have ha1R : (0 : ℝ) < (B.a1 : ℝ) := by linarith
      rw [div_le_div_iff₀ hy (by positivity)]
      have h1 : ((Clo B.c0 : ℚ) : ℝ) * E ≤ Cq * (B.a1 : ℝ) := by
        have := mul_le_mul hCq_lo hE1 hEpos.le hCq0
        linarith
      have : E * (1 + ((Clo B.c0 : ℚ) : ℝ) / (B.a1 : ℝ)) =
          E + ((Clo B.c0 : ℚ) : ℝ) * E / (B.a1 : ℝ) := by ring
      rw [this]
      have h2 : ((Clo B.c0 : ℚ) : ℝ) * E / (B.a1 : ℝ) ≤ Cq := by
        rw [div_le_iff₀ ha1R]; linarith
      linarith
    have hAup : (0 : ℝ) ≤ ((AupOf u : ℚ) : ℝ) := by
      have hu1 : (u : ℝ) < 1 := by
        rw [hu_def]; push_cast
        exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hu0 : (0 : ℝ) ≤ (u : ℝ) := le_trans (by linarith [μ.a_interior.2]) hu
      exact (Aup_pos hu0 hu1).le
    have e : E * (((AupOf u : ℚ) : ℝ) * d ^ 2 / (E + Cq)) =
        d ^ 2 * (((AupOf u : ℚ) : ℝ) * (E / (E + Cq))) := by
      field_simp
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg d)
    exact mul_le_mul_of_nonneg_left hrho hAup

set_option maxHeartbeats 1000000 in
/-- Soundness of the Thm 1 (normalized collar) leaf check (in-row form). -/
theorem checkC_sound {B : B3} {vh vc : ℚ} (h : checkC B vh vc = true)
    {k : ℕ} (μ : InteriorLaw (Fin k)) (hab : μ.a ≤ μ.b) (hsum : μ.a + μ.b ≤ 1)
    (hqE : 1 - μ.a - μ.b ≤ μ.meanEntropy) (hin : InCollar B μ) (hact : PsiActive μ) :
    μ.gap ≤ μ.cost := by
  rcases hab.eq_or_lt with heq | hlt
  · exact μ.equal_mean_hybrid heq
  simp only [checkC, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hbox, hcore⟩ := h
  obtain ⟨ha0, ha01, hb0, hb01⟩ := hbox
  obtain ⟨hE0, hE1, hx0, hx1, -, -⟩ := hin
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  set E := μ.meanEntropy with hE_def
  set d := μ.b - μ.a with hd_def
  have hdpos : 0 < d := by rw [hd_def]; linarith
  set x := d / E with hx_def
  have hxE : x * E = d := by rw [hx_def]; field_simp
  have hb0R : (0 : ℝ) ≤ (B.b0 : ℝ) := by exact_mod_cast hb0
  have ha0R : (0 : ℝ) < (B.a0 : ℝ) := by exact_mod_cast ha0
  have hx0' : 0 ≤ x := hb0R.trans hx0
  set Cq := 1 - H ((1 - (1 - μ.a - μ.b)) / 2) with hCq_def
  have hCq0 : 0 ≤ Cq := C_nonneg _
  have hy : 0 < E + Cq := by linarith
  have hu : 1 - 2 * μ.a ≤ ((((B.b1 + 1) * B.a1) : ℚ) : ℝ) := by
    push_cast
    have hdle : d ≤ (B.b1 : ℝ) * (B.a1 : ℝ) := by
      rw [← hxE]
      exact mul_le_mul hx1 hE1 hEpos.le (hx0'.trans hx1)
    have : 1 - 2 * μ.a = (1 - μ.a - μ.b) + d := by rw [hd_def]; ring
    rw [this]
    have hxE1 : x * E ≤ (B.b1 : ℝ) * (B.a1 : ℝ) := by rw [hxE]; exact hdle
    have hE1' : E ≤ (B.a1 : ℝ) := hE1
    linarith
  set u : ℚ := (B.b1 + 1) * B.a1 with hu_def
  have hAup : (0 : ℝ) ≤ ((AupOf u : ℚ) : ℝ) := by
    simp only [checkCore, Bool.and_eq_true, decide_eq_true_eq] at hcore
    have hu1 : u < 1 := hcore.1.1.1.1.1.1.1.1.2.1
    have hu0 : 0 ≤ u := hcore.1.1.1.1.1.1.1.1.1
    have hu1R : (u : ℝ) < 1 := by exact_mod_cast hu1
    have hu0R : (0 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu0
    exact (Aup_pos hu0R hu1R).le
  refine core_sound μ hcore hlt hsum hact.le hE1 hx1 hu (Z := ((AupOf u : ℚ) : ℝ) * d ^ 2 / E)
    ?_ ?_ ?_
  · -- Aup d² / (E + C) ≤ Aup d² / E
    exact div_le_div_of_nonneg_left (by positivity) hEpos (by linarith)
  · -- zLo ≤ Z
    push_cast
    have hZ : ((AupOf u : ℚ) : ℝ) * d ^ 2 / E = ((AupOf u : ℚ) : ℝ) * x ^ 2 * E := by
      rw [← hxE]; field_simp
    rw [hZ]
    have hx2 : (B.b0 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hb0R hx0 2
    have := mul_le_mul hx2 hE0 ha0R.le (sq_nonneg x)
    have := mul_le_mul_of_nonneg_left this hAup
    linarith [mul_assoc ((AupOf u : ℚ) : ℝ) ((B.b0 : ℝ) ^ 2) (B.a0 : ℝ),
      mul_assoc ((AupOf u : ℚ) : ℝ) (x ^ 2) E]
  · -- E * Z ≤ d² * (Aup * 1)
    push_cast
    have e : E * (((AupOf u : ℚ) : ℝ) * d ^ 2 / E) = d ^ 2 * (((AupOf u : ℚ) : ℝ) * 1) := by
      field_simp
    rw [e]

/-! ## Leaf predicates over the archived trees -/

/-- Kernel check of one Thm 4 leaf. `smallRatio` leaves must satisfy `q_+ ≤ E_-` (then Thm 1 owns them). -/
def leafOK4 (p : List ℕ) : SRLeaf → Bool
  | .normalized vh vc => checkN (centralRoot.ofPath p) vh vc
  | .smallRatio => decide ((centralRoot.ofPath p).c1 ≤ (centralRoot.ofPath p).a0)

/-- Kernel check of one Thm 1 leaf. -/
def leafOKC (p : List ℕ) (w : CWit) : Bool := checkC (collarRoot.ofPath p) w.vh w.vc

/-- Thm 1 cover over an archived tree whose leaves all pass `leafOKC`. -/
theorem collar_of_tree {T : PT CWit} (hall : T.allLeaves leafOKC = true) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
      1 - μ.a - μ.b ≤ μ.meanEntropy → μ.b - μ.a ≤ 4 * μ.meanEntropy →
      PsiActive μ → μ.gap ≤ μ.cost := by
  intro k μ hab hsum hE0 hE1 hqE hd4 hact
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  have hroot : collarRoot.Mem μ.meanEntropy ((μ.b - μ.a) / μ.meanEntropy) 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [collarRoot]; push_cast; linarith
    · simp only [collarRoot]; push_cast; linarith
    · simp only [collarRoot]; push_cast
      exact div_nonneg (by linarith) hEpos.le
    · simp only [collarRoot]; push_cast
      rw [div_le_iff₀ hEpos]; linarith
    · simp [collarRoot]
    · simp [collarRoot]
  obtain ⟨q, hq, hmem⟩ := PT.cover collarRoot T hroot
  have hok := PT.allLeaves_sound hall q hq
  exact checkC_sound hok μ hab hsum hqE hmem hact

/-- Thm 4 cover over an archived tree whose leaves all pass `leafOK4`, given Thm 1. -/
theorem central_of_tree {T : PT SRLeaf} (hall : T.allLeaves leafOK4 = true)
    (hC : ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
      1 - μ.a - μ.b ≤ μ.meanEntropy → μ.b - μ.a ≤ 4 * μ.meanEntropy →
      PsiActive μ → μ.gap ≤ μ.cost) :
    ∀ (k : ℕ) (μ : InteriorLaw (Fin k)), μ.a ≤ μ.b → μ.a + μ.b ≤ 1 →
      1 / 10 ≤ μ.a → 1 / 1000000 ≤ μ.meanEntropy → μ.meanEntropy ≤ 11 / 200 →
      μ.b - μ.a ≤ 4 * μ.meanEntropy → PsiActive μ → μ.gap ≤ μ.cost := by
  intro k μ hab hsum ha hE0 hE1 hd4 hact
  have hEpos : 0 < μ.meanEntropy := CKLaneD.law_meanEntropy_pos μ
  have hroot : centralRoot.Mem μ.meanEntropy ((μ.b - μ.a) / μ.meanEntropy) (1 - μ.a - μ.b) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [centralRoot]; push_cast; linarith
    · simp only [centralRoot]; push_cast; linarith
    · simp only [centralRoot]; push_cast
      exact div_nonneg (by linarith) hEpos.le
    · simp only [centralRoot]; push_cast
      rw [div_le_iff₀ hEpos]; linarith
    · simp only [centralRoot]; push_cast; linarith
    · simp only [centralRoot]; push_cast; linarith
  obtain ⟨q, hq, hmem⟩ := PT.cover centralRoot T hroot
  have hok := PT.allLeaves_sound hall q hq
  cases hlab : q.2 with
  | normalized vh vc =>
      rw [hlab] at hok
      exact checkN_sound hok μ hab hsum ha hmem hact
  | smallRatio =>
      rw [hlab] at hok
      simp only [leafOK4, decide_eq_true_eq] at hok
      have hc1 : ((centralRoot.ofPath q.1).c1 : ℝ) ≤ ((centralRoot.ofPath q.1).a0 : ℝ) := by
        exact_mod_cast hok
      obtain ⟨hE0', -, -, -, -, hq1⟩ := hmem
      exact hC k μ hab hsum hE0 hE1 (by linarith) hd4 hact

end CKLaneN1

end


