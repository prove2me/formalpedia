-- Prove2me | Definitions.Def_CK_CKLaneA1_R5Corner
-- name    : CK_CKLaneA1_R5Corner
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T19:49:44.133565+00:00
-- url     : https://prove2.me/theorems/1b7db7d0-ade1-4da2-86c9-c6aeb37bce0a
-- title:
--   Courtade–Kumar proof module `CKLaneA1.R5Corner` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA1.R5Corner` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA1.R5Corner` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA1.R5Corner (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA1/R5Corner.lean)

import Definitions.Def_CK_CKLaneA1_R5Near

-- ===== source module CKLaneA1.R5Corner =====
section

/-!
# CKLaneA1.R5Corner — the corner `a ≥ 11/32` of CE-stat row 5

With `α = 1/2 − a ≤ 5/32`, `γ = 1/2 − c`, `E = e + f`: `A = (α−γ)/E`, `W = γ/f`, `A + 2λW = A + W₂`,
`W₂ = 2γ/E`, and
`D = [Θ(A) + Θ(W₂) − Θ(A+W₂)] − [Θ(W₂) − Θ(W)] ≥ M·A·W₂(A+W₂) − θ₀(W₂ − W)`, `M = (7θ₃⁻−θ₃⁺)/2`,
from the `Θ'` bounds `θ₀ − 3θ₃⁺x² ≤ Θ'(x) ≤ θ₀ − 3θ₃⁻x²` on `(0, x_c]` (analytic near `0`, kernel
boxes on `[x₀, x_c]`), and `f − e < H(c) − H(a) ≤ K(α² − γ²)` (`K = 3.11`).  Since `E < 2f ≤ 2`,
`2M ≥ 4θ₀K` gives `D > 0`.
-/

set_option autoImplicit false

namespace CKLaneA1.R5

open GeneralCK GeneralCK.Certificates.Mixed CKLaneP Set

/-! ## `Θ'` bounds: kernel boxes -/

def TH3M : ℚ := 273 / 10
def TH3P : ℚ := 75 / 2

/-- Box `[x1, x2]` with contact bracket `[Na, Nb]` inside the monotone range of `Psi`. -/
def tbOK (x1 x2 : ℚ) (Na Nb : ℕ) : Bool :=
  brOK x1 x2 Na Nb && decide (V1N ≤ Na ∧ Nb ≤ V2N) &&
    decide (PsiUB (vd Nb) (vd Nb) ≤ 8 / L2hiD - 3 * TH3M * x2 ^ 2) &&
    decide (8 / L2loD - 3 * TH3P * x1 ^ 2 ≤ PsiLB (vd Na) (vd Na))

def tbChain : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | x1, (x2, Na, Nb) :: rest => tbOK (dq x1) (dq x2) Na Nb && tbChain x2 rest

def lastX : ℕ → List (ℕ × ℕ × ℕ) → ℕ
  | x1, [] => x1
  | _, (x2, _, _) :: rest => lastX x2 rest

theorem theta0_bounds :
    8 / ((L2hiD : ℚ) : ℝ) ≤ 8 / Real.log 2 ∧ 8 / Real.log 2 ≤ 8 / ((L2loD : ℚ) : ℝ) := by
  obtain ⟨h1, h2⟩ := log2D_bounds
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact ⟨div_le_div_of_nonneg_left (by norm_num) hl0 h2,
    div_le_div_of_nonneg_left (by norm_num) VD.L2lo_pos h1⟩

theorem TH3M_nonneg : (0 : ℝ) ≤ ((TH3M : ℚ) : ℝ) := by unfold TH3M; norm_num
theorem TH3P_nonneg : (0 : ℝ) ≤ ((TH3P : ℚ) : ℝ) := by unfold TH3P; norm_num

theorem tbOK_sound {x1 x2 : ℚ} {Na Nb : ℕ} (h : tbOK x1 x2 Na Nb = true) {x : ℝ}
    (hx1 : (x1 : ℝ) ≤ x) (hx2 : x ≤ (x2 : ℝ)) :
    8 / Real.log 2 - 3 * ((TH3P : ℚ) : ℝ) * x ^ 2 ≤ deriv e8Theta x ∧
      deriv e8Theta x ≤ 8 / Real.log 2 - 3 * ((TH3M : ℚ) : ℝ) * x ^ 2 := by
  unfold tbOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hbr, hV1, hV2⟩, hup⟩, hlo⟩ := h
  obtain ⟨da, db, hx1p, -, -, hA, hB, hk⟩ := brOK_parts hbr
  have hx1R : (0 : ℝ) < x1 := by exact_mod_cast hx1p
  have hx0 : 0 < x := hx1R.trans_le hx1
  rw [deriv_e8Theta_eq_Psi hx0]
  obtain ⟨hc1, hc2⟩ := contact_mem_of_brackets da db hx1p hA hB hx1 hx2
  have hW1 : ((dyq V1N : ℚ) : ℝ) ≤ (((vd Na).v : ℚ) : ℝ) := by
    rw [vd_v]; exact_mod_cast dyq_mono hV1
  have hW2 : (((vd Nb).v : ℚ) : ℝ) ≤ ((dyq V2N : ℚ) : ℝ) := by
    rw [vd_v]; exact_mod_cast dyq_mono hV2
  have hvab := hc1.trans hc2
  have hm1 := psi_mono ⟨hW1, hvab.trans hW2⟩ ⟨hW1.trans hc1, hc2.trans hW2⟩ hc1
  have hm2 := psi_mono ⟨hW1.trans hc1, hc2.trans hW2⟩ ⟨hW1.trans hvab, hW2⟩ hc2
  have hU := Psi_le_PsiUB db db hk (v := (((vd Nb).v : ℚ) : ℝ)) le_rfl le_rfl
  have hL := PsiLB_le_Psi da da (v := (((vd Na).v : ℚ) : ℝ)) le_rfl le_rfl
  have hupR : ((PsiUB (vd Nb) (vd Nb) : ℚ) : ℝ) ≤
      8 / ((L2hiD : ℚ) : ℝ) - 3 * ((TH3M : ℚ) : ℝ) * (x2 : ℝ) ^ 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hup; push_cast at h'; exact h'
  have hloR : 8 / ((L2loD : ℚ) : ℝ) - 3 * ((TH3P : ℚ) : ℝ) * (x1 : ℝ) ^ 2 ≤
      ((PsiLB (vd Na) (vd Na) : ℚ) : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hlo; push_cast at h'; exact h'
  obtain ⟨ht0lo, ht0hi⟩ := theta0_bounds
  have hx2sq : x ^ 2 ≤ (x2 : ℝ) ^ 2 := pow_le_pow_left₀ hx0.le hx2 2
  have hx1sq : (x1 : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx1R.le hx1 2
  have p1 := mul_le_mul_of_nonneg_left hx1sq TH3P_nonneg
  have p2 := mul_le_mul_of_nonneg_left hx2sq TH3M_nonneg
  constructor <;> linarith

theorem tbChain_sound : ∀ (l : List (ℕ × ℕ × ℕ)) (x1 : ℕ), tbChain x1 l = true →
    ∀ x : ℝ, ((dq x1 : ℚ) : ℝ) < x → x ≤ ((dq (lastX x1 l) : ℚ) : ℝ) →
      8 / Real.log 2 - 3 * ((TH3P : ℚ) : ℝ) * x ^ 2 ≤ deriv e8Theta x ∧
        deriv e8Theta x ≤ 8 / Real.log 2 - 3 * ((TH3M : ℚ) : ℝ) * x ^ 2
  | [], x1, _, x, h1, h2 => by simp only [lastX] at h2; linarith
  | (x2, Na, Nb) :: rest, x1, h, x, h1, h2 => by
    simp only [tbChain, Bool.and_eq_true] at h
    by_cases hx : x ≤ ((dq x2 : ℚ) : ℝ)
    · exact tbOK_sound h.1 h1.le hx
    · simp only [lastX] at h2
      exact tbChain_sound rest x2 h.2 x (lt_of_not_ge hx) h2

/-! ## `Θ'` bounds: analytic part near `x = 0` -/

/-- Contact threshold of the analytic region: `NA/2^40 ≥ 0.48995`. -/
def NA : ℕ := 538705722029
/-- Right end of the analytic region, `x₀ = X0N/2^48`. -/
def X0N : ℕ := 2829648220382

theorem near_data : okN NA = true ∧ 1 - 2 * dyq NA ≤ 201 / 10000 ∧
    2 * dq X0N * (vd NA).Hhi ≤ 1 - 2 * dyq NA ∧ 0 < (vd NA).Hlo ∧
    8 / L2loD * (243 / 100) * 4 ≤ 3 * TH3P ∧
    3 * TH3M ≤ 8 / L2hiD * (178 / 100) * 4 * (vd NA).Hlo ^ 2 := by
  decide +kernel

open ZeroCapLeftStationaryThetaBracket in
theorem thetaDeriv_near {x : ℝ} (hx0 : 0 < x) (hx : x ≤ ((dq X0N : ℚ) : ℝ)) :
    8 / Real.log 2 - 3 * ((TH3P : ℚ) : ℝ) * x ^ 2 ≤ deriv e8Theta x ∧
      deriv e8Theta x ≤ 8 / Real.log 2 - 3 * ((TH3M : ℚ) : ℝ) * x ^ 2 := by
  obtain ⟨hok, hy, hx0d, hHl, hcp, hcm⟩ := near_data
  rw [deriv_e8Theta_eq_Psi hx0]
  have dA := vd_sound hok
  have hva0 : (0 : ℝ) < ((dyq NA : ℚ) : ℝ) := dyq_pos hok
  have hvah : ((dyq NA : ℚ) : ℝ) ≤ 1 / 2 := dyq_le_half hok
  have hHA := VD.le_Hhi dA
  rw [vd_v] at hHA
  have hHhi0 : (0 : ℝ) ≤ (((vd NA).Hhi : ℚ) : ℝ) :=
    le_trans (H_nonneg hva0.le (by linarith)) hHA
  have hx0dR : 2 * ((dq X0N : ℚ) : ℝ) * (((vd NA).Hhi : ℚ) : ℝ) ≤ 1 - 2 * ((dyq NA : ℚ) : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hx0d; push_cast at h'; exact h'
  have hres : 2 * x * (((vd NA).Hhi : ℚ) : ℝ) ≤ 1 - 2 * ((dyq NA : ℚ) : ℝ) := by
    have := mul_le_mul_of_nonneg_right hx hHhi0
    linarith
  have hva : ((dyq NA : ℚ) : ℝ) ≤ radialContact (2 * x) 1 :=
    contact_lower_of_entropy_upper hx0 hva0.le hvah hHA hres
  have hv0 : 0 < radialContact (2 * x) 1 := radialContact_pos (by positivity) one_pos
  have hvh : radialContact (2 * x) 1 < 1 / 2 := radialContact_lt_half (by positivity) one_pos
  have heq : 2 * x * H (radialContact (2 * x) 1) = 1 * (1 - 2 * radialContact (2 * x) 1) :=
    radialContact_equation (by positivity) one_pos
  generalize radialContact (2 * x) 1 = v at hva hv0 hvh heq ⊢
  have hyR : 1 - 2 * v ≤ 201 / 10000 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hy; push_cast at h'; linarith
  obtain ⟨hPl, hPu⟩ := psi_near hv0 hvh hyR
  have hy2 : (1 - 2 * v) ^ 2 = 4 * (x ^ 2 * H v ^ 2) := by
    have : 1 - 2 * v = 2 * x * H v := by linarith
    rw [this]; ring
  rw [hy2] at hPl hPu
  have hH1 : H v ≤ 1 := H_le_one v
  have hHlo : (((vd NA).Hlo : ℚ) : ℝ) ≤ H v := by
    have := VD.Hlo_le dA
    rw [vd_v] at this
    exact this.trans (H_mono hva0.le hva hvh.le)
  have hHl0 : (0 : ℝ) < (((vd NA).Hlo : ℚ) : ℝ) := by exact_mod_cast hHl
  have hHv0 : 0 ≤ H v := hHl0.le.trans hHlo
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hxH1 : x ^ 2 * H v ^ 2 ≤ x ^ 2 := by
    have : H v ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hxH2 : x ^ 2 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2 ≤ x ^ 2 * H v ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hHl0.le hHlo 2) hx2
  obtain ⟨ht0lo, ht0hi⟩ := theta0_bounds
  have hθ0 : 0 < 8 / Real.log 2 := by positivity
  have hcpR : 8 / ((L2loD : ℚ) : ℝ) * (243 / 100) * 4 ≤ 3 * ((TH3P : ℚ) : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hcp; push_cast at h'; exact h'
  have hcmR : 3 * ((TH3M : ℚ) : ℝ) ≤
      8 / ((L2hiD : ℚ) : ℝ) * (178 / 100) * 4 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2 := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hcm; push_cast at h'; exact h'
  constructor
  · have a1 : 8 / Real.log 2 * (243 / 100) * 4 * (x ^ 2 * H v ^ 2) ≤
        8 / ((L2loD : ℚ) : ℝ) * (243 / 100) * 4 * x ^ 2 := by
      calc 8 / Real.log 2 * (243 / 100) * 4 * (x ^ 2 * H v ^ 2)
          ≤ 8 / Real.log 2 * (243 / 100) * 4 * x ^ 2 :=
            mul_le_mul_of_nonneg_left hxH1 (by positivity)
        _ ≤ 8 / ((L2loD : ℚ) : ℝ) * (243 / 100) * 4 * x ^ 2 := by
            apply mul_le_mul_of_nonneg_right _ hx2
            nlinarith
    have a2 : 8 / ((L2loD : ℚ) : ℝ) * (243 / 100) * 4 * x ^ 2 ≤ 3 * ((TH3P : ℚ) : ℝ) * x ^ 2 :=
      mul_le_mul_of_nonneg_right hcpR hx2
    nlinarith
  · have b1 : 8 / ((L2hiD : ℚ) : ℝ) * (178 / 100) * 4 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2 * x ^ 2 ≤
        8 / Real.log 2 * (178 / 100) * 4 * (x ^ 2 * H v ^ 2) := by
      have e1 : 8 / ((L2hiD : ℚ) : ℝ) * (178 / 100) * 4 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2 * x ^ 2 =
          8 / ((L2hiD : ℚ) : ℝ) * (178 / 100) * 4 * (x ^ 2 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2) := by ring
      rw [e1]
      calc 8 / ((L2hiD : ℚ) : ℝ) * (178 / 100) * 4 * (x ^ 2 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2)
          ≤ 8 / Real.log 2 * (178 / 100) * 4 * (x ^ 2 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            nlinarith
        _ ≤ 8 / Real.log 2 * (178 / 100) * 4 * (x ^ 2 * H v ^ 2) :=
            mul_le_mul_of_nonneg_left hxH2 (by positivity)
    have b2 : 3 * ((TH3M : ℚ) : ℝ) * x ^ 2 ≤
        8 / ((L2hiD : ℚ) : ℝ) * (178 / 100) * 4 * (((vd NA).Hlo : ℚ) : ℝ) ^ 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right hcmR hx2
    nlinarith

/-! ## `Θ'` bounds on `(0, x_c]` -/

def cornerBoxes : List (ℕ × ℕ × ℕ) := [(2873861473825, 538533167331, 538705722031),
    (2918074727268, 538360617421, 538533167335),
    (2962287980711, 538188072371, 538360617425),
    (3006501234154, 538015532255, 538188072376),
    (3050714487597, 537842997146, 538015532259),
    (3094927741040, 537670467117, 537842997150),
    (3139140994483, 537497942241, 537670467121),
    (3183354247926, 537325422592, 537497942245),
    (3227567501369, 537152908243, 537325422596),
    (3271780754812, 536980399268, 537152908247),
    (3315994008255, 536807895739, 536980399272),
    (3360207261698, 536635397730, 536807895743),
    (3404420515141, 536462905314, 536635397734),
    (3448633768584, 536290418564, 536462905318),
    (3492847022027, 536117937554, 536290418568),
    (3537060275470, 535945462357, 536117937558),
    (3581273528913, 535772993046, 535945462361),
    (3625486782356, 535600529694, 535772993050),
    (3669700035799, 535428072374, 535600529698),
    (3713913289242, 535255621159, 535428072378),
    (3802339796128, 534910737340, 535255621164),
    (3890766303014, 534565878819, 534910737344),
    (3979192809900, 534221046181, 534565878823),
    (4067619316786, 533876240012, 534221046186),
    (4156045823672, 533531460895, 533876240016),
    (4244472330558, 533186709413, 533531460899),
    (4332898837444, 532841986151, 533186709418),
    (4421325344330, 532497291691, 532841986155),
    (4509751851216, 532152626617, 532497291696),
    (4598178358102, 531807991511, 532152626621),
    (4686604864988, 531463386955, 531807991515),
    (4775031371874, 531118813532, 531463386959),
    (4863457878760, 530774271823, 531118813536),
    (4951884385646, 530429762409, 530774271827),
    (5040310892532, 530085285872, 530429762413),
    (5128737399418, 529740842792, 530085285876),
    (5217163906304, 529396433751, 529740842797),
    (5305590413190, 529052059327, 529396433755),
    (5394016920076, 528707720101, 529052059331),
    (5482443426962, 528363416651, 528707720105),
    (5570869933848, 528019149558, 528363416656),
    (5659296440734, 527674919399, 528019149562),
    (5747722947620, 527330726754, 527674919404),
    (5836149454506, 526986572199, 527330726758),
    (5924575961392, 526642456313, 526986572203),
    (6013002468278, 526298379672, 526642456317),
    (6101428975164, 525954342854, 526298379677),
    (6189855482050, 525610346434, 525954342858),
    (6278281988936, 525266390989, 525610346439),
    (6366708495822, 524922477095, 525266390994),
    (6455135002708, 524578605325, 524922477099),
    (6543561509594, 524234776256, 524578605329),
    (6631988016480, 523890990461, 524234776260),
    (6720414523366, 523547248514, 523890990465),
    (6808841030252, 523203550990, 523547248519),
    (6985694044024, 522516291496, 523203550994),
    (7162547057796, 521829216560, 522516291501),
    (7339400071568, 521142330752, 521829216564),
    (7516253085340, 520455638635, 521142330756),
    (7693106099112, 519769144766, 520455638639),
    (7869959112884, 519082853694, 519769144771),
    (8046812126656, 518396769958, 519082853698),
    (8223665140428, 517710898090, 518396769962),
    (8400518154200, 517025242614, 517710898094),
    (8577371167972, 516339808045, 517025242618),
    (8754224181744, 515654598889, 516339808049),
    (8931077195516, 514969619644, 515654598893),
    (9107930209288, 514284874799, 514969619649),
    (9284783223060, 513600368833, 514284874804),
    (9461636236832, 512916106216, 513600368838),
    (9638489250604, 512232091408, 512916106220),
    (9815342264376, 511548328859, 512232091412),
    (9992195278148, 510864823012, 511548328864),
    (10169048291920, 510181578295, 510864823016),
    (10345901305692, 509498599131, 510181578300),
    (10522754319464, 508815889930, 509498599136),
    (10699607333236, 508133455090, 508815889934),
    (10876460347008, 507451299002, 508133455094),
    (11053313360780, 506769426043, 507451299006),
    (11230166374552, 506087840581, 506769426047),
    (11583872402096, 504725549560, 506087840585),
    (11937578429640, 503364460653, 504725549564),
    (12291284457184, 502004608385, 503364460657),
    (12644990484728, 500646027096, 502004608390),
    (12998696512272, 499288750925, 500646027100),
    (13352402539816, 497932813816, 499288750929),
    (13706108567360, 496578249505, 497932813820),
    (14059814594904, 495225091522, 496578249509),
    (14413520622448, 493873373182, 495225091526),
    (14767226649992, 492523127583, 493873373187),
    (15120932677536, 491174387601, 492523127588),
    (15474638705080, 489827185885, 491174387605),
    (15828344732624, 488481554855, 489827185889),
    (16182050760168, 487137526695, 488481554859),
    (16535756787712, 485795133352, 487137526699),
    (16889462815256, 484454406531, 485795133356),
    (17596874870344, 481778078040, 484454406535),
    (18304286925432, 479108789872, 481778078044),
    (19011698980520, 476446786573, 479108789877),
    (19719111035608, 473792308472, 476446786578),
    (20426523090696, 471145591578, 473792308476),
    (21133935145784, 468506867490, 471145591582),
    (21841347200872, 465876363297, 468506867494),
    (22548759255960, 463254301503, 465876363302),
    (23256171311048, 460640899940, 463254301507),
    (24670995421224, 455440925063, 460640899944),
    (26085819531400, 450278085342, 455440925067),
    (27500643641576, 445153948715, 450278085346),
    (28915467751752, 440070002905, 445153948719),
    (30330291861928, 435027654315, 440070002909),
    (31745115972104, 430028227271, 435027654319),
    (33159940082280, 425072963624, 430028227275),
    (34574764192456, 420163022672, 425072963628),
    (35989588302632, 415299481409, 420163022677),
    (37404412412808, 410483335057, 415299481413),
    (38819236522984, 405715497890, 410483335061),
    (40234060633160, 400996804309, 405715497894),
    (41648884743336, 396328010157, 400996804313),
    (43063708853512, 391709794249, 396328010161),
    (43771120908600, 389419844626, 391709794253),
    (44478532963688, 387142760101, 389419844630),
    (45185945018776, 384878604660, 387142760105),
    (45893357073864, 382627437829, 384878604664),
    (46247063101408, 381506742541, 382627437833),
    (46600769128952, 380389314741, 381506742545),
    (46954475156496, 379275160645, 380389314745),
    (47308181184040, 378164286205, 379275160649),
    (47661887211584, 377056697108, 378164286209)]

theorem cornerBoxes_ok : tbChain X0N cornerBoxes = true := by decide +kernel

/-- Right end of the certified range: `x_c ≤ XCN/2^48`. -/
def XCN : ℕ := 47661887211584

theorem cornerBoxes_last : lastX X0N cornerBoxes = XCN := by decide

theorem thetaDeriv_bounds {x : ℝ} (hx0 : 0 < x) (hx : x ≤ ((dq XCN : ℚ) : ℝ)) :
    8 / Real.log 2 - 3 * ((TH3P : ℚ) : ℝ) * x ^ 2 ≤ deriv e8Theta x ∧
      deriv e8Theta x ≤ 8 / Real.log 2 - 3 * ((TH3M : ℚ) : ℝ) * x ^ 2 := by
  by_cases h : x ≤ ((dq X0N : ℚ) : ℝ)
  · exact thetaDeriv_near hx0 h
  · have h2 : x ≤ ((dq (lastX X0N cornerBoxes) : ℚ) : ℝ) := by rw [cornerBoxes_last]; exact hx
    exact tbChain_sound cornerBoxes X0N cornerBoxes_ok x (lt_of_not_ge h) h2

/-! ## Increments of `Θ` -/

theorem hasDerivAt_cubic (a b s : ℝ) :
    HasDerivAt (fun s => a * s - b * s ^ 3) (a - 3 * b * s ^ 2) s := by
  have h := ((hasDerivAt_id' s).const_mul a).sub ((hasDerivAt_pow 3 s).const_mul b)
  exact h.congr_deriv (by norm_num <;> ring)

theorem theta_sub_le_of_deriv_le {x y : ℝ} {φ φ' : ℝ → ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hφ : ∀ s ∈ Icc x y, HasDerivAt φ (φ' s) s)
    (hd : ∀ s ∈ Icc x y, deriv e8Theta s ≤ φ' s) : e8Theta y - e8Theta x ≤ φ y - φ x := by
  have hpos : ∀ s ∈ Icc x y, 0 < s := fun s hs => hx.trans_le hs.1
  have hcont : ContinuousOn (fun s => φ s - e8Theta s) (Icc x y) := by
    apply ContinuousOn.sub
    · intro s hs; exact (hφ s hs).continuousAt.continuousWithinAt
    · exact continuousOn_e8Theta_pos.mono (fun s hs => hpos s hs)
  have hmono : MonotoneOn (fun s => φ s - e8Theta s) (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont
    · intro s hs
      have hs' := interior_subset hs
      exact ((hφ s hs').differentiableAt.sub
        (hasDerivAt_e8Theta (hpos s hs')).differentiableAt).differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hdd : HasDerivAt (fun s => φ s - e8Theta s) (φ' s - deriv e8Theta s) s :=
        (hφ s hs').sub (hasDerivAt_e8Theta (hpos s hs')).differentiableAt.hasDerivAt
      rw [hdd.deriv]
      linarith [hd s hs']
  have := hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  simp only at this
  linarith

theorem theta_sub_ge_of_deriv_ge {x y : ℝ} {φ φ' : ℝ → ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hφ : ∀ s ∈ Icc x y, HasDerivAt φ (φ' s) s)
    (hd : ∀ s ∈ Icc x y, φ' s ≤ deriv e8Theta s) : φ y - φ x ≤ e8Theta y - e8Theta x := by
  have hpos : ∀ s ∈ Icc x y, 0 < s := fun s hs => hx.trans_le hs.1
  have hcont : ContinuousOn (fun s => e8Theta s - φ s) (Icc x y) := by
    apply ContinuousOn.sub
    · exact continuousOn_e8Theta_pos.mono (fun s hs => hpos s hs)
    · intro s hs; exact (hφ s hs).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (fun s => e8Theta s - φ s) (Icc x y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc x y) hcont
    · intro s hs
      have hs' := interior_subset hs
      exact ((hasDerivAt_e8Theta (hpos s hs')).differentiableAt.sub
        (hφ s hs').differentiableAt).differentiableWithinAt
    · intro s hs
      have hs' := interior_subset hs
      have hdd : HasDerivAt (fun s => e8Theta s - φ s) (deriv e8Theta s - φ' s) s :=
        (hasDerivAt_e8Theta (hpos s hs')).differentiableAt.hasDerivAt.sub (hφ s hs')
      rw [hdd.deriv]
      linarith [hd s hs']
  have := hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy
  simp only at this
  linarith

theorem theta_inc_upper {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ ((dq XCN : ℚ) : ℝ)) :
    e8Theta y - e8Theta x ≤
      8 / Real.log 2 * (y - x) - ((TH3M : ℚ) : ℝ) * (y ^ 3 - x ^ 3) := by
  have := theta_sub_le_of_deriv_le (φ := fun s => 8 / Real.log 2 * s - ((TH3M : ℚ) : ℝ) * s ^ 3)
    (φ' := fun s => 8 / Real.log 2 - 3 * ((TH3M : ℚ) : ℝ) * s ^ 2) hx hxy
    (fun s _ => hasDerivAt_cubic _ _ s)
    (fun s hs => (thetaDeriv_bounds (hx.trans_le hs.1) (hs.2.trans hy)).2)
  linarith

theorem theta_inc_lower {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hy : y ≤ ((dq XCN : ℚ) : ℝ)) :
    8 / Real.log 2 * (y - x) - ((TH3P : ℚ) : ℝ) * (y ^ 3 - x ^ 3) ≤
      e8Theta y - e8Theta x := by
  have := theta_sub_ge_of_deriv_ge (φ := fun s => 8 / Real.log 2 * s - ((TH3P : ℚ) : ℝ) * s ^ 3)
    (φ' := fun s => 8 / Real.log 2 - 3 * ((TH3P : ℚ) : ℝ) * s ^ 2) hx hxy
    (fun s _ => hasDerivAt_cubic _ _ s)
    (fun s hs => (thetaDeriv_bounds (hx.trans_le hs.1) (hs.2.trans hy)).1)
  linarith

theorem theta_val_lower {m : ℝ} (hm : 0 < m) (hmc : m ≤ ((dq XCN : ℚ) : ℝ)) :
    8 / Real.log 2 * m - ((TH3P : ℚ) : ℝ) * m ^ 3 ≤ e8Theta m := by
  by_contra hlt
  push Not at hlt
  set gap := 8 / Real.log 2 * m - ((TH3P : ℚ) : ℝ) * m ^ 3 - e8Theta m with hgap
  have hg : 0 < gap := by linarith
  have hθ : 0 < 8 / Real.log 2 := by positivity
  set ε := min (m / 2) (gap / (2 * (8 / Real.log 2))) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
  have hεm : ε ≤ m := (min_le_left _ _).trans (by linarith)
  have hεg : 8 / Real.log 2 * ε ≤ gap / 2 := by
    have h1 : ε ≤ gap / (2 * (8 / Real.log 2)) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hθ.le
    have e : 8 / Real.log 2 * (gap / (2 * (8 / Real.log 2))) = gap / 2 := by field_simp
    linarith
  have hinc := theta_inc_lower hε0 hεm hmc
  have hpos := e8Theta_pos hε0
  have hε3 : 0 ≤ ε ^ 3 := by positivity
  have hTP := TH3P_nonneg
  have : 0 ≤ ((TH3P : ℚ) : ℝ) * ε ^ 3 := mul_nonneg hTP hε3
  linarith

/-- Subadditivity defect: `Θ(x) + Θ(y) − Θ(x+y) ≥ ((7θ₃⁻ − θ₃⁺)/2)·xy(x+y)` on `(0, x_c]`. -/
theorem G_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ ((dq XCN : ℚ) : ℝ)) :
    (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) / 2 * (x * y * (x + y)) ≤
      e8Theta x + e8Theta y - e8Theta (x + y) := by
  have hTM := TH3M_nonneg
  have hTPM : ((TH3M : ℚ) : ℝ) ≤ ((TH3P : ℚ) : ℝ) := by unfold TH3M TH3P; norm_num
  -- symmetric reduction to `m ≤ M`
  have key : ∀ m M : ℝ, 0 < m → m ≤ M → m + M ≤ ((dq XCN : ℚ) : ℝ) →
      (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) / 2 * (m * M * (m + M)) ≤
        e8Theta m + e8Theta M - e8Theta (m + M) := by
    intro m M hm hmM hs
    have hM : 0 < M := hm.trans_le hmM
    have h1 := theta_inc_upper hM (show M ≤ m + M by linarith) hs
    have h2 := theta_val_lower hm (by linarith)
    have a : m ^ 2 ≤ m * M := by nlinarith
    have b := mul_le_mul_of_nonneg_left a hm.le
    have c := mul_nonneg (mul_nonneg hm.le hM.le) (sub_nonneg.mpr hmM)
    have hcub : m ^ 3 ≤ m * M * (m + M) / 2 := by nlinarith
    have hd : 0 ≤ ((TH3P : ℚ) : ℝ) - ((TH3M : ℚ) : ℝ) := by linarith
    have := mul_le_mul_of_nonneg_left hcub hd
    have e : (m + M) ^ 3 - M ^ 3 = m ^ 3 + 3 * (m * M * (m + M)) := by ring
    have e' : m + M - M = m := by ring
    rw [e'] at h1
    nlinarith
  rcases le_total x y with h | h
  · exact key x y hx h hxy
  · have h2 := key y x hy h (by linarith)
    have e1 : y * x * (y + x) = x * y * (x + y) := by ring
    have e2 : y + x = x + y := by ring
    rw [e1, e2] at h2
    linarith

/-! ## The entropy gap near `1/2` -/

def KC : ℚ := 311 / 100

theorem J_half_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 5 / 32) : J (1 / 2 - s) ≤ 2 * (KC : ℝ) * s := by
  have hy0 : 0 ≤ 2 * s := by linarith
  have hy1 : 2 * s < 1 := by linarith
  obtain ⟨h1, h2⟩ := log_taylor3 hy0 hy1
  rw [abs_le] at h1 h2
  have hL := Real.log_two_gt_d9
  have hl0 : 0 < Real.log 2 := by linarith
  have eJ : J (1 / 2 - s) = (Real.log (1 + 2 * s) - Real.log (1 - 2 * s)) / Real.log 2 := by
    unfold J
    have e1 : (1 - (1 / 2 - s)) / (1 / 2 - s) = (1 + 2 * s) / (1 - 2 * s) := by
      rw [div_eq_div_iff (by linarith) (by linarith)]; ring
    rw [e1, Real.log_div (by linarith) (by linarith)]
  rw [eJ, div_le_iff₀ hl0]
  have hKC : ((KC : ℚ) : ℝ) = 311 / 100 := by unfold KC; norm_num
  rw [hKC]
  have h1y : (11 : ℝ) / 16 ≤ 1 - 2 * s := by linarith
  have hR : (2 * s) ^ 4 / (1 - 2 * s) ≤ (2 * s) * ((5 / 16) ^ 3 * (16 / 11)) := by
    rw [div_le_iff₀ (by linarith)]
    have hy3 : (2 * s) ^ 3 ≤ (5 / 16) ^ 3 := pow_le_pow_left₀ hy0 (by linarith) 3
    have a1 : (2 * s) ^ 4 = (2 * s) * (2 * s) ^ 3 := by ring
    have a2 : (2 * s) * (2 * s) ^ 3 ≤ (2 * s) * (5 / 16) ^ 3 := mul_le_mul_of_nonneg_left hy3 hy0
    have a3 : (2 * s) * (5 / 16) ^ 3 ≤ (2 * s) * ((5 / 16) ^ 3 * (16 / 11)) * (1 - 2 * s) := by
      have : (5 / 16 : ℝ) ^ 3 ≤ (5 / 16) ^ 3 * (16 / 11) * (1 - 2 * s) := by nlinarith
      have := mul_le_mul_of_nonneg_left this hy0
      linarith
    linarith
  have hy2 : (2 * s) ^ 3 ≤ (2 * s) * (5 / 16) ^ 2 := by
    have : (2 * s) ^ 2 ≤ (5 / 16) ^ 2 := pow_le_pow_left₀ hy0 (by linarith) 2
    have a1 : (2 * s) ^ 3 = (2 * s) * (2 * s) ^ 2 := by ring
    rw [a1]; exact mul_le_mul_of_nonneg_left this hy0
  have hsl : s * 0.6931471803 ≤ s * Real.log 2 := mul_le_mul_of_nonneg_left hL.le hs0
  nlinarith

theorem H_gap {α γ : ℝ} (hγ : 0 ≤ γ) (hγα : γ ≤ α) (hα : α ≤ 5 / 32) :
    H (1 / 2 - γ) - H (1 / 2 - α) ≤ (KC : ℝ) * (α ^ 2 - γ ^ 2) := by
  have hd : ∀ s ∈ Icc (0 : ℝ) (5 / 32),
      HasDerivAt (fun s => H (1 / 2 - s) + (KC : ℝ) * s ^ 2) (-J (1 / 2 - s) + 2 * (KC : ℝ) * s) s := by
    intro s hs
    have h1 : HasDerivAt H (J (1 / 2 - s)) (1 / 2 - s) :=
      hasDerivAt_H' (by linarith [hs.2]) (by linarith [hs.1])
    have h2 : HasDerivAt (fun s : ℝ => 1 / 2 - s) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub (1 / 2 : ℝ)
    have h3 := h1.comp s h2
    have h4 := (hasDerivAt_pow 2 s).const_mul (KC : ℝ)
    exact (h3.add h4).congr_deriv (by norm_num <;> ring)
  have hmono : MonotoneOn (fun s => H (1 / 2 - s) + (KC : ℝ) * s ^ 2) (Icc 0 (5 / 32)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · intro s hs; exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs; exact (hd s (interior_subset hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hd s (interior_subset hs)).deriv]
      have := J_half_le (interior_subset hs).1 (interior_subset hs).2
      linarith
  have := hmono ⟨hγ, hγα.trans hα⟩ ⟨hγ.trans hγα, hα⟩ hγα
  simp only at this
  linarith

/-! ## The corner -/

def N11 : ℕ := 377957122048

theorem corner_data : okN N11 = true ∧ dyq N11 = 11 / 32 ∧ 0 < (vd N11).Hlo ∧
    5 / 32 / (vd N11).Hlo ≤ dq XCN ∧
    4 * (8 / L2loD) * KC ≤ 7 * TH3M - TH3P := by
  decide +kernel

set_option maxHeartbeats 1600000 in
/-- **Corner exclusion.**  A Case-E stationary configuration with `a ≥ 11/32` has `D > 0`. -/
theorem corner_sound {a c e f : ℝ} (ha0 : 0 < a) (hac : a < c) (hc : c < 1 / 2) (hHa : H a = e)
    (hef : e < f) (hf1 : f ≤ 1) (hfc : f < H c) (ha : 11 / 32 ≤ a) :
    0 < Dst ((c - a) / (e + f)) ((1 - 2 * c) / (2 * f)) (f / (e + f)) := by
  obtain ⟨hok, h11, hHl, hxc, hineq⟩ := corner_data
  have he0 : 0 < e := by rw [← hHa]; exact H_pos ha0 (by linarith)
  have hf0 : 0 < f := he0.trans hef
  have hfne : f ≠ 0 := hf0.ne'
  have h11R : ((dyq N11 : ℚ) : ℝ) = 11 / 32 := by rw [h11]; norm_num
  have hHl0 : (0 : ℝ) < (((vd N11).Hlo : ℚ) : ℝ) := by exact_mod_cast hHl
  have heH : (((vd N11).Hlo : ℚ) : ℝ) ≤ e := by
    rw [← hHa]
    have := VD.Hlo_le (vd_sound hok)
    rw [vd_v, h11R] at this
    exact this.trans (H_mono (by norm_num) ha (by linarith))
  have hxcR : 5 / 32 / (((vd N11).Hlo : ℚ) : ℝ) ≤ ((dq XCN : ℚ) : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hxc; push_cast at h'; exact h'
  have hineqR : 4 * (8 / ((L2loD : ℚ) : ℝ)) * ((KC : ℚ) : ℝ) ≤
      7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ) := by
    have h' := (Rat.cast_le (K := ℝ)).mpr hineq; push_cast at h'; exact h'
  have hgap0 := H_gap (α := 1 / 2 - a) (γ := 1 / 2 - c) (by linarith) (by linarith) (by linarith)
  have e1 : (1 : ℝ) / 2 - (1 / 2 - c) = c := by ring
  have e2 : (1 : ℝ) / 2 - (1 / 2 - a) = a := by ring
  rw [e1, e2, hHa] at hgap0
  -- coordinates `α = 1/2 − a`, `γ = 1/2 − c`, `E = e + f`
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = 1 / 2 - a := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = 1 / 2 - c := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = e + f := ⟨_, rfl⟩
  rw [← hα, ← hγ] at hgap0
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hγα : γ < α := by rw [hγ, hα]; linarith
  have hα5 : α ≤ 5 / 32 := by rw [hα]; linarith
  have hE0 : 0 < E := by rw [hE]; linarith
  have hEne : E ≠ 0 := hE0.ne'
  have hE2 : E < 2 * f := by rw [hE]; linarith
  have hEe : 2 * e < E := by rw [hE]; linarith
  have hgap : f - e < ((KC : ℚ) : ℝ) * (α ^ 2 - γ ^ 2) := by linarith
  have hA1 : (c - a) / (e + f) = (α - γ) / E := by rw [← hE, hα, hγ]; ring
  have hW1 : (1 - 2 * c) / (2 * f) = γ / f := by
    rw [hγ, div_eq_div_iff (mul_pos two_pos hf0).ne' hfne]; ring
  have hL1 : f / (e + f) = f / E := by rw [hE]
  rw [hA1, hW1, hL1]
  have hsum : (α - γ) / E + 2 * (f / E) * (γ / f) = (α - γ) / E + 2 * γ / E := by
    first | (field_simp; done) | (field_simp; ring)
  unfold Dst
  rw [hsum]
  have hA0 : 0 < (α - γ) / E := div_pos (by linarith) hE0
  have hW0 : 0 < γ / f := div_pos hγ0 hf0
  have hW20 : 0 < 2 * γ / E := div_pos (by linarith) hE0
  have hWW2 : γ / f ≤ 2 * γ / E := by
    rw [div_le_div_iff₀ hf0 hE0]
    have := mul_lt_mul_of_pos_left hE2 hγ0
    linarith
  have hAW2 : (α - γ) / E + 2 * γ / E = (α + γ) / E := by ring
  have hAW2c : (α - γ) / E + 2 * γ / E ≤ ((dq XCN : ℚ) : ℝ) := by
    rw [hAW2]
    refine le_trans ?_ hxcR
    rw [div_le_div_iff₀ hE0 hHl0]
    have h1 : (α + γ) * (((vd N11).Hlo : ℚ) : ℝ) ≤ 5 / 16 * (((vd N11).Hlo : ℚ) : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hHl0.le
    linarith
  have hG := G_lower hA0 hW20 hAW2c
  have hinc := theta_inc_upper hW0 hWW2 (by linarith)
  have hcub : 0 ≤ ((TH3M : ℚ) : ℝ) * ((2 * γ / E) ^ 3 - (γ / f) ^ 3) :=
    mul_nonneg TH3M_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hW0.le hWW2 3))
  have hWd : 2 * γ / E - γ / f = γ * (f - e) / (E * f) := by
    rw [hE]
    have hEf : e + f ≠ 0 := by linarith
    first | (field_simp; done) | (field_simp; ring)
  obtain ⟨-, ht0hi⟩ := theta0_bounds
  have hθ : 0 < 8 / Real.log 2 := by positivity
  have hKC0 : (0 : ℝ) < ((KC : ℚ) : ℝ) := by unfold KC; norm_num
  have hP : 0 < γ * (α ^ 2 - γ ^ 2) := by
    have h1 : 0 < α - γ := by linarith
    have h2 : 0 < α + γ := by linarith
    have e : α ^ 2 - γ ^ 2 = (α - γ) * (α + γ) := by ring
    rw [e]; exact mul_pos hγ0 (mul_pos h1 h2)
  have hMG : (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) / 2 *
      ((α - γ) / E * (2 * γ / E) * ((α - γ) / E + 2 * γ / E)) =
      (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) * (γ * (α ^ 2 - γ ^ 2)) / E ^ 3 := by
    first | (field_simp; done) | (field_simp; ring)
  have hEf : 0 < E * f := mul_pos hE0 hf0
  have hT1 : 8 / Real.log 2 * (2 * γ / E - γ / f) <
      8 / Real.log 2 * ((KC : ℚ) : ℝ) * (γ * (α ^ 2 - γ ^ 2)) / (E * f) := by
    rw [hWd, mul_div_assoc', div_lt_div_iff_of_pos_right hEf]
    have := mul_lt_mul_of_pos_left hgap (mul_pos hθ hγ0)
    linarith
  have hT2 : 8 / Real.log 2 * ((KC : ℚ) : ℝ) * (γ * (α ^ 2 - γ ^ 2)) / (E * f) ≤
      (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) * (γ * (α ^ 2 - γ ^ 2)) / E ^ 3 := by
    rw [div_le_div_iff₀ hEf (pow_pos hE0 3)]
    have hE2' : E ^ 2 ≤ 4 * f := by
      have h1 := pow_le_pow_left₀ hE0.le hE2.le 2
      have h2 : f * f ≤ 1 * f := mul_le_mul_of_nonneg_right hf1 hf0.le
      have e : (2 * f) ^ 2 = 4 * (f * f) := by ring
      linarith
    have hθK : 8 / Real.log 2 * ((KC : ℚ) : ℝ) * 4 ≤ 7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ) := by
      have := mul_le_mul_of_nonneg_right ht0hi hKC0.le
      linarith
    have hk1 : 8 / Real.log 2 * ((KC : ℚ) : ℝ) * E ^ 2 ≤
        (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) * f := by
      have h1 := mul_le_mul_of_nonneg_left hE2' (mul_pos hθ hKC0).le
      have h2 := mul_le_mul_of_nonneg_right hθK hf0.le
      linarith
    have hPE : 0 ≤ γ * (α ^ 2 - γ ^ 2) * E := (mul_pos hP hE0).le
    have h3 := mul_le_mul_of_nonneg_right hk1 hPE
    calc 8 / Real.log 2 * ((KC : ℚ) : ℝ) * (γ * (α ^ 2 - γ ^ 2)) * E ^ 3
        = 8 / Real.log 2 * ((KC : ℚ) : ℝ) * E ^ 2 * (γ * (α ^ 2 - γ ^ 2) * E) := by ring
      _ ≤ (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) * f * (γ * (α ^ 2 - γ ^ 2) * E) := h3
      _ = (7 * ((TH3M : ℚ) : ℝ) - ((TH3P : ℚ) : ℝ)) * (γ * (α ^ 2 - γ ^ 2)) * (E * f) := by ring
  linarith [hG, hinc, hcub, hMG, hT1, hT2]

#print axioms thetaDeriv_bounds
#print axioms G_lower
#print axioms H_gap
#print axioms corner_sound

end CKLaneA1.R5

end


