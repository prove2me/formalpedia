-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMISound2
-- name    : CK_CKLaneM07_CE_TMISound2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:48:57.222297+00:00
-- url     : https://prove2.me/theorems/28aba554-8d51-4b47-bec1-89919628db43
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMISound2` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMISound2` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMISound2` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMISound2 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMISound2.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMISound1

-- ===== source module CKLaneM07.CE.TMISound2 =====
section

/-!
# Lane M07 / CE-stat: soundness of the fixed-point Taylor-model kernel (part 2: rounding, mulC, mul)
-/

set_option autoImplicit false

namespace CKLaneM07.CE

/-! ## Floor division by a positive integer -/

theorem ediv_bounds (a b : ℤ) (hb : 0 < b) :
    ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / (b : ℝ) ∧ (a : ℝ) / (b : ℝ) < ((a / b : ℤ) : ℝ) + 1 := by
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  have hdiv := Int.emod_add_ediv_mul a b
  have h0 : 0 ≤ a % b := Int.emod_nonneg a (ne_of_gt hb)
  have h1 : a % b < b := Int.emod_lt_of_pos a hb
  have e : (a : ℝ) = (b : ℝ) * ((a / b : ℤ) : ℝ) + ((a % b : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hdiv
    push_cast at this
    linarith [this]
  have h0' : (0 : ℝ) ≤ ((a % b : ℤ) : ℝ) := by exact_mod_cast h0
  have h1' : ((a % b : ℤ) : ℝ) < (b : ℝ) := by exact_mod_cast h1
  constructor
  · rw [le_div_iff₀ hbr]; nlinarith
  · rw [div_lt_iff₀ hbr]; nlinarith

theorem ONE_pos : (0 : ℤ) < ONE := by unfold ONE; positivity

theorem SC_eq : SC = ((ONE : ℤ) : ℝ) := rfl

/-- rounding a row by `k * a / ONE`: the scaled row minus the rounded row is bounded by the length -/
theorem rowEval_round (k : ℤ) {y : ℝ} (hy : |y| ≤ 1) : ∀ r : RowI,
    |(k : ℝ) / SC * rowEval y r - rowEval y (r.map (fun a => k * a / ONE))| ≤ (r.length : ℝ)
  | [] => by simp [rowEval]
  | a :: r => by
      have ih := rowEval_round k hy r
      obtain ⟨h1, h2⟩ := ediv_bounds (k * a) ONE ONE_pos
      simp only [List.map_cons, rowEval, List.length_cons]
      push_cast at h1 h2 ⊢
      have e : (k : ℝ) / SC * ((a : ℝ) + y * rowEval y r) -
          (((k * a / ONE : ℤ) : ℝ) + y * rowEval y (r.map (fun a => k * a / ONE))) =
          ((k : ℝ) * a / SC - ((k * a / ONE : ℤ) : ℝ)) +
            y * ((k : ℝ) / SC * rowEval y r - rowEval y (r.map (fun a => k * a / ONE))) := by
        unfold SC; ring
      rw [e]
      have hA : |(k : ℝ) * a / SC - ((k * a / ONE : ℤ) : ℝ)| ≤ 1 := by
        unfold SC; rw [abs_le]; constructor <;> linarith
      calc _ ≤ |(k : ℝ) * a / SC - ((k * a / ONE : ℤ) : ℝ)| +
            |y * ((k : ℝ) / SC * rowEval y r - rowEval y (r.map (fun a => k * a / ONE)))| :=
            abs_add_le _ _
        _ ≤ 1 + 1 * (r.length : ℝ) := by
            rw [abs_mul]
            gcongr
        _ = ((r.length : ℝ) + 1) := by ring

theorem pCount_cons (r : RowI) (p : PolI) : pCount (r :: p) = r.length + pCount p := rfl

theorem pEval_round (k : ℤ) {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : ∀ p : PolI,
    |(k : ℝ) / SC * pEval x y p - pEval x y (p.map (List.map (fun a => k * a / ONE)))| ≤
      (pCount (p.map (List.map (fun a => k * a / ONE))) : ℝ)
  | [] => by simp [pEval, pCount]
  | r :: p => by
      have ih := pEval_round k hx hy p
      have hr := rowEval_round k hy r
      simp only [List.map_cons, pEval, pCount_cons, List.length_map] at ih ⊢
      push_cast
      have e : (k : ℝ) / SC * (rowEval y r + x * pEval x y p) -
          (rowEval y (r.map (fun a => k * a / ONE)) + x * pEval x y (p.map (List.map (fun a => k * a / ONE)))) =
          ((k : ℝ) / SC * rowEval y r - rowEval y (r.map (fun a => k * a / ONE))) +
            x * ((k : ℝ) / SC * pEval x y p - pEval x y (p.map (List.map (fun a => k * a / ONE)))) := by
        ring
      rw [e]
      calc _ ≤ |(k : ℝ) / SC * rowEval y r - rowEval y (r.map (fun a => k * a / ONE))| +
            |x * ((k : ℝ) / SC * pEval x y p - pEval x y (p.map (List.map (fun a => k * a / ONE))))| :=
            abs_add_le _ _
        _ ≤ (r.length : ℝ) + 1 * (pCount (p.map (List.map (fun a => k * a / ONE))) : ℝ) := by
            rw [abs_mul]
            gcongr
        _ = _ := by ring

theorem cdiv_ge (a b : ℕ) (hb : 0 < b) : (a : ℝ) / (b : ℝ) ≤ (cdiv a b : ℝ) := by
  unfold cdiv
  have hbr : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  rw [div_le_iff₀ hbr]
  have h := Nat.div_add_mod (a + b - 1) b
  have hm := Nat.mod_lt (a + b - 1) hb
  have : a ≤ b * ((a + b - 1) / b) := by omega
  have : (a : ℝ) ≤ (b : ℝ) * (((a + b - 1) / b : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem ONEn_pos : 0 < ONEn := by unfold ONEn; positivity

theorem cdiv_ge_SC (a : ℕ) : (a : ℝ) / SC ≤ (cdiv a ONEn : ℝ) := by
  rw [SC_eq_nat]; exact cdiv_ge a ONEn ONEn_pos

/-! ## Multiplication by a fixed-point constant -/

theorem EnclAt.mulC {x y u : ℝ} {s : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (k : ℤ)
    (hs : EnclAt x y u s) : EnclAt x y ((k : ℝ) / SC * u) (TMI.mulC k s) := by
  unfold EnclAt at *
  have hS := SC_pos
  simp only [TMI.mulC]
  have hround := pEval_round k hx hy s.p
  set RP := pEval x y (s.p.map (List.map (fun a => k * a / ONE)))
  set P := pEval x y s.p
  have e : (k : ℝ) / SC * u - RP / SC =
      (k : ℝ) / SC * (u - P / SC) + ((k : ℝ) / SC * P - RP) / SC := by ring
  rw [e]
  have h1 : |(k : ℝ) / SC * (u - P / SC)| ≤ ((k.natAbs * s.r : ℕ) : ℝ) / SC / SC := by
    rw [abs_mul, abs_div, abs_of_pos hS]
    push_cast
    rw [natAbs_cast]
    calc |(k : ℝ)| / SC * |u - P / SC| ≤ |(k : ℝ)| / SC * ((s.r : ℝ) / SC) := by
          gcongr
      _ = |(k : ℝ)| * (s.r : ℝ) / SC / SC := by ring
  have h2 : |((k : ℝ) / SC * P - RP) / SC| ≤
      (pCount (s.p.map (List.map (fun a => k * a / ONE))) : ℝ) / SC := by
    rw [abs_div, abs_of_pos hS]
    gcongr
  have h3 := cdiv_ge_SC (k.natAbs * s.r)
  push_cast
  calc _ ≤ |(k : ℝ) / SC * (u - P / SC)| + |((k : ℝ) / SC * P - RP) / SC| := abs_add_le _ _
    _ ≤ ((k.natAbs * s.r : ℕ) : ℝ) / SC / SC +
          (pCount (s.p.map (List.map (fun a => k * a / ONE))) : ℝ) / SC := add_le_add h1 h2
    _ ≤ (cdiv (k.natAbs * s.r) ONEn : ℝ) / SC +
          (pCount (s.p.map (List.map (fun a => k * a / ONE))) : ℝ) / SC := by
        gcongr
    _ = _ := by ring

end CKLaneM07.CE

end


