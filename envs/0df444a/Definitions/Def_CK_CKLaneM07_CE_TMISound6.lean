-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMISound6
-- name    : CK_CKLaneM07_CE_TMISound6
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T13:03:45.479473+00:00
-- url     : https://prove2.me/theorems/f5f549e2-1c7b-4437-98a9-dd4be2abcc8e
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMISound6` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMISound6` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMISound6` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMISound6 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMISound6.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMISound5
import Definitions.Def_CK_CKLaneM07_CE_Chain

-- ===== source module CKLaneM07.CE.TMISound6 =====
section

/-!
# Lane M07 / CE-stat: soundness of the fixed-point Taylor-model kernel (part 6: reciprocal, hull, shift)
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open Finset

/-! ## Reciprocal -/

noncomputable def recHornerR (w : ℝ) : ℕ → ℝ → ℝ
  | 0, a => a
  | k + 1, a => recHornerR w k (a * w + (-1) ^ k)

theorem recHornerR_eq (w : ℝ) : ∀ (k : ℕ) (a : ℝ),
    recHornerR w k a = a * w ^ k + ∑ j ∈ range k, (-1) ^ j * w ^ j
  | 0, a => by simp [recHornerR]
  | k + 1, a => by
      rw [recHornerR, recHornerR_eq w k, sum_range_succ]
      ring

theorem int_one_div (k : ℕ) : ((((-1 : ℤ) ^ k * ONE : ℤ) : ℝ)) / SC = (-1 : ℝ) ^ k := by
  have hS : SC ≠ 0 := SC_pos.ne'
  unfold SC at hS ⊢
  push_cast
  field_simp

theorem encl_recHorner {x y wv : ℝ} {w : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (K : ℕ)
    (hw : EnclAt x y wv w) : ∀ (k : ℕ) (a : ℝ) (acc : TMI), EnclAt x y a acc →
      EnclAt x y (recHornerR wv k a) (CKLaneM07.CE.recHorner K w k acc)
  | 0, a, acc, h => by simpa [recHornerR, CKLaneM07.CE.recHorner] using h
  | k + 1, a, acc, h => by
      simp only [recHornerR, CKLaneM07.CE.recHorner]
      apply encl_recHorner hx hy K hw k
      have hm := EnclAt.mul hx hy K h hw
      have ha := hm.addC ((-1) ^ k * ONE)
      rw [int_one_div] at ha
      exact ha

theorem geom_err (w : ℝ) (n : ℕ) (hw : |w| < 1) :
    |1 / (1 + w) - ∑ j ∈ range (n + 1), (-w) ^ j| = |w| ^ (n + 1) / |1 + w| := by
  have h1 : 0 < 1 + w := by linarith [(abs_lt.mp hw).1]
  have hg := geom_sum_mul (-w) (n + 1)
  have e : 1 / (1 + w) - ∑ j ∈ range (n + 1), (-w) ^ j = (-w) ^ (n + 1) / (1 + w) := by
    field_simp
    linear_combination hg
  rw [e, abs_div, abs_pow, abs_neg]

theorem encl_recip {x y u : ℝ} {s t : TMI} {K n : ℕ} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (hs : EnclAt x y u s) (h : TMI.recip K n s = some t) : 0 < u ∧ EnclAt x y (1 / u) t := by
  unfold TMI.recip at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨h0, hrho⟩ := hc
  simp only [Option.some.injEq] at h
  subst h
  have hS := SC_pos
  have hw := EnclAt.wOf hx hy hs h0
  have hc0 : 0 < c0R s := div_pos (by exact_mod_cast h0) hS
  have hwb := abs_le_of_EnclAt hx hy hw
  have hrhoR : ((pAbs s.wOf.1.p + s.wOf.1.r : ℕ) : ℝ) / SC < 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hrho
    rw [rhoQ_cast] at this
    simpa using this
  set ρ : ℝ := ((pAbs s.wOf.1.p + s.wOf.1.r : ℕ) : ℝ) / SC with hρ
  set wv := (u - c0R s) / c0R s with hwv
  have hwl : |wv| < 1 := lt_of_le_of_lt hwb hrhoR
  have hu : u = c0R s * (1 + wv) := by rw [hwv]; field_simp; ring
  have h1w : 0 < 1 + wv := by linarith [(abs_lt.mp hwl).1]
  have hupos : 0 < u := by rw [hu]; exact mul_pos hc0 h1w
  refine ⟨hupos, ?_⟩
  -- the Horner value
  have htop : EnclAt x y ((-1 : ℝ) ^ n) (TMI.const ((-1) ^ n * ONE)) := by
    have := EnclAt.const x y ((-1) ^ n * ONE)
    rw [int_one_div] at this
    exact this
  have hH := encl_recHorner hx hy K hw n ((-1 : ℝ) ^ n) _ htop
  set acc := CKLaneM07.CE.recHorner K s.wOf.1 n (TMI.const ((-1) ^ n * ONE))
  set G := recHornerR wv n ((-1 : ℝ) ^ n)
  have hG : G = ∑ j ∈ range (n + 1), (-wv) ^ j := by
    rw [show G = recHornerR wv n ((-1 : ℝ) ^ n) from rfl, recHornerR_eq, sum_range_succ]
    rw [add_comm]
    congr 1
    · refine sum_congr rfl fun j _ => ?_
      ring
    · ring
  -- inverse of the centre
  obtain ⟨hi1, hi2⟩ := ediv_bounds (ONE * ONE) (pC00 s.p) h0
  have hinv_def : s.wOf.2 = (ONE * ONE) / pC00 s.p := rfl
  rw [← hinv_def] at hi1 hi2
  set inv := s.wOf.2 with hinv
  have hSC : SC = ((ONE : ℤ) : ℝ) := rfl
  push_cast at hi1 hi2
  rw [← hSC] at hi1 hi2
  have hu0 : (0 : ℝ) < (pC00 s.p : ℝ) := by exact_mod_cast h0
  have hinvc : 1 / c0R s = SC / (pC00 s.p : ℝ) := by unfold c0R; field_simp
  have hgap : |SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC| ≤ 1 / SC := by
    have e2 : SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC = (SC * SC / (pC00 s.p : ℝ) - (inv : ℝ)) / SC := by
      field_simp
    rw [e2, abs_div, abs_of_pos hS]
    gcongr
    rw [abs_le]; constructor <;> linarith
  have hinvle : SC / (pC00 s.p : ℝ) ≤ ((inv : ℝ) + 1) / SC := by
    rw [div_le_div_iff₀ hu0 hS]
    have := (div_lt_iff₀ hu0).mp hi2
    linarith
  have hinv1 : (0 : ℝ) < (inv : ℝ) + 1 :=
    lt_of_le_of_lt (div_nonneg (mul_self_nonneg SC) hu0.le) hi2
  have hres := EnclAt.mulC hx hy inv hH
  -- the true value
  have hval : 1 / u = SC / (pC00 s.p : ℝ) * (G + (1 / (1 + wv) - G)) := by
    rw [hu, ← hinvc]; field_simp; ring
  have htail : |1 / (1 + wv) - G| ≤ ρ ^ (n + 1) / (1 - ρ) := by
    rw [hG, geom_err wv n hwl]
    have hwlo : -ρ ≤ wv := (abs_le.mp hwb).1
    have hden : 1 - ρ ≤ |1 + wv| := by
      rw [abs_of_pos h1w]; linarith
    calc |wv| ^ (n + 1) / |1 + wv| ≤ ρ ^ (n + 1) / (1 - ρ) := by
          apply div_le_div₀ (pow_nonneg (le_trans (abs_nonneg _) hwb) _)
            (pow_le_pow_left₀ (abs_nonneg _) hwb _) (by linarith) hden
      _ = _ := rfl
  have hGb := abs_le_of_EnclAt hx hy hH
  have hq := qcl_ge ((rhoQ s.wOf.1) ^ (n + 1) / (1 - rhoQ s.wOf.1) * ((((inv + 1 : ℤ)) : ℚ) / (ONE : ℚ)))
  push_cast at hq
  rw [rhoQ_cast, ← hSC] at hq
  have hcd := cdiv_ge_SC (pAbs acc.p + acc.r)
  unfold EnclAt at hres ⊢
  push_cast at hcd ⊢
  rw [hval]
  have e : SC / (pC00 s.p : ℝ) * (G + (1 / (1 + wv) - G)) - pEval x y (TMI.mulC inv acc).p / SC =
      ((inv : ℝ) / SC * G - pEval x y (TMI.mulC inv acc).p / SC) +
        (SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC) * G + SC / (pC00 s.p : ℝ) * (1 / (1 + wv) - G) := by ring
  rw [e]
  have hA : |(SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC) * G| ≤ ((pAbs acc.p : ℝ) + (acc.r : ℝ)) / SC / SC := by
    rw [abs_mul]
    calc |SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC| * |G| ≤ 1 / SC * (((pAbs acc.p + acc.r : ℕ) : ℝ) / SC) := by
          gcongr
      _ = _ := by push_cast; ring
  have hB : |SC / (pC00 s.p : ℝ) * (1 / (1 + wv) - G)| ≤ ((inv : ℝ) + 1) / SC * (ρ ^ (n + 1) / (1 - ρ)) := by
    rw [abs_mul, abs_of_pos (div_pos hS hu0)]
    exact mul_le_mul hinvle htail (abs_nonneg _) (div_pos hinv1 hS).le
  calc _ ≤ |(inv : ℝ) / SC * G - pEval x y (TMI.mulC inv acc).p / SC| +
        |(SC / (pC00 s.p : ℝ) - (inv : ℝ) / SC) * G| + |SC / (pC00 s.p : ℝ) * (1 / (1 + wv) - G)| :=
        abs_add_three _ _ _
    _ ≤ ((TMI.mulC inv acc).r : ℝ) / SC + ((pAbs acc.p : ℝ) + (acc.r : ℝ)) / SC / SC +
          ((inv : ℝ) + 1) / SC * (ρ ^ (n + 1) / (1 - ρ)) := by gcongr
    _ ≤ ((TMI.mulC inv acc).r : ℝ) / SC + (cdiv (pAbs acc.p + acc.r) ONEn : ℝ) / SC + 1 / SC +
          ((qcl ((rhoQ s.wOf.1) ^ (n + 1) / (1 - rhoQ s.wOf.1) * (((inv : ℚ) + 1) / (ONE : ℚ))) : ℕ) : ℝ) / SC := by
        have h1 : ((pAbs acc.p : ℝ) + (acc.r : ℝ)) / SC / SC ≤ (cdiv (pAbs acc.p + acc.r) ONEn : ℝ) / SC := by
          apply div_le_div_of_nonneg_right _ hS.le; linarith
        have h2 : ((inv : ℝ) + 1) / SC * (ρ ^ (n + 1) / (1 - ρ)) ≤
            ((qcl ((rhoQ s.wOf.1) ^ (n + 1) / (1 - rhoQ s.wOf.1) * (((inv : ℚ) + 1) / (ONE : ℚ))) : ℕ) : ℝ) / SC := by
          have e3 : ((inv : ℝ) + 1) / SC * (ρ ^ (n + 1) / (1 - ρ)) = ρ ^ (n + 1) / (1 - ρ) * (((inv : ℝ) + 1) / SC) := by
            ring
          rw [e3]; exact hq
        have h3 : (0 : ℝ) ≤ 1 / SC := (one_div_pos.mpr hS).le
        linarith
    _ = _ := by ring

/-! ## Hull and shifted candidates -/

theorem rowEval_half {y : ℝ} (hy : |y| ≤ 1) : ∀ r : RowI,
    |rowEval y r / 2 - rowEval y (r.map (fun z => z / 2))| ≤ (r.length : ℝ)
  | [] => by simp [rowEval]
  | a :: r => by
      have ih := rowEval_half hy r
      obtain ⟨h1, h2⟩ := ediv_bounds a 2 (by norm_num)
      simp only [List.map_cons, rowEval, List.length_cons]
      push_cast at h1 h2 ⊢
      have e : ((a : ℝ) + y * rowEval y r) / 2 - (((a / 2 : ℤ) : ℝ) + y * rowEval y (r.map (fun z => z / 2))) =
          ((a : ℝ) / 2 - ((a / 2 : ℤ) : ℝ)) + y * (rowEval y r / 2 - rowEval y (r.map (fun z => z / 2))) := by ring
      rw [e]
      calc _ ≤ |(a : ℝ) / 2 - ((a / 2 : ℤ) : ℝ)| + |y * (rowEval y r / 2 - rowEval y (r.map (fun z => z / 2)))| :=
            abs_add_le _ _
        _ ≤ 1 + 1 * (r.length : ℝ) := by
            rw [abs_mul]
            gcongr
            rw [abs_le]; constructor <;> linarith
        _ = _ := by ring

theorem pEval_half {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) : ∀ p : PolI,
    |pEval x y p / 2 - pEval x y (p.map (List.map (fun z => z / 2)))| ≤
      (pCount (p.map (List.map (fun z => z / 2))) : ℝ)
  | [] => by simp [pEval, pCount]
  | r :: p => by
      have ih := pEval_half hx hy p
      have hr := rowEval_half hy r
      simp only [List.map_cons, pEval, pCount_cons, List.length_map] at ih ⊢
      push_cast
      have e : (rowEval y r + x * pEval x y p) / 2 -
          (rowEval y (r.map (fun z => z / 2)) + x * pEval x y (p.map (List.map (fun z => z / 2)))) =
          (rowEval y r / 2 - rowEval y (r.map (fun z => z / 2))) +
            x * (pEval x y p / 2 - pEval x y (p.map (List.map (fun z => z / 2)))) := by ring
      rw [e]
      calc _ ≤ |rowEval y r / 2 - rowEval y (r.map (fun z => z / 2))| +
            |x * (pEval x y p / 2 - pEval x y (p.map (List.map (fun z => z / 2))))| := abs_add_le _ _
        _ ≤ (r.length : ℝ) + 1 * (pCount (p.map (List.map (fun z => z / 2))) : ℝ) := by
            rw [abs_mul]
            gcongr
        _ = _ := by ring

theorem encl_hull {x y va vb v : ℝ} {a b : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1)
    (ha : EnclAt x y va a) (hb : EnclAt x y vb b) (hv : (va ≤ v ∧ v ≤ vb) ∨ (vb ≤ v ∧ v ≤ va)) :
    EnclAt x y v (hull a b) := by
  have hS := SC_pos
  unfold EnclAt at ha hb ⊢
  simp only [hull]
  set avg := (pAdd a.p b.p).map (List.map (fun z => z / 2))
  have hround := pEval_half hx hy (pAdd a.p b.p)
  rw [pEval_pAdd] at hround
  have hd := abs_pEval_le hx hy (pAdd b.p (pNeg a.p))
  rw [pEval_pAdd, pEval_pNeg] at hd
  set Pa := pEval x y a.p
  set Pb := pEval x y b.p
  have hc2 := cdiv_ge (pAbs (pAdd b.p (pNeg a.p))) 2 (by norm_num)
  have hmid : |v - (Pa + Pb) / 2 / SC| ≤ ((a.r : ℝ) + (b.r : ℝ)) / SC + |Pb - Pa| / 2 / SC := by
    rw [abs_le] at ha hb ⊢
    have hPab : -|Pb - Pa| ≤ Pb - Pa ∧ Pb - Pa ≤ |Pb - Pa| := ⟨neg_abs_le _, le_abs_self _⟩
    rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · constructor
      · have : va - (Pa + Pb) / 2 / SC = (va - Pa / SC) - (Pb - Pa) / 2 / SC := by ring
        have h3 : (Pb - Pa) / 2 / SC ≤ |Pb - Pa| / 2 / SC := by gcongr; exact hPab.2
        have h4 : (a.r : ℝ) / SC ≤ ((a.r : ℝ) + (b.r : ℝ)) / SC := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) b.r]
        linarith [ha.1]
      · have : vb - (Pa + Pb) / 2 / SC = (vb - Pb / SC) + (Pb - Pa) / 2 / SC := by ring
        have h3 : (Pb - Pa) / 2 / SC ≤ |Pb - Pa| / 2 / SC := by gcongr; exact hPab.2
        have h4 : (b.r : ℝ) / SC ≤ ((a.r : ℝ) + (b.r : ℝ)) / SC := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) a.r]
        linarith [hb.2]
    · constructor
      · have : vb - (Pa + Pb) / 2 / SC = (vb - Pb / SC) + (Pb - Pa) / 2 / SC := by ring
        have h3 : -(|Pb - Pa| / 2 / SC) ≤ (Pb - Pa) / 2 / SC := by
          have h := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hPab.1 (by norm_num : (0:ℝ) ≤ 2)) hS.le
          simpa [neg_div] using h
        have h4 : (b.r : ℝ) / SC ≤ ((a.r : ℝ) + (b.r : ℝ)) / SC := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) a.r]
        linarith [hb.1]
      · have : va - (Pa + Pb) / 2 / SC = (va - Pa / SC) - (Pb - Pa) / 2 / SC := by ring
        have h3 : -(|Pb - Pa| / 2 / SC) ≤ (Pb - Pa) / 2 / SC := by
          have h := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hPab.1 (by norm_num : (0:ℝ) ≤ 2)) hS.le
          simpa [neg_div] using h
        have h4 : (a.r : ℝ) / SC ≤ ((a.r : ℝ) + (b.r : ℝ)) / SC := by gcongr; linarith [Nat.cast_nonneg (α := ℝ) b.r]
        linarith [ha.2]
  push_cast
  calc |v - pEval x y avg / SC| ≤ |v - (Pa + Pb) / 2 / SC| + |(Pa + Pb) / 2 / SC - pEval x y avg / SC| :=
        abs_sub_le _ _ _
    _ ≤ (((a.r : ℝ) + (b.r : ℝ)) / SC + |Pb - Pa| / 2 / SC) + (pCount avg : ℝ) / SC := by
        gcongr
        rw [show (Pa + Pb) / 2 / SC - pEval x y avg / SC = ((Pa + Pb) / 2 - pEval x y avg) / SC by ring,
          abs_div, abs_of_pos hS]
        gcongr
    _ ≤ ((cdiv (pAbs (pAdd b.p (pNeg a.p))) 2 : ℝ) + (a.r : ℝ) + (b.r : ℝ) + (pCount avg : ℝ)) / SC := by
        have h5 : |Pb - Pa| / 2 ≤ (cdiv (pAbs (pAdd b.p (pNeg a.p))) 2 : ℝ) := by
          have : |Pb - Pa| ≤ (pAbs (pAdd b.p (pNeg a.p)) : ℝ) := by
            rw [show Pb - Pa = Pb + -Pa by ring]; exact hd
          push_cast at hc2
          linarith [div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2)]
        have e : ((a.r : ℝ) + (b.r : ℝ)) / SC + |Pb - Pa| / 2 / SC + (pCount avg : ℝ) / SC =
            ((a.r : ℝ) + (b.r : ℝ) + |Pb - Pa| / 2 + (pCount avg : ℝ)) / SC := by ring
        rw [e]
        apply div_le_div_of_nonneg_right _ hS.le
        linarith

theorem encl_shiftP (x y : ℝ) (P : PolI) (d : ℤ) :
    EnclAt x y (pEval x y P / SC + (d : ℝ) / SC) (shiftP P d) := by
  unfold EnclAt shiftP
  rw [pEval_pAdd]
  simp [pEval, rowEval, add_div]

end CKLaneM07.CE

end


