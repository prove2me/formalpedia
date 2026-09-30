-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_TMISound5
-- name    : CK_CKLaneM07_CE_TMISound5
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:59:38.429848+00:00
-- url     : https://prove2.me/theorems/e5166d42-6dd8-4ba7-98b7-add905ec7cf7
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.TMISound5` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.TMISound5` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.TMISound5` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.TMISound5 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/TMISound5.lean)

import Definitions.Def_CK_CKLaneM07_CE_TMISound4

-- ===== source module CKLaneM07.CE.TMISound5 =====
section

/-!
# Lane M07 / CE-stat: soundness of the fixed-point Taylor-model kernel (part 5: log / reciprocal series,
hull, shifted candidates)
-/

set_option autoImplicit false

namespace CKLaneM07.CE

open Finset

/-! ## Rational constants -/

theorem qfl_bounds (q : ℚ) : (q : ℝ) - 1 / SC ≤ ((qfl q : ℤ) : ℝ) / SC ∧ ((qfl q : ℤ) : ℝ) / SC ≤ (q : ℝ) := by
  have hS := SC_pos
  unfold qfl
  have h1 := Int.floor_le (q * (ONE : ℚ))
  have h2 := Int.lt_floor_add_one (q * (ONE : ℚ))
  have c1 : ((⌊q * (ONE : ℚ)⌋ : ℤ) : ℝ) ≤ (q : ℝ) * SC := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; unfold SC; linarith
  have c2 : (q : ℝ) * SC < ((⌊q * (ONE : ℚ)⌋ : ℤ) : ℝ) + 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr h2; push_cast at this; unfold SC; linarith
  constructor
  · rw [le_div_iff₀ hS]; rw [sub_mul, div_mul_cancel₀ _ hS.ne']; linarith
  · rw [div_le_iff₀ hS]; linarith

theorem qcl_ge (q : ℚ) : (q : ℝ) ≤ ((qcl q : ℕ) : ℝ) / SC := by
  have hS := SC_pos
  unfold qcl
  rw [le_div_iff₀ hS]
  have h1 := Int.le_ceil (q * (ONE : ℚ))
  have c1 : (q : ℝ) * SC ≤ ((⌈q * (ONE : ℚ)⌉ : ℤ) : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr h1; push_cast at this; unfold SC; linarith
  have c2 : ((⌈q * (ONE : ℚ)⌉ : ℤ) : ℝ) ≤ (((⌈q * (ONE : ℚ)⌉).toNat : ℕ) : ℝ) := by
    have := Int.self_le_toNat (⌈q * (ONE : ℚ)⌉)
    exact_mod_cast this
  linarith

/-- a rational constant as a Taylor model with one unit of rounding slack -/
theorem EnclAt.qconst (x y : ℝ) (q : ℚ) : EnclAt x y (q : ℝ) (TMI.const (qfl q) 1) := by
  unfold EnclAt TMI.const
  simp only [pEval, rowEval, mul_zero, add_zero, Nat.cast_one]
  obtain ⟨h1, h2⟩ := qfl_bounds q
  rw [abs_le]; constructor <;> linarith

/-- adding a rounded rational constant with one unit of slack encloses the exact sum -/
theorem EnclAt.addQ {x y u : ℝ} {s : TMI} (q : ℚ) (hs : EnclAt x y u s) :
    EnclAt x y (u + q) ⟨(s.addC (qfl q)).p, (s.addC (qfl q)).r + 1⟩ := by
  have h := hs.addC (qfl q)
  unfold EnclAt at *
  obtain ⟨h1, h2⟩ := qfl_bounds q
  push_cast
  calc |u + (q : ℝ) - pEval x y (s.addC (qfl q)).p / SC| =
        |(u + ((qfl q : ℤ) : ℝ) / SC - pEval x y (s.addC (qfl q)).p / SC) + ((q : ℝ) - ((qfl q : ℤ) : ℝ) / SC)| := by
        congr 1; ring
    _ ≤ |u + ((qfl q : ℤ) : ℝ) / SC - pEval x y (s.addC (qfl q)).p / SC| + |(q : ℝ) - ((qfl q : ℤ) : ℝ) / SC| :=
        abs_add_le _ _
    _ ≤ ((s.addC (qfl q)).r : ℝ) / SC + 1 / SC := by
        gcongr
        rw [abs_le]; constructor <;> linarith
    _ = _ := by ring

/-! ## Horner recursions (real models) -/

/-- coefficient of the log series: `(-1)^(k+1)/k` -/
noncomputable def lc (k : ℕ) : ℝ := ((-1 : ℝ) ^ (k + 1)) / (k : ℝ)

noncomputable def logHornerR (w : ℝ) : ℕ → ℝ → ℝ
  | 0, a => a
  | k + 1, a => logHornerR w k (a * w + lc (k + 1))

theorem logHornerR_eq (w : ℝ) : ∀ (k : ℕ) (a : ℝ),
    logHornerR w k a = a * w ^ k + ∑ j ∈ range k, lc (j + 1) * w ^ j
  | 0, a => by simp [logHornerR]
  | k + 1, a => by
      rw [logHornerR, logHornerR_eq w k, sum_range_succ]
      ring

theorem lc_rat (k : ℕ) : lc (k + 1) = (((((-1 : ℚ) ^ (k + 2)) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℝ) := by
  rw [show k + 2 = k + 1 + 1 from rfl]
  simp only [lc, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_one, Rat.cast_natCast]

/-- assembling `log u = log u0 + log (1 + w)` from the series enclosure -/
theorem encl_final {x y L0 L1 S c : ℝ} {res : TMI} {rt rm : ℕ}
    (hR : EnclAt x y (S + c) res) (h1 : |L1 - S| ≤ (rt : ℝ) / SC)
    (h2 : |L0 - c| ≤ ((rm : ℝ) + 1) / SC) :
    EnclAt x y (L0 + L1) ⟨res.p, res.r + rt + rm + 1⟩ := by
  unfold EnclAt at hR ⊢
  have e : L0 + L1 - pEval x y res.p / SC = (S + c - pEval x y res.p / SC) + (L1 - S) + (L0 - c) := by ring
  rw [e]
  push_cast
  calc _ ≤ |S + c - pEval x y res.p / SC| + |L1 - S| + |L0 - c| := abs_add_three _ _ _
    _ ≤ (res.r : ℝ) / SC + (rt : ℝ) / SC + ((rm : ℝ) + 1) / SC := by gcongr
    _ = _ := by ring

theorem encl_logHorner {x y wv : ℝ} {w : TMI} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (K : ℕ)
    (hw : EnclAt x y wv w) : ∀ (k : ℕ) (a : ℝ) (acc : TMI), EnclAt x y a acc →
      EnclAt x y (logHornerR wv k a) (CKLaneM07.CE.logHorner K w k acc)
  | 0, a, acc, h => by simpa [logHornerR, CKLaneM07.CE.logHorner] using h
  | k + 1, a, acc, h => by
      simp only [logHornerR, CKLaneM07.CE.logHorner]
      apply encl_logHorner hx hy K hw k
      have hm := EnclAt.mul hx hy K h hw
      have hq := EnclAt.addQ ((((-1 : ℚ) ^ (k + 2)) / ((k + 1 : ℕ) : ℚ))) hm
      rw [← lc_rat] at hq
      exact hq

/-- the log series value produced by the Horner recursion -/
theorem log_series_eq (w : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    logHornerR w (n - 1) (lc n) * w = -∑ i ∈ range n, (-w) ^ (i + 1) / ((i : ℝ) + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : ∀ i : ℕ, lc (i + 1) * w ^ i * w = -((-w) ^ (i + 1) / ((i : ℝ) + 1)) := by
    intro i; unfold lc; push_cast; rw [neg_pow]; field_simp; ring
  calc logHornerR w m (lc (m + 1)) * w =
        (lc (m + 1) * w ^ m + ∑ j ∈ range m, lc (j + 1) * w ^ j) * w := by rw [logHornerR_eq]
    _ = ∑ i ∈ range (m + 1), lc (i + 1) * w ^ i * w := by
        rw [sum_range_succ, ← sum_mul]; ring
    _ = ∑ i ∈ range (m + 1), -((-w) ^ (i + 1) / ((i : ℝ) + 1)) := sum_congr rfl (fun i _ => key i)
    _ = _ := by rw [sum_neg_distrib]

/-! ## The log Taylor model -/

theorem tail_mono {a ρ : ℝ} (n : ℕ) (ha : 0 ≤ a) (haρ : a ≤ ρ) (hρ : ρ < 1) :
    a ^ (n + 1) / (1 - a) ≤ ρ ^ (n + 1) / (1 - ρ) := by
  have h1 : 0 < 1 - ρ := by linarith
  apply div_le_div₀ (pow_nonneg (ha.trans haρ) _) (pow_le_pow_left₀ ha haρ _) h1 (by linarith)

theorem encl_log {x y u : ℝ} {s t : TMI} {K n : ℕ} {lo hi : ℚ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hs : EnclAt x y u s)
    (hlo : (lo : ℝ) ≤ Real.log (c0R s)) (hhi : Real.log (c0R s) ≤ (hi : ℝ))
    (h : TMI.log K n s lo hi = some t) : 0 < u ∧ EnclAt x y (Real.log u) t := by
  unfold TMI.log at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨h0, hrho, hn⟩ := hc
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
  have hupos : 0 < u := by
    rw [hu]; apply mul_pos hc0; linarith [(abs_lt.mp hwl).1]
  refine ⟨hupos, ?_⟩
  -- Horner enclosure of the series
  have htop : EnclAt x y (lc n) (TMI.const (qfl (((-1 : ℚ) ^ (n + 1)) / (n : ℚ))) 1) := by
    have := EnclAt.qconst x y (((-1 : ℚ) ^ (n + 1)) / (n : ℚ))
    convert this using 1
    unfold lc; push_cast; ring
  have hH := encl_logHorner hx hy K hw (n - 1) (lc n) _ htop
  have hM := EnclAt.mul hx hy K hH hw
  rw [log_series_eq wv n hn] at hM
  have hR := hM.addC (qfl ((lo + hi) / 2))
  set S := -∑ i ∈ range n, (-wv) ^ (i + 1) / ((i : ℝ) + 1)
  -- series tail
  have hser := Real.abs_log_sub_add_sum_range_le (x := -wv) (by rwa [abs_neg]) n
  rw [abs_neg, sub_neg_eq_add] at hser
  have htail : |Real.log (1 + wv) - S| ≤ ρ ^ (n + 1) / (1 - ρ) := by
    have e : Real.log (1 + wv) - S = ∑ i ∈ range n, (-wv) ^ (i + 1) / ((i : ℝ) + 1) + Real.log (1 + wv) := by
      rw [show S = -∑ i ∈ range n, (-wv) ^ (i + 1) / ((i : ℝ) + 1) from rfl]; ring
    rw [e]
    exact hser.trans (tail_mono n (abs_nonneg _) hwb hrhoR)
  have htailq : ρ ^ (n + 1) / (1 - ρ) ≤
      ((qcl ((rhoQ s.wOf.1) ^ (n + 1) / (1 - rhoQ s.wOf.1)) : ℕ) : ℝ) / SC := by
    have := qcl_ge ((rhoQ s.wOf.1) ^ (n + 1) / (1 - rhoQ s.wOf.1))
    push_cast at this
    rw [rhoQ_cast] at this
    exact this
  -- centre constant
  obtain ⟨hm1, hm2⟩ := qfl_bounds ((lo + hi) / 2)
  have hmid : |Real.log (c0R s) - ((qfl ((lo + hi) / 2) : ℤ) : ℝ) / SC| ≤
      ((qcl ((hi - lo) / 2) : ℕ) : ℝ) / SC + 1 / SC := by
    have hq := qcl_ge ((hi - lo) / 2)
    push_cast at hm1 hm2 hq
    rw [abs_le]; constructor <;> linarith
  -- assemble
  have hlog : Real.log u = Real.log (c0R s) + Real.log (1 + wv) := by
    rw [hu, Real.log_mul hc0.ne' (by linarith [(abs_lt.mp hwl).1])]
  rw [hlog]
  have hmid' : |Real.log (c0R s) - ((qfl ((lo + hi) / 2) : ℤ) : ℝ) / SC| ≤
      (((qcl ((hi - lo) / 2) : ℕ) : ℝ) + 1) / SC := hmid.trans_eq (by ring)
  exact encl_final hR (htail.trans htailq) hmid'

end CKLaneM07.CE

end


