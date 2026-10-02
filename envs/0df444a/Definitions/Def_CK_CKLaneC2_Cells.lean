-- Prove2me | Definitions.Def_CK_CKLaneC2_Cells
-- name    : CK_CKLaneC2_Cells
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:52:17.403808+00:00
-- url     : https://prove2.me/theorems/5a194ea4-4fe2-415e-88f3-12b3056412b9
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Cells` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Cells` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Cells` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Cells (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Cells.lean)

import Definitions.Def_CK_CKLaneC2_FIdent

-- ===== source module CKLaneC2.Cells =====
section
/-
Lane C2 — the reflective cell checker for `Wt < 0` and its soundness.

A `Pt` carries a rational contact coordinate `c` and witness data for two certified logarithms
(`Af c`, `Bf c`, via `logChk`).  A cell `[p.c, q.c]` is accepted either by
  * the small-`c` form: the interval evaluation of `Fex` on
    `c ∈ [p.c,q.c]`, `a1 ∈ [a1(p.c)_lo, a1(q.c)_hi]`, `b1 ∈ [b1(p.c)_lo, b1(q.c)_hi]`, `L ∈ [Llo,Lhi]`
    has negative upper end (`a1f`, `b1f` are increasing, and `Wt = c^5 F`), or
  * the nested form: the interval evaluation of `Wex` on
    `c ∈ [p.c,q.c]`, `E ∈ [E(q.c)_lo, E(p.c)_hi]`, `K ∈ [K(p.c)_lo, K(q.c)_hi]`, `A ∈ [A(p.c)_lo, A(q.c)_hi]`
    has negative upper end (`Ef` decreasing, `Kf`, `Af` increasing).
`chainOk`/`coverOk` walk a list of consecutive points; `coverOk_sound` gives `Wt t < 0` on the
whole covered interval.  Everything numerical is decided by `decide +kernel` on `coverOk`.
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

/-- 96-bit dyadic enclosure of `log 2` (keeps all downstream rationals small). -/
def LloD : ℚ := 6864597183463434168892683891 / 9903520314283042199192993792
def LhiD : ℚ := 54916777467707473351141471129 / 79228162514264337593543950336

theorem LloD_le : LloD ≤ Llo := by decide +kernel
theorem Lhi_le : Lhi ≤ LhiD := by decide +kernel

theorem log2_boundsD : (LloD : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (LhiD : ℝ) := by
  have h := log2_bounds
  have h1 : (LloD : ℝ) ≤ (Llo : ℝ) := by exact_mod_cast LloD_le
  have h2 : (Lhi : ℝ) ≤ (LhiD : ℝ) := by exact_mod_cast Lhi_le
  exact ⟨h1.trans h.1, h.2.trans h2⟩

theorem Af_boundsD {c : ℚ} {k n : ℕ} {lo hi : ℚ}
    (h : logChk LloD LhiD ((1 + c) / (1 - c)) k n lo hi = true) :
    (lo : ℝ) ≤ Af c ∧ Af c ≤ (hi : ℝ) := by
  have := logChk_sound log2_boundsD h
  unfold Af
  push_cast at this
  exact this

theorem Bf_boundsD {c : ℚ} {k n : ℕ} {lo hi : ℚ}
    (h : logChk LloD LhiD (1 / (1 - c ^ 2)) k n lo hi = true) :
    (lo : ℝ) ≤ Bf c ∧ Bf c ≤ (hi : ℝ) := by
  have := logChk_sound log2_boundsD h
  unfold Bf
  push_cast at this
  rw [one_div, Real.log_inv] at this
  exact this

structure Pt where
  c : ℚ
  kA : ℕ
  nA : ℕ
  Alo : ℚ
  Ahi : ℚ
  kB : ℕ
  nB : ℕ
  Blo : ℚ
  Bhi : ℚ
deriving Repr

def Pt.ok (p : Pt) : Bool :=
  decide (0 < p.c) && decide (p.c < 1) &&
    logChk LloD LhiD ((1 + p.c) / (1 - p.c)) p.kA p.nA p.Alo p.Ahi &&
    logChk LloD LhiD (1 / (1 - p.c ^ 2)) p.kB p.nB p.Blo p.Bhi

/-- What an accepted point certifies. -/
structure PtFacts (p : Pt) : Prop where
  c_pos : 0 < (p.c : ℝ)
  c_lt : (p.c : ℝ) < 1
  A_lo : (p.Alo : ℝ) ≤ Af p.c
  A_hi : Af p.c ≤ (p.Ahi : ℝ)
  B_lo : (p.Blo : ℝ) ≤ Bf p.c
  B_hi : Bf p.c ≤ (p.Bhi : ℝ)

theorem Pt.ok_sound {p : Pt} (h : p.ok = true) : PtFacts p := by
  simp only [Pt.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hA := Af_boundsD h3
  have hB := Bf_boundsD h4
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, hA.1, hA.2, hB.1, hB.2⟩

def envF (p q : Pt) : List QI :=
  [⟨p.c, q.c⟩, ⟨(p.Alo - 2 * p.c) / p.c ^ 3, (q.Ahi - 2 * q.c) / q.c ^ 3⟩,
   ⟨(p.Blo - p.c ^ 2) / p.c ^ 4, (q.Bhi - q.c ^ 2) / q.c ^ 4⟩, ⟨LloD, LhiD⟩]

def envW (p q : Pt) : List QI :=
  [⟨p.c, q.c⟩, ⟨LloD + q.Blo / 2 - q.c * q.Ahi / 2, LhiD + p.Bhi / 2 - p.c * p.Alo / 2⟩,
   ⟨LloD + p.Blo / 2, LhiD + q.Bhi / 2⟩, ⟨p.Alo, q.Ahi⟩, ⟨LloD, LhiD⟩]

def cellOk (useF : Bool) (p q : Pt) : Bool :=
  decide (p.c ≤ q.c) &&
    (if useF then decide ((Ex.evalI (envF p q) Fex).hi < 0)
     else decide ((Ex.evalI (envW p q) Wex).hi < 0))

theorem envF_mem {p q : Pt} (hp : PtFacts p) (hq : PtFacts q) {t : ℝ}
    (ht1 : (p.c : ℝ) ≤ t) (ht2 : t ≤ (q.c : ℝ)) :
    Ex.EnvMem [t, a1f t, b1f t, Real.log 2] (envF p q) := by
  have ht0 : 0 < t := lt_of_lt_of_le hp.c_pos ht1
  have ht1' : t < 1 := lt_of_le_of_lt ht2 hq.c_lt
  have hp3 : (0 : ℝ) < (p.c : ℝ) ^ 3 := pow_pos hp.c_pos 3
  have hq3 : (0 : ℝ) < (q.c : ℝ) ^ 3 := pow_pos hq.c_pos 3
  have hp4 : (0 : ℝ) < (p.c : ℝ) ^ 4 := pow_pos hp.c_pos 4
  have hq4 : (0 : ℝ) < (q.c : ℝ) ^ 4 := pow_pos hq.c_pos 4
  simp only [envF, Ex.EnvMem, QI.Mem]
  refine ⟨⟨ht1, ht2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, log2_boundsD, trivial⟩
  · calc (((p.Alo - 2 * p.c) / p.c ^ 3 : ℚ) : ℝ) = ((p.Alo : ℝ) - 2 * p.c) / (p.c : ℝ) ^ 3 := by
          push_cast; ring
      _ ≤ (Af p.c - 2 * p.c) / (p.c : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right (by linarith [hp.A_lo]) hp3.le
      _ = a1f p.c := rfl
      _ ≤ a1f t := a1f_mono hp.c_pos ht1 ht1'
  · calc a1f t ≤ a1f q.c := a1f_mono ht0 ht2 hq.c_lt
      _ = (Af q.c - 2 * q.c) / (q.c : ℝ) ^ 3 := rfl
      _ ≤ ((q.Ahi : ℝ) - 2 * q.c) / (q.c : ℝ) ^ 3 :=
          div_le_div_of_nonneg_right (by linarith [hq.A_hi]) hq3.le
      _ = (((q.Ahi - 2 * q.c) / q.c ^ 3 : ℚ) : ℝ) := by push_cast; ring
  · calc (((p.Blo - p.c ^ 2) / p.c ^ 4 : ℚ) : ℝ) = ((p.Blo : ℝ) - (p.c : ℝ) ^ 2) / (p.c : ℝ) ^ 4 := by
          push_cast; ring
      _ ≤ (Bf p.c - (p.c : ℝ) ^ 2) / (p.c : ℝ) ^ 4 :=
          div_le_div_of_nonneg_right (by linarith [hp.B_lo]) hp4.le
      _ = b1f p.c := rfl
      _ ≤ b1f t := b1f_mono hp.c_pos ht1 ht1'
  · calc b1f t ≤ b1f q.c := b1f_mono ht0 ht2 hq.c_lt
      _ = (Bf q.c - (q.c : ℝ) ^ 2) / (q.c : ℝ) ^ 4 := rfl
      _ ≤ ((q.Bhi : ℝ) - (q.c : ℝ) ^ 2) / (q.c : ℝ) ^ 4 :=
          div_le_div_of_nonneg_right (by linarith [hq.B_hi]) hq4.le
      _ = (((q.Bhi - q.c ^ 2) / q.c ^ 4 : ℚ) : ℝ) := by push_cast; ring

theorem envW_mem {p q : Pt} (hp : PtFacts p) (hq : PtFacts q) {t : ℝ}
    (ht1 : (p.c : ℝ) ≤ t) (ht2 : t ≤ (q.c : ℝ)) :
    Ex.EnvMem [t, Ef t, Kf t, Af t, Real.log 2] (envW p q) := by
  have ht0 : 0 < t := lt_of_lt_of_le hp.c_pos ht1
  have ht1' : t < 1 := lt_of_le_of_lt ht2 hq.c_lt
  have hL := log2_boundsD
  simp only [envW, Ex.EnvMem, QI.Mem]
  refine ⟨⟨ht1, ht2⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, log2_boundsD, trivial⟩
  · have h1 : Ef q.c ≤ Ef t := Ef_anti ht0.le ht2 hq.c_lt
    have h2 : (q.c : ℝ) * Af q.c ≤ (q.c : ℝ) * q.Ahi :=
      mul_le_mul_of_nonneg_left hq.A_hi hq.c_pos.le
    have h3 : Ef q.c = Real.log 2 + Bf q.c / 2 - (q.c : ℝ) * Af q.c / 2 := rfl
    push_cast
    linarith [hL.1, hq.B_lo]
  · have h1 : Ef t ≤ Ef p.c := Ef_anti hp.c_pos.le ht1 ht1'
    have h2 : (p.c : ℝ) * p.Alo ≤ (p.c : ℝ) * Af p.c :=
      mul_le_mul_of_nonneg_left hp.A_lo hp.c_pos.le
    have h3 : Ef p.c = Real.log 2 + Bf p.c / 2 - (p.c : ℝ) * Af p.c / 2 := rfl
    push_cast
    linarith [hL.2, hp.B_hi]
  · have h1 : Kf p.c ≤ Kf t := Kf_mono hp.c_pos.le ht1 ht1'
    have h3 : Kf p.c = Real.log 2 + Bf p.c / 2 := rfl
    push_cast
    linarith [hL.1, hp.B_lo]
  · have h1 : Kf t ≤ Kf q.c := Kf_mono ht0.le ht2 hq.c_lt
    have h3 : Kf q.c = Real.log 2 + Bf q.c / 2 := rfl
    push_cast
    linarith [hL.2, hq.B_hi]
  · exact le_trans hp.A_lo (Af_mono (by linarith [hp.c_pos]) ht1 ht1')
  · exact le_trans (Af_mono (by linarith) ht2 hq.c_lt) hq.A_hi

theorem cellF_sound {p q : Pt} (hp : PtFacts p) (hq : PtFacts q)
    (h : (Ex.evalI (envF p q) Fex).hi < 0) :
    ∀ t : ℝ, (p.c : ℝ) ≤ t → t ≤ (q.c : ℝ) → Wt t < 0 := by
  intro t ht1 ht2
  have ht0 : 0 < t := lt_of_lt_of_le hp.c_pos ht1
  have hmem := Ex.evalI_sound (envF_mem hp hq ht1 ht2) Fex
  have h' : ((Ex.evalI (envF p q) Fex).hi : ℝ) < 0 := by exact_mod_cast h
  have hF : Ex.evalR [t, a1f t, b1f t, Real.log 2] Fex < 0 := lt_of_le_of_lt hmem.2 h'
  rw [Wt_eq_F ht0]
  exact mul_neg_of_pos_of_neg (pow_pos ht0 5) hF

theorem cellW_sound {p q : Pt} (hp : PtFacts p) (hq : PtFacts q)
    (h : (Ex.evalI (envW p q) Wex).hi < 0) :
    ∀ t : ℝ, (p.c : ℝ) ≤ t → t ≤ (q.c : ℝ) → Wt t < 0 := by
  intro t ht1 ht2
  have hmem := Ex.evalI_sound (envW_mem hp hq ht1 ht2) Wex
  have h' : ((Ex.evalI (envW p q) Wex).hi : ℝ) < 0 := by exact_mod_cast h
  unfold Wt
  exact lt_of_le_of_lt hmem.2 h'

theorem cellOk_sound {b : Bool} {p q : Pt} (hp : PtFacts p) (hq : PtFacts q)
    (h : cellOk b p q = true) :
    ∀ t : ℝ, (p.c : ℝ) ≤ t → t ≤ (q.c : ℝ) → Wt t < 0 := by
  unfold cellOk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, h2⟩ := h
  cases b with
  | true =>
      simp only [if_true] at h2
      exact cellF_sound hp hq (of_decide_eq_true h2)
  | false =>
      simp only [Bool.false_eq_true, if_false] at h2
      exact cellW_sound hp hq (of_decide_eq_true h2)

def chainOk : Pt → List (Bool × Pt) → Bool
  | _, [] => true
  | p, (b, q) :: rest => q.ok && cellOk b p q && chainOk q rest

def lastC : Pt → List (Bool × Pt) → ℚ
  | p, [] => p.c
  | _, (_, q) :: rest => lastC q rest

theorem chain_sound : ∀ (rest : List (Bool × Pt)) (p q : Pt) (b : Bool),
    PtFacts p → q.ok = true → cellOk b p q = true → chainOk q rest = true →
    ∀ t : ℝ, (p.c : ℝ) ≤ t → t ≤ (lastC q rest : ℝ) → Wt t < 0
  | [], p, q, b, hp, hq, hc, _, t, h1, h2 =>
      cellOk_sound hp (Pt.ok_sound hq) hc t h1 (by simpa [lastC] using h2)
  | (b', r) :: rest, p, q, b, hp, hq, hc, hch, t, h1, h2 => by
      simp only [chainOk, Bool.and_eq_true] at hch
      obtain ⟨⟨hr, hc'⟩, hrest⟩ := hch
      by_cases ht : t ≤ (q.c : ℝ)
      · exact cellOk_sound hp (Pt.ok_sound hq) hc t h1 ht
      · exact chain_sound rest q r b' (Pt.ok_sound hq) hr hc' hrest t
          (le_of_lt (lt_of_not_ge ht)) (by simpa [lastC] using h2)

def coverOk (p : Pt) : List (Bool × Pt) → Bool
  | [] => false
  | (b, q) :: rest => p.ok && q.ok && cellOk b p q && chainOk q rest

theorem coverOk_sound {p : Pt} {l : List (Bool × Pt)} (h : coverOk p l = true) :
    ∀ t : ℝ, (p.c : ℝ) ≤ t → t ≤ (lastC p l : ℝ) → Wt t < 0 := by
  cases l with
  | nil => simp [coverOk] at h
  | cons hd rest =>
      obtain ⟨b, q⟩ := hd
      simp only [coverOk, Bool.and_eq_true] at h
      obtain ⟨⟨⟨hp, hq⟩, hc⟩, hch⟩ := h
      intro t h1 h2
      exact chain_sound rest p q b (Pt.ok_sound hp) hq hc hch t h1 (by simpa [lastC] using h2)

end CKLaneC2

end


