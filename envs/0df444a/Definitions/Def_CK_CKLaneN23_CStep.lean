-- Prove2me | Definitions.Def_CK_CKLaneN23_CStep
-- name    : CK_CKLaneN23_CStep
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T04:40:36.19006+00:00
-- url     : https://prove2.me/theorems/ab5d8821-b686-4197-81bc-227d076b066c
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CStep` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CStep` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CStep` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CStep (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CStep.lean)

import Definitions.Def_CK_CKLaneN23_CSer2

-- ===== source module CKLaneN23.CStep =====
section

/-!
# CKLaneN23.CStep — Boolean-checked Taylor-model steps (Lane N23b)

Every chain step proves `Good f D` for a literal certificate TM `D` from the `Good` facts of its
inputs and ONE Boolean check (`mulChk`, `addChk`, `scaleChk`, `scaleLChk`, `serChk`, `serNChk`,
`tailChk`, `matchChk`).  The corner checker is the conjunction of all step checks, so the only
numerical premise of the final soundness theorem is that conjunction evaluating to `true`.

Also: TM lower/upper bounds on the whole domain (`TPoly.lowB`, `TPoly.upB`) and the sign
consequences `Good.nonneg_of` / `Good.nonpos_of` used for residual checks.
-/

namespace CKLaneN23.CT

theorem Good.of_eq {f : ℝ → ℝ → ℝ → ℝ} {d D : TMd} (h : Good f d) (hP : d.P = D.P) (hn : d.n = D.n)
    (hr : d.r ≤ D.r) : Good f D := by
  have h2 := h.weaken hr
  obtain ⟨P, r, n⟩ := D
  simp only at hP hn
  rw [hP, hn] at h2
  exact h2

/-- structural match of a computed TM against a certificate literal -/
noncomputable def matchChk (d D : TMd) : Bool :=
  decide (d.P = D.P) && decide (d.n = D.n) && decide (d.r ≤ D.r)

theorem Good.of_chk {f : ℝ → ℝ → ℝ → ℝ} {d D : TMd} (h : Good f d) (hc : matchChk d D = true) :
    Good f D := by
  unfold matchChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  exact h.of_eq hc.1.1 hc.1.2 hc.2

/-! ## arithmetic steps -/

noncomputable def mulChk (A B : TMd) (va vb n : ℕ) (D : TMd) : Bool :=
  zeroPrefix A.P va && zeroPrefix B.P vb && decide (va ≤ A.n) && decide (n ≤ va + B.n) &&
    decide (n ≤ vb + A.n) && matchChk (TMd.mul A B va vb n) D

theorem step_mul {f g : ℝ → ℝ → ℝ → ℝ} {A B D : TMd} (hA : Good f A) (hB : Good g B) (va vb n : ℕ)
    (hc : mulChk A B va vb n D = true) : Good (fun x σ τ => f x σ τ * g x σ τ) D := by
  unfold mulChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact (TMd.mul_good hA hB va vb n h1 h2 h3 h4 h5).of_chk h6

noncomputable def addChk (A B D : TMd) : Bool := matchChk (TMd.add A B) D

theorem step_add {f g : ℝ → ℝ → ℝ → ℝ} {A B D : TMd} (hA : Good f A) (hB : Good g B)
    (hc : addChk A B D = true) : Good (fun x σ τ => f x σ τ + g x σ τ) D :=
  (TMd.add_good hA hB).of_chk hc

noncomputable def scaleChk (c : ℚ) (A D : TMd) : Bool := matchChk (TMd.scale c A) D

theorem step_scale {f : ℝ → ℝ → ℝ → ℝ} {A D : TMd} (c : ℚ) (hA : Good f A)
    (hc : scaleChk c A D = true) : Good (fun x σ τ => (c : ℝ) * f x σ τ) D :=
  (TMd.scale_good hA c).of_chk hc

noncomputable def scaleLChk (c : LPoly) (A D : TMd) : Bool := matchChk (TMd.scaleL c A) D

theorem step_scaleL {f : ℝ → ℝ → ℝ → ℝ} {A D : TMd} (c : LPoly) (hA : Good f A)
    (hc : scaleLChk c A D = true) : Good (fun x σ τ => LPoly.eval (Real.log 2) c * f x σ τ) D :=
  (TMd.scaleL_good hA c).of_chk hc

noncomputable def constChk (c : LPoly) (n : ℕ) (D : TMd) : Bool := matchChk (TMd.const c n) D

theorem step_const {D : TMd} (c : LPoly) (n : ℕ) (hc : constChk c n D = true) :
    Good (fun _ _ _ => LPoly.eval (Real.log 2) c) D :=
  (TMd.const_good c n).of_chk hc

/-- an exact polynomial (remainder 0) -/
theorem step_exact {f : ℝ → ℝ → ℝ → ℝ} (P : TPoly) (n : ℕ)
    (h : ∀ x σ τ, Dom x σ τ → f x σ τ = ev P x σ τ) : Good f ⟨P, 0, n⟩ :=
  ⟨Encl.exact n h, le_refl _⟩

/-! ## series steps (Horner + tail, or tail of a given TM) -/

noncomputable def serChk (X : TMd) (vx n : ℕ) (cs : List LPoly) (T zmax : ℚ) (m : ℕ) (D : TMd) : Bool :=
  zeroPrefix X.P vx && decide (vx ≤ X.n) && decide (n ≤ X.n) && decide (0 ≤ T) &&
    decide (magC X vx * Eps ^ vx ≤ zmax) && decide (n ≤ vx * m) &&
    matchChk (tmTail (tmHorner X vx n cs) X vx T m) D

theorem step_ser {x : ℝ → ℝ → ℝ → ℝ} {X D : TMd} {g : ℝ → ℝ} (hx : Good x X) (vx n : ℕ)
    (cs : List LPoly) (T zmax : ℚ) (m : ℕ)
    (hser : ∀ z : ℝ, |z| ≤ zmax → |g z - hornerL cs z| ≤ T * |z| ^ m)
    (hc : serChk X vx n cs T zmax m D = true) : Good (fun a σ τ => g (x a σ τ)) D := by
  unfold serChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  obtain ⟨hH, hHn⟩ := tmHorner_good hx vx n h1 h2 h3 cs
  have ht := tmTail_good (P := hornerL cs) (g := g) hx vx h1 h2 hH h4 hser h5 (by rw [hHn]; exact h6)
  exact ht.of_chk h7

theorem step_ser_nonneg {x : ℝ → ℝ → ℝ → ℝ} {X D : TMd} {g : ℝ → ℝ} (hx : Good x X) (vx n : ℕ)
    (cs : List LPoly) (T zmax : ℚ) (m : ℕ) (hxpos : ∀ a σ τ, Dom a σ τ → 0 ≤ x a σ τ)
    (hser : ∀ z : ℝ, 0 ≤ z → z ≤ zmax → |g z - hornerL cs z| ≤ T * |z| ^ m)
    (hc : serChk X vx n cs T zmax m D = true) : Good (fun a σ τ => g (x a σ τ)) D := by
  unfold serChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hc
  obtain ⟨hH, hHn⟩ := tmHorner_good hx vx n h1 h2 h3 cs
  have ht := tmTail_good_nonneg (P := hornerL cs) (g := g) hx vx h1 h2 hH hxpos h4 hser h5
    (by rw [hHn]; exact h6)
  exact ht.of_chk h7

noncomputable def tailChk (Y X : TMd) (vx : ℕ) (T zmax : ℚ) (m : ℕ) (D : TMd) : Bool :=
  zeroPrefix X.P vx && decide (vx ≤ X.n) && decide (0 ≤ T) && decide (magC X vx * Eps ^ vx ≤ zmax) &&
    decide (Y.n ≤ vx * m) && matchChk (tmTail Y X vx T m) D

theorem step_tail {x : ℝ → ℝ → ℝ → ℝ} {X Y D : TMd} {P g : ℝ → ℝ} (hx : Good x X) (vx : ℕ)
    (hY : Good (fun a σ τ => P (x a σ τ)) Y) (T zmax : ℚ) (m : ℕ)
    (hser : ∀ z : ℝ, |z| ≤ zmax → |g z - P z| ≤ T * |z| ^ m)
    (hc : tailChk Y X vx T zmax m D = true) : Good (fun a σ τ => g (x a σ τ)) D := by
  unfold tailChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact (tmTail_good hx vx h1 h2 hY h3 hser h4 h5).of_chk h6

theorem step_tail_nonneg {x : ℝ → ℝ → ℝ → ℝ} {X Y D : TMd} {P g : ℝ → ℝ} (hx : Good x X) (vx : ℕ)
    (hY : Good (fun a σ τ => P (x a σ τ)) Y) (T zmax : ℚ) (m : ℕ)
    (hxpos : ∀ a σ τ, Dom a σ τ → 0 ≤ x a σ τ)
    (hser : ∀ z : ℝ, 0 ≤ z → z ≤ zmax → |g z - P z| ≤ T * |z| ^ m)
    (hc : tailChk Y X vx T zmax m D = true) : Good (fun a σ τ => g (x a σ τ)) D := by
  unfold tailChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  exact (tmTail_good_nonneg hx vx h1 h2 hY hxpos h3 hser h4 h5).of_chk h6

/-! ## lower / upper bounds on the whole domain -/

noncomputable def QPoly.lowB (s : QPoly) : ℚ :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => ℚ) 0
    (fun m rest _ => if m.1 = (0, 0) then (LPoly.intv m.2).1 - QPoly.absB rest
      else -QPoly.absB (m :: rest)) s

noncomputable def QPoly.upB (s : QPoly) : ℚ :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => ℚ) 0
    (fun m rest _ => if m.1 = (0, 0) then (LPoly.intv m.2).2 + QPoly.absB rest
      else QPoly.absB (m :: rest)) s

theorem QPoly.lowB_spec {σ τ : ℝ} (hσ : |σ| ≤ 1 / 2) (hτ : |τ| ≤ 1 / 2) (s : QPoly) :
    (QPoly.lowB s : ℝ) ≤ QPoly.eval σ τ (Real.log 2) s ∧
      QPoly.eval σ τ (Real.log 2) s ≤ (QPoly.upB s : ℝ) := by
  cases s with
  | nil => simp [QPoly.lowB, QPoly.upB, QPoly.eval_nil]
  | cons m rest =>
    obtain ⟨⟨i, k⟩, l⟩ := m
    have hb := QPoly.absB_spec hσ hτ log2_lo log2_hi rest
    have hb' := abs_le.mp hb
    by_cases hm : (i, k) = (0, 0)
    · simp only [Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      have ha := LPoly.intv_spec log2_lo log2_hi l
      show ((if ((0, 0) : ℕ × ℕ) = (0, 0) then (LPoly.intv l).1 - QPoly.absB rest
          else -QPoly.absB (((0, 0), l) :: rest) : ℚ) : ℝ) ≤ _ ∧
        _ ≤ ((if ((0, 0) : ℕ × ℕ) = (0, 0) then (LPoly.intv l).2 + QPoly.absB rest
          else QPoly.absB (((0, 0), l) :: rest) : ℚ) : ℝ)
      rw [if_pos rfl, if_pos rfl, QPoly.eval_cons]
      simp only [pow_zero, one_mul]
      push_cast
      constructor <;> linarith [ha.1, ha.2, hb'.1, hb'.2]
    · have hc := QPoly.absB_spec hσ hτ log2_lo log2_hi (((i, k), l) :: rest)
      have hc' := abs_le.mp hc
      show ((if (i, k) = (0, 0) then (LPoly.intv l).1 - QPoly.absB rest
          else -QPoly.absB (((i, k), l) :: rest) : ℚ) : ℝ) ≤ _ ∧
        _ ≤ ((if (i, k) = (0, 0) then (LPoly.intv l).2 + QPoly.absB rest
          else QPoly.absB (((i, k), l) :: rest) : ℚ) : ℝ)
      rw [if_neg hm, if_neg hm]
      push_cast
      constructor <;> linarith [hc'.1, hc'.2]

noncomputable def TPoly.lowB (P : TPoly) : ℚ :=
  @List.rec QPoly (fun _ => ℚ) 0 (fun s rest _ => QPoly.lowB s - Eps * bsum (entryBounds rest)) P

noncomputable def TPoly.upB (P : TPoly) : ℚ :=
  @List.rec QPoly (fun _ => ℚ) 0 (fun s rest _ => QPoly.upB s + Eps * bsum (entryBounds rest)) P

theorem TPoly.lowB_spec {x σ τ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (Eps : ℝ)) (hσ : |σ| ≤ 1 / 2)
    (hτ : |τ| ≤ 1 / 2) (P : TPoly) :
    (TPoly.lowB P : ℝ) ≤ TPoly.eval x σ τ (Real.log 2) P ∧
      TPoly.eval x σ τ (Real.log 2) P ≤ (TPoly.upB P : ℝ) := by
  cases P with
  | nil => simp [TPoly.lowB, TPoly.upB, TPoly.eval_nil]
  | cons s rest =>
    show ((QPoly.lowB s - Eps * bsum (entryBounds rest) : ℚ) : ℝ) ≤ _ ∧
      _ ≤ ((QPoly.upB s + Eps * bsum (entryBounds rest) : ℚ) : ℝ)
    rw [TPoly.eval_cons]
    have h1 := QPoly.lowB_spec hσ hτ s
    have h2 := (entryBounds_spec rest).eval_le hx0 hx hσ hτ
    have h3 := abs_le.mp (show |x * TPoly.eval x σ τ (Real.log 2) rest| ≤ (Eps : ℝ) * bsum (entryBounds rest) by
      rw [abs_mul, abs_of_nonneg hx0]
      exact mul_le_mul hx h2 (abs_nonneg _) Eps_pos'.le)
    push_cast
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]

noncomputable def nonnegChk (D : TMd) (k : ℕ) : Bool :=
  zeroPrefix D.P k && decide (k ≤ D.n) && decide (D.r * Eps ^ (D.n - k) ≤ TPoly.lowB (TPoly.drop D.P k))

noncomputable def nonposChk (D : TMd) (k : ℕ) : Bool :=
  zeroPrefix D.P k && decide (k ≤ D.n) && decide (TPoly.upB (TPoly.drop D.P k) + D.r * Eps ^ (D.n - k) ≤ 0)

theorem Good.split_val {f : ℝ → ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (k : ℕ) (hk : k ≤ D.n)
    (hz : zeroPrefix D.P k = true) {x σ τ : ℝ} (hd : Dom x σ τ) :
    |f x σ τ - x ^ k * TPoly.eval x σ τ (Real.log 2) (TPoly.drop D.P k)| ≤
      x ^ k * ((D.r : ℝ) * (Eps : ℝ) ^ (D.n - k)) := by
  have h1 := hf.1 x σ τ hd
  unfold ev at h1
  rw [zeroPrefix_eval x σ τ _ D.P k hz] at h1
  have hx0 := hd.1.le
  have hr : (0 : ℝ) ≤ D.r := by exact_mod_cast hf.2
  have h4 : x ^ D.n ≤ (Eps : ℝ) ^ (D.n - k) * x ^ k := pow_le_E_pow hx0 hd.2.1 hk
  calc |f x σ τ - x ^ k * TPoly.eval x σ τ (Real.log 2) (TPoly.drop D.P k)| ≤ (D.r : ℝ) * x ^ D.n := h1
    _ ≤ (D.r : ℝ) * ((Eps : ℝ) ^ (D.n - k) * x ^ k) := mul_le_mul_of_nonneg_left h4 hr
    _ = x ^ k * ((D.r : ℝ) * (Eps : ℝ) ^ (D.n - k)) := by ring

theorem Good.nonneg_of {f : ℝ → ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (k : ℕ)
    (hc : nonnegChk D k = true) : ∀ x σ τ, Dom x σ τ → 0 ≤ f x σ τ := by
  unfold nonnegChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hz, hk⟩, hlow⟩ := hc
  intro x σ τ hd
  have hs := _root_.abs_le.mp (hf.split_val k hk hz hd)
  have hb := (TPoly.lowB_spec hd.1.le hd.2.1 hd.2.2.1 hd.2.2.2 (TPoly.drop D.P k)).1
  have hlow' : ((D.r * Eps ^ (D.n - k) : ℚ) : ℝ) ≤ (TPoly.lowB (TPoly.drop D.P k) : ℝ) := by
    exact_mod_cast hlow
  push_cast at hlow'
  have hxk : 0 ≤ x ^ k := pow_nonneg hd.1.le _
  have : x ^ k * ((D.r : ℝ) * (Eps : ℝ) ^ (D.n - k)) ≤
      x ^ k * TPoly.eval x σ τ (Real.log 2) (TPoly.drop D.P k) :=
    mul_le_mul_of_nonneg_left (hlow'.trans hb) hxk
  linarith [hs.1]

theorem Good.nonpos_of {f : ℝ → ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (k : ℕ)
    (hc : nonposChk D k = true) : ∀ x σ τ, Dom x σ τ → f x σ τ ≤ 0 := by
  unfold nonposChk at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hz, hk⟩, hup⟩ := hc
  intro x σ τ hd
  have hs := _root_.abs_le.mp (hf.split_val k hk hz hd)
  have hb := (TPoly.lowB_spec hd.1.le hd.2.1 hd.2.2.1 hd.2.2.2 (TPoly.drop D.P k)).2
  have hup' : ((TPoly.upB (TPoly.drop D.P k) + D.r * Eps ^ (D.n - k) : ℚ) : ℝ) ≤ 0 := by
    exact_mod_cast hup
  push_cast at hup'
  have hxk : 0 ≤ x ^ k := pow_nonneg hd.1.le _
  have : x ^ k * (TPoly.eval x σ τ (Real.log 2) (TPoly.drop D.P k) + (D.r : ℝ) * (Eps : ℝ) ^ (D.n - k)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hxk (by linarith)
  nlinarith [hs.2]

end CKLaneN23.CT

end


