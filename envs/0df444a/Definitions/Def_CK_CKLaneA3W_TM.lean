-- Prove2me | Definitions.Def_CK_CKLaneA3W_TM
-- name    : CK_CKLaneA3W_TM
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:19:27.096708+00:00
-- url     : https://prove2.me/theorems/206afe16-45f1-42eb-b98c-4b0b67ea707c
-- title:
--   Courtade–Kumar proof module `CKLaneA3W.TM` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3W.TM` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3W.TM` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3W.TM (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3W/TM.lean)

import Definitions.Def_CK_CKLaneA3W_Bound

/-!
# CKLaneA3W.TM — Taylor-model enclosures in `t` over the high-u domain

Domain: `0 < t ≤ 7/50`, `0 < ρ < 1`; polynomials are evaluated at `σ = ρ - 1/2`, `L = log 2`.
`Encl f P r n` : `|f t ρ - P(t, ρ-1/2, log 2)| ≤ r * t^n` on the domain.
-/

namespace CKLaneA3W

def Dom (t ρ : ℝ) : Prop := 0 < t ∧ t ≤ (Tq : ℝ) ∧ 0 < ρ ∧ ρ < 1

theorem Dom.sigma {t ρ : ℝ} (h : Dom t ρ) : |ρ - 1 / 2| ≤ 1 / 2 := by
  obtain ⟨_, _, h3, h4⟩ := h
  rw [abs_le]; constructor <;> linarith

theorem Tq_pos : (0 : ℝ) < (Tq : ℝ) := by norm_num [Tq]

noncomputable def ev (P : TPoly) (t ρ : ℝ) : ℝ := TPoly.eval t (ρ - 1 / 2) (Real.log 2) P

def Encl (f : ℝ → ℝ → ℝ) (P : TPoly) (r : ℚ) (n : ℕ) : Prop :=
  ∀ t ρ, Dom t ρ → |f t ρ - ev P t ρ| ≤ (r : ℝ) * t ^ n

theorem Encl.congr {f g : ℝ → ℝ → ℝ} {P : TPoly} {r : ℚ} {n : ℕ}
    (h : Encl f P r n) (hfg : ∀ t ρ, Dom t ρ → f t ρ = g t ρ) : Encl g P r n := by
  intro t ρ hd; rw [← hfg t ρ hd]; exact h t ρ hd

theorem Encl.exact {f : ℝ → ℝ → ℝ} {P : TPoly} (n : ℕ)
    (h : ∀ t ρ, Dom t ρ → f t ρ = ev P t ρ) : Encl f P 0 n := by
  intro t ρ hd; rw [h t ρ hd]; simp

theorem Encl.weaken {f : ℝ → ℝ → ℝ} {P : TPoly} {r r' : ℚ} {n : ℕ}
    (h : Encl f P r n) (hr : r ≤ r') : Encl f P r' n := by
  intro t ρ hd
  have ht : 0 ≤ t ^ n := pow_nonneg hd.1.le n
  exact (h t ρ hd).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hr) ht)

theorem pow_le_T_pow {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) {a n : ℕ} (han : n ≤ a) :
    t ^ a ≤ (Tq : ℝ) ^ (a - n) * t ^ n := by
  have : t ^ a = t ^ (a - n) * t ^ n := by rw [← pow_add]; congr 1; omega
  rw [this]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht _) (pow_nonneg ht0 _)

/-- lowering the order -/
theorem Encl.lower {f : ℝ → ℝ → ℝ} {P : TPoly} {r r' : ℚ} {n k : ℕ}
    (h : Encl f P r n) (hk : k ≤ n) (hr0 : 0 ≤ r) (hr : r * Tq ^ (n - k) ≤ r') : Encl f P r' k := by
  intro t ρ hd
  have h1 := h t ρ hd
  have h2 := pow_le_T_pow hd.1.le hd.2.1 hk
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr' : (r : ℝ) * (Tq : ℝ) ^ (n - k) ≤ r' := by exact_mod_cast hr
  calc |f t ρ - ev P t ρ| ≤ r * t ^ n := h1
    _ ≤ r * ((Tq : ℝ) ^ (n - k) * t ^ k) := mul_le_mul_of_nonneg_left h2 hr0'
    _ = (r * (Tq : ℝ) ^ (n - k)) * t ^ k := by ring
    _ ≤ r' * t ^ k := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

theorem Encl.add {f g : ℝ → ℝ → ℝ} {P Q R : TPoly} {r s r' : ℚ} {n : ℕ}
    (hf : Encl f P r n) (hg : Encl g Q s n) (hR : TPoly.add P Q = R) (hr : r + s ≤ r') :
    Encl (fun t ρ => f t ρ + g t ρ) R r' n := by
  intro t ρ hd
  have h1 := hf t ρ hd; have h2 := hg t ρ hd
  have hL : Real.log 2 ≠ 0 := by positivity
  have he : ev R t ρ = ev P t ρ + ev Q t ρ := by
    rw [← hR]; unfold ev; exact TPoly.eval_add _ _ _ hL _ _
  rw [he]
  have hr' : ((r : ℝ) + s) ≤ r' := by exact_mod_cast hr
  calc |f t ρ + g t ρ - (ev P t ρ + ev Q t ρ)|
      = |(f t ρ - ev P t ρ) + (g t ρ - ev Q t ρ)| := by ring_nf
    _ ≤ |f t ρ - ev P t ρ| + |g t ρ - ev Q t ρ| := abs_add_le _ _
    _ ≤ r * t ^ n + s * t ^ n := add_le_add h1 h2
    _ = ((r : ℝ) + s) * t ^ n := by ring
    _ ≤ r' * t ^ n := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

theorem Encl.scale {f : ℝ → ℝ → ℝ} {P R : TPoly} {r r' : ℚ} {n : ℕ} (c : ℚ)
    (hf : Encl f P r n) (hR : TPoly.scale c P = R) (hr : |c| * r ≤ r') :
    Encl (fun t ρ => (c : ℝ) * f t ρ) R r' n := by
  intro t ρ hd
  have h1 := hf t ρ hd
  have he : ev R t ρ = (c : ℝ) * ev P t ρ := by
    rw [← hR]; unfold ev; exact TPoly.eval_scale _ _ _ _ _
  rw [he, ← mul_sub, abs_mul]
  have hr' : (|(c : ℝ)| * r) ≤ r' := by exact_mod_cast (by simpa [Rat.cast_abs] using hr)
  calc |(c : ℝ)| * |f t ρ - ev P t ρ| ≤ |(c : ℝ)| * (r * t ^ n) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (|(c : ℝ)| * r) * t ^ n := by ring
    _ ≤ r' * t ^ n := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

/-! ## zero prefix (valuation) -/

noncomputable def zeroPrefix (P : TPoly) : ℕ → Bool :=
  @List.rec SPoly (fun _ => ℕ → Bool) (fun _ => true)
    (fun s _ ih => fun k => Nat.rec (motive := fun _ => Bool) true
      (fun k' _ => s.isEmpty && ih k') k) P

theorem zeroPrefix_eval (t σ L : ℝ) (P : TPoly) (v : ℕ) (h : zeroPrefix P v = true) :
    TPoly.eval t σ L P = t ^ v * TPoly.eval t σ L (TPoly.drop P v) := by
  induction P generalizing v with
  | nil => simp [TPoly.eval_nil, TPoly.drop_nil]
  | cons s P ih =>
    cases v with
    | zero => simp [TPoly.drop_zero]
    | succ v =>
      have h' : s.isEmpty = true ∧ zeroPrefix P v = true := by
        have : zeroPrefix (s :: P) (v + 1) = (s.isEmpty && zeroPrefix P v) := rfl
        rw [this] at h; simpa using h
      have hs : s = [] := List.isEmpty_iff.mp h'.1
      rw [TPoly.drop_cons_succ, TPoly.eval_cons, hs, SPoly.eval_nil, ih v h'.2]
      ring

/-- magnitude bound with valuation -/
theorem EntryBnd.eval_le_val {P : TPoly} {β : List ℚ} (h : EntryBnd P β) {v : ℕ}
    (hz : zeroPrefix P v = true) {t σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) (hσ : |σ| ≤ 1 / 2) :
    |TPoly.eval t σ (Real.log 2) P| ≤ t ^ v * (bsum (ldrop β v) : ℝ) := by
  rw [zeroPrefix_eval t σ _ P v hz, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
  exact mul_le_mul_of_nonneg_left ((h.drop v).eval_le ht0 ht hσ) (pow_nonneg ht0 _)

/-! ## truncated product soundness -/

theorem scaleSTake_eval (t σ L : ℝ) (hL : L ≠ 0) (s : SPoly) (Q : TPoly) (k : ℕ) :
    TPoly.eval t σ L (TPoly.scaleSTake s Q k) = SPoly.eval σ L s * TPoly.eval t σ L (TPoly.take Q k) := by
  induction Q generalizing k with
  | nil =>
    show TPoly.eval t σ L [] = _
    simp [TPoly.take_nil, TPoly.eval_nil]
  | cons p Q ih =>
    cases k with
    | zero =>
      show TPoly.eval t σ L [] = _
      simp [TPoly.take_zero, TPoly.eval_nil]
    | succ k =>
      show TPoly.eval t σ L (SPoly.mul s p :: TPoly.scaleSTake s Q k) = _
      rw [TPoly.eval_cons, ih k, TPoly.take_cons_succ, TPoly.eval_cons, SPoly.eval_mul σ L hL]
      ring

noncomputable def HB (β γ : List ℚ) : ℕ → ℚ :=
  @List.rec ℚ (fun _ => ℕ → ℚ) (fun _ => 0)
    (fun b β' ih => fun n => Nat.rec (motive := fun _ => ℚ) (bsum (b :: β') * bsum γ)
      (fun n' _ => b * bsum (ldrop γ (n' + 1)) + ih n') n) β

theorem mulT_nil (Q : TPoly) (n : ℕ) : TPoly.mulT [] Q n = [] := rfl
theorem mulT_cons_zero (s : SPoly) (P Q : TPoly) : TPoly.mulT (s :: P) Q 0 = [] := rfl
theorem mulT_cons_succ (s : SPoly) (P Q : TPoly) (n : ℕ) :
    TPoly.mulT (s :: P) Q (n + 1) = TPoly.add (TPoly.scaleSTake s Q (n + 1)) ([] :: TPoly.mulT P Q n) :=
  rfl

theorem mulT_err {P Q : TPoly} {β γ : List ℚ} (hP : EntryBnd P β) (hQ : EntryBnd Q γ) (n : ℕ)
    {t σ : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ (Tq : ℝ)) (hσ : |σ| ≤ 1 / 2) :
    |TPoly.eval t σ (Real.log 2) P * TPoly.eval t σ (Real.log 2) Q -
      TPoly.eval t σ (Real.log 2) (TPoly.mulT P Q n)| ≤ t ^ n * (HB β γ n : ℝ) := by
  have hL : Real.log 2 ≠ 0 := by positivity
  induction hP generalizing n with
  | nil => simp [mulT_nil, TPoly.eval_nil, HB]
  | @cons s b P' β' hsb hrest ih =>
    cases n with
    | zero =>
      rw [mulT_cons_zero, TPoly.eval_nil, sub_zero, pow_zero, one_mul, abs_mul]
      show _ ≤ ((bsum (b :: β') * bsum γ : ℚ) : ℝ)
      push_cast
      have hPc : EntryBnd (s :: P') (b :: β') := List.Forall₂.cons hsb hrest
      exact mul_le_mul (hPc.eval_le ht0 ht hσ) (hQ.eval_le ht0 ht hσ)
        (abs_nonneg _) ((abs_nonneg _).trans (hPc.eval_le ht0 ht hσ))
    | succ n =>
      rw [mulT_cons_succ, TPoly.eval_add _ _ _ hL, scaleSTake_eval _ _ _ hL, TPoly.eval_cons,
        TPoly.eval_cons (s := []), SPoly.eval_nil]
      have hsplit := TPoly.eval_take_drop t σ (Real.log 2) Q (n + 1)
      have ih' := ih n
      show _ ≤ t ^ (n + 1) * ((b * bsum (ldrop γ (n + 1)) + HB β' γ n : ℚ) : ℝ)
      push_cast
      set p := TPoly.eval t σ (Real.log 2) P'
      set q := TPoly.eval t σ (Real.log 2) Q
      set qt := TPoly.eval t σ (Real.log 2) (TPoly.take Q (n + 1))
      set qd := TPoly.eval t σ (Real.log 2) (TPoly.drop Q (n + 1))
      set m := TPoly.eval t σ (Real.log 2) (TPoly.mulT P' Q n)
      set sv := SPoly.eval σ (Real.log 2) s
      have hkey : (sv + t * p) * q - (sv * qt + (0 + t * m)) = sv * t ^ (n + 1) * qd + t * (p * q - m) := by
        rw [hsplit]; ring
      rw [hkey]
      have h1 : |sv| ≤ b := hsb σ hσ
      have h2 : |qd| ≤ bsum (ldrop γ (n + 1)) := (hQ.drop (n + 1)).eval_le ht0 ht hσ
      have hb0 : (0 : ℝ) ≤ b := (abs_nonneg _).trans h1
      calc |sv * t ^ (n + 1) * qd + t * (p * q - m)|
          ≤ |sv * t ^ (n + 1) * qd| + |t * (p * q - m)| := abs_add_le _ _
        _ = |sv| * t ^ (n + 1) * |qd| + t * |p * q - m| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0 _), abs_of_nonneg ht0]
        _ ≤ b * t ^ (n + 1) * bsum (ldrop γ (n + 1)) + t * (t ^ n * HB β' γ n) := by
            apply add_le_add
            · apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (pow_nonneg ht0 _)) h2 (abs_nonneg _)
              exact mul_nonneg hb0 (pow_nonneg ht0 _)
            · exact mul_le_mul_of_nonneg_left ih' ht0
        _ = t ^ (n + 1) * (b * bsum (ldrop γ (n + 1)) + HB β' γ n) := by ring

theorem Encl.mul {f g : ℝ → ℝ → ℝ} {P Q R : TPoly} {β γ : List ℚ} {r1 r2 r : ℚ}
    {n1 n2 v1 v2 n : ℕ}
    (hf : Encl f P r1 n1) (bP : EntryBnd P β) (hg : Encl g Q r2 n2) (bQ : EntryBnd Q γ)
    (hz1 : zeroPrefix P v1 = true) (hz2 : zeroPrefix Q v2 = true)
    (hv1 : v1 ≤ n1) (hn1 : n ≤ v1 + n2) (hn2 : n ≤ v2 + n1)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hR : TPoly.mulT P Q n = R)
    (hrem : HB β γ n + (bsum (ldrop β v1) + r1 * Tq ^ (n1 - v1)) * r2 * Tq ^ (v1 + n2 - n)
        + bsum (ldrop γ v2) * r1 * Tq ^ (v2 + n1 - n) ≤ r) :
    Encl (fun t ρ => f t ρ * g t ρ) R r n := by
  intro t ρ hd
  have ht0 : 0 ≤ t := hd.1.le
  have ht := hd.2.1
  have hσ := hd.sigma
  set p := ev P t ρ
  set q := ev Q t ρ
  have e1 := hf t ρ hd
  have e2 := hg t ρ hd
  have hm := mulT_err bP bQ n ht0 ht hσ
  rw [← hR]
  change |f t ρ * g t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)| ≤ _
  have hp : |p| ≤ t ^ v1 * (bsum (ldrop β v1) : ℝ) := bP.eval_le_val hz1 ht0 ht hσ
  have hq : |q| ≤ t ^ v2 * (bsum (ldrop γ v2) : ℝ) := bQ.eval_le_val hz2 ht0 ht hσ
  have hr1' : (0 : ℝ) ≤ r1 := by exact_mod_cast hr1
  have hr2' : (0 : ℝ) ≤ r2 := by exact_mod_cast hr2
  have hB1 : (0 : ℝ) ≤ bsum (ldrop β v1) := by exact_mod_cast bsum_nonneg _ (ldrop_nonneg _ bP.nonneg _)
  have hB2 : (0 : ℝ) ≤ bsum (ldrop γ v2) := by exact_mod_cast bsum_nonneg _ (ldrop_nonneg _ bQ.nonneg _)
  -- |f| ≤ t^v1 * K1
  have hf_abs : |f t ρ| ≤ t ^ v1 * ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) := by
    have h3 : |f t ρ| ≤ |p| + r1 * t ^ n1 := by
      have := abs_sub_abs_le_abs_sub (f t ρ) p
      linarith
    have h4 : t ^ n1 ≤ (Tq : ℝ) ^ (n1 - v1) * t ^ v1 := pow_le_T_pow ht0 ht hv1
    nlinarith [pow_nonneg ht0 v1, mul_le_mul_of_nonneg_left h4 hr1']
  have hsplit : f t ρ * g t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n) =
      f t ρ * (g t ρ - q) + q * (f t ρ - p) + (p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)) := by
    ring
  rw [hsplit]
  have hA : |f t ρ * (g t ρ - q)| ≤ ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * (Tq : ℝ) ^ (v1 + n2 - n) * t ^ n := by
    rw [abs_mul]
    have h5 : t ^ (v1 + n2) ≤ (Tq : ℝ) ^ (v1 + n2 - n) * t ^ n := pow_le_T_pow ht0 ht hn1
    have hK : (0 : ℝ) ≤ (bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1) := by
      have : (0 : ℝ) ≤ (Tq : ℝ) ^ (n1 - v1) := pow_nonneg Tq_pos.le _
      positivity
    calc |f t ρ| * |g t ρ - q| ≤ (t ^ v1 * ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1))) * (r2 * t ^ n2) :=
          mul_le_mul hf_abs e2 (abs_nonneg _) (by positivity)
      _ = ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * t ^ (v1 + n2) := by rw [pow_add]; ring
      _ ≤ ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * ((Tq : ℝ) ^ (v1 + n2 - n) * t ^ n) :=
          mul_le_mul_of_nonneg_left h5 (mul_nonneg hK hr2')
      _ = _ := by ring
  have hB : |q * (f t ρ - p)| ≤ (bsum (ldrop γ v2) : ℝ) * r1 * (Tq : ℝ) ^ (v2 + n1 - n) * t ^ n := by
    rw [abs_mul]
    have h6 : t ^ (v2 + n1) ≤ (Tq : ℝ) ^ (v2 + n1 - n) * t ^ n := pow_le_T_pow ht0 ht hn2
    calc |q| * |f t ρ - p| ≤ (t ^ v2 * (bsum (ldrop γ v2) : ℝ)) * (r1 * t ^ n1) :=
          mul_le_mul hq e1 (abs_nonneg _) (by positivity)
      _ = (bsum (ldrop γ v2) : ℝ) * r1 * t ^ (v2 + n1) := by rw [pow_add]; ring
      _ ≤ (bsum (ldrop γ v2) : ℝ) * r1 * ((Tq : ℝ) ^ (v2 + n1 - n) * t ^ n) :=
          mul_le_mul_of_nonneg_left h6 (mul_nonneg hB2 hr1')
      _ = _ := by ring
  have hC : |p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)| ≤ t ^ n * (HB β γ n : ℝ) := hm
  have hrem' : (HB β γ n : ℝ) + ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * (Tq : ℝ) ^ (v1 + n2 - n)
      + (bsum (ldrop γ v2) : ℝ) * r1 * (Tq : ℝ) ^ (v2 + n1 - n) ≤ r := by exact_mod_cast hrem
  calc |f t ρ * (g t ρ - q) + q * (f t ρ - p) + (p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n))|
      ≤ |f t ρ * (g t ρ - q)| + |q * (f t ρ - p)| + |p * q - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.mulT P Q n)| :=
        abs_add_three _ _ _
    _ ≤ _ + _ + _ := add_le_add (add_le_add hA hB) hC
    _ = ((HB β γ n : ℝ) + ((bsum (ldrop β v1) : ℝ) + r1 * (Tq : ℝ) ^ (n1 - v1)) * r2 * (Tq : ℝ) ^ (v1 + n2 - n)
      + (bsum (ldrop γ v2) : ℝ) * r1 * (Tq : ℝ) ^ (v2 + n1 - n)) * t ^ n := by ring
    _ ≤ r * t ^ n := mul_le_mul_of_nonneg_right hrem' (pow_nonneg ht0 _)

/-! ## division by t, truncation -/

theorem Encl.divt {f : ℝ → ℝ → ℝ} {P : TPoly} {r : ℚ} {n : ℕ}
    (hf : Encl f ([] :: P) r (n + 1)) : Encl (fun t ρ => f t ρ / t) P r n := by
  intro t ρ hd
  have h1 := hf t ρ hd
  have ht := hd.1
  unfold ev at h1 ⊢
  rw [TPoly.eval_cons, SPoly.eval_nil, zero_add] at h1
  have : f t ρ / t - TPoly.eval t (ρ - 1 / 2) (Real.log 2) P =
      (f t ρ - t * TPoly.eval t (ρ - 1 / 2) (Real.log 2) P) / t := by field_simp
  rw [this, abs_div, abs_of_pos ht, div_le_iff₀ ht]
  calc _ ≤ (r : ℝ) * t ^ (n + 1) := h1
    _ = (r : ℝ) * t ^ n * t := by ring

theorem Encl.trunc {f : ℝ → ℝ → ℝ} {P : TPoly} {β : List ℚ} {r r' : ℚ} {n k : ℕ}
    (hf : Encl f P r n) (bP : EntryBnd P β) (hk : k ≤ n) (hr0 : 0 ≤ r)
    (hr : bsum (ldrop β k) + r * Tq ^ (n - k) ≤ r') : Encl f (TPoly.take P k) r' k := by
  intro t ρ hd
  have h1 := hf t ρ hd
  have ht0 := hd.1.le
  have hsplit := TPoly.eval_take_drop t (ρ - 1 / 2) (Real.log 2) P k
  have hd2 := (bP.drop k).eval_le ht0 hd.2.1 hd.sigma
  unfold ev at h1 ⊢
  have h2 := pow_le_T_pow ht0 hd.2.1 hk
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr' : (bsum (ldrop β k) : ℝ) + r * (Tq : ℝ) ^ (n - k) ≤ r' := by exact_mod_cast hr
  calc |f t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.take P k)|
      = |(f t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) P) +
          t ^ k * TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop P k)| := by rw [hsplit]; ring_nf
    _ ≤ |f t ρ - TPoly.eval t (ρ - 1 / 2) (Real.log 2) P| +
          |t ^ k * TPoly.eval t (ρ - 1 / 2) (Real.log 2) (TPoly.drop P k)| := abs_add_le _ _
    _ ≤ r * t ^ n + t ^ k * bsum (ldrop β k) := by
        apply add_le_add h1
        rw [abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
        exact mul_le_mul_of_nonneg_left hd2 (pow_nonneg ht0 _)
    _ ≤ r * ((Tq : ℝ) ^ (n - k) * t ^ k) + t ^ k * bsum (ldrop β k) := by
        exact add_le_add (mul_le_mul_of_nonneg_left h2 hr0') (le_refl _)
    _ = ((bsum (ldrop β k) : ℝ) + r * (Tq : ℝ) ^ (n - k)) * t ^ k := by ring
    _ ≤ r' * t ^ k := mul_le_mul_of_nonneg_right hr' (pow_nonneg ht0 _)

end CKLaneA3W


