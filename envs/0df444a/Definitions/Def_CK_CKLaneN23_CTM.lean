-- Prove2me | Definitions.Def_CK_CKLaneN23_CTM
-- name    : CK_CKLaneN23_CTM
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:03:12.454309+00:00
-- url     : https://prove2.me/theorems/99143b76-c2c1-4ab7-ae47-69afa15d41ff
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CTM` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CTM` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CTM` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CTM (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CTM.lean)

import Definitions.Def_CK_CKLaneN23_CBound

-- ===== source module CKLaneN23.CTM =====
section

/-!
# CKLaneN23.CTM — Taylor-model enclosures in the corner scale `x` (adapted from Lane A3)

Domain: `0 < x ≤ Eps`, `|σ| ≤ 1/2`, `|τ| ≤ 1/2`; polynomials evaluated at `L = log 2`.
`Encl f P r n` : `|f x σ τ - P(x, σ, τ, log 2)| ≤ r * x^n` on the domain.
-/

namespace CKLaneN23.CT

def Dom (x σ τ : ℝ) : Prop := 0 < x ∧ x ≤ (Eps : ℝ) ∧ |σ| ≤ 1 / 2 ∧ |τ| ≤ 1 / 2

theorem Eps_pos' : (0 : ℝ) < (Eps : ℝ) := by exact_mod_cast Eps_pos

noncomputable def ev (P : TPoly) (x σ τ : ℝ) : ℝ := TPoly.eval x σ τ (Real.log 2) P

def Encl (f : ℝ → ℝ → ℝ → ℝ) (P : TPoly) (r : ℚ) (n : ℕ) : Prop :=
  ∀ x σ τ, Dom x σ τ → |f x σ τ - ev P x σ τ| ≤ (r : ℝ) * x ^ n

theorem Encl.congr {f g : ℝ → ℝ → ℝ → ℝ} {P : TPoly} {r : ℚ} {n : ℕ}
    (h : Encl f P r n) (hfg : ∀ x σ τ, Dom x σ τ → f x σ τ = g x σ τ) : Encl g P r n := by
  intro x σ τ hd; rw [← hfg x σ τ hd]; exact h x σ τ hd

theorem Encl.exact {f : ℝ → ℝ → ℝ → ℝ} {P : TPoly} (n : ℕ)
    (h : ∀ x σ τ, Dom x σ τ → f x σ τ = ev P x σ τ) : Encl f P 0 n := by
  intro x σ τ hd; rw [h x σ τ hd]; simp

theorem pow_le_E_pow {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (Eps : ℝ)) {a n : ℕ} (han : n ≤ a) :
    x ^ a ≤ (Eps : ℝ) ^ (a - n) * x ^ n := by
  have : x ^ a = x ^ (a - n) * x ^ n := by rw [← pow_add]; congr 1; omega
  rw [this]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx _) (pow_nonneg hx0 _)

theorem Encl.lower {f : ℝ → ℝ → ℝ → ℝ} {P : TPoly} {r r' : ℚ} {n k : ℕ}
    (h : Encl f P r n) (hk : k ≤ n) (hr0 : 0 ≤ r) (hr : r * Eps ^ (n - k) ≤ r') : Encl f P r' k := by
  intro x σ τ hd
  have h1 := h x σ τ hd
  have h2 := pow_le_E_pow hd.1.le hd.2.1 hk
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr' : (r : ℝ) * (Eps : ℝ) ^ (n - k) ≤ r' := by exact_mod_cast hr
  calc |f x σ τ - ev P x σ τ| ≤ r * x ^ n := h1
    _ ≤ r * ((Eps : ℝ) ^ (n - k) * x ^ k) := mul_le_mul_of_nonneg_left h2 hr0'
    _ = (r * (Eps : ℝ) ^ (n - k)) * x ^ k := by ring
    _ ≤ r' * x ^ k := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

theorem Encl.add {f g : ℝ → ℝ → ℝ → ℝ} {P Q R : TPoly} {r s r' : ℚ} {n : ℕ}
    (hf : Encl f P r n) (hg : Encl g Q s n) (hR : TPoly.add P Q = R) (hr : r + s ≤ r') :
    Encl (fun x σ τ => f x σ τ + g x σ τ) R r' n := by
  intro x σ τ hd
  have h1 := hf x σ τ hd; have h2 := hg x σ τ hd
  have he : ev R x σ τ = ev P x σ τ + ev Q x σ τ := by
    rw [← hR]; unfold ev; exact TPoly.eval_add _ _ _ _ _ _
  rw [he]
  have hr' : ((r : ℝ) + s) ≤ r' := by exact_mod_cast hr
  calc |f x σ τ + g x σ τ - (ev P x σ τ + ev Q x σ τ)|
      = |(f x σ τ - ev P x σ τ) + (g x σ τ - ev Q x σ τ)| := by ring_nf
    _ ≤ |f x σ τ - ev P x σ τ| + |g x σ τ - ev Q x σ τ| := abs_add_le _ _
    _ ≤ r * x ^ n + s * x ^ n := add_le_add h1 h2
    _ = ((r : ℝ) + s) * x ^ n := by ring
    _ ≤ r' * x ^ n := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

theorem Encl.scale {f : ℝ → ℝ → ℝ → ℝ} {P R : TPoly} {r r' : ℚ} {n : ℕ} (c : ℚ)
    (hf : Encl f P r n) (hR : TPoly.scale c P = R) (hr : |c| * r ≤ r') :
    Encl (fun x σ τ => (c : ℝ) * f x σ τ) R r' n := by
  intro x σ τ hd
  have h1 := hf x σ τ hd
  have he : ev R x σ τ = (c : ℝ) * ev P x σ τ := by
    rw [← hR]; unfold ev; exact TPoly.eval_scale _ _ _ _ _ _
  rw [he, ← mul_sub, abs_mul]
  have hr' : (|(c : ℝ)| * r) ≤ r' := by exact_mod_cast (by simpa [Rat.cast_abs] using hr)
  calc |(c : ℝ)| * |f x σ τ - ev P x σ τ| ≤ |(c : ℝ)| * (r * x ^ n) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (|(c : ℝ)| * r) * x ^ n := by ring
    _ ≤ r' * x ^ n := mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _)

/-! ## zero prefix (valuation) -/

noncomputable def zeroPrefix (P : TPoly) : ℕ → Bool :=
  @List.rec QPoly (fun _ => ℕ → Bool) (fun _ => true)
    (fun s _ ih => fun k => Nat.rec (motive := fun _ => Bool) true
      (fun k' _ => s.isEmpty && ih k') k) P

theorem zeroPrefix_eval (x σ τ L : ℝ) (P : TPoly) (v : ℕ) (h : zeroPrefix P v = true) :
    TPoly.eval x σ τ L P = x ^ v * TPoly.eval x σ τ L (TPoly.drop P v) := by
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
      rw [TPoly.drop_cons_succ, TPoly.eval_cons, hs, QPoly.eval_nil, ih v h'.2]
      ring

theorem EntryBnd.eval_le_val {P : TPoly} {β : List ℚ} (h : EntryBnd P β) {v : ℕ}
    (hz : zeroPrefix P v = true) {x σ τ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (Eps : ℝ))
    (hσ : |σ| ≤ 1 / 2) (hτ : |τ| ≤ 1 / 2) :
    |TPoly.eval x σ τ (Real.log 2) P| ≤ x ^ v * (bsum (ldrop β v) : ℝ) := by
  rw [zeroPrefix_eval x σ τ _ P v hz, abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
  exact mul_le_mul_of_nonneg_left ((h.drop v).eval_le hx0 hx hσ hτ) (pow_nonneg hx0 _)

/-! ## truncated product soundness -/

theorem scaleSTake_eval (x σ τ L : ℝ) (hL : L ≠ 0) (s : QPoly) (Q : TPoly) (k : ℕ) :
    TPoly.eval x σ τ L (TPoly.scaleSTake s Q k) = QPoly.eval σ τ L s * TPoly.eval x σ τ L (TPoly.take Q k) := by
  induction Q generalizing k with
  | nil =>
    show TPoly.eval x σ τ L [] = _
    simp [TPoly.take_nil, TPoly.eval_nil]
  | cons p Q ih =>
    cases k with
    | zero =>
      show TPoly.eval x σ τ L [] = _
      simp [TPoly.take_zero, TPoly.eval_nil]
    | succ k =>
      show TPoly.eval x σ τ L (QPoly.mul s p :: TPoly.scaleSTake s Q k) = _
      rw [TPoly.eval_cons, ih k, TPoly.take_cons_succ, TPoly.eval_cons, QPoly.eval_mul σ τ L hL]
      ring

noncomputable def HB (β γ : List ℚ) : ℕ → ℚ :=
  @List.rec ℚ (fun _ => ℕ → ℚ) (fun _ => 0)
    (fun b β' ih => fun n => Nat.rec (motive := fun _ => ℚ) (bsum (b :: β') * bsum γ)
      (fun n' _ => b * bsum (ldrop γ (n' + 1)) + ih n') n) β

theorem mulT_nil (Q : TPoly) (n : ℕ) : TPoly.mulT [] Q n = [] := rfl
theorem mulT_cons_zero (s : QPoly) (P Q : TPoly) : TPoly.mulT (s :: P) Q 0 = [] := rfl
theorem mulT_cons_succ (s : QPoly) (P Q : TPoly) (n : ℕ) :
    TPoly.mulT (s :: P) Q (n + 1) = TPoly.add (TPoly.scaleSTake s Q (n + 1)) ([] :: TPoly.mulT P Q n) :=
  rfl

theorem mulT_err {P Q : TPoly} {β γ : List ℚ} (hP : EntryBnd P β) (hQ : EntryBnd Q γ) (n : ℕ)
    {x σ τ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (Eps : ℝ)) (hσ : |σ| ≤ 1 / 2) (hτ : |τ| ≤ 1 / 2) :
    |TPoly.eval x σ τ (Real.log 2) P * TPoly.eval x σ τ (Real.log 2) Q -
      TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n)| ≤ x ^ n * (HB β γ n : ℝ) := by
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
      exact mul_le_mul (hPc.eval_le hx0 hx hσ hτ) (hQ.eval_le hx0 hx hσ hτ)
        (abs_nonneg _) ((abs_nonneg _).trans (hPc.eval_le hx0 hx hσ hτ))
    | succ n =>
      rw [mulT_cons_succ, TPoly.eval_add, scaleSTake_eval _ _ _ _ hL, TPoly.eval_cons,
        TPoly.eval_cons (s := []), QPoly.eval_nil]
      have hsplit := TPoly.eval_take_drop x σ τ (Real.log 2) Q (n + 1)
      have ih' := ih n
      show _ ≤ x ^ (n + 1) * ((b * bsum (ldrop γ (n + 1)) + HB β' γ n : ℚ) : ℝ)
      push_cast
      set p := TPoly.eval x σ τ (Real.log 2) P'
      set q := TPoly.eval x σ τ (Real.log 2) Q
      set qt := TPoly.eval x σ τ (Real.log 2) (TPoly.take Q (n + 1))
      set qd := TPoly.eval x σ τ (Real.log 2) (TPoly.drop Q (n + 1))
      set m := TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P' Q n)
      set sv := QPoly.eval σ τ (Real.log 2) s
      have hkey : (sv + x * p) * q - (sv * qt + (0 + x * m)) = sv * x ^ (n + 1) * qd + x * (p * q - m) := by
        rw [hsplit]; ring
      rw [hkey]
      have h1 : |sv| ≤ b := hsb σ τ hσ hτ
      have h2 : |qd| ≤ bsum (ldrop γ (n + 1)) := (hQ.drop (n + 1)).eval_le hx0 hx hσ hτ
      have hb0 : (0 : ℝ) ≤ b := (abs_nonneg _).trans h1
      calc |sv * x ^ (n + 1) * qd + x * (p * q - m)|
          ≤ |sv * x ^ (n + 1) * qd| + |x * (p * q - m)| := abs_add_le _ _
        _ = |sv| * x ^ (n + 1) * |qd| + x * |p * q - m| := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hx0 _), abs_of_nonneg hx0]
        _ ≤ b * x ^ (n + 1) * bsum (ldrop γ (n + 1)) + x * (x ^ n * HB β' γ n) := by
            apply add_le_add
            · apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (pow_nonneg hx0 _)) h2 (abs_nonneg _)
              exact mul_nonneg hb0 (pow_nonneg hx0 _)
            · exact mul_le_mul_of_nonneg_left ih' hx0
        _ = x ^ (n + 1) * (b * bsum (ldrop γ (n + 1)) + HB β' γ n) := by ring

theorem Encl.mul {f g : ℝ → ℝ → ℝ → ℝ} {P Q R : TPoly} {β γ : List ℚ} {r1 r2 r : ℚ}
    {n1 n2 v1 v2 n : ℕ}
    (hf : Encl f P r1 n1) (bP : EntryBnd P β) (hg : Encl g Q r2 n2) (bQ : EntryBnd Q γ)
    (hz1 : zeroPrefix P v1 = true) (hz2 : zeroPrefix Q v2 = true)
    (hv1 : v1 ≤ n1) (hn1 : n ≤ v1 + n2) (hn2 : n ≤ v2 + n1)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hR : TPoly.mulT P Q n = R)
    (hrem : HB β γ n + (bsum (ldrop β v1) + r1 * Eps ^ (n1 - v1)) * r2 * Eps ^ (v1 + n2 - n)
        + bsum (ldrop γ v2) * r1 * Eps ^ (v2 + n1 - n) ≤ r) :
    Encl (fun x σ τ => f x σ τ * g x σ τ) R r n := by
  intro x σ τ hd
  have hx0 : 0 ≤ x := hd.1.le
  have hx := hd.2.1
  have hσ := hd.2.2.1
  have hτ := hd.2.2.2
  set p := ev P x σ τ
  set q := ev Q x σ τ
  have e1 := hf x σ τ hd
  have e2 := hg x σ τ hd
  have hm := mulT_err bP bQ n hx0 hx hσ hτ
  rw [← hR]
  change |f x σ τ * g x σ τ - TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n)| ≤ _
  have hp : |p| ≤ x ^ v1 * (bsum (ldrop β v1) : ℝ) := bP.eval_le_val hz1 hx0 hx hσ hτ
  have hq : |q| ≤ x ^ v2 * (bsum (ldrop γ v2) : ℝ) := bQ.eval_le_val hz2 hx0 hx hσ hτ
  have hr1' : (0 : ℝ) ≤ r1 := by exact_mod_cast hr1
  have hr2' : (0 : ℝ) ≤ r2 := by exact_mod_cast hr2
  have hB1 : (0 : ℝ) ≤ bsum (ldrop β v1) := by exact_mod_cast bsum_nonneg _ (ldrop_nonneg _ bP.nonneg _)
  have hB2 : (0 : ℝ) ≤ bsum (ldrop γ v2) := by exact_mod_cast bsum_nonneg _ (ldrop_nonneg _ bQ.nonneg _)
  have hf_abs : |f x σ τ| ≤ x ^ v1 * ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1)) := by
    have h3 : |f x σ τ| ≤ |p| + r1 * x ^ n1 := by
      have := abs_sub_abs_le_abs_sub (f x σ τ) p
      linarith
    have h4 : x ^ n1 ≤ (Eps : ℝ) ^ (n1 - v1) * x ^ v1 := pow_le_E_pow hx0 hx hv1
    nlinarith [pow_nonneg hx0 v1, mul_le_mul_of_nonneg_left h4 hr1']
  have hsplit : f x σ τ * g x σ τ - TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n) =
      f x σ τ * (g x σ τ - q) + q * (f x σ τ - p) + (p * q - TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n)) := by
    ring
  rw [hsplit]
  have hA : |f x σ τ * (g x σ τ - q)| ≤ ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1)) * r2 * (Eps : ℝ) ^ (v1 + n2 - n) * x ^ n := by
    rw [abs_mul]
    have h5 : x ^ (v1 + n2) ≤ (Eps : ℝ) ^ (v1 + n2 - n) * x ^ n := pow_le_E_pow hx0 hx hn1
    have hK : (0 : ℝ) ≤ (bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1) := by
      have : (0 : ℝ) ≤ (Eps : ℝ) ^ (n1 - v1) := pow_nonneg Eps_pos'.le _
      positivity
    calc |f x σ τ| * |g x σ τ - q| ≤ (x ^ v1 * ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1))) * (r2 * x ^ n2) :=
          mul_le_mul hf_abs e2 (abs_nonneg _) (by positivity)
      _ = ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1)) * r2 * x ^ (v1 + n2) := by rw [pow_add]; ring
      _ ≤ ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1)) * r2 * ((Eps : ℝ) ^ (v1 + n2 - n) * x ^ n) :=
          mul_le_mul_of_nonneg_left h5 (mul_nonneg hK hr2')
      _ = _ := by ring
  have hB : |q * (f x σ τ - p)| ≤ (bsum (ldrop γ v2) : ℝ) * r1 * (Eps : ℝ) ^ (v2 + n1 - n) * x ^ n := by
    rw [abs_mul]
    have h6 : x ^ (v2 + n1) ≤ (Eps : ℝ) ^ (v2 + n1 - n) * x ^ n := pow_le_E_pow hx0 hx hn2
    calc |q| * |f x σ τ - p| ≤ (x ^ v2 * (bsum (ldrop γ v2) : ℝ)) * (r1 * x ^ n1) :=
          mul_le_mul hq e1 (abs_nonneg _) (by positivity)
      _ = (bsum (ldrop γ v2) : ℝ) * r1 * x ^ (v2 + n1) := by rw [pow_add]; ring
      _ ≤ (bsum (ldrop γ v2) : ℝ) * r1 * ((Eps : ℝ) ^ (v2 + n1 - n) * x ^ n) :=
          mul_le_mul_of_nonneg_left h6 (mul_nonneg hB2 hr1')
      _ = _ := by ring
  have hC : |p * q - TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n)| ≤ x ^ n * (HB β γ n : ℝ) := hm
  have hrem' : (HB β γ n : ℝ) + ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1)) * r2 * (Eps : ℝ) ^ (v1 + n2 - n)
      + (bsum (ldrop γ v2) : ℝ) * r1 * (Eps : ℝ) ^ (v2 + n1 - n) ≤ r := by exact_mod_cast hrem
  calc |f x σ τ * (g x σ τ - q) + q * (f x σ τ - p) + (p * q - TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n))|
      ≤ |f x σ τ * (g x σ τ - q)| + |q * (f x σ τ - p)| + |p * q - TPoly.eval x σ τ (Real.log 2) (TPoly.mulT P Q n)| :=
        abs_add_three _ _ _
    _ ≤ _ + _ + _ := add_le_add (add_le_add hA hB) hC
    _ = ((HB β γ n : ℝ) + ((bsum (ldrop β v1) : ℝ) + r1 * (Eps : ℝ) ^ (n1 - v1)) * r2 * (Eps : ℝ) ^ (v1 + n2 - n)
      + (bsum (ldrop γ v2) : ℝ) * r1 * (Eps : ℝ) ^ (v2 + n1 - n)) * x ^ n := by ring
    _ ≤ r * x ^ n := mul_le_mul_of_nonneg_right hrem' (pow_nonneg hx0 _)

/-! ## division by x, truncation -/

theorem Encl.divx {f : ℝ → ℝ → ℝ → ℝ} {P : TPoly} {r : ℚ} {n : ℕ}
    (hf : Encl f ([] :: P) r (n + 1)) : Encl (fun x σ τ => f x σ τ / x) P r n := by
  intro x σ τ hd
  have h1 := hf x σ τ hd
  have hx := hd.1
  unfold ev at h1 ⊢
  rw [TPoly.eval_cons, QPoly.eval_nil, zero_add] at h1
  have : f x σ τ / x - TPoly.eval x σ τ (Real.log 2) P =
      (f x σ τ - x * TPoly.eval x σ τ (Real.log 2) P) / x := by field_simp
  rw [this, abs_div, abs_of_pos hx, div_le_iff₀ hx]
  calc _ ≤ (r : ℝ) * x ^ (n + 1) := h1
    _ = (r : ℝ) * x ^ n * x := by ring

theorem Encl.trunc {f : ℝ → ℝ → ℝ → ℝ} {P : TPoly} {β : List ℚ} {r r' : ℚ} {n k : ℕ}
    (hf : Encl f P r n) (bP : EntryBnd P β) (hk : k ≤ n) (hr0 : 0 ≤ r)
    (hr : bsum (ldrop β k) + r * Eps ^ (n - k) ≤ r') : Encl f (TPoly.take P k) r' k := by
  intro x σ τ hd
  have h1 := hf x σ τ hd
  have hx0 := hd.1.le
  have hsplit := TPoly.eval_take_drop x σ τ (Real.log 2) P k
  have hd2 := (bP.drop k).eval_le hx0 hd.2.1 hd.2.2.1 hd.2.2.2
  unfold ev at h1 ⊢
  have h2 := pow_le_E_pow hx0 hd.2.1 hk
  have hr0' : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr' : (bsum (ldrop β k) : ℝ) + r * (Eps : ℝ) ^ (n - k) ≤ r' := by exact_mod_cast hr
  calc |f x σ τ - TPoly.eval x σ τ (Real.log 2) (TPoly.take P k)|
      = |(f x σ τ - TPoly.eval x σ τ (Real.log 2) P) +
          x ^ k * TPoly.eval x σ τ (Real.log 2) (TPoly.drop P k)| := by rw [hsplit]; ring_nf
    _ ≤ |f x σ τ - TPoly.eval x σ τ (Real.log 2) P| +
          |x ^ k * TPoly.eval x σ τ (Real.log 2) (TPoly.drop P k)| := abs_add_le _ _
    _ ≤ r * x ^ n + x ^ k * bsum (ldrop β k) := by
        apply add_le_add h1
        rw [abs_mul, abs_of_nonneg (pow_nonneg hx0 _)]
        exact mul_le_mul_of_nonneg_left hd2 (pow_nonneg hx0 _)
    _ ≤ r * ((Eps : ℝ) ^ (n - k) * x ^ k) + x ^ k * bsum (ldrop β k) := by
        exact add_le_add (mul_le_mul_of_nonneg_left h2 hr0') (le_refl _)
    _ = ((bsum (ldrop β k) : ℝ) + r * (Eps : ℝ) ^ (n - k)) * x ^ k := by ring
    _ ≤ r' * x ^ k := mul_le_mul_of_nonneg_right hr' (pow_nonneg hx0 _)

end CKLaneN23.CT

end


