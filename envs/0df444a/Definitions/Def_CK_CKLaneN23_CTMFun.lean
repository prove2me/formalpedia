-- Prove2me | Definitions.Def_CK_CKLaneN23_CTMFun
-- name    : CK_CKLaneN23_CTMFun
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:47:42.978666+00:00
-- url     : https://prove2.me/theorems/44468abf-94da-4ade-8ee6-c7b51a794807
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CTMFun` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CTMFun` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CTMFun` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CTMFun (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CTMFun.lean)

import Definitions.Def_CK_CKLaneN23_CTM

-- ===== source module CKLaneN23.CTMFun =====
section

/-!
# CKLaneN23.CTMFun — functional Taylor-model operations (kernel-evaluable) with soundness

(Adapted from Lane A3's `CKLaneA3.TMFun`.)  A `TMd` is `(P, r, n)`;
`Good f d := Encl f d.P d.r d.n ∧ 0 ≤ d.r`.  Remainders are rounded up to multiples of `2^-40`.
-/

namespace CKLaneN23.CT

structure TMd where
  P : TPoly
  r : ℚ
  n : ℕ

def Good (f : ℝ → ℝ → ℝ → ℝ) (d : TMd) : Prop := Encl f d.P d.r d.n ∧ 0 ≤ d.r

noncomputable def rup (x : ℚ) : ℚ := ((⌈x * 1099511627776⌉ : ℤ) : ℚ) / 1099511627776

theorem le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup
  rw [le_div_iff₀ (by norm_num)]
  exact Int.le_ceil _

noncomputable def entryBounds (P : TPoly) : List ℚ :=
  @List.rec QPoly (fun _ => List ℚ) [] (fun s _ ih => rup (QPoly.absB s) :: ih) P

theorem entryBounds_spec (P : TPoly) : EntryBnd P (entryBounds P) := by
  induction P with
  | nil => exact List.Forall₂.nil
  | cons s P ih =>
    refine List.Forall₂.cons ?_ ih
    intro σ τ hσ hτ
    exact (QPoly.absB_spec hσ hτ log2_lo log2_hi s).trans (by exact_mod_cast le_rup _)

theorem zeroPrefix_zero (P : TPoly) : zeroPrefix P 0 = true := by cases P <;> rfl

theorem HB_nonneg (β γ : List ℚ) (hβ : Nonneg β) (hγ : Nonneg γ) (n : ℕ) : 0 ≤ HB β γ n := by
  induction β generalizing n with
  | nil => show (0 : ℚ) ≤ 0; exact le_refl _
  | cons b β ih =>
    have hb : 0 ≤ b := hβ b List.mem_cons_self
    have hβ' : Nonneg β := fun x hx => hβ x (List.mem_cons_of_mem _ hx)
    cases n with
    | zero =>
      show 0 ≤ bsum (b :: β) * bsum γ
      exact mul_nonneg (bsum_nonneg _ hβ) (bsum_nonneg _ hγ)
    | succ n =>
      show 0 ≤ b * bsum (ldrop γ (n + 1)) + HB β γ n
      exact add_nonneg (mul_nonneg hb (bsum_nonneg _ (ldrop_nonneg _ hγ _))) (ih hβ' n)

noncomputable def mulRem (β γ : List ℚ) (r1 r2 : ℚ) (n1 n2 v1 v2 n : ℕ) : ℚ :=
  HB β γ n + (bsum (ldrop β v1) + r1 * Eps ^ (n1 - v1)) * r2 * Eps ^ (v1 + n2 - n)
    + bsum (ldrop γ v2) * r1 * Eps ^ (v2 + n1 - n)

noncomputable def TMd.mul (a b : TMd) (va vb n : ℕ) : TMd :=
  ⟨TPoly.mulT a.P b.P n, rup (mulRem (entryBounds a.P) (entryBounds b.P) a.r b.r a.n b.n va vb n), n⟩

theorem Eps_nonneg : (0 : ℚ) ≤ Eps := Eps_pos.le

theorem TMd.mul_good {f g : ℝ → ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) (va vb n : ℕ)
    (hza : zeroPrefix a.P va = true) (hzb : zeroPrefix b.P vb = true)
    (hva : va ≤ a.n) (hn1 : n ≤ va + b.n) (hn2 : n ≤ vb + a.n) :
    Good (fun x σ τ => f x σ τ * g x σ τ) (TMd.mul a b va vb n) := by
  have hβ := entryBounds_spec a.P
  have hγ := entryBounds_spec b.P
  refine ⟨?_, ?_⟩
  · exact Encl.mul ha.1 hβ hb.1 hγ hza hzb hva hn1 hn2 ha.2 hb.2 rfl (le_rup _)
  · refine le_trans ?_ (le_rup _)
    unfold mulRem
    have h1 := HB_nonneg _ _ hβ.nonneg hγ.nonneg n
    have h2 := bsum_nonneg _ (ldrop_nonneg _ hβ.nonneg va)
    have h3 := bsum_nonneg _ (ldrop_nonneg _ hγ.nonneg vb)
    have ha2 := ha.2
    have hb2 := hb.2
    have hT := Eps_nonneg
    positivity

noncomputable def TMd.add (a b : TMd) : TMd :=
  ⟨TPoly.add a.P b.P, rup (a.r * Eps ^ (a.n - min a.n b.n) + b.r * Eps ^ (b.n - min a.n b.n)), min a.n b.n⟩

theorem TMd.add_good {f g : ℝ → ℝ → ℝ → ℝ} {a b : TMd} (ha : Good f a) (hb : Good g b) :
    Good (fun x σ τ => f x σ τ + g x σ τ) (TMd.add a b) := by
  have hT := Eps_nonneg
  have h1 : Encl f a.P (a.r * Eps ^ (a.n - min a.n b.n)) (min a.n b.n) :=
    Encl.lower ha.1 (min_le_left _ _) ha.2 (le_refl _)
  have h2 : Encl g b.P (b.r * Eps ^ (b.n - min a.n b.n)) (min a.n b.n) :=
    Encl.lower hb.1 (min_le_right _ _) hb.2 (le_refl _)
  refine ⟨Encl.add h1 h2 rfl (le_rup _), ?_⟩
  refine le_trans ?_ (le_rup _)
  have := ha.2; have := hb.2
  positivity

noncomputable def TMd.scale (c : ℚ) (a : TMd) : TMd := ⟨TPoly.scale c a.P, rup (|c| * a.r), a.n⟩

theorem TMd.scale_good {f : ℝ → ℝ → ℝ → ℝ} {a : TMd} (ha : Good f a) (c : ℚ) :
    Good (fun x σ τ => (c : ℝ) * f x σ τ) (TMd.scale c a) := by
  refine ⟨Encl.scale c ha.1 rfl (le_rup _), ?_⟩
  refine le_trans ?_ (le_rup _)
  have := ha.2
  positivity

/-- scaling by a Laurent constant `c(L)` -/
noncomputable def TMd.scaleL (c : LPoly) (a : TMd) : TMd :=
  ⟨TPoly.mulQ [((0, 0), c)] a.P, rup (LPoly.absB c * a.r), a.n⟩

theorem LPoly.absB_nonneg (c : LPoly) : 0 ≤ LPoly.absB c := by
  unfold LPoly.absB; exact le_max_of_le_left (abs_nonneg _)

theorem TMd.scaleL_good {f : ℝ → ℝ → ℝ → ℝ} {a : TMd} (ha : Good f a) (c : LPoly) :
    Good (fun x σ τ => LPoly.eval (Real.log 2) c * f x σ τ) (TMd.scaleL c a) := by
  refine ⟨?_, le_trans (mul_nonneg (LPoly.absB_nonneg c) ha.2) (le_rup _)⟩
  intro x σ τ hd
  have h1 := ha.1 x σ τ hd
  have hL : Real.log 2 ≠ 0 := by positivity
  have he : ev (TPoly.mulQ [((0, 0), c)] a.P) x σ τ = LPoly.eval (Real.log 2) c * ev a.P x σ τ := by
    unfold ev
    rw [TPoly.eval_mulQ _ _ _ _ hL]
    simp [QPoly.eval_cons, QPoly.eval_nil]
  show |LPoly.eval (Real.log 2) c * f x σ τ - ev (TPoly.mulQ [((0, 0), c)] a.P) x σ τ| ≤ _
  rw [he, ← mul_sub, abs_mul]
  have hc := LPoly.absB_spec log2_lo log2_hi c
  have hr : (0 : ℝ) ≤ a.r := by exact_mod_cast ha.2
  have hup : ((LPoly.absB c * a.r : ℚ) : ℝ) ≤ (rup (LPoly.absB c * a.r) : ℝ) := by exact_mod_cast le_rup _
  push_cast at hup
  calc |LPoly.eval (Real.log 2) c| * |f x σ τ - ev a.P x σ τ|
      ≤ (LPoly.absB c : ℝ) * ((a.r : ℝ) * x ^ a.n) :=
        mul_le_mul hc h1 (abs_nonneg _) (by exact_mod_cast LPoly.absB_nonneg c)
    _ = ((LPoly.absB c : ℝ) * a.r) * x ^ a.n := by ring
    _ ≤ (rup (LPoly.absB c * a.r) : ℝ) * x ^ a.n :=
        mul_le_mul_of_nonneg_right hup (pow_nonneg hd.1.le _)

/-- exact Laurent constant `c` as a TM of order `n` -/
def TMd.const (c : LPoly) (n : ℕ) : TMd := ⟨[[((0, 0), c)]], 0, n⟩

theorem TMd.const_good (c : LPoly) (n : ℕ) :
    Good (fun _ _ _ => LPoly.eval (Real.log 2) c) (TMd.const c n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro x σ τ _
  simp [ev, TMd.const, TPoly.eval_cons, TPoly.eval_nil, QPoly.eval_cons, QPoly.eval_nil]

def TMd.zero (n : ℕ) : TMd := ⟨[], 0, n⟩

theorem TMd.zero_good (n : ℕ) : Good (fun _ _ _ => (0 : ℝ)) (TMd.zero n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro x σ τ _
  simp [ev, TMd.zero, TPoly.eval_nil]

/-- the scale variable `x` itself -/
def TMd.X (n : ℕ) : TMd := ⟨[[], [((0, 0), [(0, 1)])]], 0, n⟩

theorem TMd.X_good (n : ℕ) : Good (fun x _ _ => x) (TMd.X n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro x σ τ _
  simp [ev, TMd.X, TPoly.eval_cons, TPoly.eval_nil, QPoly.eval_cons, QPoly.eval_nil,
    LPoly.eval_cons, LPoly.eval_nil]

/-- the parameter `σ` -/
def TMd.Sg (n : ℕ) : TMd := ⟨[[((1, 0), [(0, 1)])]], 0, n⟩

theorem TMd.Sg_good (n : ℕ) : Good (fun _ σ _ => σ) (TMd.Sg n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro x σ τ _
  simp [ev, TMd.Sg, TPoly.eval_cons, TPoly.eval_nil, QPoly.eval_cons, QPoly.eval_nil,
    LPoly.eval_cons, LPoly.eval_nil]

/-- the parameter `τ` -/
def TMd.Tu (n : ℕ) : TMd := ⟨[[((0, 1), [(0, 1)])]], 0, n⟩

theorem TMd.Tu_good (n : ℕ) : Good (fun _ _ τ => τ) (TMd.Tu n) := by
  refine ⟨Encl.exact n ?_, le_refl _⟩
  intro x σ τ _
  simp [ev, TMd.Tu, TPoly.eval_cons, TPoly.eval_nil, QPoly.eval_cons, QPoly.eval_nil,
    LPoly.eval_cons, LPoly.eval_nil]

/-- weaken the remainder -/
theorem Good.weaken {f : ℝ → ℝ → ℝ → ℝ} {d : TMd} (h : Good f d) {r' : ℚ} (hr : d.r ≤ r') :
    Good f ⟨d.P, r', d.n⟩ := by
  refine ⟨?_, le_trans h.2 hr⟩
  intro x σ τ hd
  have h1 := h.1 x σ τ hd
  have hr' : (d.r : ℝ) ≤ r' := by exact_mod_cast hr
  exact h1.trans (mul_le_mul_of_nonneg_right hr' (pow_nonneg hd.1.le _))

theorem Good.congr {f g : ℝ → ℝ → ℝ → ℝ} {d : TMd} (h : Good f d)
    (hfg : ∀ x σ τ, Dom x σ τ → f x σ τ = g x σ τ) : Good g d :=
  ⟨h.1.congr hfg, h.2⟩

/-! ## Horner evaluation of a Laurent-coefficient polynomial at a TM -/

noncomputable def hornerL (cs : List LPoly) (z : ℝ) : ℝ :=
  @List.rec LPoly (fun _ => ℝ) 0 (fun c _ ih => LPoly.eval (Real.log 2) c + z * ih) cs

theorem hornerL_nil (z : ℝ) : hornerL [] z = 0 := rfl
theorem hornerL_cons (c : LPoly) (cs : List LPoly) (z : ℝ) :
    hornerL (c :: cs) z = LPoly.eval (Real.log 2) c + z * hornerL cs z := rfl

noncomputable def tmHorner (X : TMd) (vx n : ℕ) (cs : List LPoly) : TMd :=
  @List.rec LPoly (fun _ => TMd) (TMd.zero n)
    (fun c _ acc => TMd.add (TMd.const c n) (TMd.mul X acc vx 0 n)) cs

theorem tmHorner_good {x : ℝ → ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n) (cs : List LPoly) :
    Good (fun a σ τ => hornerL cs (x a σ τ)) (tmHorner X vx n cs) ∧ (tmHorner X vx n cs).n = n := by
  induction cs with
  | nil => exact ⟨TMd.zero_good n, rfl⟩
  | cons c cs ih =>
    obtain ⟨hacc, han⟩ := ih
    have hm := TMd.mul_good hx hacc vx 0 n hz (zeroPrefix_zero _) hvx (by omega) (by omega)
    have hadd := TMd.add_good (TMd.const_good c n) hm
    refine ⟨?_, ?_⟩
    · exact hadd
    · show min n n = n
      exact min_self n

/-! ## magnitude of a TM-enclosed function -/

theorem Good.abs_le {x : ℝ → ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) {v : ℕ}
    (hz : zeroPrefix X.P v = true) (hv : v ≤ X.n) {a σ τ : ℝ} (hd : Dom a σ τ) :
    |x a σ τ| ≤ a ^ v * ((bsum (ldrop (entryBounds X.P) v) : ℝ) + X.r * (Eps : ℝ) ^ (X.n - v)) := by
  have ha0 := hd.1.le
  have h1 := hx.1 a σ τ hd
  have hp := (entryBounds_spec X.P).eval_le_val hz ha0 hd.2.1 hd.2.2.1 hd.2.2.2
  have h4 : a ^ X.n ≤ (Eps : ℝ) ^ (X.n - v) * a ^ v := pow_le_E_pow ha0 hd.2.1 hv
  have hr : (0 : ℝ) ≤ X.r := by exact_mod_cast hx.2
  unfold ev at h1
  have h3 : |x a σ τ| ≤ |TPoly.eval a σ τ (Real.log 2) X.P| + X.r * a ^ X.n := by
    have := abs_sub_abs_le_abs_sub (x a σ τ) (TPoly.eval a σ τ (Real.log 2) X.P)
    linarith
  nlinarith [mul_le_mul_of_nonneg_left h4 hr, pow_nonneg ha0 v]

/-- magnitude constant: `|x| ≤ a^v * magC X v` -/
noncomputable def magC (X : TMd) (v : ℕ) : ℚ := bsum (ldrop (entryBounds X.P) v) + X.r * Eps ^ (X.n - v)

theorem magC_nonneg {x : ℝ → ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (v : ℕ) : 0 ≤ magC X v := by
  unfold magC
  have h1 := bsum_nonneg _ (ldrop_nonneg _ (entryBounds_spec X.P).nonneg v)
  have h2 := hx.2
  have h3 := Eps_nonneg
  positivity

/-! ## composition with a series having a power remainder -/

/-- If `|g z - hornerL cs z| ≤ T |z|^m` whenever `|z| ≤ zmax`, and `X` encloses `x` with valuation
`v` (so `|x| ≤ a^v magC`), then `g ∘ x` is enclosed by the Horner TM with remainder increased by
`T magC^m Eps^(v m - n)`. -/
noncomputable def tmCompose (X : TMd) (vx n : ℕ) (cs : List LPoly) (T : ℚ) (m : ℕ) : TMd :=
  let H := tmHorner X vx n cs
  ⟨H.P, rup (H.r + T * magC X vx ^ m * Eps ^ (vx * m - n)), n⟩

theorem tmCompose_good {x : ℝ → ℝ → ℝ → ℝ} {X : TMd} (hx : Good x X) (vx n : ℕ)
    (hz : zeroPrefix X.P vx = true) (hvx : vx ≤ X.n) (hn : n ≤ X.n) (cs : List LPoly)
    {g : ℝ → ℝ} {T zmax : ℚ} {m : ℕ} (hT : 0 ≤ T)
    (hser : ∀ z : ℝ, |z| ≤ zmax → |g z - hornerL cs z| ≤ T * |z| ^ m)
    (hmax : magC X vx * Eps ^ vx ≤ zmax) (hord : n ≤ vx * m) :
    Good (fun a σ τ => g (x a σ τ)) (tmCompose X vx n cs T m) := by
  obtain ⟨hH, hHn⟩ := tmHorner_good hx vx n hz hvx hn cs
  have hM := magC_nonneg hx vx
  refine ⟨?_, ?_⟩
  · intro a σ τ hd
    have ha0 := hd.1.le
    have hxa := hx.abs_le hz hvx hd
    have hsup : |x a σ τ| ≤ (zmax : ℝ) := by
      have h1 : a ^ vx ≤ (Eps : ℝ) ^ vx := pow_le_pow_left₀ ha0 hd.2.1 vx
      have h2 : ((magC X vx : ℚ) : ℝ) * (Eps : ℝ) ^ vx ≤ zmax := by exact_mod_cast hmax
      calc |x a σ τ| ≤ a ^ vx * (magC X vx : ℝ) := by unfold magC; push_cast; linarith [hxa]
        _ ≤ (Eps : ℝ) ^ vx * (magC X vx : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by exact_mod_cast hM)
        _ ≤ zmax := by linarith
    have hs := hser (x a σ τ) hsup
    have hh := hH.1 a σ τ hd
    rw [hHn] at hh
    have hpow : |x a σ τ| ^ m ≤ (a ^ vx * (magC X vx : ℝ)) ^ m := by
      apply pow_le_pow_left₀ (abs_nonneg _)
      unfold magC; push_cast; linarith [hxa]
    have hE : (a ^ vx) ^ m ≤ (Eps : ℝ) ^ (vx * m - n) * a ^ n := by
      rw [← pow_mul]; exact pow_le_E_pow ha0 hd.2.1 hord
    have hT' : (0 : ℝ) ≤ T := by exact_mod_cast hT
    have hM' : (0 : ℝ) ≤ magC X vx := by exact_mod_cast hM
    have htail : |g (x a σ τ) - hornerL cs (x a σ τ)| ≤
        (T : ℝ) * (magC X vx : ℝ) ^ m * (Eps : ℝ) ^ (vx * m - n) * a ^ n := by
      calc |g (x a σ τ) - hornerL cs (x a σ τ)| ≤ T * |x a σ τ| ^ m := hs
        _ ≤ T * (a ^ vx * (magC X vx : ℝ)) ^ m := mul_le_mul_of_nonneg_left hpow hT'
        _ = T * (magC X vx : ℝ) ^ m * (a ^ vx) ^ m := by rw [mul_pow]; ring
        _ ≤ T * (magC X vx : ℝ) ^ m * ((Eps : ℝ) ^ (vx * m - n) * a ^ n) :=
            mul_le_mul_of_nonneg_left hE (by positivity)
        _ = _ := by ring
    have hup : (((tmHorner X vx n cs).r + T * magC X vx ^ m * Eps ^ (vx * m - n) : ℚ) : ℝ) ≤
        (rup ((tmHorner X vx n cs).r + T * magC X vx ^ m * Eps ^ (vx * m - n)) : ℝ) := by
      exact_mod_cast le_rup _
    push_cast at hup
    show |g (x a σ τ) - ev (tmHorner X vx n cs).P a σ τ| ≤ _
    calc |g (x a σ τ) - ev (tmHorner X vx n cs).P a σ τ|
        ≤ |g (x a σ τ) - hornerL cs (x a σ τ)| + |hornerL cs (x a σ τ) - ev (tmHorner X vx n cs).P a σ τ| := by
          have := abs_sub_le (g (x a σ τ)) (hornerL cs (x a σ τ)) (ev (tmHorner X vx n cs).P a σ τ)
          linarith
      _ ≤ T * (magC X vx : ℝ) ^ m * (Eps : ℝ) ^ (vx * m - n) * a ^ n + ((tmHorner X vx n cs).r : ℝ) * a ^ n :=
          add_le_add htail hh
      _ = (((tmHorner X vx n cs).r : ℝ) + T * (magC X vx : ℝ) ^ m * (Eps : ℝ) ^ (vx * m - n)) * a ^ n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hup (pow_nonneg ha0 _)
  · refine le_trans ?_ (le_rup _)
    have := hH.2
    have := Eps_nonneg
    positivity

end CKLaneN23.CT

end


