-- Prove2me | Definitions.Def_CK_CKLaneR2_TM3_Fun
-- name    : CK_CKLaneR2_TM3_Fun
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:13:15.932105+00:00
-- url     : https://prove2.me/theorems/20be6ee9-7c45-40ab-8426-05b7542940d7
-- title:
--   Courtade–Kumar proof module `CKLaneR2.TM3.Fun` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneR2.TM3.Fun` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneR2.TM3.Fun` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneR2.TM3.Fun (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneR2/TM3/Fun.lean)

import Definitions.Def_CK_CKLaneR2_TM3_Scalar

-- ===== source module CKLaneR2.TM3.Fun =====
section

/-!
# Lane C: TM3 elementary functions on Taylor models (reciprocal, log, average) and soundness

These are bit-exact mirrors of tm3c.py `recip`, `log` and `average` (tm3 v2).
They extend the Python code with ok-flags: Python raises an exception where Lean sets `ok := false`.
-/

namespace CKLaneR2.TM3

/-! ## Reciprocal -/

noncomputable def recipLoop (one N : ℕ) (w : TM) (j : ℕ) : TM → TM :=
  @Nat.rec (fun _ => TM → TM) (fun S => S) (fun _ ih S => ih (TM.addc (TM.mul one N w S) one)) j

theorem recipLoop_zero (one N : ℕ) (w S : TM) : recipLoop one N w 0 S = S := rfl
theorem recipLoop_succ (one N : ℕ) (w : TM) (j : ℕ) (S : TM) :
    recipLoop one N w (j + 1) S = recipLoop one N w j (TM.addc (TM.mul one N w S) one) := rfl

noncomputable def TM.recip (one N : ℕ) (X : TM) : TM :=
  let kap : Int := ((one * one : ℕ) : Int) / c0P X.p
  let w := TM.neg (TM.addc (TM.mulc one X kap) (-(one : Int)))
  let R := TM.mulc one (recipLoop one N w N (TM.const one 0)) kap
  ⟨R.p, R.r + cdiv (kap.toNat * w.bound ^ (N + 1)) (one ^ N * (one - w.bound)),
    X.ok && R.ok && decide (0 < X.lower) && decide (w.bound * 4 < one * 3)⟩

/-- Horner form of the geometric sum `Σ_{k ≤ j} w^k`. -/
noncomputable def hornerG (w : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => w * hornerG w j + 1

theorem one_sub_mul_hornerG (w : ℝ) (j : ℕ) : (1 - w) * hornerG w j = 1 - w ^ (j + 1) := by
  induction j with
  | zero => simp [hornerG]
  | succ j ih => simp only [hornerG]; rw [pow_succ]; linear_combination w * ih

theorem recipLoop_contains {one : ℕ} (hone : 0 < one) (N : ℕ) {w : TM} {wf : ℝ → ℝ → ℝ → ℝ}
    (hw : Contains one w wf) (j : ℕ) :
    ∀ (S : TM) (m : ℕ), Contains one S (fun x y z => hornerG (wf x y z) m) →
      Contains one (recipLoop one N w j S) (fun x y z => hornerG (wf x y z) (m + j)) := by
  have hne : (one : ℝ) ≠ 0 := by exact_mod_cast hone.ne'
  induction j with
  | zero => intro S m hS; simpa [recipLoop_zero] using hS
  | succ j ih =>
    intro S m hS
    rw [recipLoop_succ]
    have hstep : Contains one (TM.addc (TM.mul one N w S) one) (fun x y z => hornerG (wf x y z) (m + 1)) := by
      have h1 := Contains.addc (Contains.mul hone N hw hS) one
      refine Contains.congr h1 (fun x y z _ _ _ => ?_)
      simp only [hornerG]
      push_cast
      rw [div_self hne]
    have h2 := ih _ (m + 1) hstep
    have e : m + 1 + j = m + (j + 1) := by omega
    rw [e] at h2
    exact h2

theorem Contains.recip {one : ℕ} (hone : 0 < one) (N : ℕ) {X : TM} {f : ℝ → ℝ → ℝ → ℝ}
    (hX : Contains one X f) : Contains one (TM.recip one N X) (fun x y z => (f x y z)⁻¹) := by
  intro hok x y z hx hy hz
  simp only [TM.recip, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨hXok, hRok⟩, hlow⟩, hBw⟩ := hok
  set kap : Int := ((one * one : ℕ) : Int) / c0P X.p with hkap
  set w := TM.neg (TM.addc (TM.mulc one X kap) (-(one : Int))) with hwdef
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hne : (one : ℝ) ≠ 0 := hone'.ne'
  set wf : ℝ → ℝ → ℝ → ℝ := fun x y z => -((kap : ℝ) / one * f x y z + ((-(one : Int) : Int) : ℝ) / one)
    with hwf
  have hw : Contains one w wf := Contains.neg (Contains.addc (Contains.mulc hone hX kap) _)
  have hwok : w.ok = true := by simp [hwdef, TM.neg, TM.addc, TM.mulc, hXok]
  have hS0' : Contains one (TM.const one 0) (fun _ _ _ => (1 : ℝ)) := by
    apply Contains.const; push_cast; rw [div_self hne]; simp
  have hS0 : Contains one (TM.const one 0) (fun x y z => hornerG (wf x y z) 0) :=
    Contains.congr hS0' (fun x y z _ _ _ => by simp [hornerG])
  have hS := recipLoop_contains hone N hw N _ 0 hS0
  simp only [Nat.zero_add] at hS
  have hR := Contains.mulc hone hS kap
  -- values at the point
  have hf : 0 < f x y z := by
    have := Contains.lower_le hone hX hXok x y z hx hy hz
    have h0 : (0 : ℝ) < (X.lower : ℝ) / one := div_pos (by exact_mod_cast hlow) hone'
    linarith
  set wv := wf x y z with hwv
  have hwv' : wv = 1 - (kap : ℝ) / one * f x y z := by
    rw [hwv, hwf]; push_cast; rw [neg_div, div_self hne]; ring
  have hwb : |wv| ≤ (w.bound : ℝ) / one := Contains.abs_le_bound hone hw hwok x y z hx hy hz
  have hBw' : (w.bound : ℝ) / one < 3 / 4 := by
    rw [div_lt_iff₀ hone']; have : (w.bound : ℝ) * 4 < one * 3 := by exact_mod_cast hBw
    linarith
  have hwlt : |wv| < 3 / 4 := lt_of_le_of_lt hwb hBw'
  have hkf : 0 < (kap : ℝ) / one * f x y z := by
    have := (abs_lt.mp hwlt).2
    rw [hwv'] at this; linarith
  have hk1 : 0 < (kap : ℝ) / one := by
    by_contra hcon; push_neg at hcon
    nlinarith
  have hkap_pos : 0 < (kap : ℝ) := by
    have e : (kap : ℝ) = (kap : ℝ) / one * one := by field_simp
    rw [e]; exact mul_pos hk1 hone'
  have hkapi : 0 < kap := by exact_mod_cast hkap_pos
  -- truncated geometric series
  have hRx := hR hRok x y z hx hy hz
  have hgeo := one_sub_mul_hornerG wv N
  have h1w : 0 < 1 - wv := by linarith [(abs_lt.mp hwlt).2]
  have hfinv : (f x y z)⁻¹ = (kap : ℝ) / one / (1 - wv) := by
    rw [hwv', show (1 : ℝ) - (1 - (kap : ℝ) / one * f x y z) = (kap : ℝ) / one * f x y z by ring]
    field_simp
  have hH : hornerG wv N = (1 - wv ^ (N + 1)) / (1 - wv) := by
    rw [eq_div_iff h1w.ne']; linarith [hgeo]
  have htail_eq : (f x y z)⁻¹ - (kap : ℝ) / one * hornerG wv N
      = (kap : ℝ) / one * (wv ^ (N + 1) / (1 - wv)) := by
    rw [hfinv, hH]; ring
  -- tail bound
  have hBw1 : (w.bound : ℝ) < one := (div_lt_one hone').mp (by linarith)
  have hBwN : w.bound < one := by exact_mod_cast hBw1
  have hpos' : 0 < (1 : ℝ) - (w.bound : ℝ) / one := by
    rw [sub_pos, div_lt_one hone']; exact hBw1
  have hden' : (1 : ℝ) - (w.bound : ℝ) / one ≤ 1 - wv := by linarith [(abs_le.mp hwb).2]
  have hkt : ((kap.toNat : ℕ) : ℝ) = (kap : ℝ) := by
    have := Int.toNat_of_nonneg hkapi.le; exact_mod_cast this
  have hsub : ((one - w.bound : ℕ) : ℝ) = (one : ℝ) - w.bound := by rw [Nat.cast_sub hBwN.le]
  have htail_le : |(kap : ℝ) / one * (wv ^ (N + 1) / (1 - wv))|
      ≤ ((kap.toNat * w.bound ^ (N + 1) : ℕ) : ℝ) / ((one ^ N * (one - w.bound) : ℕ) : ℝ) / one := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, hkt, hsub]
    rw [abs_mul, abs_of_pos (div_pos hkap_pos hone'), abs_div, abs_pow, abs_of_pos h1w]
    have hc0 : (0 : ℝ) ≤ ((w.bound : ℝ) / one) ^ (N + 1) := by positivity
    calc (kap : ℝ) / one * (|wv| ^ (N + 1) / (1 - wv))
        ≤ (kap : ℝ) / one * (((w.bound : ℝ) / one) ^ (N + 1) / (1 - (w.bound : ℝ) / one)) := by
          apply mul_le_mul_of_nonneg_left _ (div_pos hkap_pos hone').le
          calc |wv| ^ (N + 1) / (1 - wv) ≤ ((w.bound : ℝ) / one) ^ (N + 1) / (1 - wv) :=
                div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hwb _) h1w.le
            _ ≤ ((w.bound : ℝ) / one) ^ (N + 1) / (1 - (w.bound : ℝ) / one) :=
                div_le_div_of_nonneg_left hc0 hpos' hden'
      _ = (kap : ℝ) * (w.bound : ℝ) ^ (N + 1) / ((one : ℝ) ^ N * ((one : ℝ) - w.bound)) / one :=
          tail_id2 (one : ℝ) (w.bound : ℝ) (kap : ℝ) hone' hBw1 N
  have hden_pos : 0 < one ^ N * (one - w.bound) := Nat.mul_pos (pow_pos hone _) (by omega)
  have hcd := le_cdiv (kap.toNat * w.bound ^ (N + 1)) (one ^ N * (one - w.bound)) hden_pos
  have e : (f x y z)⁻¹ - evalP 0 (TM.mulc one (recipLoop one N w N (TM.const one 0)) kap).p x y z / one
      = ((f x y z)⁻¹ - (kap : ℝ) / one * hornerG wv N)
        + ((kap : ℝ) / one * hornerG wv N
          - evalP 0 (TM.mulc one (recipLoop one N w N (TM.const one 0)) kap).p x y z / one) := by ring
  rw [e, htail_eq]
  push_cast
  calc _ ≤ |(kap : ℝ) / one * (wv ^ (N + 1) / (1 - wv))|
        + |(kap : ℝ) / one * hornerG wv N
          - evalP 0 (TM.mulc one (recipLoop one N w N (TM.const one 0)) kap).p x y z / one| := abs_add_le _ _
    _ ≤ ((kap.toNat * w.bound ^ (N + 1) : ℕ) : ℝ) / ((one ^ N * (one - w.bound) : ℕ) : ℝ) / one
        + ((TM.mulc one (recipLoop one N w N (TM.const one 0)) kap).r : ℝ) / one := add_le_add htail_le hRx
    _ ≤ (cdiv (kap.toNat * w.bound ^ (N + 1)) (one ^ N * (one - w.bound)) : ℝ) / one
        + ((TM.mulc one (recipLoop one N w N (TM.const one 0)) kap).r : ℝ) / one := by
        gcongr
    _ = _ := by ring

/-! ## Log -/

noncomputable def sgI (k : ℕ) : Int := if k % 2 = 1 then 1 else -1

noncomputable def sgR (k : ℕ) : ℝ := if k % 2 = 1 then 1 else -1

theorem sgR_eq (k : ℕ) : sgR k = ((sgI k : ℤ) : ℝ) := by unfold sgR sgI; split_ifs <;> simp

theorem abs_sgI (k : ℕ) : |((sgI k : ℤ) : ℝ)| = 1 := by unfold sgI; split_ifs <;> simp

/-- The rounded series constant `sgI k * (one / k)` is within one unit of `sgR k / k`. -/
theorem const_err (one k : ℕ) (hone : 0 < one) (hk : 0 < k) :
    |sgR k / k - ((sgI k * ((one : ℤ) / (k : ℤ)) : ℤ) : ℝ) / one| ≤ 1 / one := by
  have hq := ediv_err (one : ℤ) (k : ℤ) (by exact_mod_cast hk)
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hne : (one : ℝ) ≠ 0 := hone'.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [sgR_eq]
  have e : ((sgI k : ℤ) : ℝ) / k - ((sgI k * ((one : ℤ) / (k : ℤ)) : ℤ) : ℝ) / one
      = -((sgI k : ℤ) : ℝ) / one * ((((one : ℤ) / (k : ℤ) : ℤ) : ℝ) - ((one : ℤ) : ℝ) / ((k : ℤ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [e, abs_mul, abs_div, abs_neg, abs_sgI, abs_of_pos hone']
  calc 1 / (one : ℝ) * |(((one : ℤ) / (k : ℤ) : ℤ) : ℝ) - ((one : ℤ) : ℝ) / ((k : ℤ) : ℝ)| ≤ 1 / one * 1 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 1 / one := mul_one _

noncomputable def logStep (one N : ℕ) (w : TM) (k : ℕ) (S : TM) : TM :=
  ⟨(TM.addc (TM.mul one N w S) (sgI k * ((one : Int) / (k : Int)))).p, (TM.mul one N w S).r + 1,
    (TM.mul one N w S).ok⟩

noncomputable def logLoop (one N : ℕ) (w : TM) (j : ℕ) : TM → TM :=
  @Nat.rec (fun _ => TM → TM) (fun S => S) (fun k ih S => ih (logStep one N w (k + 1) S)) j

theorem logLoop_zero (one N : ℕ) (w S : TM) : logLoop one N w 0 S = S := rfl
theorem logLoop_succ (one N : ℕ) (w : TM) (j : ℕ) (S : TM) :
    logLoop one N w (j + 1) S = logLoop one N w j (logStep one N w (j + 1) S) := rfl

noncomputable def TM.log (P N : ℕ) (X : TM) : TM :=
  let one := 2 ^ P
  let kap : Int := ((one * one : ℕ) : Int) / c0P X.p
  let w := TM.addc (TM.mulc one X kap) (-(one : Int))
  let S := TM.mul one N w (logLoop one N w (N - 1) (TM.const (sgI N * ((one : Int) / (N : Int))) 1))
  let R := TM.addc S (-(logScalar P kap.toNat).1)
  ⟨R.p, R.r + cdiv (w.bound ^ (N + 1)) (one ^ (N - 1) * (one - w.bound)) + (logScalar P kap.toNat).2,
    X.ok && R.ok && decide (0 < X.lower) && decide (w.bound * 4 < one * 3)
      && decide (2 * (logScalarEY P kap.toNat).2.natAbs ≤ one) && decide (1 ≤ N)⟩

/-- Real mirror of `logLoop`. -/
noncomputable def rLoop (w : ℝ) : ℕ → ℝ → ℝ
  | 0, v => v
  | k + 1, v => rLoop w k (w * v + sgR (k + 1) / ((k : ℝ) + 1))

theorem rLoop_eq (w : ℝ) (j : ℕ) (v : ℝ) :
    rLoop w j v = w ^ j * v + ∑ k ∈ Finset.range j, sgR (k + 1) / ((k : ℝ) + 1) * w ^ k := by
  induction j generalizing v with
  | zero => simp [rLoop]
  | succ j ih =>
    simp only [rLoop]; rw [ih, Finset.sum_range_succ]; ring

theorem w_mul_rLoop (w : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    w * rLoop w (N - 1) (sgR N / N) = l1pSum w N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [show M + 1 - 1 = M by omega, rLoop_eq]
  unfold l1pSum
  rw [Finset.sum_range_succ]
  have hs : ∀ k : ℕ, sgR (k + 1) = (-1 : ℝ) ^ k := by
    intro k; unfold sgR; rw [neg_one_pow_eq_sg k]
  have h1 : ∑ k ∈ Finset.range M, w * (sgR (k + 1) / ((k : ℝ) + 1) * w ^ k)
      = ∑ x ∈ Finset.range M, (-1 : ℝ) ^ x * w ^ (x + 1) / ((x : ℝ) + 1) :=
    Finset.sum_congr rfl (fun k _ => by rw [hs]; ring)
  have h2 : w * (w ^ M * (sgR (M + 1) / ((M + 1 : ℕ) : ℝ))) = (-1 : ℝ) ^ M * w ^ (M + 1) / ((M : ℝ) + 1) := by
    rw [hs]; push_cast; ring
  rw [mul_add, Finset.mul_sum, h1, h2]; ring

theorem logLoop_contains {one : ℕ} (hone : 0 < one) (N : ℕ) {w : TM} {wf : ℝ → ℝ → ℝ → ℝ}
    (hw : Contains one w wf) (j : ℕ) :
    ∀ (S : TM) (v : ℝ → ℝ → ℝ → ℝ), Contains one S v →
      Contains one (logLoop one N w j S) (fun x y z => rLoop (wf x y z) j (v x y z)) := by
  induction j with
  | zero => intro S v hS; simpa [logLoop_zero, rLoop] using hS
  | succ j ih =>
    intro S v hS
    rw [logLoop_succ]
    have hstep : Contains one (logStep one N w (j + 1) S)
        (fun x y z => wf x y z * v x y z + sgR (j + 1) / ((j : ℝ) + 1)) := by
      intro hok x y z hx hy hz
      have hM := Contains.mul hone N hw hS
      have h1 := Contains.addc hM (sgI (j + 1) * ((one : Int) / ((j + 1 : ℕ) : Int))) hok x y z hx hy hz
      have hc := const_err one (j + 1) hone (Nat.succ_pos j)
      simp only [logStep, TM.addc] at h1 ⊢
      set c : ℤ := sgI (j + 1) * ((one : Int) / ((j + 1 : ℕ) : Int)) with hcdef
      set E := evalP 0 (addP (TM.mul one N w S).p [[[c]]]) x y z
      have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hc
      have e : wf x y z * v x y z + sgR (j + 1) / ((j : ℝ) + 1) - E / one
          = (wf x y z * v x y z + (c : ℝ) / one - E / one) + (sgR (j + 1) / ((j : ℝ) + 1) - (c : ℝ) / one) := by
        ring
      rw [e]
      push_cast
      calc _ ≤ |wf x y z * v x y z + (c : ℝ) / one - E / one| + |sgR (j + 1) / ((j : ℝ) + 1) - (c : ℝ) / one| :=
            abs_add_le _ _
        _ ≤ ((TM.mul one N w S).r : ℝ) / one + 1 / one := add_le_add h1 hc
        _ = (((TM.mul one N w S).r : ℝ) + 1) / one := by ring
    have h2 := ih _ _ hstep
    refine Contains.congr h2 (fun x y z _ _ _ => ?_)
    simp only [rLoop]

theorem Contains.log (P : ℕ) (hP : 3 ≤ P) (N : ℕ) {X : TM} {f : ℝ → ℝ → ℝ → ℝ}
    (hX : Contains (2 ^ P) X f) :
    Contains (2 ^ P) (TM.log P N X) (fun x y z => Real.log (f x y z)) := by
  intro hok x y z hx hy hz
  simp only [TM.log, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨⟨⟨hXok, hRok⟩, hlow⟩, hBw⟩, hys⟩, hN⟩ := hok
  have hone : 0 < 2 ^ P := pow_pos (by norm_num) _
  set one := 2 ^ P with hone_def
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  have hne : (one : ℝ) ≠ 0 := hone'.ne'
  set kap : Int := ((one * one : ℕ) : Int) / c0P X.p with hkap
  set w := TM.addc (TM.mulc one X kap) (-(one : Int)) with hwdef
  set wf : ℝ → ℝ → ℝ → ℝ := fun x y z => (kap : ℝ) / one * f x y z + ((-(one : Int) : Int) : ℝ) / one
    with hwf
  have hw : Contains one w wf := Contains.addc (Contains.mulc hone hX kap) _
  have hwok : w.ok = true := by simp [hwdef, TM.addc, TM.mulc, hXok]
  have hS0 : Contains one (TM.const (sgI N * ((one : Int) / (N : Int))) 1) (fun _ _ _ => sgR N / N) := by
    apply Contains.const
    have := const_err one N hone hN
    push_cast at this ⊢
    exact this
  have hL := logLoop_contains hone N hw (N - 1) _ _ hS0
  have hS := Contains.mul hone N hw hL
  set Sm := TM.mul one N w (logLoop one N w (N - 1) (TM.const (sgI N * ((one : Int) / (N : Int))) 1))
    with hSm
  -- point values
  have hf : 0 < f x y z := by
    have := Contains.lower_le hone hX hXok x y z hx hy hz
    have h0 : (0 : ℝ) < (X.lower : ℝ) / one := div_pos (by exact_mod_cast hlow) hone'
    linarith
  set wv := wf x y z with hwv
  have hwv' : wv = (kap : ℝ) / one * f x y z - 1 := by
    rw [hwv, hwf]; push_cast; rw [neg_div, div_self hne]; ring
  have hwb : |wv| ≤ (w.bound : ℝ) / one := Contains.abs_le_bound hone hw hwok x y z hx hy hz
  have hBw' : (w.bound : ℝ) / one < 3 / 4 := by
    rw [div_lt_iff₀ hone']; have : (w.bound : ℝ) * 4 < one * 3 := by exact_mod_cast hBw
    linarith
  have hwlt : |wv| < 3 / 4 := lt_of_le_of_lt hwb hBw'
  have hkf : 0 < (kap : ℝ) / one * f x y z := by
    have := (abs_lt.mp hwlt).1
    rw [hwv'] at this; linarith
  have hk1 : 0 < (kap : ℝ) / one := by
    by_contra hcon; push_neg at hcon
    nlinarith
  have hkap_pos : 0 < (kap : ℝ) := by
    have e : (kap : ℝ) = (kap : ℝ) / one * one := by field_simp
    rw [e]; exact mul_pos hk1 hone'
  have hkapi : 0 < kap := by exact_mod_cast hkap_pos
  have hkt : ((kap.toNat : ℕ) : ℝ) = (kap : ℝ) := by
    have := Int.toNat_of_nonneg hkapi.le; exact_mod_cast this
  have hktpos : 0 < kap.toNat := by omega
  -- scalar log of kap
  have hls := logScalar_sound P hP kap.toNat hktpos hys
  have hcast1 : (((2 ^ P : ℕ) : ℝ)) = (2 : ℝ) ^ P := by push_cast; rfl
  have hls' : |((logScalar P kap.toNat).1 : ℝ) / one - Real.log ((kap : ℝ) / one)|
      ≤ ((logScalar P kap.toNat).2 : ℝ) / one := by
    rw [hkt, ← hcast1] at hls
    have e : ((logScalar P kap.toNat).1 : ℝ) / one - Real.log ((kap : ℝ) / one)
        = (((logScalar P kap.toNat).1 : ℝ) - one * Real.log ((kap : ℝ) / one)) / one := by
      field_simp
    rw [e, abs_div, abs_of_pos hone']
    exact div_le_div_of_nonneg_right hls hone'.le
  -- log f = log(1 + w) - log(kap/one)
  have hlogf : Real.log (f x y z) = Real.log (1 + wv) - Real.log ((kap : ℝ) / one) := by
    rw [hwv', show 1 + ((kap : ℝ) / one * f x y z - 1) = (kap : ℝ) / one * f x y z by ring,
      Real.log_mul hk1.ne' hf.ne']
    ring
  have hser := abs_log_one_add_sub_l1pSum (by linarith [hwlt] : |wv| < 1) N
  have hSok : Sm.ok = true := by simpa [TM.addc, hSm] using hRok
  have hSx := hS hSok x y z hx hy hz
  simp only at hSx
  rw [← hwv, w_mul_rLoop wv N hN] at hSx
  -- tail bound
  have hBw1 : (w.bound : ℝ) < one := (div_lt_one hone').mp (by linarith)
  have hBwN : w.bound < one := by exact_mod_cast hBw1
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hden_pos : 0 < one ^ (N - 1) * (one - w.bound) := Nat.mul_pos (pow_pos hone _) (by omega)
  have hcd := le_cdiv (w.bound ^ (N + 1)) (one ^ (N - 1) * (one - w.bound)) hden_pos
  have hpos' : 0 < (1 : ℝ) - (w.bound : ℝ) / one := by
    rw [sub_pos, div_lt_one hone']; exact hBw1
  have hden' : (1 : ℝ) - (w.bound : ℝ) / one ≤ 1 - |wv| := by linarith
  have hsub : ((one - w.bound : ℕ) : ℝ) = (one : ℝ) - w.bound := by rw [Nat.cast_sub hBwN.le]
  have htail : |wv| ^ (N + 1) / (1 - |wv|)
      ≤ ((w.bound ^ (N + 1) : ℕ) : ℝ) / ((one ^ (N - 1) * (one - w.bound) : ℕ) : ℝ) / one := by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, hsub, hM, show M + 1 - 1 = M by omega]
    have hc0 : (0 : ℝ) ≤ ((w.bound : ℝ) / one) ^ (M + 1 + 1) := by positivity
    have h1a : (0 : ℝ) < 1 - |wv| := by linarith
    calc |wv| ^ (M + 1 + 1) / (1 - |wv|) ≤ ((w.bound : ℝ) / one) ^ (M + 1 + 1) / (1 - |wv|) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hwb _) h1a.le
      _ ≤ ((w.bound : ℝ) / one) ^ (M + 1 + 1) / (1 - (w.bound : ℝ) / one) :=
          div_le_div_of_nonneg_left hc0 hpos' hden'
      _ = (w.bound : ℝ) ^ (M + 1 + 1) / ((one : ℝ) ^ M * ((one : ℝ) - w.bound)) / one :=
          tail_id3 (one : ℝ) (w.bound : ℝ) hone' hBw1 M
  -- assemble
  have hRp : evalP 0 (TM.addc Sm (-(logScalar P kap.toNat).1)).p x y z
      = evalP 0 Sm.p x y z + ((-(logScalar P kap.toNat).1 : ℤ) : ℝ) := by
    simp only [TM.addc]; rw [evalP_addP]
    have : evalP 0 [[[-(logScalar P kap.toNat).1]]] x y z = ((-(logScalar P kap.toNat).1 : ℤ) : ℝ) := by
      simp [evalP, evalC, evalR]
    rw [this]
  rw [hRp, hlogf]
  have e : Real.log (1 + wv) - Real.log ((kap : ℝ) / one)
      - (evalP 0 Sm.p x y z + ((-(logScalar P kap.toNat).1 : ℤ) : ℝ)) / one
      = (Real.log (1 + wv) - l1pSum wv N) + (l1pSum wv N - evalP 0 Sm.p x y z / one)
        + (((logScalar P kap.toNat).1 : ℝ) / one - Real.log ((kap : ℝ) / one)) := by
    push_cast; ring
  rw [e]
  simp only [TM.addc]
  push_cast
  calc _ ≤ |Real.log (1 + wv) - l1pSum wv N| + |l1pSum wv N - evalP 0 Sm.p x y z / one|
        + |((logScalar P kap.toNat).1 : ℝ) / one - Real.log ((kap : ℝ) / one)| := abs_add_three _ _ _
    _ ≤ ((w.bound ^ (N + 1) : ℕ) : ℝ) / ((one ^ (N - 1) * (one - w.bound) : ℕ) : ℝ) / one
        + (Sm.r : ℝ) / one + ((logScalar P kap.toNat).2 : ℝ) / one := by
        gcongr
        · exact hser.trans htail
    _ ≤ (cdiv (w.bound ^ (N + 1)) (one ^ (N - 1) * (one - w.bound)) : ℝ) / one
        + (Sm.r : ℝ) / one + ((logScalar P kap.toNat).2 : ℝ) / one := by
        gcongr
    _ = _ := by ring

/-! ## Average (a quantity pinched between two TMs) -/

noncomputable def TM.average (A B : TM) : TM :=
  ⟨roundP 2 (addP A.p B.p), cdiv (absP (addP B.p (smulP (-1) A.p)) + fracP 2 (addP A.p B.p)) 2 + A.r + B.r,
    A.ok && B.ok⟩

theorem Contains.average {one : ℕ} (hone : 0 < one) {A B : TM} {fa fb v : ℝ → ℝ → ℝ → ℝ}
    (hA : Contains one A fa) (hB : Contains one B fb)
    (hv : ∀ x y z : ℝ, |x| ≤ 1 → |y| ≤ 1 → |z| ≤ 1 →
      (fa x y z ≤ v x y z ∧ v x y z ≤ fb x y z) ∨ (fb x y z ≤ v x y z ∧ v x y z ≤ fa x y z)) :
    Contains one (TM.average A B) v := by
  intro hok x y z hx hy hz
  simp only [TM.average, Bool.and_eq_true] at hok
  have h1 := hA hok.1 x y z hx hy hz
  have h2 := hB hok.2 x y z hx hy hz
  have hone' : (0 : ℝ) < one := by exact_mod_cast hone
  simp only [TM.average]
  set a := evalP 0 A.p x y z
  set b := evalP 0 B.p x y z
  set S := addP A.p B.p
  set Dm := absP (addP B.p (smulP (-1) A.p))
  set M := evalP 0 (modP 2 S) x y z
  have hS : evalP 0 S x y z = a + b := evalP_addP x y z A.p B.p 0
  have hR := evalP_round x y z 2 S 0
  have hM : |M| ≤ fracP 2 S := abs_evalP_mod_le x y z 2 (by norm_num) S 0 hx hy hz
  have hD : |b - a| ≤ Dm := by
    have := abs_evalP_le x y z (addP B.p (smulP (-1) A.p)) 0 hx hy hz
    rw [evalP_addP, evalP_smulP] at this
    have e : b - a = evalP 0 B.p x y z + ((-1 : ℤ) : ℝ) * evalP 0 A.p x y z := by push_cast; ring
    rw [e]; exact this
  have hmid : |v x y z - (fa x y z + fb x y z) / 2| ≤ |fa x y z - fb x y z| / 2 := by
    have l1 := le_abs_self (fa x y z - fb x y z)
    have l2 := neg_abs_le (fa x y z - fb x y z)
    rw [abs_le]
    rcases hv x y z hx hy hz with ⟨l, u⟩ | ⟨l, u⟩ <;> constructor <;> linarith
  have hH : evalP 0 (roundP 2 S) x y z = (a + b - M) / 2 := by
    rw [← hS]; push_cast at hR; linarith
  have hfab : |fa x y z - fb x y z| ≤ ((A.r : ℝ) + Dm + B.r) / one := by
    have e : fa x y z - fb x y z = (fa x y z - a / one) + (a - b) / one - (fb x y z - b / one) := by ring
    rw [e]
    have hba : |(a - b) / one| ≤ (Dm : ℝ) / one := by
      rw [abs_div, abs_of_pos hone', abs_sub_comm]; exact div_le_div_of_nonneg_right hD hone'.le
    calc _ ≤ |fa x y z - a / one + (a - b) / one| + |fb x y z - b / one| := abs_sub _ _
      _ ≤ |fa x y z - a / one| + |(a - b) / one| + |fb x y z - b / one| :=
          add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (A.r : ℝ) / one + (Dm : ℝ) / one + (B.r : ℝ) / one := add_le_add (add_le_add h1 hba) h2
      _ = _ := by ring
  have hcd := le_cdiv (Dm + fracP 2 S) 2 (by norm_num)
  rw [hH]
  have e : v x y z - (a + b - M) / 2 / one
      = (v x y z - (fa x y z + fb x y z) / 2) + ((fa x y z - a / one) + (fb x y z - b / one)) / 2
        + M / (2 * one) := by
    field_simp; ring
  rw [e]
  have hMq : |M / (2 * one)| ≤ (fracP 2 S : ℝ) / (2 * one) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * one)]
    exact div_le_div_of_nonneg_right hM (by positivity)
  have hpair : |((fa x y z - a / one) + (fb x y z - b / one)) / 2| ≤ ((A.r : ℝ) + B.r) / one / 2 := by
    rw [abs_div, abs_two]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    calc _ ≤ |fa x y z - a / one| + |fb x y z - b / one| := abs_add_le _ _
      _ ≤ (A.r : ℝ) / one + (B.r : ℝ) / one := add_le_add h1 h2
      _ = _ := by ring
  have hm2 : |v x y z - (fa x y z + fb x y z) / 2| ≤ ((A.r : ℝ) + Dm + B.r) / one / 2 :=
    hmid.trans (div_le_div_of_nonneg_right hfab (by norm_num))
  have hcd' : ((Dm + fracP 2 S : ℕ) : ℝ) / 2 ≤ (cdiv (Dm + fracP 2 S) 2 : ℝ) := by
    have := hcd; push_cast at this ⊢; exact this
  push_cast
  calc _ ≤ |v x y z - (fa x y z + fb x y z) / 2| + |((fa x y z - a / one) + (fb x y z - b / one)) / 2|
        + |M / (2 * one)| := abs_add_three _ _ _
    _ ≤ ((A.r : ℝ) + Dm + B.r) / one / 2 + ((A.r : ℝ) + B.r) / one / 2 + (fracP 2 S : ℝ) / (2 * one) :=
        add_le_add (add_le_add hm2 hpair) hMq
    _ = (((Dm + fracP 2 S : ℕ) : ℝ) / 2 + A.r + B.r) / one := by
        push_cast; field_simp; ring
    _ ≤ ((cdiv (Dm + fracP 2 S) 2 : ℝ) + A.r + B.r) / one := by
        gcongr

end CKLaneR2.TM3

end


