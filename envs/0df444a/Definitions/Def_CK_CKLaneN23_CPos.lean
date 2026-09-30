-- Prove2me | Definitions.Def_CK_CKLaneN23_CPos
-- name    : CK_CKLaneN23_CPos
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:01:08.401273+00:00
-- url     : https://prove2.me/theorems/d21733d6-1f32-44fc-b79a-3f5ebc062279
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CPos` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CPos` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CPos` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CPos (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CPos.lean)

import Definitions.Def_CK_CKLaneN23_CStep2

-- ===== source module CKLaneN23.CPos =====
section

/-!
# CKLaneN23.CPos — positivity of a valuation-2 TM on the whole corner domain from a box grid (Lane N23b)

For a box `σ ∈ [σ0, σ1]`, `τ ∈ [τ0, τ1]` the quotient `Q = drop P 2` is re-expanded at the box centre
(`shiftT`, exact rational arithmetic: `σ = σc + hσ σ'`, `τ = τc + hτ τ'` with `|σ'|, |τ'| ≤ 1/2`) and
bounded below by the signed Horner bound `boxLowT` over `x ∈ [0, Eps]`.  `pos_of_grid`: if on every box
of a uniform `mS × mT` grid `r Eps^(n-2) ≤ boxLowT (shift Q)`, then the enclosed function is `≥ 0` on `Dom`.
-/

namespace CKLaneN23.CT

open GeneralCK

/-! ## linear substitution -/

/-- `c + h·v`, `v` = the variable of `key` (`(1,0)` = σ, `(0,1)` = τ); zero entries dropped -/
noncomputable def linQ (c h : ℚ) (key : ℕ × ℕ) : QPoly :=
  (if c = 0 then [] else [((0, 0), [(0, c)])]) ++ (if h = 0 then [] else [(key, [(0, h)])])

theorem QPoly.eval_append (σ τ L : ℝ) (s1 s2 : QPoly) :
    QPoly.eval σ τ L (s1 ++ s2) = QPoly.eval σ τ L s1 + QPoly.eval σ τ L s2 := by
  induction s1 with
  | nil => simp [QPoly.eval_nil]
  | cons m s ih => rw [List.cons_append, QPoly.eval_cons, QPoly.eval_cons, ih]; ring

theorem eval_linQ (c h : ℚ) (i k : ℕ) (σ τ : ℝ) :
    QPoly.eval σ τ (Real.log 2) (linQ c h (i, k)) = (c : ℝ) + (h : ℝ) * (σ ^ i * τ ^ k) := by
  unfold linQ
  rw [QPoly.eval_append]
  split_ifs with hc hh hh
  · simp [hc, hh, QPoly.eval_nil]
  · simp [hc, QPoly.eval_cons, QPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]; ring
  · simp [hh, QPoly.eval_cons, QPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]
  · simp [QPoly.eval_cons, QPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]; ring

noncomputable def qpowQ (p : QPoly) (k : ℕ) : QPoly :=
  Nat.rec (motive := fun _ => QPoly) [((0, 0), [(0, 1)])] (fun _ acc => QPoly.mul acc p) k

theorem eval_qpowQ (σ τ : ℝ) (p : QPoly) (k : ℕ) :
    QPoly.eval σ τ (Real.log 2) (qpowQ p k) = QPoly.eval σ τ (Real.log 2) p ^ k := by
  have hL : Real.log 2 ≠ 0 := by positivity
  induction k with
  | zero => simp [qpowQ, QPoly.eval_cons, QPoly.eval_nil, LPoly.eval_cons, LPoly.eval_nil]
  | succ k ih =>
    show QPoly.eval σ τ (Real.log 2) (QPoly.mul (qpowQ p k) p) = _
    rw [QPoly.eval_mul σ τ _ hL, ih, pow_succ]

noncomputable def shiftQ (ps pt : QPoly) (s : QPoly) : QPoly :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => QPoly) []
    (fun m _ acc => QPoly.add (QPoly.mul (QPoly.mul (qpowQ ps m.1.1) (qpowQ pt m.1.2)) [((0, 0), m.2)]) acc) s

theorem eval_shiftQ (σ τ : ℝ) (ps pt s : QPoly) :
    QPoly.eval σ τ (Real.log 2) (shiftQ ps pt s) =
      QPoly.eval (QPoly.eval σ τ (Real.log 2) ps) (QPoly.eval σ τ (Real.log 2) pt) (Real.log 2) s := by
  have hL : Real.log 2 ≠ 0 := by positivity
  induction s with
  | nil => rfl
  | cons m s ih =>
    show QPoly.eval σ τ (Real.log 2)
        (QPoly.add (QPoly.mul (QPoly.mul (qpowQ ps m.1.1) (qpowQ pt m.1.2)) [((0, 0), m.2)])
          (shiftQ ps pt s)) = _
    rw [QPoly.eval_add, QPoly.eval_mul σ τ _ hL, QPoly.eval_mul σ τ _ hL, eval_qpowQ, eval_qpowQ, ih,
      QPoly.eval_cons (σ := QPoly.eval σ τ (Real.log 2) ps)]
    simp [QPoly.eval_cons, QPoly.eval_nil]

noncomputable def shiftT (ps pt : QPoly) (P : TPoly) : TPoly :=
  @List.rec QPoly (fun _ => TPoly) [] (fun s _ acc => shiftQ ps pt s :: acc) P

theorem eval_shiftT (x σ τ : ℝ) (ps pt : QPoly) (P : TPoly) :
    TPoly.eval x σ τ (Real.log 2) (shiftT ps pt P) =
      TPoly.eval x (QPoly.eval σ τ (Real.log 2) ps) (QPoly.eval σ τ (Real.log 2) pt) (Real.log 2) P := by
  induction P with
  | nil => rfl
  | cons s P ih =>
    show QPoly.eval σ τ (Real.log 2) (shiftQ ps pt s) + x * TPoly.eval x σ τ (Real.log 2) (shiftT ps pt P) = _
    rw [eval_shiftQ, ih, TPoly.eval_cons]

/-! ## signed Horner lower bound over `x ∈ [0, Eps]` -/

noncomputable def boxLowT (P : TPoly) : ℚ :=
  @List.rec QPoly (fun _ => ℚ) 0 (fun s _ acc => QPoly.lowB s + Eps * min acc 0) P

theorem boxLowT_spec {x σ τ : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ (Eps : ℝ)) (hσ : |σ| ≤ 1 / 2)
    (hτ : |τ| ≤ 1 / 2) (P : TPoly) : (boxLowT P : ℝ) ≤ TPoly.eval x σ τ (Real.log 2) P := by
  induction P with
  | nil => simp [boxLowT, TPoly.eval_nil]
  | cons s P ih =>
    show ((QPoly.lowB s + Eps * min (boxLowT P) 0 : ℚ) : ℝ) ≤ _
    rw [TPoly.eval_cons]
    have h1 := (QPoly.lowB_spec hσ hτ s).1
    have hm : ((min (boxLowT P) 0 : ℚ) : ℝ) ≤ 0 := by exact_mod_cast min_le_right _ _
    have hm2 : ((min (boxLowT P) 0 : ℚ) : ℝ) ≤ TPoly.eval x σ τ (Real.log 2) P :=
      le_trans (by exact_mod_cast min_le_left _ _) ih
    have h3 : (Eps : ℝ) * ((min (boxLowT P) 0 : ℚ) : ℝ) ≤ x * ((min (boxLowT P) 0 : ℚ) : ℝ) :=
      mul_le_mul_of_nonpos_right hx hm
    have h4 : x * ((min (boxLowT P) 0 : ℚ) : ℝ) ≤ x * TPoly.eval x σ τ (Real.log 2) P :=
      mul_le_mul_of_nonneg_left hm2 hx0
    push_cast
    push_cast at h3 h4
    linarith

/-! ## boxes and grids -/

noncomputable def boxChk (P : TPoly) (r : ℚ) (n : ℕ) (a b c d : ℚ) : Bool :=
  decide (r * Eps ^ (n - 2) ≤
    boxLowT (shiftT (linQ ((a + b) / 2) (b - a) (1, 0)) (linQ ((c + d) / 2) (d - c) (0, 1)) (TPoly.drop P 2)))

/-- uniform grid check of `f` on the `m` sub-intervals of `[lo, hi]` (Lane A3's `grid`) -/
noncomputable def grid (lo hi : ℚ) (f : ℚ → ℚ → Bool) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) m

theorem grid_aux (lo hi : ℚ) (f : ℚ → ℚ → Bool) (m k : ℕ)
    (h : Nat.rec (motive := fun _ => Bool) true
      (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) k = true) :
    ∀ j < k, f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m) = true := by
  induction k with
  | zero => intro j hj; omega
  | succ k ih =>
    intro j hj
    have h' : Nat.rec (motive := fun _ => Bool) true
        (fun j ih => ih && f (lo + (hi - lo) * (j : ℚ) / m) (lo + (hi - lo) * ((j : ℚ) + 1) / m)) k = true ∧
        f (lo + (hi - lo) * (k : ℚ) / m) (lo + (hi - lo) * ((k : ℚ) + 1) / m) = true := by
      simpa using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
    · exact ih h'.1 j hj'
    · rw [hj']; exact h'.2

theorem grid_cover (lo hi : ℚ) (hlt : lo < hi) (f : ℚ → ℚ → Bool) (m : ℕ) (hm : 0 < m)
    (h : grid lo hi f m = true) {x : ℝ} (hx1 : (lo : ℝ) ≤ x) (hx2 : x ≤ (hi : ℝ)) :
    ∃ a b : ℚ, f a b = true ∧ (a : ℝ) ≤ x ∧ x ≤ (b : ℝ) ∧ a < b := by
  have hall := grid_aux lo hi f m m h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlt' : (lo : ℝ) < hi := by exact_mod_cast hlt
  have hd : (0 : ℝ) < (hi : ℝ) - lo := by linarith
  set y : ℝ := (x - lo) / ((hi : ℝ) - lo) * m with hy
  have hq0 : 0 ≤ (x - lo) / ((hi : ℝ) - lo) := div_nonneg (by linarith) hd.le
  have hq1 : (x - lo) / ((hi : ℝ) - lo) ≤ 1 := by rw [div_le_one hd]; linarith
  have hy0 : 0 ≤ y := by rw [hy]; exact mul_nonneg hq0 hm'.le
  have hy1 : y ≤ m := by
    rw [hy]
    have := mul_le_mul_of_nonneg_right hq1 hm'.le
    linarith
  have e : (x - lo) / ((hi : ℝ) - lo) * ((hi : ℝ) - lo) = x - lo := div_mul_cancel₀ _ hd.ne'
  let j : ℕ := min (⌊y⌋₊) (m - 1)
  have hj : j < m := by omega
  refine ⟨lo + (hi - lo) * (j : ℚ) / m, lo + (hi - lo) * ((j : ℚ) + 1) / m, hall j hj, ?_, ?_, ?_⟩
  · push_cast
    have h1 : (j : ℝ) ≤ y := by
      have : (j : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      exact this.trans (Nat.floor_le hy0)
    have key : ((hi : ℝ) - lo) * j / m ≤ x - lo := by
      rw [div_le_iff₀ hm']
      have := mul_le_mul_of_nonneg_left h1 hd.le
      have hyx : ((hi : ℝ) - lo) * y = (x - lo) * m := by
        rw [hy]; linear_combination (m : ℝ) * e
      linarith
    linarith
  · push_cast
    have h2 : y ≤ (j : ℝ) + 1 := by
      by_cases hc : ⌊y⌋₊ ≤ m - 1
      · have : j = ⌊y⌋₊ := min_eq_left hc
        rw [this]; exact (Nat.lt_floor_add_one y).le
      · push Not at hc
        have hj' : j = m - 1 := min_eq_right hc.le
        rw [hj']
        have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]; exact hy1
    have key : x - lo ≤ ((hi : ℝ) - lo) * ((j : ℝ) + 1) / m := by
      rw [le_div_iff₀ hm']
      have := mul_le_mul_of_nonneg_left h2 hd.le
      have hyx : ((hi : ℝ) - lo) * y = (x - lo) * m := by
        rw [hy]; linear_combination (m : ℝ) * e
      linarith
    linarith
  · have hm'' : (0 : ℚ) < m := by exact_mod_cast hm
    have hd' : (0 : ℚ) < hi - lo := by linarith
    have : (hi - lo) * (j : ℚ) / m < (hi - lo) * ((j : ℚ) + 1) / m := by
      apply div_lt_div_of_pos_right _ hm''
      nlinarith
    linarith

/-- a point of a box has unit-box coordinates -/
theorem unit_coord {a b v : ℝ} (hab : a < b) (h1 : a ≤ v) (h2 : v ≤ b) :
    |(v - (a + b) / 2) / (b - a)| ≤ 1 / 2 := by
  have hd : 0 < b - a := by linarith
  rw [abs_le, le_div_iff₀ hd, div_le_iff₀ hd]
  constructor <;> linarith

noncomputable def posGrid (P : TPoly) (r : ℚ) (n mS mT : ℕ) : Bool :=
  grid (-1 / 2) (1 / 2) (fun a b => grid (-1 / 2) (1 / 2) (fun c d => boxChk P r n a b c d) mT) mS

theorem pos_of_grid {f : ℝ → ℝ → ℝ → ℝ} {D : TMd} (hf : Good f D) (hn : 2 ≤ D.n)
    (hz : zeroPrefix D.P 2 = true) (mS mT : ℕ) (hmS : 0 < mS) (hmT : 0 < mT)
    (hB : posGrid D.P D.r D.n mS mT = true) : ∀ x σ τ, Dom x σ τ → 0 ≤ f x σ τ := by
  intro x σ τ hd
  have hs := abs_le.mp (hf.split_val 2 hn hz hd)
  have hσ1 : ((-1 / 2 : ℚ) : ℝ) ≤ σ := by have := (abs_le.mp hd.2.2.1).1; push_cast; linarith
  have hσ2 : σ ≤ ((1 / 2 : ℚ) : ℝ) := by have := (abs_le.mp hd.2.2.1).2; push_cast; linarith
  have hτ1 : ((-1 / 2 : ℚ) : ℝ) ≤ τ := by have := (abs_le.mp hd.2.2.2).1; push_cast; linarith
  have hτ2 : τ ≤ ((1 / 2 : ℚ) : ℝ) := by have := (abs_le.mp hd.2.2.2).2; push_cast; linarith
  obtain ⟨a, b, hab, ha, hb, hab'⟩ := grid_cover (-1 / 2) (1 / 2) (by norm_num) _ mS hmS hB hσ1 hσ2
  obtain ⟨c, d, hcd, hc, hdd, hcd'⟩ := grid_cover (-1 / 2) (1 / 2) (by norm_num) _ mT hmT hab hτ1 hτ2
  have hq := of_decide_eq_true hcd
  set σ' := (σ - ((a : ℝ) + b) / 2) / ((b : ℝ) - a) with hσ'
  set τ' := (τ - ((c : ℝ) + d) / 2) / ((d : ℝ) - c) with hτ'
  have hab'' : (a : ℝ) < b := by exact_mod_cast hab'
  have hcd'' : (c : ℝ) < d := by exact_mod_cast hcd'
  have hσu : |σ'| ≤ 1 / 2 := unit_coord hab'' ha hb
  have hτu : |τ'| ≤ 1 / 2 := unit_coord hcd'' hc hdd
  have hbl := boxLowT_spec hd.1.le hd.2.1 hσu hτu
    (shiftT (linQ ((a + b) / 2) (b - a) (1, 0)) (linQ ((c + d) / 2) (d - c) (0, 1)) (TPoly.drop D.P 2))
  rw [eval_shiftT, eval_linQ, eval_linQ] at hbl
  have hba : (b : ℝ) - a ≠ 0 := (by linarith : (0 : ℝ) < b - a).ne'
  have hdc : (d : ℝ) - c ≠ 0 := (by linarith : (0 : ℝ) < d - c).ne'
  have e1 : (((a + b) / 2 : ℚ) : ℝ) + ((b - a : ℚ) : ℝ) * (σ' ^ 1 * τ' ^ 0) = σ := by
    rw [hσ']; push_cast; field_simp; ring
  have e2 : (((c + d) / 2 : ℚ) : ℝ) + ((d - c : ℚ) : ℝ) * (σ' ^ 0 * τ' ^ 1) = τ := by
    rw [hτ']; push_cast; field_simp; ring
  rw [e1, e2] at hbl
  have hq' : ((D.r * Eps ^ (D.n - 2) : ℚ) : ℝ) ≤ ((boxLowT (shiftT (linQ ((a + b) / 2) (b - a) (1, 0))
      (linQ ((c + d) / 2) (d - c) (0, 1)) (TPoly.drop D.P 2)) : ℚ) : ℝ) := by exact_mod_cast hq
  push_cast at hq'
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have hk : x ^ 2 * ((D.r : ℝ) * (Eps : ℝ) ^ (D.n - 2)) ≤
      x ^ 2 * TPoly.eval x σ τ (Real.log 2) (TPoly.drop D.P 2) :=
    mul_le_mul_of_nonneg_left (hq'.trans hbl) hx2
  linarith [hs.1]

end CKLaneN23.CT

end


