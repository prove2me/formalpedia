-- Prove2me | Definitions.Def_CK_CKLaneN23_CPoly
-- name    : CK_CKLaneN23_CPoly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:52:23.005338+00:00
-- url     : https://prove2.me/theorems/c79cb52f-970b-41f2-9bbd-0333b72bbfc0
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CPoly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CPoly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CPoly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CPoly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CPoly.lean)

import Mathlib

-- ===== source module CKLaneN23.CPoly =====
section

/-!
# CKLaneN23.CPoly — exact sparse polynomials for the RA-stat corner Taylor-model checker

(Adapted from Lane A3's `CKLaneA3.Poly`; extended to TWO bounded parameters.)
Kernel-evaluable representation (all recursion through `List.rec` / `Nat.rec`):
* `LPoly` : Laurent polynomial in `L` (intended `L = log 2`): `(c, q)` means `q * L^c`.
* `QPoly` : polynomial in `(σ, τ)` with `LPoly` coefficients: `((i, k), l)` means `σ^i τ^k l`.
* `TPoly` : dense polynomial in `s` with `QPoly` coefficients: `[c₀, c₁, …] = c₀ + s (c₁ + s (…))`.
Sortedness is used for compactness only, never for soundness.
-/

namespace CKLaneN23.CT

abbrev LPoly := List (ℤ × ℚ)
abbrev QPoly := List ((ℕ × ℕ) × LPoly)
abbrev TPoly := List QPoly

/-! ## LPoly -/

noncomputable def LPoly.eval (L : ℝ) (l : LPoly) : ℝ :=
  @List.rec (ℤ × ℚ) (fun _ => ℝ) 0 (fun m _ ih => (m.2 : ℝ) * L ^ m.1 + ih) l

theorem LPoly.eval_nil (L : ℝ) : LPoly.eval L [] = 0 := rfl
theorem LPoly.eval_cons (L : ℝ) (m : ℤ × ℚ) (l : LPoly) :
    LPoly.eval L (m :: l) = (m.2 : ℝ) * L ^ m.1 + LPoly.eval L l := rfl

noncomputable def LPoly.add (l1 : LPoly) : LPoly → LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly → LPoly) (fun l2 => l2)
    (fun m1 t1 rec => fun l2 =>
      @List.rec (ℤ × ℚ) (fun _ => LPoly) (m1 :: t1)
        (fun m2 t2 ih =>
          if m1.1 < m2.1 then m1 :: rec (m2 :: t2)
          else if m2.1 < m1.1 then m2 :: ih
          else if m1.2 + m2.2 = 0 then rec t2 else (m1.1, m1.2 + m2.2) :: rec t2) l2) l1

theorem LPoly.add_nil (l2 : LPoly) : LPoly.add [] l2 = l2 := rfl
theorem LPoly.add_cons_nil (m1 : ℤ × ℚ) (t1 : LPoly) : LPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem LPoly.add_cons_cons (m1 m2 : ℤ × ℚ) (t1 t2 : LPoly) :
    LPoly.add (m1 :: t1) (m2 :: t2) =
      if m1.1 < m2.1 then m1 :: LPoly.add t1 (m2 :: t2)
      else if m2.1 < m1.1 then m2 :: LPoly.add (m1 :: t1) t2
      else if m1.2 + m2.2 = 0 then LPoly.add t1 t2 else (m1.1, m1.2 + m2.2) :: LPoly.add t1 t2 :=
  rfl

theorem LPoly.eval_add (L : ℝ) (l1 l2 : LPoly) :
    LPoly.eval L (LPoly.add l1 l2) = LPoly.eval L l1 + LPoly.eval L l2 := by
  induction l1 generalizing l2 with
  | nil => simp [LPoly.add_nil, LPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction l2 with
    | nil => simp [LPoly.add_cons_nil, LPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [LPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [LPoly.eval_cons, ih1, LPoly.eval_cons, LPoly.eval_cons]; ring
      · rw [LPoly.eval_cons, ih2]; simp only [LPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := by omega
        rw [ih1, LPoly.eval_cons, LPoly.eval_cons, he]
        have : ((m1.2 : ℝ) + (m2.2 : ℝ)) = 0 := by exact_mod_cast h3
        linear_combination (-(L ^ m2.1)) * this
      · have he : m1.1 = m2.1 := by omega
        rw [LPoly.eval_cons, ih1, LPoly.eval_cons, LPoly.eval_cons, he]
        push_cast; ring

noncomputable def LPoly.mulMono (c : ℤ) (q : ℚ) (l : LPoly) : LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly) [] (fun m _ ih => (c + m.1, q * m.2) :: ih) l

theorem LPoly.eval_mulMono (L : ℝ) (hL : L ≠ 0) (c : ℤ) (q : ℚ) (l : LPoly) :
    LPoly.eval L (LPoly.mulMono c q l) = (q : ℝ) * L ^ c * LPoly.eval L l := by
  induction l with
  | nil => simp [LPoly.mulMono, LPoly.eval_nil]
  | cons m t ih =>
    show (((q * m.2 : ℚ)) : ℝ) * L ^ (c + m.1) + LPoly.eval L (LPoly.mulMono c q t) = _
    rw [ih, LPoly.eval_cons, zpow_add₀ hL]; push_cast; ring

noncomputable def LPoly.mul (l1 l2 : LPoly) : LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly) [] (fun m _ ih => LPoly.add (LPoly.mulMono m.1 m.2 l2) ih) l1

theorem LPoly.eval_mul (L : ℝ) (hL : L ≠ 0) (l1 l2 : LPoly) :
    LPoly.eval L (LPoly.mul l1 l2) = LPoly.eval L l1 * LPoly.eval L l2 := by
  induction l1 with
  | nil => simp [LPoly.mul, LPoly.eval_nil]
  | cons m t ih =>
    show LPoly.eval L (LPoly.add (LPoly.mulMono m.1 m.2 l2) (LPoly.mul t l2)) = _
    rw [LPoly.eval_add L, LPoly.eval_mulMono L hL, ih, LPoly.eval_cons]; ring

noncomputable def LPoly.scale (q : ℚ) (l : LPoly) : LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly) [] (fun m _ ih => (m.1, q * m.2) :: ih) l

theorem LPoly.eval_scale (L : ℝ) (q : ℚ) (l : LPoly) :
    LPoly.eval L (LPoly.scale q l) = (q : ℝ) * LPoly.eval L l := by
  induction l with
  | nil => simp [LPoly.scale, LPoly.eval_nil]
  | cons m t ih =>
    show (((q * m.2 : ℚ)) : ℝ) * L ^ m.1 + LPoly.eval L (LPoly.scale q t) = _
    rw [ih, LPoly.eval_cons]; push_cast; ring

/-! ## QPoly (two parameters) -/

/-- lexicographic strict order on exponent pairs -/
def klt (a b : ℕ × ℕ) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

theorem klt_eq {a b : ℕ × ℕ} (h1 : klt a b = false) (h2 : klt b a = false) : a = b := by
  unfold klt at h1 h2
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1 h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have e1 : a.1 = b.1 := by omega
  have e2 : a.2 = b.2 := by
    rcases h1b with h | h
    · exact absurd e1 h
    · rcases h2b with h' | h'
      · exact absurd e1.symm h'
      · omega
  exact Prod.ext e1 e2

noncomputable def QPoly.eval (σ τ L : ℝ) (s : QPoly) : ℝ :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => ℝ) 0
    (fun m _ ih => σ ^ m.1.1 * τ ^ m.1.2 * LPoly.eval L m.2 + ih) s

theorem QPoly.eval_nil (σ τ L : ℝ) : QPoly.eval σ τ L [] = 0 := rfl
theorem QPoly.eval_cons (σ τ L : ℝ) (m : (ℕ × ℕ) × LPoly) (s : QPoly) :
    QPoly.eval σ τ L (m :: s) = σ ^ m.1.1 * τ ^ m.1.2 * LPoly.eval L m.2 + QPoly.eval σ τ L s := rfl

noncomputable def QPoly.add (s1 : QPoly) : QPoly → QPoly :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => QPoly → QPoly) (fun s2 => s2)
    (fun m1 t1 rec => fun s2 =>
      @List.rec ((ℕ × ℕ) × LPoly) (fun _ => QPoly) (m1 :: t1)
        (fun m2 t2 ih =>
          if klt m1.1 m2.1 = true then m1 :: rec (m2 :: t2)
          else if klt m2.1 m1.1 = true then m2 :: ih
          else if LPoly.add m1.2 m2.2 = [] then rec t2
          else (m1.1, LPoly.add m1.2 m2.2) :: rec t2) s2) s1

theorem QPoly.add_nil (s2 : QPoly) : QPoly.add [] s2 = s2 := rfl
theorem QPoly.add_cons_nil (m1 : (ℕ × ℕ) × LPoly) (t1 : QPoly) : QPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem QPoly.add_cons_cons (m1 m2 : (ℕ × ℕ) × LPoly) (t1 t2 : QPoly) :
    QPoly.add (m1 :: t1) (m2 :: t2) =
      if klt m1.1 m2.1 = true then m1 :: QPoly.add t1 (m2 :: t2)
      else if klt m2.1 m1.1 = true then m2 :: QPoly.add (m1 :: t1) t2
      else if LPoly.add m1.2 m2.2 = [] then QPoly.add t1 t2
      else (m1.1, LPoly.add m1.2 m2.2) :: QPoly.add t1 t2 :=
  rfl

theorem QPoly.eval_add (σ τ L : ℝ) (s1 s2 : QPoly) :
    QPoly.eval σ τ L (QPoly.add s1 s2) = QPoly.eval σ τ L s1 + QPoly.eval σ τ L s2 := by
  induction s1 generalizing s2 with
  | nil => simp [QPoly.add_nil, QPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction s2 with
    | nil => simp [QPoly.add_cons_nil, QPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [QPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [QPoly.eval_cons, ih1, QPoly.eval_cons, QPoly.eval_cons]; ring
      · rw [QPoly.eval_cons, ih2]; simp only [QPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := klt_eq (by simpa using h1) (by simpa using h2)
        have hz : LPoly.eval L (LPoly.add m1.2 m2.2) = 0 := by rw [h3]; rfl
        rw [LPoly.eval_add] at hz
        rw [ih1, QPoly.eval_cons, QPoly.eval_cons, he]
        linear_combination (-(σ ^ m2.1.1 * τ ^ m2.1.2)) * hz
      · have he : m1.1 = m2.1 := klt_eq (by simpa using h1) (by simpa using h2)
        rw [QPoly.eval_cons, ih1, QPoly.eval_cons, QPoly.eval_cons, LPoly.eval_add, he]
        ring

/-- multiply every entry by `σ^i τ^k l` (entries whose product is `[]` are dropped). -/
noncomputable def QPoly.mulMono (key : ℕ × ℕ) (l : LPoly) (s : QPoly) : QPoly :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => QPoly) []
    (fun m _ ih => if LPoly.mul l m.2 = [] then ih
      else ((key.1 + m.1.1, key.2 + m.1.2), LPoly.mul l m.2) :: ih) s

theorem QPoly.eval_mulMono (σ τ L : ℝ) (hL : L ≠ 0) (key : ℕ × ℕ) (l : LPoly) (s : QPoly) :
    QPoly.eval σ τ L (QPoly.mulMono key l s) =
      σ ^ key.1 * τ ^ key.2 * LPoly.eval L l * QPoly.eval σ τ L s := by
  induction s with
  | nil => simp [QPoly.mulMono, QPoly.eval_nil]
  | cons m t ih =>
    show QPoly.eval σ τ L
        (if LPoly.mul l m.2 = [] then QPoly.mulMono key l t
         else ((key.1 + m.1.1, key.2 + m.1.2), LPoly.mul l m.2) :: QPoly.mulMono key l t) = _
    split_ifs with h
    · have hz : LPoly.eval L (LPoly.mul l m.2) = 0 := by rw [h]; rfl
      rw [LPoly.eval_mul L hL] at hz
      rw [ih, QPoly.eval_cons]
      linear_combination (-(σ ^ key.1 * σ ^ m.1.1 * (τ ^ key.2 * τ ^ m.1.2))) * hz
    · rw [QPoly.eval_cons, ih, QPoly.eval_cons, LPoly.eval_mul L hL, pow_add, pow_add]; ring

noncomputable def QPoly.mul (s1 s2 : QPoly) : QPoly :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => QPoly) []
    (fun m _ ih => QPoly.add (QPoly.mulMono m.1 m.2 s2) ih) s1

theorem QPoly.eval_mul (σ τ L : ℝ) (hL : L ≠ 0) (s1 s2 : QPoly) :
    QPoly.eval σ τ L (QPoly.mul s1 s2) = QPoly.eval σ τ L s1 * QPoly.eval σ τ L s2 := by
  induction s1 with
  | nil => simp [QPoly.mul, QPoly.eval_nil]
  | cons m t ih =>
    show QPoly.eval σ τ L (QPoly.add (QPoly.mulMono m.1 m.2 s2) (QPoly.mul t s2)) = _
    rw [QPoly.eval_add, QPoly.eval_mulMono σ τ L hL, ih, QPoly.eval_cons]; ring

noncomputable def QPoly.scale (q : ℚ) (s : QPoly) : QPoly :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => QPoly) [] (fun m _ ih => (m.1, LPoly.scale q m.2) :: ih) s

theorem QPoly.eval_scale (σ τ L : ℝ) (q : ℚ) (s : QPoly) :
    QPoly.eval σ τ L (QPoly.scale q s) = (q : ℝ) * QPoly.eval σ τ L s := by
  induction s with
  | nil => simp [QPoly.scale, QPoly.eval_nil]
  | cons m t ih =>
    show σ ^ m.1.1 * τ ^ m.1.2 * LPoly.eval L (LPoly.scale q m.2) + QPoly.eval σ τ L (QPoly.scale q t) = _
    rw [ih, LPoly.eval_scale, QPoly.eval_cons]; ring

/-! ## TPoly (dense in s) -/

noncomputable def TPoly.eval (x σ τ L : ℝ) (P : TPoly) : ℝ :=
  @List.rec QPoly (fun _ => ℝ) 0 (fun s _ ih => QPoly.eval σ τ L s + x * ih) P

theorem TPoly.eval_nil (x σ τ L : ℝ) : TPoly.eval x σ τ L [] = 0 := rfl
theorem TPoly.eval_cons (x σ τ L : ℝ) (s : QPoly) (P : TPoly) :
    TPoly.eval x σ τ L (s :: P) = QPoly.eval σ τ L s + x * TPoly.eval x σ τ L P := rfl

noncomputable def TPoly.add (P1 : TPoly) : TPoly → TPoly :=
  @List.rec QPoly (fun _ => TPoly → TPoly) (fun P2 => P2)
    (fun s1 t1 rec => fun P2 =>
      @List.rec QPoly (fun _ => TPoly) (s1 :: t1)
        (fun s2 t2 _ => QPoly.add s1 s2 :: rec t2) P2) P1

theorem TPoly.add_nil (P2 : TPoly) : TPoly.add [] P2 = P2 := rfl
theorem TPoly.add_cons_nil (s1 : QPoly) (t1 : TPoly) : TPoly.add (s1 :: t1) [] = s1 :: t1 := rfl
theorem TPoly.add_cons_cons (s1 s2 : QPoly) (t1 t2 : TPoly) :
    TPoly.add (s1 :: t1) (s2 :: t2) = QPoly.add s1 s2 :: TPoly.add t1 t2 := rfl

theorem TPoly.eval_add (x σ τ L : ℝ) (P1 P2 : TPoly) :
    TPoly.eval x σ τ L (TPoly.add P1 P2) = TPoly.eval x σ τ L P1 + TPoly.eval x σ τ L P2 := by
  induction P1 generalizing P2 with
  | nil => simp [TPoly.add_nil, TPoly.eval_nil]
  | cons s1 t1 ih =>
    cases P2 with
    | nil => simp [TPoly.add_cons_nil, TPoly.eval_nil]
    | cons s2 t2 =>
      rw [TPoly.add_cons_cons, TPoly.eval_cons, TPoly.eval_cons, TPoly.eval_cons, ih,
        QPoly.eval_add]
      ring

noncomputable def TPoly.scale (q : ℚ) (P : TPoly) : TPoly :=
  @List.rec QPoly (fun _ => TPoly) [] (fun s _ ih => QPoly.scale q s :: ih) P

theorem TPoly.eval_scale (x σ τ L : ℝ) (q : ℚ) (P : TPoly) :
    TPoly.eval x σ τ L (TPoly.scale q P) = (q : ℝ) * TPoly.eval x σ τ L P := by
  induction P with
  | nil => simp [TPoly.scale, TPoly.eval_nil]
  | cons s P ih =>
    show QPoly.eval σ τ L (QPoly.scale q s) + x * TPoly.eval x σ τ L (TPoly.scale q P) = _
    rw [ih, QPoly.eval_scale, TPoly.eval_cons]; ring

/-- multiply every s-coefficient by the `QPoly` `c` -/
noncomputable def TPoly.mulQ (c : QPoly) (P : TPoly) : TPoly :=
  @List.rec QPoly (fun _ => TPoly) [] (fun s _ ih => QPoly.mul c s :: ih) P

theorem TPoly.eval_mulQ (x σ τ L : ℝ) (hL : L ≠ 0) (c : QPoly) (P : TPoly) :
    TPoly.eval x σ τ L (TPoly.mulQ c P) = QPoly.eval σ τ L c * TPoly.eval x σ τ L P := by
  induction P with
  | nil => simp [TPoly.mulQ, TPoly.eval_nil]
  | cons s P ih =>
    show QPoly.eval σ τ L (QPoly.mul c s) + x * TPoly.eval x σ τ L (TPoly.mulQ c P) = _
    rw [ih, QPoly.eval_mul σ τ L hL, TPoly.eval_cons]; ring

/-- `s * P`, keeping only the first `k` s-coefficients. -/
noncomputable def TPoly.scaleSTake (s : QPoly) (P : TPoly) : ℕ → TPoly :=
  @List.rec QPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun p _ ih => fun k => Nat.rec (motive := fun _ => TPoly) []
      (fun k' _ => QPoly.mul s p :: ih k') k) P

/-- truncated product: s-coefficients of index `< n` of `P * Q`. -/
noncomputable def TPoly.mulT (P Q : TPoly) : ℕ → TPoly :=
  @List.rec QPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s _ ih => fun n => Nat.rec (motive := fun _ => TPoly) []
      (fun n' _ => TPoly.add (TPoly.scaleSTake s Q (n' + 1)) ([] :: ih n')) n) P

noncomputable def TPoly.take (P : TPoly) : ℕ → TPoly :=
  @List.rec QPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s _ ih => fun k => Nat.rec (motive := fun _ => TPoly) [] (fun k' _ => s :: ih k') k) P

noncomputable def TPoly.drop (P : TPoly) : ℕ → TPoly :=
  @List.rec QPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s P' ih => fun k => Nat.rec (motive := fun _ => TPoly) (s :: P') (fun k' _ => ih k') k) P

theorem TPoly.take_nil (k : ℕ) : TPoly.take [] k = [] := rfl
theorem TPoly.take_zero (P : TPoly) : TPoly.take P 0 = [] := by cases P <;> rfl
theorem TPoly.take_cons_succ (s : QPoly) (P : TPoly) (k : ℕ) :
    TPoly.take (s :: P) (k + 1) = s :: TPoly.take P k := rfl
theorem TPoly.drop_nil (k : ℕ) : TPoly.drop [] k = [] := rfl
theorem TPoly.drop_zero (P : TPoly) : TPoly.drop P 0 = P := by cases P <;> rfl
theorem TPoly.drop_cons_succ (s : QPoly) (P : TPoly) (k : ℕ) :
    TPoly.drop (s :: P) (k + 1) = TPoly.drop P k := rfl

theorem TPoly.eval_take_drop (x σ τ L : ℝ) (P : TPoly) (k : ℕ) :
    TPoly.eval x σ τ L P = TPoly.eval x σ τ L (TPoly.take P k) +
      x ^ k * TPoly.eval x σ τ L (TPoly.drop P k) := by
  induction P generalizing k with
  | nil => simp [TPoly.take_nil, TPoly.drop_nil, TPoly.eval_nil]
  | cons s P ih =>
    cases k with
    | zero => simp [TPoly.take_zero, TPoly.drop_zero, TPoly.eval_nil]
    | succ k =>
      rw [TPoly.take_cons_succ, TPoly.drop_cons_succ, TPoly.eval_cons, TPoly.eval_cons, ih k]
      ring

end CKLaneN23.CT

end


