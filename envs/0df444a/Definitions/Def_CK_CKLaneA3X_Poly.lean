-- Prove2me | Definitions.Def_CK_CKLaneA3X_Poly
-- name    : CK_CKLaneA3X_Poly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:16:04.827806+00:00
-- url     : https://prove2.me/theorems/641c8458-a49c-4df9-a783-429e427df97d
-- title:
--   Courtade–Kumar proof module `CKLaneA3X.Poly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3X.Poly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3X.Poly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3X.Poly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/Poly.lean)

import Mathlib

/-!
# CKLaneA3X.Poly — exact sparse polynomials for the high-u Taylor-model checker

Three-level representation (all kernel-evaluable via `List.rec`; no well-founded recursion):
* `LPoly` : Laurent polynomial in `L` (intended `L = log 2`): list of `(c, q)` meaning `q * L^c`.
* `SPoly` : polynomial in `σ` with `LPoly` coefficients: list of `(b, l)` meaning `σ^b * l`.
* `TPoly` : dense polynomial in `t` with `SPoly` coefficients: `[s₀, s₁, …]` means `s₀ + t*(s₁ + t*(…))`.

Only `eval`-soundness matters for the checker; sortedness is used for compactness but never for
soundness.
-/

namespace CKLaneA3X

abbrev LPoly := List (ℤ × ℚ)
abbrev SPoly := List (ℕ × LPoly)
abbrev TPoly := List SPoly

/-! ## LPoly -/

noncomputable def LPoly.eval (L : ℝ) (l : LPoly) : ℝ :=
  @List.rec (ℤ × ℚ) (fun _ => ℝ) 0 (fun m _ ih => (m.2 : ℝ) * L ^ m.1 + ih) l

theorem LPoly.eval_nil (L : ℝ) : LPoly.eval L [] = 0 := rfl
theorem LPoly.eval_cons (L : ℝ) (m : ℤ × ℚ) (l : LPoly) :
    LPoly.eval L (m :: l) = (m.2 : ℝ) * L ^ m.1 + LPoly.eval L l := rfl

/-- merge-add (sorted by exponent). Soundness does not depend on sortedness. -/
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

theorem LPoly.eval_add (L : ℝ) (hL : L ≠ 0) (l1 l2 : LPoly) :
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

/-- multiply every term by `q * L^c` -/
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
    rw [LPoly.eval_add L hL, LPoly.eval_mulMono L hL, ih, LPoly.eval_cons]; ring

noncomputable def LPoly.scale (q : ℚ) (l : LPoly) : LPoly :=
  @List.rec (ℤ × ℚ) (fun _ => LPoly) [] (fun m _ ih => (m.1, q * m.2) :: ih) l

theorem LPoly.eval_scale (L : ℝ) (q : ℚ) (l : LPoly) :
    LPoly.eval L (LPoly.scale q l) = (q : ℝ) * LPoly.eval L l := by
  induction l with
  | nil => simp [LPoly.scale, LPoly.eval_nil]
  | cons m t ih =>
    show (((q * m.2 : ℚ)) : ℝ) * L ^ m.1 + LPoly.eval L (LPoly.scale q t) = _
    rw [ih, LPoly.eval_cons]; push_cast; ring

/-! ## SPoly -/

noncomputable def SPoly.eval (σ L : ℝ) (s : SPoly) : ℝ :=
  @List.rec (ℕ × LPoly) (fun _ => ℝ) 0 (fun m _ ih => σ ^ m.1 * LPoly.eval L m.2 + ih) s

theorem SPoly.eval_nil (σ L : ℝ) : SPoly.eval σ L [] = 0 := rfl
theorem SPoly.eval_cons (σ L : ℝ) (m : ℕ × LPoly) (s : SPoly) :
    SPoly.eval σ L (m :: s) = σ ^ m.1 * LPoly.eval L m.2 + SPoly.eval σ L s := rfl

noncomputable def SPoly.add (s1 : SPoly) : SPoly → SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly → SPoly) (fun s2 => s2)
    (fun m1 t1 rec => fun s2 =>
      @List.rec (ℕ × LPoly) (fun _ => SPoly) (m1 :: t1)
        (fun m2 t2 ih =>
          if m1.1 < m2.1 then m1 :: rec (m2 :: t2)
          else if m2.1 < m1.1 then m2 :: ih
          else if LPoly.add m1.2 m2.2 = [] then rec t2
          else (m1.1, LPoly.add m1.2 m2.2) :: rec t2) s2) s1

theorem SPoly.add_nil (s2 : SPoly) : SPoly.add [] s2 = s2 := rfl
theorem SPoly.add_cons_nil (m1 : ℕ × LPoly) (t1 : SPoly) : SPoly.add (m1 :: t1) [] = m1 :: t1 := rfl
theorem SPoly.add_cons_cons (m1 m2 : ℕ × LPoly) (t1 t2 : SPoly) :
    SPoly.add (m1 :: t1) (m2 :: t2) =
      if m1.1 < m2.1 then m1 :: SPoly.add t1 (m2 :: t2)
      else if m2.1 < m1.1 then m2 :: SPoly.add (m1 :: t1) t2
      else if LPoly.add m1.2 m2.2 = [] then SPoly.add t1 t2
      else (m1.1, LPoly.add m1.2 m2.2) :: SPoly.add t1 t2 :=
  rfl

theorem SPoly.eval_add (σ L : ℝ) (hL : L ≠ 0) (s1 s2 : SPoly) :
    SPoly.eval σ L (SPoly.add s1 s2) = SPoly.eval σ L s1 + SPoly.eval σ L s2 := by
  induction s1 generalizing s2 with
  | nil => simp [SPoly.add_nil, SPoly.eval_nil]
  | cons m1 t1 ih1 =>
    induction s2 with
    | nil => simp [SPoly.add_cons_nil, SPoly.eval_nil]
    | cons m2 t2 ih2 =>
      rw [SPoly.add_cons_cons]
      split_ifs with h1 h2 h3
      · rw [SPoly.eval_cons, ih1, SPoly.eval_cons, SPoly.eval_cons]; ring
      · rw [SPoly.eval_cons, ih2]; simp only [SPoly.eval_cons]; ring
      · have he : m1.1 = m2.1 := by omega
        have hz : LPoly.eval L (LPoly.add m1.2 m2.2) = 0 := by rw [h3]; rfl
        rw [LPoly.eval_add L hL] at hz
        rw [ih1, SPoly.eval_cons, SPoly.eval_cons, he]
        linear_combination (-(σ ^ m2.1)) * hz
      · have he : m1.1 = m2.1 := by omega
        rw [SPoly.eval_cons, ih1, SPoly.eval_cons, SPoly.eval_cons, LPoly.eval_add L hL, he]
        ring

/-- multiply every entry by `σ^b * l` (entries whose product is `[]` are dropped). -/
noncomputable def SPoly.mulMono (b : ℕ) (l : LPoly) (s : SPoly) : SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly) []
    (fun m _ ih => if LPoly.mul l m.2 = [] then ih else (b + m.1, LPoly.mul l m.2) :: ih) s

theorem SPoly.eval_mulMono (σ L : ℝ) (hL : L ≠ 0) (b : ℕ) (l : LPoly) (s : SPoly) :
    SPoly.eval σ L (SPoly.mulMono b l s) = σ ^ b * LPoly.eval L l * SPoly.eval σ L s := by
  induction s with
  | nil => simp [SPoly.mulMono, SPoly.eval_nil]
  | cons m t ih =>
    show SPoly.eval σ L
        (if LPoly.mul l m.2 = [] then SPoly.mulMono b l t
         else (b + m.1, LPoly.mul l m.2) :: SPoly.mulMono b l t) = _
    split_ifs with h
    · have hz : LPoly.eval L (LPoly.mul l m.2) = 0 := by rw [h]; rfl
      rw [LPoly.eval_mul L hL] at hz
      rw [ih, SPoly.eval_cons]
      linear_combination (-(σ ^ b * σ ^ m.1)) * hz
    · rw [SPoly.eval_cons, ih, SPoly.eval_cons, LPoly.eval_mul L hL, pow_add]; ring

noncomputable def SPoly.mul (s1 s2 : SPoly) : SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly) [] (fun m _ ih => SPoly.add (SPoly.mulMono m.1 m.2 s2) ih) s1

theorem SPoly.eval_mul (σ L : ℝ) (hL : L ≠ 0) (s1 s2 : SPoly) :
    SPoly.eval σ L (SPoly.mul s1 s2) = SPoly.eval σ L s1 * SPoly.eval σ L s2 := by
  induction s1 with
  | nil => simp [SPoly.mul, SPoly.eval_nil]
  | cons m t ih =>
    show SPoly.eval σ L (SPoly.add (SPoly.mulMono m.1 m.2 s2) (SPoly.mul t s2)) = _
    rw [SPoly.eval_add σ L hL, SPoly.eval_mulMono σ L hL, ih, SPoly.eval_cons]; ring

noncomputable def SPoly.scale (q : ℚ) (s : SPoly) : SPoly :=
  @List.rec (ℕ × LPoly) (fun _ => SPoly) [] (fun m _ ih => (m.1, LPoly.scale q m.2) :: ih) s

theorem SPoly.eval_scale (σ L : ℝ) (q : ℚ) (s : SPoly) :
    SPoly.eval σ L (SPoly.scale q s) = (q : ℝ) * SPoly.eval σ L s := by
  induction s with
  | nil => simp [SPoly.scale, SPoly.eval_nil]
  | cons m t ih =>
    show σ ^ m.1 * LPoly.eval L (LPoly.scale q m.2) + SPoly.eval σ L (SPoly.scale q t) = _
    rw [ih, LPoly.eval_scale, SPoly.eval_cons]; ring

/-! ## TPoly (dense in t) -/

noncomputable def TPoly.eval (t σ L : ℝ) (P : TPoly) : ℝ :=
  @List.rec SPoly (fun _ => ℝ) 0 (fun s _ ih => SPoly.eval σ L s + t * ih) P

theorem TPoly.eval_nil (t σ L : ℝ) : TPoly.eval t σ L [] = 0 := rfl
theorem TPoly.eval_cons (t σ L : ℝ) (s : SPoly) (P : TPoly) :
    TPoly.eval t σ L (s :: P) = SPoly.eval σ L s + t * TPoly.eval t σ L P := rfl

noncomputable def TPoly.add (P1 : TPoly) : TPoly → TPoly :=
  @List.rec SPoly (fun _ => TPoly → TPoly) (fun P2 => P2)
    (fun s1 t1 rec => fun P2 =>
      @List.rec SPoly (fun _ => TPoly) (s1 :: t1)
        (fun s2 t2 _ => SPoly.add s1 s2 :: rec t2) P2) P1

theorem TPoly.add_nil (P2 : TPoly) : TPoly.add [] P2 = P2 := rfl
theorem TPoly.add_cons_nil (s1 : SPoly) (t1 : TPoly) : TPoly.add (s1 :: t1) [] = s1 :: t1 := rfl
theorem TPoly.add_cons_cons (s1 s2 : SPoly) (t1 t2 : TPoly) :
    TPoly.add (s1 :: t1) (s2 :: t2) = SPoly.add s1 s2 :: TPoly.add t1 t2 := rfl

theorem TPoly.eval_add (t σ L : ℝ) (hL : L ≠ 0) (P1 P2 : TPoly) :
    TPoly.eval t σ L (TPoly.add P1 P2) = TPoly.eval t σ L P1 + TPoly.eval t σ L P2 := by
  induction P1 generalizing P2 with
  | nil => simp [TPoly.add_nil, TPoly.eval_nil]
  | cons s1 t1 ih =>
    cases P2 with
    | nil => simp [TPoly.add_cons_nil, TPoly.eval_nil]
    | cons s2 t2 =>
      rw [TPoly.add_cons_cons, TPoly.eval_cons, TPoly.eval_cons, TPoly.eval_cons, ih,
        SPoly.eval_add σ L hL]
      ring

noncomputable def TPoly.scale (q : ℚ) (P : TPoly) : TPoly :=
  @List.rec SPoly (fun _ => TPoly) [] (fun s _ ih => SPoly.scale q s :: ih) P

theorem TPoly.eval_scale (t σ L : ℝ) (q : ℚ) (P : TPoly) :
    TPoly.eval t σ L (TPoly.scale q P) = (q : ℝ) * TPoly.eval t σ L P := by
  induction P with
  | nil => simp [TPoly.scale, TPoly.eval_nil]
  | cons s P ih =>
    show SPoly.eval σ L (SPoly.scale q s) + t * TPoly.eval t σ L (TPoly.scale q P) = _
    rw [ih, SPoly.eval_scale, TPoly.eval_cons]; ring

/-- `s * P`, keeping only the first `k` t-coefficients. -/
noncomputable def TPoly.scaleSTake (s : SPoly) (P : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun p _ ih => fun k => Nat.rec (motive := fun _ => TPoly) []
      (fun k' _ => SPoly.mul s p :: ih k') k) P

/-- truncated product: t-coefficients of index `< n` of `P * Q`. -/
noncomputable def TPoly.mulT (P Q : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s _ ih => fun n => Nat.rec (motive := fun _ => TPoly) []
      (fun n' _ => TPoly.add (TPoly.scaleSTake s Q (n' + 1)) ([] :: ih n')) n) P

/-- `t`-coefficient list truncation (first `k` entries). -/
noncomputable def TPoly.take (P : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s _ ih => fun k => Nat.rec (motive := fun _ => TPoly) [] (fun k' _ => s :: ih k') k) P

noncomputable def TPoly.drop (P : TPoly) : ℕ → TPoly :=
  @List.rec SPoly (fun _ => ℕ → TPoly) (fun _ => [])
    (fun s P' ih => fun k => Nat.rec (motive := fun _ => TPoly) (s :: P') (fun k' _ => ih k') k) P

theorem TPoly.take_nil (k : ℕ) : TPoly.take [] k = [] := rfl
theorem TPoly.take_zero (P : TPoly) : TPoly.take P 0 = [] := by cases P <;> rfl
theorem TPoly.take_cons_succ (s : SPoly) (P : TPoly) (k : ℕ) :
    TPoly.take (s :: P) (k + 1) = s :: TPoly.take P k := rfl
theorem TPoly.drop_nil (k : ℕ) : TPoly.drop [] k = [] := rfl
theorem TPoly.drop_zero (P : TPoly) : TPoly.drop P 0 = P := by cases P <;> rfl
theorem TPoly.drop_cons_succ (s : SPoly) (P : TPoly) (k : ℕ) :
    TPoly.drop (s :: P) (k + 1) = TPoly.drop P k := rfl

theorem TPoly.eval_take_drop (t σ L : ℝ) (P : TPoly) (k : ℕ) :
    TPoly.eval t σ L P = TPoly.eval t σ L (TPoly.take P k) + t ^ k * TPoly.eval t σ L (TPoly.drop P k) := by
  induction P generalizing k with
  | nil => simp [TPoly.take_nil, TPoly.drop_nil, TPoly.eval_nil]
  | cons s P ih =>
    cases k with
    | zero => simp [TPoly.take_zero, TPoly.drop_zero, TPoly.eval_nil]
    | succ k =>
      rw [TPoly.take_cons_succ, TPoly.drop_cons_succ, TPoly.eval_cons, TPoly.eval_cons, ih k]
      ring

end CKLaneA3X


