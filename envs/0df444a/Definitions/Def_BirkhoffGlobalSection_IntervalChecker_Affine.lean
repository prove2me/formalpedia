-- Prove2me | Definitions.Def_BirkhoffGlobalSection_IntervalChecker_Affine
-- name    : BirkhoffGlobalSection_IntervalChecker_Affine
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-01T08:17:59.126993+00:00
-- url     : https://prove2.me/theorems/af014359-89c8-4430-bc88-9eb6ba2a4a94
-- title:
--   Affine arithmetic over exact checker scalars
-- statement:
--   Affine forms $a+\sum_k b_k d_k\pm e$ over the exact scalars of `BirkhoffGlobalSection_IntervalChecker` (noise point $d$ with $|d_k|\le 1$): constants, box variables, sums, scalings and products (the quadratic part moved into the error), each proved to represent the corresponding real operation at the same noise point (`rep_add`, `rep_scal`, `rep_mul`, ...), and `mem_range` turning a form into an interval. Dense polynomials are evaluated in affine arithmetic by Horner's rule; after the exact Taylor shift this gives the affine form of a polynomial on a box (`rep_shiftNP`). Everything is computable and kernel-reducible.
-- source:
--   Joung–van Koert, https://arxiv.org/abs/2407.19159v3, Proposition 4.4 (tangential Hessian); gate form via the block Hessian of Grisa 2026 (Thm 3.7(b)). Certificate: numerics/phase4_D/gen_gate_cert_tmx.py (exact emulator), Lean files by gen_gate_lean.py / gen_gate_platform.py.

import Definitions.Def_BirkhoffGlobalSection_IntervalChecker_Dense

/-!
# Affine arithmetic over exact checker scalars

An *affine form* `⟨a, b, e⟩` over the checker scalars `α` stands for the set of reals
`a + Σₖ bₖ dₖ + ε` with `|ε| ≤ e`, where `d = (d₀, d₁, …)` is a *noise point*, `|dₖ| ≤ 1`.
A box `∏ [cₖ - hₖ, cₖ + hₖ]` is parametrized by `xₖ = cₖ + hₖ dₖ`, so every box variable is an affine
form (`AF.var`). Sums, scalings and products of affine forms (`AF.add`, `AF.scal`, `AF.mul`) represent
the sums, scalings and products of the represented reals **at the same noise point**; the product
moves its quadratic part into the error. `AF.range` turns a form into an interval (`Iv`) for the
branch-and-bound checker `check_sound`.

Dense polynomials (`NP`) are evaluated in affine arithmetic by Horner's rule (`AF.evalNP`). Combined
with the exact Taylor shift `NP.shift`, evaluating at the *centred* box variables `hₖ dₖ` gives the exact
constant and linear Taylor coefficients of a polynomial at the box centre, with all higher-order terms
bounded in the error (`rep_shiftNP`): the affine form of a polynomial on a box.

All operations are exact (no rounding) and defined by structural recursion, so they reduce in the
kernel (`decide +kernel`). Soundness is `Rep` preservation: `rep_var`, `rep_const`, `rep_add`,
`rep_neg`, `rep_sub`, `rep_scal`, `rep_mul`, and `mem_range`.

Affine arithmetic: Comba–Stolfi, *Affine arithmetic and its applications to computer graphics*
(SIBGRAPI 1993); de Figueiredo–Stolfi, Numerical Algorithms 37 (2004) 147–158.
-/

namespace BirkhoffGlobalSection.TangentialHessian.Checker

open CNum

variable {α : Type} [CNum α]

namespace CNum

/-- `|a|`. -/
def aabs (a : α) : α := amax a (neg a)

@[simp] theorem toReal_aabs (a : α) : toReal (aabs a) = |toReal a| := by
  simp [aabs, abs_eq_max_neg]

end CNum

/-- An affine form `a + Σₖ bₖ dₖ ± e`. -/
structure AF (α : Type) where
  a : α
  b : List α
  e : α

namespace AF

/-- Pointwise sum of coefficient lists, the shorter padded with zeros. -/
def zipAdd : List α → List α → List α
  | x :: xs, y :: ys => CNum.add x y :: zipAdd xs ys
  | [], ys => ys
  | xs, [] => xs

/-- `Σ |bₖ|`. -/
def sumAbs : List α → α
  | [] => zero
  | x :: xs => CNum.add (aabs x) (sumAbs xs)

/-- The radius `Σ |bₖ| + e`: every represented value lies within it of the centre `a`. -/
def rad (A : AF α) : α := CNum.add (sumAbs A.b) A.e

/-- The constant `q`. -/
def const (q : α) : AF α := ⟨q, [], zero⟩

/-- The box variable `c + h dₖ` (noise symbol number `k`). -/
def var (k : ℕ) (c h : α) : AF α := ⟨c, List.replicate k zero ++ [h], zero⟩

def add (A B : AF α) : AF α := ⟨CNum.add A.a B.a, zipAdd A.b B.b, CNum.add A.e B.e⟩

def neg (A : AF α) : AF α := ⟨CNum.neg A.a, A.b.map CNum.neg, A.e⟩

def sub (A B : AF α) : AF α := add A (neg B)

/-- `q · A` for a scalar `q`. -/
def scal (q : α) (A : AF α) : AF α := ⟨CNum.mul q A.a, A.b.map (CNum.mul q), CNum.mul (aabs q) A.e⟩

/-- Product: exact constant and linear parts, the quadratic part `(A - a₁)(B - a₂)` and the cross terms
with the errors go into the new error `|a₁| e₂ + |a₂| e₁ + rad A · rad B`. -/
def mul (A B : AF α) : AF α :=
  ⟨CNum.mul A.a B.a, zipAdd (A.b.map (CNum.mul B.a)) (B.b.map (CNum.mul A.a)),
    CNum.add (CNum.add (CNum.mul (aabs A.a) B.e) (CNum.mul (aabs B.a) A.e)) (CNum.mul (rad A) (rad B))⟩

/-- The enclosing interval `[a - rad, a + rad]`. -/
def range (A : AF α) : Iv α := (CNum.sub A.a (rad A), CNum.add A.a (rad A))

/-! ### Semantics -/

/-- The real linear part `Σₖ bₖ dₖ` (over the common length). -/
noncomputable def lin : List α → List ℝ → ℝ
  | x :: xs, t :: ts => toReal x * t + lin xs ts
  | _, _ => 0

/-- A noise point: every coordinate in `[-1, 1]`. -/
def Noise (d : List ℝ) : Prop := ∀ t ∈ d, |t| ≤ 1

/-- `A` represents the real `x` at the noise point `d`. -/
def Rep (d : List ℝ) (A : AF α) (x : ℝ) : Prop := |x - (toReal A.a + lin A.b d)| ≤ toReal A.e

@[simp] theorem lin_nil_left (d : List ℝ) : lin ([] : List α) d = 0 := by cases d <;> rfl

@[simp] theorem lin_nil_right (b : List α) : lin b [] = 0 := by cases b <;> rfl

theorem lin_zipAdd (b c : List α) (d : List ℝ) : lin (zipAdd b c) d = lin b d + lin c d := by
  induction b generalizing c d with
  | nil => cases c <;> simp [zipAdd]
  | cons x xs ih =>
    cases c with
    | nil => simp [zipAdd]
    | cons y ys =>
      cases d with
      | nil => simp [zipAdd]
      | cons t ts => simp only [zipAdd, lin, toReal_add, ih]; ring

theorem lin_map_mul (q : α) (b : List α) (d : List ℝ) :
    lin (b.map (CNum.mul q)) d = toReal q * lin b d := by
  induction b generalizing d with
  | nil => simp
  | cons x xs ih =>
    cases d with
    | nil => simp
    | cons t ts => simp only [List.map_cons, lin, toReal_mul, ih]; ring

theorem lin_map_neg (b : List α) (d : List ℝ) : lin (b.map CNum.neg) d = -lin b d := by
  induction b generalizing d with
  | nil => simp
  | cons x xs ih =>
    cases d with
    | nil => simp
    | cons t ts => simp only [List.map_cons, lin, toReal_neg, ih]; ring

theorem sumAbs_nonneg (b : List α) : 0 ≤ toReal (sumAbs b) := by
  induction b with
  | nil => simp [sumAbs]
  | cons x xs ih => simp only [sumAbs, toReal_add, toReal_aabs]; positivity

theorem abs_lin_le {d : List ℝ} (hd : Noise d) (b : List α) : |lin b d| ≤ toReal (sumAbs b) := by
  induction b generalizing d with
  | nil => simp [sumAbs]
  | cons x xs ih =>
    cases d with
    | nil => simpa using sumAbs_nonneg (x :: xs)
    | cons t ts =>
      have ht : |t| ≤ 1 := hd t (List.mem_cons_self ..)
      have hts : Noise ts := fun s hs => hd s (List.mem_cons_of_mem _ hs)
      simp only [lin, sumAbs, toReal_add, toReal_aabs]
      calc |toReal x * t + lin xs ts| ≤ |toReal x * t| + |lin xs ts| := abs_add_le _ _
        _ ≤ |toReal x| + toReal (sumAbs xs) := by
          rw [abs_mul]
          gcongr
          · nlinarith [abs_nonneg (toReal x)]
          · exact ih hts

theorem lin_var (k : ℕ) (h : α) (d : List ℝ) :
    lin (List.replicate k zero ++ [h]) d = toReal h * d.getD k 0 := by
  induction k generalizing d with
  | zero => cases d <;> simp [lin]
  | succ k ih =>
    cases d with
    | nil => simp
    | cons t ts => simp [List.replicate_succ, lin, ih]

/-! ### Soundness -/

theorem rep_const (d : List ℝ) (q : α) : Rep d (const q) (toReal q) := by simp [Rep, const]

theorem rep_var (d : List ℝ) (k : ℕ) (c h : α) :
    Rep d (var k c h) (toReal c + toReal h * d.getD k 0) := by
  simp [Rep, var, lin_var]

theorem rep_add {d : List ℝ} {A B : AF α} {x y : ℝ} (hA : Rep d A x) (hB : Rep d B y) :
    Rep d (add A B) (x + y) := by
  unfold Rep at *
  simp only [add, toReal_add, lin_zipAdd]
  calc |x + y - (toReal A.a + toReal B.a + (lin A.b d + lin B.b d))|
      = |(x - (toReal A.a + lin A.b d)) + (y - (toReal B.a + lin B.b d))| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hA hB

theorem rep_neg {d : List ℝ} {A : AF α} {x : ℝ} (hA : Rep d A x) : Rep d (neg A) (-x) := by
  unfold Rep at *
  simp only [neg, toReal_neg, lin_map_neg]
  rw [show -x - (-toReal A.a + -lin A.b d) = -(x - (toReal A.a + lin A.b d)) by ring, abs_neg]
  exact hA

theorem rep_sub {d : List ℝ} {A B : AF α} {x y : ℝ} (hA : Rep d A x) (hB : Rep d B y) :
    Rep d (sub A B) (x - y) := by
  simpa [sub, sub_eq_add_neg] using rep_add hA (rep_neg hB)

theorem rep_scal {d : List ℝ} (q : α) {A : AF α} {x : ℝ} (hA : Rep d A x) :
    Rep d (scal q A) (toReal q * x) := by
  unfold Rep at *
  simp only [scal, toReal_mul, toReal_aabs, lin_map_mul]
  rw [show toReal q * x - (toReal q * toReal A.a + toReal q * lin A.b d)
      = toReal q * (x - (toReal A.a + lin A.b d)) by ring, abs_mul]
  exact mul_le_mul_of_nonneg_left hA (abs_nonneg _)

theorem rep_mul {d : List ℝ} (hd : Noise d) {A B : AF α} {x y : ℝ} (hA : Rep d A x) (hB : Rep d B y) :
    Rep d (mul A B) (x * y) := by
  unfold Rep at *
  simp only [mul, rad, toReal_add, toReal_mul, toReal_aabs, lin_zipAdd, lin_map_mul]
  set a₁ := toReal A.a
  set a₂ := toReal B.a
  set L₁ := lin A.b d
  set L₂ := lin B.b d
  set u := x - (a₁ + L₁) with hu
  set v := y - (a₂ + L₂) with hv
  have hL₁ := abs_lin_le hd A.b
  have hL₂ := abs_lin_le hd B.b
  have e₁ : x * y - (a₁ * a₂ + (a₂ * L₁ + a₁ * L₂)) = a₁ * v + a₂ * u + (L₁ + u) * (L₂ + v) := by
    rw [hu, hv]; ring
  have h₁ : |L₁ + u| ≤ toReal (sumAbs A.b) + toReal A.e :=
    (abs_add_le _ _).trans (add_le_add hL₁ hA)
  have h₂ : |L₂ + v| ≤ toReal (sumAbs B.b) + toReal B.e :=
    (abs_add_le _ _).trans (add_le_add hL₂ hB)
  rw [e₁]
  calc |a₁ * v + a₂ * u + (L₁ + u) * (L₂ + v)|
      ≤ |a₁ * v| + |a₂ * u| + |(L₁ + u) * (L₂ + v)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ = |a₁| * |v| + |a₂| * |u| + |L₁ + u| * |L₂ + v| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ |a₁| * toReal B.e + |a₂| * toReal A.e
          + (toReal (sumAbs A.b) + toReal A.e) * (toReal (sumAbs B.b) + toReal B.e) := by
        gcongr
        exact (abs_nonneg _).trans h₁

/-- The represented value lies in `range A`. -/
theorem mem_range {d : List ℝ} (hd : Noise d) {A : AF α} {x : ℝ} (hA : Rep d A x) :
    Mem x (range A) := by
  unfold Rep at hA
  have hL := abs_lin_le hd A.b
  have h := (abs_sub_abs_le_abs_sub x (toReal A.a))
  unfold Mem range rad
  simp only [toReal_sub, toReal_add]
  constructor
  · have := neg_abs_le (x - (toReal A.a + lin A.b d))
    have := neg_abs_le (lin A.b d)
    linarith
  · have := le_abs_self (x - (toReal A.a + lin A.b d))
    have := le_abs_self (lin A.b d)
    linarith

/-! ### Dense polynomials in affine arithmetic -/

/-- Horner's rule `v₀ + X (v₁ + X (v₂ + …))`. -/
def horner (X : AF α) : List (AF α) → AF α
  | [] => const zero
  | v :: vs => add v (mul X (horner X vs))

/-- Affine evaluation of a dense polynomial at affine forms `Xs` (one per variable). -/
def evalNP : (n : ℕ) → NP α n → List (AF α) → AF α
  | 0, c, _ => const (c : α)
  | n + 1, cs, X :: Xs => horner X ((cs : List (NP α n)).map (fun c => evalNP n c Xs))
  | _ + 1, _, [] => const zero

theorem rep_zero (d : List ℝ) : Rep d (const (zero : α)) 0 := by
  simpa using rep_const (α := α) d zero

theorem rep_horner {d : List ℝ} (hd : Noise d) {X : AF α} {x : ℝ} (hX : Rep d X x) :
    ∀ (vs : List (AF α)) (ws : List ℝ), List.Forall₂ (Rep d) vs ws →
      Rep d (horner X vs) (NP.sumPowR x 0 ws)
  | [], [], _ => by simpa [horner, NP.sumPowR] using rep_zero (α := α) d
  | v :: vs, w :: ws, .cons hv hrest => by
    have h := rep_add hv (rep_mul hd hX (rep_horner hd hX vs ws hrest))
    simpa [horner, NP.sumPowR, NP.sumPowR_succ] using h

/-- Affine evaluation of a dense polynomial represents its real value. -/
theorem rep_evalNP {d : List ℝ} (hd : Noise d) :
    ∀ (n : ℕ) (p : NP α n) (Xs : List (AF α)) (xs : List ℝ), List.Forall₂ (Rep d) Xs xs →
      Rep d (evalNP n p Xs) (NP.eval n p xs)
  | 0, c, _, _, _ => by simpa [evalNP, NP.eval] using rep_const (α := α) d c
  | _ + 1, _, [], [], _ => by simpa [evalNP, NP.eval] using rep_zero (α := α) d
  | n + 1, cs, X :: Xs, x :: xs, .cons hX hrest => by
    simp only [evalNP, NP.eval]
    refine rep_horner hd hX _ _ ?_
    induction (cs : List (NP α n)) with
    | nil => exact List.Forall₂.nil
    | cons c cs ih => exact List.Forall₂.cons (rep_evalNP hd n c Xs xs hrest) ih

/-- **Affine form of a polynomial on a box.** If the `Xs` represent the offsets `ts` from the box
centre `M`, the affine Horner evaluation of the Taylor-shifted polynomial represents `p` at `M + ts`. -/
theorem rep_shiftNP {d : List ℝ} (hd : Noise d) (n : ℕ) (M : List α) (p : NP α n) (Xs : List (AF α))
    (ts : List ℝ) (hX : List.Forall₂ (Rep d) Xs ts) (hM : M.length = n) (ht : ts.length = n) :
    Rep d (evalNP n (NP.shift n M p) Xs) (NP.eval n p (NP.addPt M ts)) := by
  rw [← NP.eval_shift n M p ts hM ht]
  exact rep_evalNP hd n _ Xs ts hX

end AF

end BirkhoffGlobalSection.TangentialHessian.Checker


