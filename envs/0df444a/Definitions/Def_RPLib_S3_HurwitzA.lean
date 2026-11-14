-- Prove2me | Definitions.Def_RPLib_S3_HurwitzA
-- name    : RPLib_S3_HurwitzA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:51:37.233017+00:00
-- url     : https://prove2.me/theorems/cec92332-ce34-4382-aeb5-395262175e46
-- title:
--   Binary quadratic forms: reduction theory
-- statement:
--   Integral binary quadratic forms $f = [a, b, c]$, their discriminant, content, positive definiteness and the right action of $SL_2(\mathbb{Z})$ by substitution. Every positive definite form is equivalent to a reduced form ($|b| \le a \le c$, and $b \ge 0$ if $|b| = a$ or $a = c$), and two equivalent reduced forms are equal.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. A. Buell, Binary Quadratic Forms: Classical Theory and Modern Computations, Springer 1989, Chapter 2

import Mathlib

/-!
# Binary quadratic forms and reduction theory (RP project, unit S3-Hurwitz, part A)

Pure Mathlib (Mathlib has no binary quadratic forms).

* `BQF`: integral binary quadratic forms `a x² + b x y + c y²`; `disc`, `eval`, `PosDef`, `content`,
  `IsPrimitive`, `IsReduced` (all decidable).
* `act γ f = f ∘ γ` (substitution `(x, y) ↦ (p x + q y, r x + s y)` for `γ = [[p, q], [r, s]]`), a right
  action: `act (γ * δ) f = act δ (act γ f)`. It matches conjugation: the form `[c, d - a, -b]` of
  `γ = [[a, b], [c, d]]` is `v ↦ det [v, γ v]`, so the form of `g⁻¹ γ g` is `act g` of the form of `γ`.
  The left `MulAction SL(2, ℤ) BQF` is `γ • f = act γ⁻¹ f` (same orbits and stabilizers).
* Invariance of `disc`, `PosDef`, `content`, `IsPrimitive`.
* Reduction: every positive definite form is equivalent to a reduced one (`exists_act_isReduced`), and two
  equivalent reduced forms are equal (`IsReduced.eq_of_mem_orbit`).
* Finiteness: the reduced forms of discriminant `D` are the explicit finset `reducedForms D`.
* Stabilizers of reduced forms have order 2, 4 (`[a, 0, a]`) or 6 (`[a, a, a]`)
  (`card_stabilizer_of_isReduced`).
-/

set_option autoImplicit false

namespace RamanujanPetersson.Hurwitz

open Matrix MatrixGroups

/-- An integral binary quadratic form `a x² + b x y + c y²`. -/
@[ext] structure BQF where
  /-- coefficient of `x²` -/
  a : ℤ
  /-- coefficient of `x y` -/
  b : ℤ
  /-- coefficient of `y²` -/
  c : ℤ
  deriving DecidableEq

namespace BQF

/-- The discriminant `b² - 4 a c`. -/
def disc (f : BQF) : ℤ := f.b ^ 2 - 4 * f.a * f.c

/-- The value `a x² + b x y + c y²`. -/
def eval (f : BQF) (x y : ℤ) : ℤ := f.a * x ^ 2 + f.b * x * y + f.c * y ^ 2

/-- Positive definite: `a > 0` and negative discriminant (equivalently, positive at every nonzero
vector, `posDef_iff`). -/
def PosDef (f : BQF) : Prop := 0 < f.a ∧ f.disc < 0

instance (f : BQF) : Decidable f.PosDef := inferInstanceAs (Decidable (_ ∧ _))

/-- The content `gcd(a, b, c)`. -/
def content (f : BQF) : ℕ := Int.gcd f.a (Int.gcd f.b f.c)

/-- Primitive: `gcd(a, b, c) = 1`. -/
def IsPrimitive (f : BQF) : Prop := f.content = 1

instance (f : BQF) : Decidable f.IsPrimitive := inferInstanceAs (Decidable (_ = _))

/-- Reduced (with the boundary conventions): `|b| ≤ a ≤ c`, `b ≠ -a`, and `b ≥ 0` if `a = c`. -/
def IsReduced (f : BQF) : Prop := -f.a < f.b ∧ f.b ≤ f.a ∧ f.a ≤ f.c ∧ (f.a = f.c → 0 ≤ f.b)

instance (f : BQF) : Decidable f.IsReduced := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → _)))

/-- Substitution `(x, y) ↦ (p x + q y, r x + s y)`. -/
def subst (f : BQF) (p q r s : ℤ) : BQF :=
  ⟨f.a * p ^ 2 + f.b * p * r + f.c * r ^ 2,
   2 * f.a * p * q + f.b * (p * s + q * r) + 2 * f.c * r * s,
   f.a * q ^ 2 + f.b * q * s + f.c * s ^ 2⟩

/-! ### Sanity lemmas for the definitions -/

theorem disc_sanity : (⟨1, 1, 1⟩ : BQF).disc = -3 ∧ (⟨1, 0, 1⟩ : BQF).disc = -4 ∧
    (⟨2, 1, 3⟩ : BQF).disc = -23 := by decide

theorem eval_sanity : (⟨1, 1, 1⟩ : BQF).eval 2 (-1) = 3 := by decide

theorem posDef_sanity : (⟨1, 0, 1⟩ : BQF).PosDef ∧ ¬ (⟨1, 0, -1⟩ : BQF).PosDef ∧
    ¬ (⟨-1, 0, -1⟩ : BQF).PosDef := by decide

theorem isPrimitive_sanity : (⟨2, 1, 3⟩ : BQF).IsPrimitive ∧ ¬ (⟨2, 2, 2⟩ : BQF).IsPrimitive ∧
    (⟨2, 2, 2⟩ : BQF).content = 2 := by decide

theorem isReduced_sanity : (⟨1, 1, 1⟩ : BQF).IsReduced ∧ (⟨2, -1, 3⟩ : BQF).IsReduced ∧
    ¬ (⟨1, -1, 1⟩ : BQF).IsReduced ∧ ¬ (⟨2, -1, 2⟩ : BQF).IsReduced ∧
    ¬ (⟨3, 1, 2⟩ : BQF).IsReduced := by decide

theorem subst_sanity : (⟨1, 0, 1⟩ : BQF).subst 0 (-1) 1 0 = ⟨1, 0, 1⟩ ∧
    (⟨2, 1, 3⟩ : BQF).subst 1 1 0 1 = ⟨2, 5, 6⟩ := by decide

/-! ### Basic identities -/

variable (f : BQF)

@[simp] theorem eval_one_zero : f.eval 1 0 = f.a := by simp [eval]

@[simp] theorem eval_zero_one : f.eval 0 1 = f.c := by simp [eval]

theorem four_a_mul_eval (x y : ℤ) :
    4 * f.a * f.eval x y = (2 * f.a * x + f.b * y) ^ 2 - f.disc * y ^ 2 := by
  simp only [eval, disc]; ring

theorem four_c_mul_eval (x y : ℤ) :
    4 * f.c * f.eval x y = (2 * f.c * y + f.b * x) ^ 2 - f.disc * x ^ 2 := by
  simp only [eval, disc]; ring

/-- A discriminant is `0` or `1` mod `4`. -/
theorem disc_emod_four : f.disc % 4 = 0 ∨ f.disc % 4 = 1 := by
  rcases Int.even_or_odd f.b with ⟨k, hk⟩ | ⟨k, hk⟩
  · obtain ⟨X, hX⟩ : ∃ X, f.disc = 4 * X := ⟨k ^ 2 - f.a * f.c, by simp only [disc, hk]; ring⟩
    omega
  · obtain ⟨X, hX⟩ : ∃ X, f.disc = 4 * X + 1 :=
      ⟨k ^ 2 + k - f.a * f.c, by simp only [disc, hk]; ring⟩
    omega

theorem one_le_sq {x : ℤ} (hx : x ≠ 0) : 1 ≤ x ^ 2 := by
  have : 0 < x ^ 2 := by positivity
  omega

/-- Positive definiteness is positivity at every nonzero vector. -/
theorem posDef_iff : f.PosDef ↔ ∀ x y : ℤ, (x ≠ 0 ∨ y ≠ 0) → 0 < f.eval x y := by
  constructor
  · rintro ⟨ha, hD⟩ x y hxy
    by_cases hy : y = 0
    · subst hy
      have hx : x ≠ 0 := by tauto
      have := one_le_sq hx
      simp only [eval]; nlinarith
    · have hy2 := one_le_sq hy
      have h := f.four_a_mul_eval x y
      have h2 : 0 < 4 * f.a * f.eval x y := by
        rw [h]; nlinarith [sq_nonneg (2 * f.a * x + f.b * y)]
      nlinarith
  · intro h
    have ha : 0 < f.a := by simpa using h 1 0 (by simp)
    refine ⟨ha, ?_⟩
    by_contra hD
    push_neg at hD
    have h1 := h (-f.b) (2 * f.a) (Or.inr (by positivity))
    have h2 := f.four_a_mul_eval (-f.b) (2 * f.a)
    nlinarith [mul_pos ha h1, mul_nonneg (sq_nonneg f.a) hD]

theorem content_dvd_a : (f.content : ℤ) ∣ f.a := Int.gcd_dvd_left _ _

theorem content_dvd_b : (f.content : ℤ) ∣ f.b :=
  (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)

theorem content_dvd_c : (f.content : ℤ) ∣ f.c :=
  (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)

theorem dvd_content {d : ℕ} (ha : (d : ℤ) ∣ f.a) (hb : (d : ℤ) ∣ f.b) (hc : (d : ℤ) ∣ f.c) :
    d ∣ f.content :=
  Int.dvd_gcd ha (Int.natCast_dvd_natCast.2 (Int.dvd_gcd hb hc))

theorem dvd_subst {d : ℤ} (ha : d ∣ f.a) (hb : d ∣ f.b) (hc : d ∣ f.c) (p q r s : ℤ) :
    d ∣ (f.subst p q r s).a ∧ d ∣ (f.subst p q r s).b ∧ d ∣ (f.subst p q r s).c := by
  refine ⟨?_, ?_, ?_⟩
  · exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hb _) _)) (dvd_mul_of_dvd_left hc _)
  · exact dvd_add (dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ha _) _) _)
      (dvd_mul_of_dvd_left hb _))
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hc _) _) _)
  · exact dvd_add (dvd_add (dvd_mul_of_dvd_left ha _)
      (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hb _) _)) (dvd_mul_of_dvd_left hc _)

/-! ### Reduced forms: inequalities -/

variable {f}

theorem IsReduced.a_pos (hf : f.IsReduced) : 0 < f.a := by
  obtain ⟨h1, h2, -, -⟩ := hf; omega

theorem IsReduced.c_pos (hf : f.IsReduced) : 0 < f.c := by
  have := hf.a_pos; obtain ⟨-, -, h3, -⟩ := hf; omega

theorem IsReduced.disc_neg (hf : f.IsReduced) : f.disc < 0 := by
  have ha := hf.a_pos
  obtain ⟨h1, h2, h3, -⟩ := hf
  simp only [disc]
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℤ) ≤ f.a + f.b),
    mul_le_mul_of_nonneg_left h3 ha.le]

theorem IsReduced.posDef (hf : f.IsReduced) : f.PosDef := ⟨hf.a_pos, hf.disc_neg⟩

/-- For a reduced form and `x, y ≠ 0`: `f(x, y) ≥ a + c - |b|`. -/
theorem IsReduced.add_sub_abs_le_eval (hf : f.IsReduced) {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    f.a + f.c - |f.b| ≤ f.eval x y := by
  have ha := hf.a_pos
  obtain ⟨h1, h2, h3, -⟩ := hf
  have hu : 1 ≤ |x| := Int.one_le_abs hx
  have hv : 1 ≤ |y| := Int.one_le_abs hy
  have hb : |f.b| ≤ f.a := abs_le.2 ⟨by omega, h2⟩
  have hbxy : -(|f.b| * (|x| * |y|)) ≤ f.b * x * y := by
    have h' : |f.b * x * y| = |f.b| * (|x| * |y|) := by rw [abs_mul, abs_mul, mul_assoc]
    linarith [neg_abs_le (f.b * x * y)]
  have hxy1 : 1 ≤ |x| * |y| := by nlinarith
  have key : 0 ≤ f.a * (|x| ^ 2 - |x| * |y| + |y| ^ 2 - 1) := by
    apply mul_nonneg ha.le
    nlinarith [sq_nonneg (|x| - |y|)]
  have key2 : 0 ≤ (f.c - f.a) * (|y| ^ 2 - 1) := by
    apply mul_nonneg (by linarith)
    nlinarith
  have key3 : 0 ≤ (f.a - |f.b|) * (|x| * |y| - 1) := mul_nonneg (by linarith) (by linarith)
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  have hy2 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
  simp only [eval]
  rw [hx2, hy2]
  nlinarith

theorem IsReduced.c_le_eval (hf : f.IsReduced) {x y : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) :
    f.c ≤ f.eval x y := by
  have h := hf.add_sub_abs_le_eval hx hy
  have hb : |f.b| ≤ f.a := abs_le.2 ⟨by have := hf.1; omega, hf.2.1⟩
  linarith

/-- `a` is the minimum of a reduced form on nonzero vectors. -/
theorem IsReduced.a_le_eval (hf : f.IsReduced) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    f.a ≤ f.eval x y := by
  have ha := hf.a_pos
  have hac := hf.2.2.1
  by_cases hx : x = 0
  · subst hx
    have hy : y ≠ 0 := by tauto
    have := one_le_sq hy
    simp only [eval]; nlinarith
  · by_cases hy : y = 0
    · subst hy
      have := one_le_sq hx
      simp only [eval]; nlinarith
    · exact hac.trans (hf.c_le_eval hx hy)

/-- If a reduced form takes the value `a` at `(p, r)` with `r ≠ 0`, then `c = a`. -/
theorem IsReduced.c_eq_a_of_eval (hf : f.IsReduced) {p r : ℤ} (hr : r ≠ 0) (h : f.eval p r = f.a) :
    f.c = f.a := by
  have ha := hf.a_pos
  have hac := hf.2.2.1
  by_cases hp : p = 0
  · subst hp
    have h1 := one_le_sq hr
    simp only [eval] at h
    have hc := hf.c_pos
    exact le_antisymm (by nlinarith) hac
  · have := hf.c_le_eval hp hr
    omega

end BQF

open BQF

/-! ### The action of `SL(2, ℤ)` -/

/-- The right action by substitution: `(act γ f) (x, y) = f (γ (x, y))`. -/
def act (γ : SL(2, ℤ)) (f : BQF) : BQF := f.subst (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

theorem det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

theorem inv_apply_00 (γ : SL(2, ℤ)) : (γ⁻¹) 0 0 = γ 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_apply_01 (γ : SL(2, ℤ)) : (γ⁻¹) 0 1 = -γ 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_apply_10 (γ : SL(2, ℤ)) : (γ⁻¹) 1 0 = -γ 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_apply_11 (γ : SL(2, ℤ)) : (γ⁻¹) 1 1 = γ 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem eval_act (γ : SL(2, ℤ)) (f : BQF) (x y : ℤ) :
    (act γ f).eval x y = f.eval (γ 0 0 * x + γ 0 1 * y) (γ 1 0 * x + γ 1 1 * y) := by
  simp only [act, subst, eval]; ring

theorem act_a (γ : SL(2, ℤ)) (f : BQF) : (act γ f).a = f.eval (γ 0 0) (γ 1 0) := rfl

theorem act_c (γ : SL(2, ℤ)) (f : BQF) : (act γ f).c = f.eval (γ 0 1) (γ 1 1) := rfl

theorem disc_act (γ : SL(2, ℤ)) (f : BQF) : (act γ f).disc = f.disc := by
  have h := det_eq γ
  simp only [act, subst, disc]
  linear_combination (γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 + 1) * (f.b ^ 2 - 4 * f.a * f.c) * h

theorem act_mul (γ δ : SL(2, ℤ)) (f : BQF) : act (γ * δ) f = act δ (act γ f) := by
  simp only [act, subst, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    BQF.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

@[simp] theorem act_one (f : BQF) : act 1 f = f := by
  ext <;> simp [act, subst]

theorem act_inv_act (γ : SL(2, ℤ)) (f : BQF) : act γ⁻¹ (act γ f) = f := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem act_act_inv (γ : SL(2, ℤ)) (f : BQF) : act γ (act γ⁻¹ f) = f := by
  rw [← act_mul, inv_mul_cancel, act_one]

/-- The left action `γ • f = act γ⁻¹ f`. -/
instance : MulAction SL(2, ℤ) BQF where
  smul γ f := act γ⁻¹ f
  one_smul f := by show act 1⁻¹ f = f; rw [inv_one, act_one]
  mul_smul γ δ f := by show act (γ * δ)⁻¹ f = act γ⁻¹ (act δ⁻¹ f); rw [_root_.mul_inv_rev, act_mul]

theorem smul_def (γ : SL(2, ℤ)) (f : BQF) : γ • f = act γ⁻¹ f := rfl

theorem act_eq_smul (γ : SL(2, ℤ)) (f : BQF) : act γ f = γ⁻¹ • f := by
  rw [smul_def, inv_inv]

theorem mem_orbit_iff_act (f g : BQF) :
    g ∈ MulAction.orbit SL(2, ℤ) f ↔ ∃ γ : SL(2, ℤ), act γ f = g := by
  constructor
  · rintro ⟨γ, rfl⟩; exact ⟨γ⁻¹, rfl⟩
  · rintro ⟨γ, rfl⟩; exact ⟨γ⁻¹, by show γ⁻¹ • f = act γ f; rw [smul_def, inv_inv]⟩

theorem mem_stabilizer_iff_act (γ : SL(2, ℤ)) (f : BQF) :
    γ ∈ MulAction.stabilizer SL(2, ℤ) f ↔ act γ f = f := by
  rw [MulAction.mem_stabilizer_iff, smul_def]
  constructor
  · intro h
    calc act γ f = act γ (act γ⁻¹ f) := by rw [h]
      _ = f := act_act_inv γ f
  · intro h
    calc act γ⁻¹ f = act γ⁻¹ (act γ f) := by rw [h]
      _ = f := act_inv_act γ f

theorem posDef_act_of (γ : SL(2, ℤ)) {f : BQF} (hf : f.PosDef) : (act γ f).PosDef := by
  refine ⟨?_, by rw [disc_act]; exact hf.2⟩
  rw [act_a]
  apply (posDef_iff f).1 hf
  by_contra h
  push_neg at h
  have := det_eq γ
  rw [h.1, h.2] at this
  simp at this

theorem posDef_act_iff (γ : SL(2, ℤ)) (f : BQF) : (act γ f).PosDef ↔ f.PosDef :=
  ⟨fun h => by simpa [act_inv_act] using posDef_act_of γ⁻¹ h, posDef_act_of γ⟩

theorem content_dvd_content_act (γ : SL(2, ℤ)) (f : BQF) : f.content ∣ (act γ f).content := by
  obtain ⟨h1, h2, h3⟩ := f.dvd_subst f.content_dvd_a f.content_dvd_b f.content_dvd_c
    (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
  exact dvd_content _ h1 h2 h3

theorem content_act (γ : SL(2, ℤ)) (f : BQF) : (act γ f).content = f.content :=
  Nat.dvd_antisymm (by simpa [act_inv_act] using content_dvd_content_act γ⁻¹ (act γ f))
    (content_dvd_content_act γ f)

theorem isPrimitive_act_iff (γ : SL(2, ℤ)) (f : BQF) : (act γ f).IsPrimitive ↔ f.IsPrimitive := by
  show (act γ f).content = 1 ↔ f.content = 1
  rw [content_act]

theorem disc_smul (γ : SL(2, ℤ)) (f : BQF) : (γ • f).disc = f.disc := disc_act _ _

theorem posDef_smul_iff (γ : SL(2, ℤ)) (f : BQF) : (γ • f).PosDef ↔ f.PosDef := posDef_act_iff _ _

theorem content_smul (γ : SL(2, ℤ)) (f : BQF) : (γ • f).content = f.content := content_act _ _

theorem isPrimitive_smul_iff (γ : SL(2, ℤ)) (f : BQF) : (γ • f).IsPrimitive ↔ f.IsPrimitive :=
  isPrimitive_act_iff _ _

theorem act_S (f : BQF) : act ModularGroup.S f = ⟨f.c, -f.b, f.a⟩ := by
  ext <;> simp [act, subst, ModularGroup.coe_S]

theorem act_T_zpow (k : ℤ) (f : BQF) :
    act (ModularGroup.T ^ k) f = ⟨f.a, f.b + 2 * f.a * k, f.a * k ^ 2 + f.b * k + f.c⟩ := by
  ext <;> simp [act, subst, ModularGroup.coe_T_zpow] <;> ring

/-- Sanity: the action on `[2, 1, 3]` by `T` and `S`. -/
theorem act_sanity : act ModularGroup.T ⟨2, 1, 3⟩ = ⟨2, 5, 6⟩ ∧
    act ModularGroup.S ⟨2, 1, 3⟩ = ⟨3, -1, 2⟩ := by
  constructor
  · simpa using act_T_zpow 1 ⟨2, 1, 3⟩
  · rw [act_S]

/-! ### Reduction: existence -/

/-- Every positive definite form is equivalent to a reduced one. -/
theorem exists_act_isReduced (f : BQF) (hf : f.PosDef) : ∃ γ : SL(2, ℤ), (act γ f).IsReduced := by
  suffices H : ∀ n : ℕ, ∀ f : BQF, f.a.toNat = n → f.PosDef →
      ∃ γ : SL(2, ℤ), (act γ f).IsReduced from H _ f rfl hf
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
  have ha : 0 < f.a := hf.1
  obtain ⟨k, m, hkm, hm0, hm1⟩ : ∃ k m : ℤ, 2 * f.a * k + m = f.a - f.b ∧ 0 ≤ m ∧ m < 2 * f.a :=
    ⟨(f.a - f.b) / (2 * f.a), (f.a - f.b) % (2 * f.a), Int.mul_ediv_add_emod _ _,
      Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
  have hf1 := act_T_zpow k f
  have hpos1 : (act (ModularGroup.T ^ k) f).PosDef := posDef_act_of _ hf
  generalize hb1d : f.b + 2 * f.a * k = b1 at hf1
  generalize hc1d : f.a * k ^ 2 + f.b * k + f.c = c1 at hf1
  have hlo : -f.a < b1 := by rw [← hb1d]; linarith
  have hhi : b1 ≤ f.a := by rw [← hb1d]; linarith
  rw [hf1] at hpos1
  have hc1pos : 0 < c1 := by
    have := (posDef_iff _).1 hpos1 0 1 (by simp)
    simpa using this
  rcases lt_trichotomy f.a c1 with hlt | heq | hgt
  · exact ⟨ModularGroup.T ^ k, by rw [hf1]; exact ⟨hlo, hhi, hlt.le, fun h => absurd h hlt.ne⟩⟩
  · by_cases hb : 0 ≤ b1
    · exact ⟨ModularGroup.T ^ k, by rw [hf1]; exact ⟨hlo, hhi, heq.le, fun _ => hb⟩⟩
    · refine ⟨ModularGroup.T ^ k * ModularGroup.S, ?_⟩
      rw [act_mul, hf1, act_S]
      refine ⟨?_, ?_, ?_, fun _ => ?_⟩ <;> simp only <;> omega
  · have hpos2 : (act ModularGroup.S (⟨f.a, b1, c1⟩ : BQF)).PosDef := posDef_act_of _ hpos1
    rw [act_S] at hpos2
    obtain ⟨γ, hγ⟩ := ih c1.toNat (by omega) ⟨c1, -b1, f.a⟩ rfl hpos2
    refine ⟨ModularGroup.T ^ k * ModularGroup.S * γ, ?_⟩
    rw [act_mul, act_mul, hf1, act_S]
    exact hγ

/-! ### Reduction: uniqueness -/

/-- If `f` and `act γ f` are both reduced, then `act γ f = f`. -/
theorem BQF.IsReduced.act_eq {f : BQF} (hf : f.IsReduced) {γ : SL(2, ℤ)} (hg : (act γ f).IsReduced) :
    act γ f = f := by
  have hdet := det_eq γ
  have hD := disc_act γ f
  have ha0 := hf.a_pos
  have h1 : f.a ≤ (act γ f).a := by
    rw [act_a]
    apply hf.a_le_eval
    by_contra h
    push_neg at h
    rw [h.1, h.2] at hdet
    simp at hdet
  have e : (act γ f).eval (γ 1 1) (-γ 1 0) = f.a := by
    have := congrArg BQF.a (act_inv_act γ f)
    rwa [act_a, inv_apply_00, inv_apply_10] at this
  have h2 : (act γ f).a ≤ f.a := by
    rw [← e]
    apply hg.a_le_eval
    by_contra h
    push_neg at h
    have h' : γ 1 0 = 0 := by linarith [h.2]
    rw [h.1, h'] at hdet
    simp at hdet
  have ha : (act γ f).a = f.a := le_antisymm h2 h1
  by_cases hr : γ 1 0 = 0
  · have hps : γ 0 0 * γ 1 1 = 1 := by rw [hr] at hdet; linarith
    have hp : γ 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hps
    have hb : (act γ f).b = f.b + 2 * (f.a * (γ 0 0 * γ 0 1)) := by
      simp only [act, subst]; rw [hr]; linear_combination f.b * hps
    have hlo := hg.1
    have hhi := hg.2.1
    rw [ha, hb] at hlo hhi
    have hf1 := hf.1
    have hf2 := hf.2.1
    have ht1 : γ 0 0 * γ 0 1 < 1 := by
      by_contra h; push_neg at h; nlinarith
    have ht2 : -1 < γ 0 0 * γ 0 1 := by
      by_contra h; push_neg at h; nlinarith
    have ht : γ 0 0 * γ 0 1 = 0 := by omega
    have hq : γ 0 1 = 0 := by simpa [hp] using ht
    have hbb : (act γ f).b = f.b := by rw [hb, ht]; ring
    have hcc : (act γ f).c = f.c := by
      simp only [disc] at hD
      rw [ha, hbb] at hD
      have : f.a * ((act γ f).c - f.c) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · omega
      · linarith
    exact BQF.ext ha hbb hcc
  · have hfc : f.c = f.a := hf.c_eq_a_of_eval hr (by rw [← act_a]; exact ha)
    have hgc : (act γ f).c = (act γ f).a :=
      hg.c_eq_a_of_eval (neg_ne_zero.2 hr) (by rw [e, ha])
    have hb0 : 0 ≤ f.b := hf.2.2.2 hfc.symm
    have hb0' : 0 ≤ (act γ f).b := hg.2.2.2 hgc.symm
    have hsq : (act γ f).b ^ 2 = f.b ^ 2 := by
      simp only [disc] at hD
      rw [hgc, ha, hfc] at hD
      linarith
    have hbb : (act γ f).b = f.b := by nlinarith
    exact BQF.ext ha hbb (by rw [hgc, ha, hfc])

/-- Two equivalent reduced forms are equal. -/
theorem BQF.IsReduced.eq_of_mem_orbit {f g : BQF} (hf : f.IsReduced) (hg : g.IsReduced)
    (h : g ∈ MulAction.orbit SL(2, ℤ) f) : g = f := by
  obtain ⟨γ, rfl⟩ := (mem_orbit_iff_act f g).1 h
  exact hf.act_eq hg

/-- Every positive definite form has a unique reduced form in its orbit. -/
theorem existsUnique_reduced (f : BQF) (hf : f.PosDef) :
    ∃! g : BQF, g ∈ MulAction.orbit SL(2, ℤ) f ∧ g.IsReduced := by
  obtain ⟨γ, hγ⟩ := exists_act_isReduced f hf
  refine ⟨act γ f, ⟨(mem_orbit_iff_act _ _).2 ⟨γ, rfl⟩, hγ⟩, ?_⟩
  rintro g ⟨hg, hgr⟩
  apply hγ.eq_of_mem_orbit hgr
  obtain ⟨δ, rfl⟩ := (mem_orbit_iff_act f g).1 hg
  refine (mem_orbit_iff_act _ _).2 ⟨γ⁻¹ * δ, ?_⟩
  rw [act_mul, act_inv_act]

/-! ### Finiteness of reduced forms -/

/-- Enumeration map `(i, j) ↦ [i + 1, j - m, ((j - m)² - D) / (4 (i + 1))]`. -/
def redEmb (D : ℤ) (m : ℕ) : ℕ × ℕ ↪ BQF where
  toFun p := ⟨(p.1 : ℤ) + 1, (p.2 : ℤ) - m, (((p.2 : ℤ) - m) ^ 2 - D) / (4 * ((p.1 : ℤ) + 1))⟩
  inj' p q h := by
    simp only [BQF.mk.injEq] at h
    exact Prod.ext (by omega) (by omega)

/-- The (computable) finset of reduced forms of discriminant `D`. -/
def reducedForms (D : ℤ) : Finset BQF :=
  ((Finset.range ((-D) / 3).toNat ×ˢ Finset.range (2 * ((-D) / 3).toNat + 1)).map
    (redEmb D ((-D) / 3).toNat)).filter (fun f => f.disc = D ∧ f.IsReduced)

theorem three_mul_a_le {f : BQF} (hf : f.IsReduced) : 3 * f.a ≤ -f.disc := by
  have ha := hf.a_pos
  obtain ⟨h1, h2, h3, -⟩ := hf
  simp only [disc]
  nlinarith [mul_nonneg (sub_nonneg.2 h2) (by linarith : (0 : ℤ) ≤ f.a + f.b),
    mul_le_mul_of_nonneg_left h3 ha.le, mul_le_mul_of_nonneg_left (by omega : (1 : ℤ) ≤ f.c) ha.le]

theorem mem_reducedForms {D : ℤ} {f : BQF} : f ∈ reducedForms D ↔ f.disc = D ∧ f.IsReduced := by
  constructor
  · intro h; exact (Finset.mem_filter.1 h).2
  · rintro ⟨hD, hf⟩
    refine Finset.mem_filter.2 ⟨?_, hD, hf⟩
    rw [Finset.mem_map]
    have ha := hf.a_pos
    have h3a := three_mul_a_le hf
    rw [hD] at h3a
    obtain ⟨h1, h2, h3, -⟩ := hf
    refine ⟨((f.a - 1).toNat, (f.b + (((-D) / 3).toNat : ℤ)).toNat), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]; omega
    · have hb2 : f.b ^ 2 - D = 4 * f.a * f.c := by rw [← hD]; simp only [disc]; ring
      have e1 : (((f.a - 1).toNat : ℕ) : ℤ) = f.a - 1 := Int.toNat_of_nonneg (by omega)
      have e2 : (((f.b + (((-D) / 3).toNat : ℤ)).toNat : ℕ) : ℤ) = f.b + (((-D) / 3).toNat : ℤ) :=
        Int.toNat_of_nonneg (by omega)
      refine BQF.ext ?_ ?_ ?_
      · show (((f.a - 1).toNat : ℕ) : ℤ) + 1 = f.a
        rw [e1]; ring
      · show (((f.b + (((-D) / 3).toNat : ℤ)).toNat : ℕ) : ℤ) - (((-D) / 3).toNat : ℤ) = f.b
        rw [e2]; ring
      · show (((((f.b + (((-D) / 3).toNat : ℤ)).toNat : ℕ) : ℤ) - (((-D) / 3).toNat : ℤ)) ^ 2 - D) /
          (4 * ((((f.a - 1).toNat : ℕ) : ℤ) + 1)) = f.c
        rw [e1, e2, add_sub_cancel_right, sub_add_cancel, hb2, Int.mul_ediv_cancel_left _ (by omega)]

theorem reducedForms_sanity : reducedForms (-3) = {⟨1, 1, 1⟩} ∧ reducedForms (-4) = {⟨1, 0, 1⟩} ∧
    reducedForms (-20) = {⟨1, 0, 5⟩, ⟨2, 2, 3⟩} ∧
    reducedForms (-23) = {⟨1, 1, 6⟩, ⟨2, -1, 3⟩, ⟨2, 1, 3⟩} := by decide

theorem finite_reduced (D : ℤ) : {f : BQF | f.disc = D ∧ f.IsReduced}.Finite :=
  (reducedForms D).finite_toSet.subset (fun _ hf => mem_reducedForms.2 hf)

/-! ### Stabilizers of reduced forms -/

/-- The four entries of `γ`. -/
def ent (γ : SL(2, ℤ)) : ℤ × ℤ × ℤ × ℤ := (γ 0 0, γ 0 1, γ 1 0, γ 1 1)

theorem ent_injective : Function.Injective ent := by
  intro γ δ h
  simp only [ent, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Matrix.SpecialLinearGroup.ext γ δ (fun i j => ?_)
  fin_cases i <;> fin_cases j <;> assumption

/-- The matrix with entries `v` (determinant 1). -/
def mkSL (v : ℤ × ℤ × ℤ × ℤ) (h : v.1 * v.2.2.2 - v.2.1 * v.2.2.1 = 1) : SL(2, ℤ) :=
  ⟨!![v.1, v.2.1; v.2.2.1, v.2.2.2], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem ent_mkSL (v : ℤ × ℤ × ℤ × ℤ) (h : v.1 * v.2.2.2 - v.2.1 * v.2.2.1 = 1) :
    ent (mkSL v h) = v := by
  simp [ent, mkSL]

/-- Counting a stabilizer through the entries of its elements. -/
theorem card_stabilizer_eq (f : BQF) (S : Finset (ℤ × ℤ × ℤ × ℤ))
    (hS : ∀ γ : SL(2, ℤ), act γ f = f ↔ ent γ ∈ S)
    (hdet : ∀ v ∈ S, v.1 * v.2.2.2 - v.2.1 * v.2.2.1 = 1) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) f) = S.card := by
  have himg : ent '' (MulAction.stabilizer SL(2, ℤ) f : Set SL(2, ℤ)) = ↑S := by
    ext v
    simp only [Set.mem_image, SetLike.mem_coe, mem_stabilizer_iff_act, Finset.mem_coe]
    constructor
    · rintro ⟨γ, hγ, rfl⟩; exact (hS γ).1 hγ
    · intro hv
      exact ⟨mkSL v (hdet v hv), (hS _).2 (by rw [ent_mkSL]; exact hv), ent_mkSL _ _⟩
  rw [← Set.ncard_coe_finset, ← himg, Set.ncard_image_of_injective _ ent_injective,
    ← Nat.card_coe_set_eq]
  rfl

/-- `{-1, 0, 1}⁴`. -/
def boxFin : Finset (ℤ × ℤ × ℤ × ℤ) :=
  ({-1, 0, 1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ) ×ˢ ({-1, 0, 1} : Finset ℤ) ×ˢ
    ({-1, 0, 1} : Finset ℤ)

/-- Entry vectors in the box with determinant 1 fixing `g`. -/
def stabFin (g : BQF) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  boxFin.filter (fun v => v.1 * v.2.2.2 - v.2.1 * v.2.2.1 = 1 ∧ g.subst v.1 v.2.1 v.2.2.1 v.2.2.2 = g)

theorem stabFin_card_101 : (stabFin ⟨1, 0, 1⟩).card = 4 := by decide

theorem stabFin_card_111 : (stabFin ⟨1, 1, 1⟩).card = 6 := by decide

theorem det_of_mem_stabFin (g : BQF) : ∀ v ∈ stabFin g, v.1 * v.2.2.2 - v.2.1 * v.2.2.1 = 1 :=
  fun _ hv => (Finset.mem_filter.1 hv).2.1

theorem ent_mem_boxFin {γ : SL(2, ℤ)} (h1 : -1 ≤ γ 0 0 ∧ γ 0 0 ≤ 1) (h2 : -1 ≤ γ 0 1 ∧ γ 0 1 ≤ 1)
    (h3 : -1 ≤ γ 1 0 ∧ γ 1 0 ≤ 1) (h4 : -1 ≤ γ 1 1 ∧ γ 1 1 ≤ 1) : ent γ ∈ boxFin := by
  simp only [boxFin, ent, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton]
  omega

theorem act_eq_iff_mem_stabFin {g : BQF} (γ : SL(2, ℤ)) (hbox : act γ g = g → ent γ ∈ boxFin) :
    act γ g = g ↔ ent γ ∈ stabFin g := by
  constructor
  · intro h; exact Finset.mem_filter.2 ⟨hbox h, det_eq γ, h⟩
  · intro h; exact (Finset.mem_filter.1 h).2.2

theorem bound_of_sq_le_one {x : ℤ} (h : x ^ 2 ≤ 1) : -1 ≤ x ∧ x ≤ 1 := by
  constructor <;> nlinarith

theorem box_101 (γ : SL(2, ℤ)) (h : act γ ⟨1, 0, 1⟩ = ⟨1, 0, 1⟩) : ent γ ∈ boxFin := by
  have hA := congrArg BQF.a h
  have hC := congrArg BQF.c h
  simp only [act, subst] at hA hC
  apply ent_mem_boxFin <;> apply bound_of_sq_le_one <;> nlinarith [sq_nonneg (γ 0 0),
    sq_nonneg (γ 0 1), sq_nonneg (γ 1 0), sq_nonneg (γ 1 1)]

theorem box_111 (γ : SL(2, ℤ)) (h : act γ ⟨1, 1, 1⟩ = ⟨1, 1, 1⟩) : ent γ ∈ boxFin := by
  have hA := congrArg BQF.a h
  have hC := congrArg BQF.c h
  simp only [act, subst] at hA hC
  have b1 : 3 * γ 1 0 ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * γ 0 0 + γ 1 0)]
  have b2 : 3 * γ 0 0 ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * γ 1 0 + γ 0 0)]
  have b3 : 3 * γ 1 1 ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * γ 0 1 + γ 1 1)]
  have b4 : 3 * γ 0 1 ^ 2 ≤ 4 := by nlinarith [sq_nonneg (2 * γ 1 1 + γ 0 1)]
  apply ent_mem_boxFin <;> apply bound_of_sq_le_one <;> omega

theorem act_scale (γ : SL(2, ℤ)) (n : ℤ) (g : BQF) :
    act γ ⟨n * g.a, n * g.b, n * g.c⟩ = ⟨n * (act γ g).a, n * (act γ g).b, n * (act γ g).c⟩ := by
  simp only [act, subst, BQF.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem act_scale_eq_iff (γ : SL(2, ℤ)) {n : ℤ} (hn : n ≠ 0) (g : BQF) :
    act γ ⟨n * g.a, n * g.b, n * g.c⟩ = ⟨n * g.a, n * g.b, n * g.c⟩ ↔ act γ g = g := by
  rw [act_scale, BQF.mk.injEq, mul_right_inj' hn, mul_right_inj' hn, mul_right_inj' hn, BQF.ext_iff]

/-- The generic stabilizer is `{±1}`. -/
theorem act_eq_iff_generic {f : BQF} (hf : f.IsReduced) (h0 : ¬ (f.b = 0 ∧ f.a = f.c))
    (h1 : ¬ (f.a = f.b ∧ f.b = f.c)) (γ : SL(2, ℤ)) :
    act γ f = f ↔ ent γ ∈ ({(1, 0, 0, 1), (-1, 0, 0, -1)} : Finset (ℤ × ℤ × ℤ × ℤ)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, ent, Prod.mk.injEq]
  constructor
  · intro hγ
    have hdet := det_eq γ
    have hA : f.eval (γ 0 0) (γ 1 0) = f.a := by rw [← act_a, hγ]
    have hC : f.eval (γ 0 1) (γ 1 1) = f.c := by rw [← act_c, hγ]
    have hB : (act γ f).b = f.b := by rw [hγ]
    simp only [act, subst] at hB
    have ha := hf.a_pos
    by_cases hr : γ 1 0 = 0
    · have hps : γ 0 0 * γ 1 1 = 1 := by rw [hr] at hdet; linarith
      have hp : γ 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hps
      rw [hr] at hB
      have h2 : 2 * (f.a * (γ 0 0 * γ 0 1)) = 0 := by linear_combination hB - f.b * hps
      have hq : γ 0 1 = 0 := by simpa [ha.ne', hp] using h2
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' hps with ⟨hp1, hs1⟩ | ⟨hp1, hs1⟩
      · left; exact ⟨hp1, hq, hr, hs1⟩
      · right; exact ⟨hp1, hq, hr, hs1⟩
    · exfalso
      have hfc : f.c = f.a := hf.c_eq_a_of_eval hr hA
      have hb0 : 0 ≤ f.b := hf.2.2.2 hfc.symm
      have hblt : f.b < f.a := by
        rcases lt_or_eq_of_le hf.2.1 with h | h
        · exact h
        · exact absurd ⟨h.symm, h ▸ hfc.symm⟩ h1
      have hbpos : 0 < f.b := by
        rcases lt_or_eq_of_le hb0 with h | h
        · exact h
        · exact absurd ⟨h.symm, hfc.symm⟩ h0
      have hp : γ 0 0 = 0 := by
        by_contra hp
        have := hf.add_sub_abs_le_eval hp hr
        rw [abs_of_nonneg hb0, hA] at this
        omega
      have hqr : γ 0 1 * γ 1 0 = -1 := by rw [hp] at hdet; linarith
      have hq : γ 0 1 ≠ 0 := left_ne_zero_of_mul (by rw [hqr]; norm_num)
      have hs : γ 1 1 = 0 := by
        by_contra hs
        have := hf.add_sub_abs_le_eval hq hs
        rw [abs_of_nonneg hb0, hC] at this
        omega
      rw [hp, hs] at hB
      have h3 : f.b * (γ 0 1 * γ 1 0) = f.b := by linear_combination hB
      rw [hqr] at h3
      omega
  · rintro (⟨h00, h01, h10, h11⟩ | ⟨h00, h01, h10, h11⟩) <;>
      ext <;> simp [act, subst, h00, h01, h10, h11]

/-- Stabilizer orders of reduced forms: 4 for `[a, 0, a]`, 6 for `[a, a, a]`, otherwise 2. -/
theorem card_stabilizer_of_isReduced {f : BQF} (hf : f.IsReduced) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) f) =
      if f.b = 0 ∧ f.a = f.c then 4 else if f.a = f.b ∧ f.b = f.c then 6 else 2 := by
  have ha := hf.a_pos
  split_ifs with h0 h1
  · obtain ⟨a, b, c⟩ := f
    simp only at h0 ha
    obtain ⟨rfl, rfl⟩ := h0
    have key : ∀ γ : SL(2, ℤ), act γ ⟨a, 0, a⟩ = ⟨a, 0, a⟩ ↔ act γ ⟨1, 0, 1⟩ = ⟨1, 0, 1⟩ :=
      fun γ => by simpa using act_scale_eq_iff γ ha.ne' ⟨1, 0, 1⟩
    rw [card_stabilizer_eq _ (stabFin ⟨1, 0, 1⟩)
      (fun γ => (key γ).trans (act_eq_iff_mem_stabFin γ (box_101 γ))) (det_of_mem_stabFin _),
      stabFin_card_101]
  · obtain ⟨a, b, c⟩ := f
    simp only at h1 ha
    obtain ⟨rfl, rfl⟩ := h1
    have key : ∀ γ : SL(2, ℤ), act γ ⟨a, a, a⟩ = ⟨a, a, a⟩ ↔ act γ ⟨1, 1, 1⟩ = ⟨1, 1, 1⟩ :=
      fun γ => by simpa using act_scale_eq_iff γ ha.ne' ⟨1, 1, 1⟩
    rw [card_stabilizer_eq _ (stabFin ⟨1, 1, 1⟩)
      (fun γ => (key γ).trans (act_eq_iff_mem_stabFin γ (box_111 γ))) (det_of_mem_stabFin _),
      stabFin_card_111]
  · rw [card_stabilizer_eq f _ (act_eq_iff_generic hf h0 h1) (by decide)]
    decide

/-- Stabilizers along an orbit have the same order. -/
theorem card_stabilizer_act (γ : SL(2, ℤ)) (f : BQF) :
    Nat.card (MulAction.stabilizer SL(2, ℤ) (act γ f)) = Nat.card (MulAction.stabilizer SL(2, ℤ) f) :=
  (Nat.card_congr (MulAction.stabilizerEquivStabilizer (act_eq_smul γ f)).toEquiv).symm

end RamanujanPetersson.Hurwitz


