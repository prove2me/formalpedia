-- Prove2me | Definitions.Def_ChapterGaugeFixing
-- name    : ChapterGaugeFixing
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-07T14:17:31.663468+00:00
-- url     : https://prove2.me/theorems/7ded80dc-5b4f-467d-bfc9-068cdad25160
-- title:
--   BRST doublets and the gauge-fixing fermion
-- statement:
--   Formal definitions for the BRST doublets and the gauge-fixing fermion of the timepiece Lean 4 formalization (module `BookProof.GaugeFixing`, source chapter `BookProof/ChapterGaugeFixing.lean`).
--
--   Plan item **E.6** of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`: the *abstract algebraic skeleton* of the gauge-fixing machinery on which the concrete BRST charges of the Navier–Stokes chapters (`BookProof.NavierStokesFlow.nsBrst`, the Yang–Mills charge) rest. It is deliberately self-contained: no Hilbert spaces, no analysis, only a bi-graded algebra with two odd operators.
--
--   The fields are placed in bidegrees `(Form Degree, Ghost Number)`:
--
--   | field | bidegree | rôle | | :-- | :-- | :-- | | `phi` | `(0, 0)` | physical scalar | | `v` | `(1, 0)` | gauge field to be eliminated | | `c` | `(1, 1)` | ghost | | `c_bar` | `(1, -1)` | anti-ghost | | `B` | `(1, 0)` | Nakanishi–Lautrup auxiliary field |
--
--   The BRST operator `s` raises the ghost number by one and the exterior derivative `d` raises the form degree by one. The BRST action on the generators is `s v = c`, `s c̄ = B`, `s φ = 0`; the pairs `(v, c)` and `(c̄, B)` are therefore **BRST doublets (contractible pairs)**, which is the formal content of the statement that `v` and the ghosts decouple.
--
--   Because Method B needs a *product* (unlike the purely linear constructions of plan items E.1–E.4), `s` must act as an **odd derivation**: passing over the anti-ghost `c̄` (ghost number `-1`) produces a minus sign, `s (c̄ · X) = (s c̄) · X − c̄ · (s X)`. This single instance of the graded Leibniz rule is what `GaugeFixingSystem.s_mul_c_bar` records; no general `(-1)^n` grading typeclass is needed.
--
--   * `s_c_eq_zero`, `s_B_eq_zero` — the ghost and the auxiliary field are BRST-closed, a consequence of nilpotency (E.6.4, E.6.5); * `Psi` — the Gauge-Fixing Fermion `Ψ = c̄ · (v − dφ)`, of bidegree `(2, -1)` (E.6.6); * `L_gf_evaluation` — **the culminating identity** `s Ψ = B · (v − dφ) − c̄ · c` (E.6.7). Physically: `B · (v − dφ)` is the Lagrange multiplier enforcing the delta function `δ(v − dφ)`, i.e. it sets `v = dφ`, and `− c̄ · c` is a ghost mass term with no momentum dependence, so the ghosts drop out of the physics. BRST exactness *strictly generates* the gauge-fixing Lagrangian; * `L_gf_invariant` — `s (s Ψ) = 0`, so the gauge-fixing Lagrangian is BRST-invariant (E.6.8); * `BrstIntegral` / `int_L_gf_eq_zero` — a "path-integral" evaluation functional killing BRST-exact terms, hence `ℒ_gf` has zero impact on physical observables (E.6.9).
--
--   * The axioms of `GaugeFixingSystem` (`s_nilpotent`, `s_mul_c_bar`, …) are *definitional fields of a structure*, not `axiom` declarations and not claims about continuum physics; they are the standard defining relations of a BRST complex. The discipline that continuum existence statements are named hypotheses rather than axioms is untouched. * The structure is **not** vacuous, and the identity `L_gf_evaluation` is **not** vacuously true: `matrixModel` is an explicit model built from `2 × 2` real matrices (the superalgebra `M(1|1)` with the odd differential `s x = Q x − (−1)^g x Q`, `Q` nilpotent) in which the ghost, the auxiliary field, the Fermion `Ψ` and its BRST variation `s Ψ` are all non-zero (`matrixModel_c_ne_zero`, `matrixModel_B_ne_zero`, `matrixModel_Psi_ne_zero`, `matrixModel_s_Psi_ne_zero`), and the evaluation functional of `matrixModelIntegral` is non-zero as well (`matrixModelIntegral_ne_zero`). * Nothing here claims anything about the Navier–Stokes continuum problem; this is the algebraic skeleton only.
--
--   Everything in this module is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaugeFixing.lean

import Mathlib

/-!
# Method B: BRST doublets and the Gauge-Fixing Fermion

Plan item **E.6** of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`: the *abstract algebraic
skeleton* of the gauge-fixing machinery on which the concrete BRST charges of the
Navier–Stokes chapters (`BookProof.NavierStokesFlow.nsBrst`, the Yang–Mills charge)
rest.  It is deliberately self-contained: no Hilbert spaces, no analysis, only a
bi-graded algebra with two odd operators.

## The mechanism

The fields are placed in bidegrees `(Form Degree, Ghost Number)`:

| field | bidegree | rôle |
| :-- | :-- | :-- |
| `phi` | `(0, 0)` | physical scalar |
| `v` | `(1, 0)` | gauge field to be eliminated |
| `c` | `(1, 1)` | ghost |
| `c_bar` | `(1, -1)` | anti-ghost |
| `B` | `(1, 0)` | Nakanishi–Lautrup auxiliary field |

The BRST operator `s` raises the ghost number by one and the exterior derivative
`d` raises the form degree by one.  The BRST action on the generators is
`s v = c`, `s c̄ = B`, `s φ = 0`; the pairs `(v, c)` and `(c̄, B)` are therefore
**BRST doublets (contractible pairs)**, which is the formal content of the
statement that `v` and the ghosts decouple.

Because Method B needs a *product* (unlike the purely linear constructions of
plan items E.1–E.4), `s` must act as an **odd derivation**: passing over the
anti-ghost `c̄` (ghost number `-1`) produces a minus sign,
`s (c̄ · X) = (s c̄) · X − c̄ · (s X)`.  This single instance of the graded Leibniz
rule is what `GaugeFixingSystem.s_mul_c_bar` records; no general `(-1)^n` grading
typeclass is needed.

## Results

* `s_c_eq_zero`, `s_B_eq_zero` — the ghost and the auxiliary field are
  BRST-closed, a consequence of nilpotency (E.6.4, E.6.5);
* `Psi` — the Gauge-Fixing Fermion `Ψ = c̄ · (v − dφ)`, of bidegree `(2, -1)`
  (E.6.6);
* `L_gf_evaluation` — **the culminating identity**
  `s Ψ = B · (v − dφ) − c̄ · c` (E.6.7).  Physically: `B · (v − dφ)` is the
  Lagrange multiplier enforcing the delta function `δ(v − dφ)`, i.e. it sets
  `v = dφ`, and `− c̄ · c` is a ghost mass term with no momentum dependence, so
  the ghosts drop out of the physics.  BRST exactness *strictly generates* the
  gauge-fixing Lagrangian;
* `L_gf_invariant` — `s (s Ψ) = 0`, so the gauge-fixing Lagrangian is
  BRST-invariant (E.6.8);
* `BrstIntegral` / `int_L_gf_eq_zero` — a "path-integral" evaluation functional
  killing BRST-exact terms, hence `ℒ_gf` has zero impact on physical
  observables (E.6.9).

## Honesty notes

* The axioms of `GaugeFixingSystem` (`s_nilpotent`, `s_mul_c_bar`, …) are
  *definitional fields of a structure*, not `axiom` declarations and not claims
  about continuum physics; they are the standard defining relations of a BRST
  complex.  The discipline that continuum existence statements are named
  hypotheses rather than axioms is untouched.
* The structure is **not** vacuous, and the identity `L_gf_evaluation` is **not**
  vacuously true: `matrixModel` is an explicit model built from `2 × 2` real
  matrices (the superalgebra `M(1|1)` with the odd differential
  `s x = Q x − (−1)^g x Q`, `Q` nilpotent) in which the ghost, the auxiliary
  field, the Fermion `Ψ` and its BRST variation `s Ψ` are all non-zero
  (`matrixModel_c_ne_zero`, `matrixModel_B_ne_zero`, `matrixModel_Psi_ne_zero`,
  `matrixModel_s_Psi_ne_zero`), and the evaluation functional of
  `matrixModelIntegral` is non-zero as well (`matrixModelIntegral_ne_zero`).
* Nothing here claims anything about the Navier–Stokes continuum problem; this
  is the algebraic skeleton only.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.GaugeFixing

/-! ## E.6.1 — bidegrees -/

/-- A bidegree is a pair `(form degree, ghost number)`. -/
abbrev BiDegree : Type := ℤ × ℤ

/-- Addition of bidegrees: the bidegree of a product. -/
def addDeg (a b : BiDegree) : BiDegree := (a.1 + b.1, a.2 + b.2)





/-! ## E.6.2/E.6.3 — the gauge-fixing system -/

/-- A **gauge-fixing system** on a bigraded family of carriers `F`.

It bundles the additive structure of each graded piece, a product that adds
bidegrees, the exterior derivative `d` (raising the form degree) and the BRST
operator `s` (raising the ghost number), the five fields `φ, v, c, c̄, B`, and the
defining BRST relations.  The last field is the *specific* graded Leibniz rule for
the anti-ghost, the only instance of the sign rule the development needs. -/
structure GaugeFixingSystem (F : BiDegree → Type) where
  /-- The zero element of each graded piece. -/
  zero : ∀ deg : BiDegree, F deg
  /-- Addition inside a graded piece. -/
  add : ∀ deg : BiDegree, F deg → F deg → F deg
  /-- Subtraction inside a graded piece. -/
  sub : ∀ deg : BiDegree, F deg → F deg → F deg
  /-- The product, which adds bidegrees. -/
  mul : ∀ a b : BiDegree, F a → F b → F (addDeg a b)
  /-- The exterior derivative, `(p, g) → (p + 1, g)`. -/
  d : ∀ {p g : ℤ}, F (p, g) → F (p + 1, g)
  /-- The BRST operator, `(p, g) → (p, g + 1)`. -/
  s : ∀ {p g : ℤ}, F (p, g) → F (p, g + 1)
  /-- `d` annihilates zero. -/
  d_zero : ∀ p g : ℤ, d (zero (p, g)) = zero (p + 1, g)
  /-- Subtracting zero changes nothing. -/
  sub_zero : ∀ (deg : BiDegree) (x : F deg), sub deg x (zero deg) = x
  /-- The BRST operator is nilpotent, `s² = 0`. -/
  s_nilpotent : ∀ (p g : ℤ) (x : F (p, g)), s (s x) = zero (p, g + 1 + 1)
  /-- `s` is additive (stated for subtraction, the form the development uses). -/
  s_sub : ∀ (p g : ℤ) (x y : F (p, g)),
    s (sub (p, g) x y) = sub (p, g + 1) (s x) (s y)
  /-- `s` commutes with the exterior derivative. -/
  sd_commute : ∀ (p g : ℤ) (x : F (p, g)), s (d x) = d (s x)
  /-- The physical scalar, bidegree `(0, 0)`. -/
  phi : F (0, 0)
  /-- The gauge field to be eliminated, bidegree `(1, 0)`. -/
  v : F (1, 0)
  /-- The ghost, bidegree `(1, 1)`. -/
  c : F (1, 1)
  /-- The anti-ghost, bidegree `(1, -1)`. -/
  c_bar : F (1, -1)
  /-- The Nakanishi–Lautrup auxiliary field, bidegree `(1, 0)`. -/
  B : F (1, 0)
  /-- BRST doublet `(v, c)`: `s v = c`. -/
  def_s_v : s v = c
  /-- The physical scalar is BRST-invariant: `s φ = 0`. -/
  def_s_phi : s phi = zero (0, 1)
  /-- BRST doublet `(c̄, B)`: `s c̄ = B`. -/
  def_s_c_bar : s c_bar = B
  /-- The graded Leibniz rule across the anti-ghost:
  `s (c̄ · X) = B · X − c̄ · (s X)` for `X` of bidegree `(1, 0)`
  (the right-hand side uses `s c̄ = B`). -/
  s_mul_c_bar : ∀ X : F (1, 0),
    s (mul (1, -1) (1, 0) c_bar X) =
      sub (2, 0) (mul (1, 0) (1, 0) B X) (mul (1, -1) (1, 1) c_bar (s X))

variable {F : BiDegree → Type} (S : GaugeFixingSystem F)

/-! ## E.6.4/E.6.5 — the doublet partners are BRST-closed -/





/-! ## E.6.6/E.6.7/E.6.8 — the Gauge-Fixing Fermion -/

/-- The gauge-fixed combination `v − dφ`, bidegree `(1, 0)`; the constraint
imposed by the BRST-exact Lagrangian is exactly its vanishing. -/
def gaugeField : F (1, 0) := S.sub (1, 0) S.v (S.d S.phi)

/-- **E.6.6.** The Gauge-Fixing Fermion `Ψ = c̄ · (v − dφ)`, bidegree `(2, -1)`. -/
def Psi : F (2, -1) := S.mul (1, -1) (1, 0) S.c_bar (gaugeField S)









/-! ## E.6.9 — the path-integral evaluation -/

/-- The BRST variation of an element of bidegree `(2, -1)`, viewed in the top
bidegree `(2, 0)`. -/
def sTop (X : F (2, -1)) : F (2, 0) := S.s X

/-- A "path-integral" evaluation of the top bidegree `(2, 0)` which annihilates
BRST-exact terms — the algebraic shadow of BRST invariance of the vacuum. -/
structure BrstIntegral {F : BiDegree → Type} (S : GaugeFixingSystem F) where
  /-- The evaluation functional on bidegree `(2, 0)`. -/
  int : F (2, 0) → ℝ
  /-- BRST-exact terms integrate to zero. -/
  int_of_s : ∀ X : F (2, -1), int (sTop S X) = 0





/-! ## A concrete non-degenerate model

The axioms of `GaugeFixingSystem` are consistent *and* the culminating identity
`L_gf_evaluation` is not vacuous.  The model is the superalgebra `M(1|1)` of
`2 × 2` real matrices, graded by the ghost number parity, with the odd
differential `s x = Q x − (−1)^g x Q` built from the nilpotent matrix `Q = E₁₂`.
Because `s` is a super-commutator with the odd element `Q`, it is automatically an
odd derivation, and `Q² = 0` makes it nilpotent.  The BRST doublets are realised
by `v = E₁₁`, `c = s v = −Q`, `c̄ = E₂₁`, `B = s c̄ = 1`. -/

/-- The carrier of the model: `2 × 2` real matrices. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-- The nilpotent odd generator `Q = E₁₂` of the model. -/
def Qm : Mat2 := !![0, 1; 0, 0]

/-- The anti-ghost of the model, `c̄ = E₂₁`. -/
def Pm : Mat2 := !![0, 0; 1, 0]

/-- The gauge field of the model, `v = E₁₁`. -/
def Vm : Mat2 := !![1, 0; 0, 0]

theorem Qm_mul_Qm : Qm * Qm = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Qm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Qm_Pm_add_Pm_Qm : Qm * Pm + Pm * Qm = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Qm, Pm]

theorem Qm_mul_Vm : Qm * Vm = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Qm, Vm, Matrix.mul_apply, Fin.sum_univ_two]

theorem Vm_mul_Qm : Vm * Qm = Qm := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Qm, Vm, Matrix.mul_apply, Fin.sum_univ_two]







/-- The BRST differential of the model: the super-commutator with `Q`. -/
noncomputable def sMat (g : ℤ) (x : Mat2) : Mat2 := Qm * x - ((-1 : ℝ) ^ g) • (x * Qm)

theorem sMat_nilpotent (g : ℤ) (x : Mat2) : sMat (g + 1) (sMat g x) = 0 := by
  have hsgn : ((-1 : ℝ) ^ (g + 1)) = -((-1 : ℝ) ^ g) := by
    rw [zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]; ring
  simp only [sMat, hsgn, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    neg_smul, ← mul_assoc, Qm_mul_Qm, Matrix.zero_mul]
  rw [mul_assoc x Qm Qm, Qm_mul_Qm, Matrix.mul_zero]
  simp

theorem sMat_sub (g : ℤ) (x y : Mat2) : sMat g (x - y) = sMat g x - sMat g y := by
  simp only [sMat, mul_sub, sub_mul, smul_sub]
  abel

theorem sMat_zero (g : ℤ) : sMat g 0 = 0 := by simp [sMat]

theorem sMat_Vm : sMat 0 Vm = -Qm := by simp [sMat, Qm_mul_Vm, Vm_mul_Qm]

theorem sMat_one : sMat 0 (1 : Mat2) = 0 := by simp [sMat]

theorem sMat_Pm : sMat (-1) Pm = 1 := by
  have hneg : ((-1 : ℝ) ^ (-1 : ℤ)) = -1 := by norm_num
  rw [sMat, hneg]
  simp only [neg_smul, one_smul, sub_neg_eq_add]
  exact Qm_Pm_add_Pm_Qm

/-- The graded Leibniz rule holds in the model, for every `X`. -/
theorem sMat_leibniz (X : Mat2) : sMat (-1) (Pm * X) = 1 * X - Pm * sMat 0 X := by
  have hneg : ((-1 : ℝ) ^ (-1 : ℤ)) = -1 := by norm_num
  have h0 : ((-1 : ℝ) ^ (0 : ℤ)) = 1 := by norm_num
  have h3 : Qm * Pm * X + Pm * Qm * X = X := by rw [← add_mul, Qm_Pm_add_Pm_Qm, one_mul]
  simp only [sMat, hneg, h0, one_smul, neg_smul, sub_neg_eq_add]
  calc Qm * (Pm * X) + Pm * X * Qm
      = (Qm * Pm * X + Pm * Qm * X) - Pm * Qm * X + Pm * X * Qm := by
        rw [mul_assoc Qm Pm X]; abel
    _ = X - Pm * Qm * X + Pm * X * Qm := by rw [h3]
    _ = 1 * X - Pm * (Qm * X - X * Qm) := by
        rw [one_mul, mul_sub, ← mul_assoc, ← mul_assoc]; abel

/-- The `2 × 2` matrix model of a gauge-fixing system: the exterior derivative is
trivial, and the BRST operator is the super-commutator with the nilpotent `Q`. -/
noncomputable def matrixModel : GaugeFixingSystem (fun _ => Mat2) where
  zero := fun _ => 0
  add := fun _ x y => x + y
  sub := fun _ x y => x - y
  mul := fun _ _ x y => x * y
  d := fun _ => 0
  s := fun {_ g} x => sMat g x
  d_zero := fun _ _ => rfl
  sub_zero := fun _ x => sub_zero x
  s_nilpotent := fun _ g x => sMat_nilpotent g x
  s_sub := fun _ g x y => sMat_sub g x y
  sd_commute := fun _ _ _ => sMat_zero _
  phi := 1
  v := Vm
  c := -Qm
  c_bar := Pm
  B := 1
  def_s_v := sMat_Vm
  def_s_phi := sMat_one
  def_s_c_bar := sMat_Pm
  s_mul_c_bar := sMat_leibniz













/-- The evaluation functional of the model: the lower-left matrix entry.  It kills
every BRST-exact term, as `BrstIntegral` requires. -/
noncomputable def matrixModelIntegral : BrstIntegral matrixModel where
  int := fun X => X 1 0
  int_of_s := by
    intro X
    have hneg : ((-1 : ℝ) ^ (-1 : ℤ)) = -1 := by norm_num
    have h1 : (Qm * X) 1 0 = 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, Qm]
    have h2 : (X * Qm) 1 0 = 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, Qm]
    change (sMat (-1) X) 1 0 = 0
    simp [sMat, hneg, Matrix.sub_apply, h1, h2]



end BookProof.GaugeFixing


