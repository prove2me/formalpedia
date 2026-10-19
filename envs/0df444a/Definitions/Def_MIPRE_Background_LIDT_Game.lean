-- Prove2me | Definitions.Def_MIPRE_Background_LIDT_Game
-- name    : MIPRE_Background_LIDT_Game
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-16T23:08:43.744569+00:00
-- url     : https://prove2.me/theorems/d95d70d5-5e14-491c-b38e-31e124b28a49
-- title:
--   Definitions of Game: The classical low individual degree test The `(m, q, d)`-low individual degree test of Ji, Natarajan, Vidick, Wright…
-- statement:
--   The definitions of the module `MIPRE.Background.LIDT.Game` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The classical low individual degree test. The `(m, q, d)`-low individual degree test of Ji, Natarajan, Vidick, Wright and Yuen, *Quantum soundness of the classical low individual degree test* (arXiv:2009.12982, Figure 1), as a two-player game `MIPRE.LIDT.lidtGame` over a finite field `F` with `q` elements. With probability `1/3` each, the verifier runs one of three sub-tests, on a uniform point `u ∈ F^m`: * *axis-parallel lines*: one player (chosen at random) receives the line through `u` in a uniform coordinate direction and answers a univariate polynomial `f` of degree `≤ d`, the other…
--
--   **Definitions** (24): `MIPRE.LIDT.Answer` (Answers: a field element, a polynomial of degree `≤ d`, or one of degree `≤ m·d`.); `MIPRE.LIDT.Answer.toValue` (The field element answered to a point question; ill-typed answers are read as `0` (they are rejected by the test, so this only helps the…); `MIPRE.LIDT.Line` (A line in `F^m`, presented by a base point and a direction: `{base + t • direction}`.); `MIPRE.LIDT.Line.Mem` (Membership of a point in a line.); `MIPRE.LIDT.Line.instDecidablePredPointMem`; `MIPRE.LIDT.Line.param` (The parameter of a point of a canonically presented line: its coordinate at the first nonzero coordinate of the direction (`0` for a…); `MIPRE.LIDT.Line.through` (The canonical presentation of the line through `u` in direction `v`: if `v ≠ 0` and `j` is its first nonzero coordinate, the direction is…); `MIPRE.LIDT.LinePoly` (Univariate polynomials over `F` of degree at most `n`, given by their coefficients.); `MIPRE.LIDT.LinePoly.eval` (Evaluation of a polynomial of degree at most `n`.); `MIPRE.LIDT.LowIndDegPoly` (Polynomials in `m` variables of individual degree at most `d`, given by their coefficients on the monomials `∏ᵢ Xᵢ^(eᵢ)` with all `eᵢ ≤ d`.); `MIPRE.LIDT.LowIndDegPoly.eval` (Evaluation at a point of `F^m`.); `MIPRE.LIDT.Point` (Points of `F^m`.); `MIPRE.LIDT.Question` (Questions: a point, an axis-parallel line, or a (diagonal) line.); and -8 more.
--
--   **Embedded lemmas** (2): the small results the bodies of these definitions need (proof fields, `simp` rules, decidability and finiteness instances), proved inside the bundle so that it imports no unproved statement: `sum_weight`, `weight_nonneg`.
--
--   **Formalization Note** The bundle is the module `MIPRE.Background.LIDT.Game` (`MIPRE/Background/LIDT/Game.lean`) with every declaration not listed removed, imports rewritten to the bundles of the module's import closure; the declarations keep their names, statements and bodies; the source module is split over 2 imported bundle(s).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Game.lean; blueprint def:lidt

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Game.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances

/-!
# The classical low individual degree test

The `(m, q, d)`-low individual degree test of Ji, Natarajan, Vidick, Wright and Yuen,
*Quantum soundness of the classical low individual degree test* (arXiv:2009.12982,
Figure 1), as a two-player game `MIPRE.LIDT.lidtGame` over a finite field `F` with `q`
elements. With probability `1/3` each, the verifier runs one of three sub-tests, on a
uniform point `u ∈ F^m`:

* *axis-parallel lines*: one player (chosen at random) receives the line through `u` in a
  uniform coordinate direction and answers a univariate polynomial `f` of degree `≤ d`,
  the other receives `u` and answers `a ∈ F`; accept iff `f(u) = a`;
* *self-consistency*: both receive `u`, accept iff the answers agree;
* *diagonal lines*: as the first test, with the line through `u` in a direction `v`
  uniform among the vectors whose coordinates beyond a uniform index `j` vanish (`v = 0`,
  a singleton line, is allowed), and a polynomial of degree `≤ m·d`.

Polynomials are represented by their coefficients (`LinePoly`), so that the alphabets are
finite types without further ado. A line is a pair `(base, direction)`; the verifier only
ever asks the *canonical* presentation `Line.through u v` of a line (direction rescaled so
that its first nonzero coordinate is `1`, base point moved so that this coordinate is
`0`), so that a line is the same question however it was sampled. Line answers are
polynomials in the parameter `t` of `base + t • direction`, and are evaluated at the
parameter `Line.param ℓ u` of the sampled point. The question distribution is the
push-forward of the verifier's random choices `Sample`.
-/

namespace MIPRE.LIDT

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d : ℕ)

/-- Points of `F^m`. -/
abbrev Point := Fin m → F

/-- Univariate polynomials over `F` of degree at most `n`, given by their coefficients. -/
abbrev LinePoly (n : ℕ) := Fin (n + 1) → F

/-- Evaluation of a polynomial of degree at most `n`. -/
def LinePoly.eval {F : Type*} [Field F] {n : ℕ} (f : LinePoly F n) (t : F) : F :=
  ∑ i, f i * t ^ (i : ℕ)

/-- A line in `F^m`, presented by a base point and a direction: `{base + t • direction}`. -/
abbrev Line := Point F m × Point F m

namespace Line

variable {F m}

/-- The canonical presentation of the line through `u` in direction `v`: if `v ≠ 0` and
`j` is its first nonzero coordinate, the direction is `v / v_j` and the base point is the
point of the line with vanishing `j`-th coordinate; if `v = 0`, the pair `(u, 0)`. -/
noncomputable def through (u v : Point F m) : Line F m :=
  if h : ∃ j, v j ≠ 0 then
    let j := Fin.find (fun j => v j ≠ 0) h
    (u - u j • ((v j)⁻¹ • v), (v j)⁻¹ • v)
  else (u, 0)

/-- Membership of a point in a line. -/
def Mem (ℓ : Line F m) (x : Point F m) : Prop := ∃ t : F, x = ℓ.1 + t • ℓ.2

instance (ℓ : Line F m) : DecidablePred ℓ.Mem := fun _ => by unfold Mem; infer_instance

/-- The parameter of a point of a canonically presented line: its coordinate at the first
nonzero coordinate of the direction (`0` for a singleton line). -/
noncomputable def param (ℓ : Line F m) (x : Point F m) : F :=
  if h : ∃ j, ℓ.2 j ≠ 0 then x (Fin.find (fun j => ℓ.2 j ≠ 0) h) else 0

end Line

/-- Questions: a point, an axis-parallel line, or a (diagonal) line. -/
inductive Question
  | point (u : Point F m)
  | axisLine (ℓ : Line F m)
  | diagLine (ℓ : Line F m)
  deriving DecidableEq, Fintype

/-- Answers: a field element, a polynomial of degree `≤ d`, or one of degree `≤ m·d`. -/
inductive Answer
  | value (a : F)
  | axisPoly (f : LinePoly F d)
  | diagPoly (f : LinePoly F (m * d))
  deriving DecidableEq, Fintype

/-- The verifier's random choices: the sub-test, whether the roles are swapped (the line
goes to player B), the point `u`, the direction index `i` or `j`, and for diagonal lines
the first `j + 1` coordinates of the direction (the others vanish). -/
inductive Sample
  | axis (swap : Bool) (u : Point F m) (i : Fin m)
  | selfConsistency (u : Point F m)
  | diag (swap : Bool) (u : Point F m) (j : Fin m) (v : Fin (j.val + 1) → F)
  deriving DecidableEq, Fintype

namespace Sample

variable {F m}

/-- The probability of a sample: each sub-test has probability `1/3`, and within a sub-test
the swap, the point, the direction index and the direction are uniform. -/
noncomputable def weight : Sample F m → ℝ
  | axis _ _ _ => 1 / (6 * m * Fintype.card (Point F m))
  | selfConsistency _ => 1 / (3 * Fintype.card (Point F m))
  | diag _ _ j _ => 1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ) ^ (j.val + 1))

omit [DecidableEq F] in
theorem weight_nonneg (s : Sample F m) : 0 ≤ s.weight := by
  cases s <;> simp only [weight] <;> positivity

/-- Samples as a disjoint union of products, for summing over them. -/
def equivSum : Sample F m ≃
    (Bool × Point F m × Fin m) ⊕ Point F m ⊕ (Bool × Point F m × Σ j : Fin m, Fin (j.val + 1) → F) where
  toFun
    | axis b u i => .inl (b, u, i)
    | selfConsistency u => .inr (.inl u)
    | diag b u j v => .inr (.inr (b, u, ⟨j, v⟩))
  invFun
    | .inl (b, u, i) => axis b u i
    | .inr (.inl u) => selfConsistency u
    | .inr (.inr (b, u, ⟨j, v⟩)) => diag b u j v
  left_inv s := by cases s <;> rfl
  right_inv x := by rcases x with ⟨b, u, i⟩ | u | ⟨b, u, j, v⟩ <;> rfl

omit [DecidableEq F] in
/-- The total probability is one (for `m ≠ 0`). -/
theorem sum_weight [NeZero m] : ∑ s : Sample F m, s.weight = 1 := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hQ : (Fintype.card (Point F m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← equivSum.symm.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma, equivSum,
    Equiv.coe_fn_symm_mk, weight, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    Fintype.card_fin, Fintype.card_fun, Fintype.card_prod, nsmul_eq_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_mul]
  have hdiag : ∀ j : Fin m, ((Fintype.card F : ℝ) ^ (j.val + 1)) *
      (1 / (6 * m * (Fintype.card F : ℝ) ^ m * (Fintype.card F : ℝ) ^ (j.val + 1))) =
      1 / (6 * m * (Fintype.card F : ℝ) ^ m) := by
    intro j
    field_simp
  simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The direction with the given first `j + 1` coordinates and vanishing other coordinates. -/
def extend {j : Fin m} (v : Fin (j.val + 1) → F) : Point F m :=
  fun k => if h : k.val ≤ j.val then v ⟨k.val, Nat.lt_succ_of_le h⟩ else 0

/-- The question pair of a sample (first component to player A). -/
noncomputable def questions : Sample F m → Question F m × Question F m
  | axis swap u i =>
      let p := (Question.axisLine (Line.through u (Pi.single i 1)), Question.point u)
      if swap then p.swap else p
  | selfConsistency u => (.point u, .point u)
  | diag swap u _ v =>
      let p := (Question.diagLine (Line.through u (extend v)), Question.point u)
      if swap then p.swap else p

end Sample

/-- The decision predicate: a line answer `f` and a point answer `a` are accepted iff the
point lies on the line and `f` evaluated at the parameter of the point is `a`; two point
answers are accepted iff the points are equal and the answers agree. -/
noncomputable def accepts : Question F m → Question F m → Answer F m d → Answer F m d → Bool
  | .axisLine ℓ, .point x, .axisPoly f, .value a => decide (ℓ.Mem x ∧ f.eval (ℓ.param x) = a)
  | .point x, .axisLine ℓ, .value a, .axisPoly f => decide (ℓ.Mem x ∧ f.eval (ℓ.param x) = a)
  | .point x, .point y, .value a, .value b => decide (x = y ∧ a = b)
  | .diagLine ℓ, .point x, .diagPoly f, .value a => decide (ℓ.Mem x ∧ f.eval (ℓ.param x) = a)
  | .point x, .diagLine ℓ, .value a, .diagPoly f => decide (ℓ.Mem x ∧ f.eval (ℓ.param x) = a)
  | _, _, _, _ => false

/-- The `(m, q, d)`-low individual degree test as a game, `q = Fintype.card F`, `m ≠ 0`. -/
noncomputable def lidtGame [NeZero m] :
    Game (Question F m) (Question F m) (Answer F m d) (Answer F m d) where
  μ x y := ∑ s : Sample F m, s.weight * if s.questions = (x, y) then 1 else 0
  μ_nonneg _ _ := Finset.sum_nonneg fun s _ =>
    mul_nonneg s.weight_nonneg (by split_ifs <;> norm_num)
  μ_sum_one := by
    rw [← Fintype.sum_prod_type', Finset.sum_comm]
    simp only [← Finset.mul_sum, Prod.mk.eta, Fintype.sum_ite_eq, mul_one]
    exact Sample.sum_weight
  D := accepts F m d

/-! ## Vocabulary for the soundness theorem -/

variable {F m d} [NeZero m]

/-- Polynomials in `m` variables of individual degree at most `d`, given by their
coefficients on the monomials `∏ᵢ Xᵢ^(eᵢ)` with all `eᵢ ≤ d`. -/
abbrev LowIndDegPoly := (Fin m → Fin (d + 1)) → F

/-- Evaluation at a point of `F^m`. -/
def LowIndDegPoly.eval (p : LowIndDegPoly (F := F) (m := m) (d := d)) (u : Point F m) : F :=
  ∑ e, p e * ∏ i, u i ^ (e i : ℕ)

/-- The field element answered to a point question; ill-typed answers are read as `0`
(they are rejected by the test, so this only helps the strategy). -/
def Answer.toValue : Answer F m d → F
  | .value a => a
  | _ => 0

/-- The point measurements of player A in a strategy for the test, as POVMs with outcomes
in `F`. -/
noncomputable def pointPOVMA (S : TensorProductStrategy (lidtGame F m d)) (u : Point F m) :
    POVM F (Fin S.dA) :=
  (S.PA.toPOVM (.point u)).map Answer.toValue

/-- The point measurements of player B in a strategy for the test, as POVMs with outcomes
in `F`. -/
noncomputable def pointPOVMB (S : TensorProductStrategy (lidtGame F m d)) (u : Point F m) :
    POVM F (Fin S.dB) :=
  (S.PB.toPOVM (.point u)).map Answer.toValue

/-- Evaluation at `u` of a measurement `G` with polynomial outcomes: the POVM with outcomes
in `F` whose operator for `a` is the sum of the operators of the polynomials `p` with
`p(u) = a`. -/
noncomputable def evalPOVM {n : Type*} [Fintype n] [DecidableEq n]
    (G : ProjectiveMeasurement Unit (LowIndDegPoly (F := F) (m := m) (d := d)) (Matrix n n ℂ))
    (u : Point F m) : POVM F n :=
  (G.toPOVM ()).map fun p => p.eval u

/-- The error bound of the soundness theorem, as proved in the MIPStarRE development:
`100000 · k² · m⁴ · (ε^(1/40000) + (d/q)^(1/40000) + exp(−k / (2560000 m²)))`. -/
noncomputable def lidtError (m d q k : ℕ) (ε : ℝ) : ℝ :=
  100000 * (k : ℝ) ^ 2 * (m : ℝ) ^ 4 *
    (ε ^ (1 / 40000 : ℝ) + ((d : ℝ) / q) ^ (1 / 40000 : ℝ) +
      Real.exp (-(k : ℝ) / (2560000 * (m : ℝ) ^ 2)))

end MIPRE.LIDT


