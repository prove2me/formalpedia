-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P11
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P11
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T23:39:56.590851+00:00
-- url     : https://prove2.me/theorems/d0bd72fa-073b-4152-b5a7-1e22bf61abe3
-- title:
--   Definitions for Quantum dynamical semigroups for diffusion models with Hartree interaction
-- statement:
--   The objects the formalized statements of *Quantum dynamical semigroups for diffusion models with Hartree interaction* (arXiv:math-ph/0309052) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Position`: Cartesian coordinates on real d-space, with its usual product Lebesgue measure.
--   - `L2Space`: The paper's complex L² space, as equivalence classes modulo almost-everywhere equality.
--   - `CoordinateGenerator`: Labels for position and momentum generators, respectively.
--   - `QuadraticExpression`: An ordered polynomial of total degree at most two in position and momentum. The coefficient `quadratic a b` multiplies the composition a after b. Coefficients are arbitrary complex numbers; symmetry and ellipticity are not assumed.
--   - `coordinateDerivative`: Coordinate derivative of a smooth complex function along the kth real coordinate.
--   - `generatorAction`: Position is multiplication by x_k; momentum is -i times the coordinate derivative.
--   - `transposeGeneratorAction`: The bilinear distributional transpose of a coordinate generator: x_k stays unchanged, while -i∂_k becomes +i∂_k. No complex conjugation is taken.
--   - `quadraticAction`: The differential expression p₂(x,-i∇), including constant and linear terms.
--   - `quadraticTransposeAction`: The formal bilinear transpose of the same ordered expression. Transposition reverses each word: (A B)ᵗ = Bᵗ Aᵗ.
--   - `initialQuadraticGraph`: Graph of the initial realization on complex C_c^∞ functions, (3.8), PDF p.8. The explicit MemLp witnesses merely construct the L² classes of the smooth compactly supported function and its polynomial differential expression.
--   - `maximalQuadraticGraph`: Graph of the maximal distributional realization, (3.9), PDF p.8. A pair (u,v) belongs precisely when P u = v as distributions. The integrability clauses prevent the totalized Bochner integral from encoding an undefined pairing. For these compact tests they follow from L² and smoothness.
-- source:
--   Quantum dynamical semigroups for diffusion models with Hartree interaction, arXiv:math-ph/0309052v2, https://arxiv.org/abs/math-ph/0309052v2

import Mathlib

/-!
Statements from Arnold--Sparber, arXiv:math-ph/0309052v2.
Only Lemma 3.3 is drafted here. The other assigned nodes have explicit interface
deferrals in the unit's HARD.md and GAPS.json. No finite-dimensional replacement
of the paper's trace-class evolution is used.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakenext100.P11

/-- Cartesian coordinates on real d-space, with its usual product Lebesgue measure. -/
abbrev Position (d : ℕ) := Fin d → ℝ

/-- The paper's complex L² space, as equivalence classes modulo almost-everywhere equality. -/
abbrev L2Space (d : ℕ) := Lp ℂ 2 (volume : Measure (Position d))

/-- Labels for position and momentum generators, respectively. -/
abbrev CoordinateGenerator (d : ℕ) := Sum (Fin d) (Fin d)

/-- An ordered polynomial of total degree at most two in position and momentum.
The coefficient `quadratic a b` multiplies the composition a after b. Coefficients
are arbitrary complex numbers; symmetry and ellipticity are not assumed. -/
structure QuadraticExpression (d : ℕ) where
  constant : ℂ
  linear : CoordinateGenerator d → ℂ
  quadratic : CoordinateGenerator d → CoordinateGenerator d → ℂ

/-- Coordinate derivative of a smooth complex function along the kth real coordinate. -/
def coordinateDerivative {d : ℕ} (k : Fin d) (f : Position d → ℂ)
    (x : Position d) : ℂ :=
  fderiv ℝ f x (Pi.single k 1)

/-- Position is multiplication by x_k; momentum is -i times the coordinate derivative. -/
def generatorAction {d : ℕ} (a : CoordinateGenerator d)
    (f : Position d → ℂ) : Position d → ℂ :=
  match a with
  | Sum.inl k => fun x => (x k : ℂ) * f x
  | Sum.inr k => fun x => -Complex.I * coordinateDerivative k f x

/-- The bilinear distributional transpose of a coordinate generator: x_k stays
unchanged, while -i∂_k becomes +i∂_k. No complex conjugation is taken. -/
def transposeGeneratorAction {d : ℕ} (a : CoordinateGenerator d)
    (f : Position d → ℂ) : Position d → ℂ :=
  match a with
  | Sum.inl k => fun x => (x k : ℂ) * f x
  | Sum.inr k => fun x => Complex.I * coordinateDerivative k f x

/-- The differential expression p₂(x,-i∇), including constant and linear terms. -/
def quadraticAction {d : ℕ} (P : QuadraticExpression d)
    (f : Position d → ℂ) : Position d → ℂ :=
  fun x => P.constant * f x +
    ∑ a, P.linear a * generatorAction a f x +
    ∑ a, ∑ b, P.quadratic a b * generatorAction a (generatorAction b f) x

/-- The formal bilinear transpose of the same ordered expression. Transposition
reverses each word: (A B)ᵗ = Bᵗ Aᵗ. -/
def quadraticTransposeAction {d : ℕ} (P : QuadraticExpression d)
    (f : Position d → ℂ) : Position d → ℂ :=
  fun x => P.constant * f x +
    ∑ a, P.linear a * transposeGeneratorAction a f x +
    ∑ a, ∑ b, P.quadratic a b *
      transposeGeneratorAction b (transposeGeneratorAction a f) x

/-- Graph of the initial realization on complex C_c^∞ functions, (3.8), PDF p.8.
The explicit MemLp witnesses merely construct the L² classes of the smooth
compactly supported function and its polynomial differential expression. -/
def initialQuadraticGraph {d : ℕ} (P : QuadraticExpression d) :
    Set (L2Space d × L2Space d) :=
  {z | ∃ f : Position d → ℂ, ContDiff ℝ ⊤ f ∧ HasCompactSupport f ∧
    ∃ (hf : MemLp f 2 (volume : Measure (Position d)))
      (hPf : MemLp (quadraticAction P f) 2 (volume : Measure (Position d))),
      z = (hf.toLp f, hPf.toLp (quadraticAction P f))}

/-- Graph of the maximal distributional realization, (3.9), PDF p.8.
A pair (u,v) belongs precisely when P u = v as distributions. The integrability
clauses prevent the totalized Bochner integral from encoding an undefined
pairing. For these compact tests they follow from L² and smoothness. -/
def maximalQuadraticGraph {d : ℕ} (P : QuadraticExpression d) :
    Set (L2Space d × L2Space d) :=
  {z | ∀ test : Position d → ℂ, ContDiff ℝ ⊤ test → HasCompactSupport test →
    Integrable (fun x => z.2 x * test x) volume ∧
    Integrable (fun x => z.1 x * quadraticTransposeAction P test x) volume ∧
    (∫ x, z.2 x * test x) = ∫ x, z.1 x * quadraticTransposeAction P test x}

/-- Sanity check: the zero polynomial has zero action, including at the zero function. -/
example {d : ℕ} (f : Position d → ℂ) :
    quadraticAction (QuadraticExpression.mk 0 (fun _ => 0) (fun _ _ => 0)) f = 0 := by
  funext x
  simp [quadraticAction]

/-- Sanity check pinning the sign of the momentum transpose. -/
example {d : ℕ} (k : Fin d) (f : Position d → ℂ) (x : Position d) :
    transposeGeneratorAction (Sum.inr k) f x =
      Complex.I * fderiv ℝ f x (Pi.single k 1) := by
  rfl

end QAlgorithms.Papers.Independent.Intakenext100.P11


