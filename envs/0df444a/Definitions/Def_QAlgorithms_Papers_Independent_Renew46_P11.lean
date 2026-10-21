-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P11
-- name    : QAlgorithms_Papers_Independent_Renew46_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:05:51.489002+00:00
-- url     : https://prove2.me/theorems/d2bb05ca-eb68-46a0-80d5-a742040855df
-- title:
--   Definitions for Product formulas in functional calculi for sectorial operators
-- statement:
--   The objects the formalized statements of *Product formulas in functional calculi for sectorial operators* (arXiv:1309.0318) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ElementaryCalculus`: Section 2.1, PDF p.4: the possibly nonunital elementary algebra and its bounded representation. The map outside E is never used as an evaluation.
--   - `IsRegularizer`: Section 2.1, PDF p.4: injective bounded elementary regularisers.
--   - `IsProper`: Section 2.1, PDF p.4: properness requires a regulariser for the algebra unit.
--   - `Regularisable`: Section 2.1, PDF p.4: the actual regularisable subalgebra carrier.
--   - `calculusValue`: Section 2.1, PDF p.4: the graph of rho(e)^(-1)rho(ef), with e selected from Reg(f). The empty graph fallback is used only outside Fr.
--   - `RegularInverse`: An algebra inverse belonging to Fr, rather than a formal total reciprocal.
--   - `graphPrecompose`: Precomposition by a bounded map, retaining domains (PDF p.6).
--   - `graphPostcompose`: Postcomposition by a bounded map, retaining domains (PDF p.6).
--   - `PositiveReal`: Positive scalar argument carrier for Section 4.1, PDF p.11.
--   - `StieltjesRepresentation`: Equation (4.1), PDF p.11. Radon measures on the locally compact, second-countable half-line are represented by locally finite Borel measures. Positive-argument kernels are explicitly integrable to exclude Bochner fallback values; this follows from the weighted condition (4.2).
--   - `StieltjesClass`: Generalised Stieltjes class S_alpha, including constants and mass at zero (Section 4.1, PDF pp.11–12). Only positive orders are used in statements.
--   - `BoundedStieltjesRepresentation`: Finite positive measure representation (4.3) without the singular term; atoms at zero supply constants (Section 4.1, PDF pp.12–13).
--   - `BoundedStieltjesClass`: The bounded generalised Stieltjes class S_alpha,b (PDF p.12).
--   - `cutPlane`: The cut plane C \ (-infinity,0], Section 4.1, PDF p.11.
--   - `CutSymbol`: One common symbol carrier for the Stieltjes and Bernstein algebras.
--   - `symbolExtension`: The zero extension is used only to express differentiability on the cut plane and to evaluate at points known to be in it.
--   - `ComplexStieltjesClass`: Holomorphic extensions of S_alpha, Section 4.1, PDF p.11.
--   - `ComplexStieltjesSpan`: Complex linear span S_tilde_n, Section 4.1, PDF p.13.
--   - `reciprocalPullback`: Inversion of the scalar argument, Section 4.3, PDF p.16. The cut plane is invariant under this inversion.
--   - `TildeTOrder`: T_tilde_n, using the equivalent condition f(1/z) in S_tilde_n explicitly stated after (4.12), PDF p.16.
--   - `TildeT`: The positive-order union T_tilde, Section 4.3, PDF p.17.
--   - `CompletelyMonotone`: Section 5.1, PDF p.26: complete monotonicity on the open positive axis. Smoothness is included, so total derivatives cannot vanish by default.
--   - `Bernstein`: Bernstein functions, Section 5.1, PDF p.26.
--   - `HolomorphicBernstein`: The holomorphic extension of a Bernstein function to the right half-plane (Section 5.1, PDF pp.26–27). Outside that half-plane values are unused.
--   - `SpecialBernstein`: Nonzero special Bernstein functions, Section 5.1, PDF p.27.
--   - `LaplaceImage`: A_+^1(C_+), PDF p.26, as scalar Laplace transforms. A finite complex Radon measure is represented by a finite positive Borel measure and an integrable complex density. This represents every such measure and preserves zero atoms. Equality holds on the whole half-plane.
-- source:
--   Product formulas in functional calculi for sectorial operators, arXiv:1309.0318v2, https://arxiv.org/abs/1309.0318v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P06

/-! Batty–Gomilko–Tomilov, arXiv:1309.0318v2. Graphs preserve actual domains.
Concrete calculi not constructed here are explicitly deferred in HARD.md.
Compilation is pending the requested batch handoff. -/

noncomputable section

attribute [local instance] Classical.propDecidable

open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace QAlgorithms.Papers.Independent.Renew46.P11

open QAlgorithms.Papers.Independent.Next46.P06
open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore restrictGraph)

universe u v w

variable {F : Type u} [CommRing F] [Algebra ℂ F]
variable {X : Type v} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable {Y : Type w} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- Section 2.1, PDF p.4: the possibly nonunital elementary algebra and its
bounded representation. The map outside E is never used as an evaluation. -/
structure ElementaryCalculus (F : Type u) [CommRing F] [Algebra ℂ F]
    (X : Type v) [NormedAddCommGroup X] [NormedSpace ℂ X] where
  elementary : Set F
  rho : F → X →L[ℂ] X
  representation : AlgebraRepresentationOn rho elementary

/-- Section 2.1, PDF p.4: injective bounded elementary regularisers. -/
def IsRegularizer (C : ElementaryCalculus F X) (f e : F) : Prop :=
  e ∈ C.elementary ∧ e * f ∈ C.elementary ∧ Function.Injective (C.rho e)

/-- Section 2.1, PDF p.4: properness requires a regulariser for the algebra unit. -/
def IsProper (C : ElementaryCalculus F X) : Prop := ∃ e, IsRegularizer C 1 e

/-- Section 2.1, PDF p.4: the actual regularisable subalgebra carrier. -/
def Regularisable (C : ElementaryCalculus F X) (f : F) : Prop :=
  ∃ e, IsRegularizer C f e

/-- Section 2.1, PDF p.4: the graph of rho(e)^(-1)rho(ef), with e selected
from Reg(f). The empty graph fallback is used only outside Fr. -/
def calculusValue (C : ElementaryCalculus F X) (f : F) : Graph X :=
  if h : Regularisable C f then
    let e := Classical.choose h
    {p | C.rho (e * f) p.1 = C.rho e p.2}
  else ∅

/-- An algebra inverse belonging to Fr, rather than a formal total reciprocal. -/
def RegularInverse (C : ElementaryCalculus F X) (f q : F) : Prop :=
  f * q = 1 ∧ Regularisable C q

/-- Precomposition by a bounded map, retaining domains (PDF p.6). -/
def graphPrecompose (B : Graph Y) (u : X →L[ℂ] Y) : Set (X × Y) :=
  {p | (u p.1, p.2) ∈ B}

/-- Postcomposition by a bounded map, retaining domains (PDF p.6). -/
def graphPostcompose (u : X →L[ℂ] Y) (B : Graph X) : Set (X × Y) :=
  {p | ∃ y, (p.1, y) ∈ B ∧ p.2 = u y}

example (C : ElementaryCalculus F X) (e : F) :
    IsRegularizer C 1 e ↔ e ∈ C.elementary ∧ Function.Injective (C.rho e) := by
  simp [IsRegularizer]

example (C : ElementaryCalculus F X) (f : F) (h : ¬ Regularisable C f) :
    calculusValue C f = ∅ := by
  simp [calculusValue, h]

example (u : X →L[ℂ] Y) (x : X) (y : Y) :
    (x, y) ∈ graphPrecompose (identityGraph : Graph Y) u ↔ y = u x := Iff.rfl

/-- Positive scalar argument carrier for Section 4.1, PDF p.11. -/
abbrev PositiveReal := {x : ℝ // 0 < x}

/-- Equation (4.1), PDF p.11. Radon measures on the locally compact,
second-countable half-line are represented by locally finite Borel measures.
Positive-argument kernels are explicitly integrable to exclude Bochner
fallback values; this follows from the weighted condition (4.2). -/
def StieltjesRepresentation (alpha : ℝ) (f : PositiveReal → ℝ)
    (a : ℝ) (mu : Measure ℝ≥0) : Prop :=
  0 ≤ a ∧ IsLocallyFiniteMeasure mu ∧
  Integrable (fun t : ℝ≥0 => Real.rpow (1 + (t : ℝ)) (-alpha)) mu ∧
  ∀ z : PositiveReal,
    Integrable (fun t : ℝ≥0 => Real.rpow (z.1 + (t : ℝ)) (-alpha)) mu ∧
    f z = a + ∫ t : ℝ≥0, Real.rpow (z.1 + (t : ℝ)) (-alpha) ∂mu

/-- Generalised Stieltjes class S_alpha, including constants and mass at zero
(Section 4.1, PDF pp.11–12). Only positive orders are used in statements. -/
def StieltjesClass (alpha : ℝ) : Set (PositiveReal → ℝ) :=
  {f | ∃ a mu, StieltjesRepresentation alpha f a mu}

/-- Finite positive measure representation (4.3) without the singular term;
atoms at zero supply constants (Section 4.1, PDF pp.12–13). -/
def BoundedStieltjesRepresentation (alpha : ℝ) (f : PositiveReal → ℝ)
    (nu : Measure ℝ≥0) : Prop :=
  IsFiniteMeasure nu ∧ ∀ z : PositiveReal,
    Integrable (fun s : ℝ≥0 => Real.rpow (1 + z.1 * (s : ℝ)) (-alpha)) nu ∧
    f z = ∫ s : ℝ≥0, Real.rpow (1 + z.1 * (s : ℝ)) (-alpha) ∂nu

/-- The bounded generalised Stieltjes class S_alpha,b (PDF p.12). -/
def BoundedStieltjesClass (alpha : ℝ) : Set (PositiveReal → ℝ) :=
  {f | f ∈ StieltjesClass alpha ∧ ∃ nu, BoundedStieltjesRepresentation alpha f nu}

example (alpha a : ℝ) (ha : 0 ≤ a) :
    StieltjesRepresentation alpha (fun _ => a) a 0 := by
  refine ⟨ha, inferInstance, ?_, ?_⟩
  · simp
  · intro z
    simp

example (z : PositiveReal) : Real.rpow (1 + z.1 * (0 : ℝ)) (-(1 : ℝ)) = 1 := by
  simp

/-- The cut plane C \ (-infinity,0], Section 4.1, PDF p.11. -/
def cutPlane : Set ℂ := {z | z ≠ 0 ∧ |z.arg| < Real.pi}

/-- One common symbol carrier for the Stieltjes and Bernstein algebras. -/
abbrev CutSymbol := cutPlane → ℂ

/-- The zero extension is used only to express differentiability on the cut
plane and to evaluate at points known to be in it. -/
def symbolExtension (f : CutSymbol) (z : ℂ) : ℂ :=
  if hz : z ∈ cutPlane then f ⟨z, hz⟩ else 0

/-- Holomorphic extensions of S_alpha, Section 4.1, PDF p.11. -/
def ComplexStieltjesClass (alpha : ℝ) : Set CutSymbol :=
  {f | DifferentiableOn ℂ (symbolExtension f) cutPlane ∧
    ∃ g ∈ StieltjesClass alpha, ∀ x : PositiveReal,
      symbolExtension f (x.1 : ℂ) = (g x : ℂ)}

/-- Complex linear span S_tilde_n, Section 4.1, PDF p.13. -/
def ComplexStieltjesSpan (n : ℕ) : Submodule ℂ CutSymbol :=
  Submodule.span ℂ (ComplexStieltjesClass (n : ℝ))

/-- Inversion of the scalar argument, Section 4.3, PDF p.16.
The cut plane is invariant under this inversion. -/
def reciprocalPullback (f : CutSymbol) : CutSymbol :=
  fun z => symbolExtension f (z.1⁻¹)

/-- T_tilde_n, using the equivalent condition f(1/z) in S_tilde_n
explicitly stated after (4.12), PDF p.16. -/
def TildeTOrder (n : ℕ) : Set CutSymbol :=
  {f | reciprocalPullback f ∈ ComplexStieltjesSpan n}

/-- The positive-order union T_tilde, Section 4.3, PDF p.17. -/
def TildeT : Set CutSymbol := {f | ∃ n : ℕ, 0 < n ∧ f ∈ TildeTOrder n}

example (f : CutSymbol) : symbolExtension f 0 = 0 := by
  simp [symbolExtension, cutPlane]

example (f : CutSymbol) (n : ℕ) :
    f ∈ TildeTOrder n ↔ reciprocalPullback f ∈ ComplexStieltjesSpan n := Iff.rfl

/-- Section 5.1, PDF p.26: complete monotonicity on the open positive axis.
Smoothness is included, so total derivatives cannot vanish by default. -/
def CompletelyMonotone (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Set.Ioi 0) ∧
  ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n f x

/-- Bernstein functions, Section 5.1, PDF p.26. -/
def Bernstein (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Set.Ioi 0) ∧ (∀ x, 0 < x → 0 ≤ f x) ∧
  CompletelyMonotone (deriv f)

/-- The holomorphic extension of a Bernstein function to the right half-plane
(Section 5.1, PDF pp.26–27). Outside that half-plane values are unused. -/
def HolomorphicBernstein (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f {z | 0 < z.re} ∧
  Bernstein (fun x : ℝ => (f (x : ℂ)).re) ∧
  ∀ x : ℝ, 0 < x → (f (x : ℂ)).im = 0

/-- Nonzero special Bernstein functions, Section 5.1, PDF p.27. -/
def SpecialBernstein (f : ℂ → ℂ) : Prop :=
  HolomorphicBernstein f ∧ (∃ x : ℝ, 0 < x ∧ f (x : ℂ) ≠ 0) ∧
  HolomorphicBernstein (fun z => z / f z)

/-- A_+^1(C_+), PDF p.26, as scalar Laplace transforms.
A finite complex Radon measure is represented by a finite positive Borel
measure and an integrable complex density. This represents every such
measure and preserves zero atoms. Equality holds on the whole half-plane. -/
def LaplaceImage (f : ℂ → ℂ) : Prop :=
  ∃ (mu : Measure ℝ≥0) (h : ℝ≥0 → ℂ), IsFiniteMeasure mu ∧ Integrable h mu ∧
    ∀ z : ℂ, 0 < z.re →
      Integrable (fun t : ℝ≥0 => Complex.exp (-((t : ℝ) : ℂ) * z) * h t) mu ∧
      f z = ∫ t : ℝ≥0, Complex.exp (-((t : ℝ) : ℂ) * z) * h t ∂mu

example : LaplaceImage (fun _ => 0) := by
  refine ⟨0, (fun _ => 0), inferInstance, ?_, ?_⟩
  · simp
  · intro z hz
    simp

end QAlgorithms.Papers.Independent.Renew46.P11


