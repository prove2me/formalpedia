-- Prove2me | Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity
-- name    : InterleavedUnitaryNOF_LowerBound_Regularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:09:03.744924+00:00
-- url     : https://prove2.me/theorems/687cd239-f8f1-4a47-bfa5-fa4afe966f2d
-- title:
--   Equal-measure finite type, grid norms and normalized local boxes
-- statement:
--   An equal partition is a measurable finite cell-label map with every cell of mass $1/q$. Finite-type cylinders have factors constant on products of these cells. Local boxes carry supported measurable Boolean factors; restrictions of Haar are divided by their own mass.
--
--   $$\|u\|_{U(2,d)}=\left(\mathbb E_{s,s'}[(\mathbb E_t u(s,t)u(s',t))^d]\right)^{1/(2d)}.$$
--
--   Regularity compares this norm to $(1+\epsilon)\mathbb E u$. Minimum degree is a pointwise bound at every point of the stated row domain. The conditional-overlap kernel, local densities, box volumes and regular-index set use these shared definitions. All theorem applications have positive normalized domains and positive moment indices.
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Definitions 4.4, 4.6 and Theorem 4.7 context, pp.11–13; §§4.2–4.3, pp.15–17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Distributions

open MeasureTheory
open scoped ENNReal

namespace InterleavedUnitaryNOF.LowerBound

/-- Equal-measure cells cover every point, including null exceptional points. -/
structure EqualPartition (S : Type*) [MeasurableSpace S] (μ : Measure S) where
  count : ℕ
  positive : 0 < count
  label : S → Fin count
  measurable_label : Measurable label
  equal_mass : ∀ i, μ (label ⁻¹' {i}) = (count : ℝ≥0∞)⁻¹

def CellConstant {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {μ : Measure S} {ν : Measure T} (P : EqualPartition S μ) (Q : EqualPartition T ν)
    (f : S × T → Bool) : Prop :=
  ∀ s s' t t', P.label s = P.label s' → Q.label t = Q.label t' → f (s,t) = f (s',t')

structure CylinderPartitions {m : ℕ} [NeZero m] (c : Cylinder m) where
  X : EqualPartition (Quart m) (haarPower m 4)
  Y : EqualPartition (Quart m) (haarPower m 4)
  Z : EqualPartition (Duo m) (haarPower m 2)
  constant_f : CellConstant Y Z c.f
  constant_g : CellConstant X Z c.g
  constant_h : CellConstant X Y c.h

def FiniteType {m : ℕ} [NeZero m] (c : Cylinder m) : Prop := Nonempty (CylinderPartitions c)

noncomputable def normalizedRestriction {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (A : Set S) : Measure S := (μ A)⁻¹ • μ.restrict A

noncomputable def density {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) (u : S × T → ℝ) : ℝ := ∫ v, u v ∂(μ.prod ν)

/-- U(2,d), with independent samples and real exponent 1/(2d). -/
noncomputable def gridNorm {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) (u : S × T → ℝ) (d : ℕ) : ℝ :=
  Real.rpow (∫ s, ∫ s', (∫ t, u (s,t) * u (s',t) ∂ν)^d ∂μ ∂μ)
    (1 / (2 * (d : ℝ)))

def Regular {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) (u : S × T → ℝ) (ε : ℝ) (d : ℕ) : Prop :=
  gridNorm μ ν u d ≤ (1+ε) * density μ ν u

def MinDegree {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure S) (ν : Measure T) (domain : Set S) (u : S × T → ℝ) (ε : ℝ) : Prop :=
  ∀ s ∈ domain, (1-ε) * density μ ν u ≤ ∫ t, u (s,t) ∂ν

noncomputable def lpNorm {S : Type*} [MeasurableSpace S]
    (μ : Measure S) (u : S → ℝ) (p : ℕ) : ℝ :=
  Real.rpow (∫ s, |u s|^p ∂μ) (1 / (p : ℝ))

/-- Explicit conditional expectation kernel under μ₁ given X,Y. -/
noncomputable def conditionalOverlap {m : ℕ} [NeZero m]
    (f g : Quart m × Duo m → Bool) (xy : Quart m × Quart m) : ℝ :=
  ∫ e, bval (f (xy.2, ![e,(firstProduct xy.1 xy.2 * e * secondProduct xy.1 xy.2)⁻¹])) *
    bval (g (xy.1, ![e,(firstProduct xy.1 xy.2 * e * secondProduct xy.1 xy.2)⁻¹])) ∂haar m

/-- One supported Boolean pair on a measurable box. No regularity is built in. -/
structure BoxPiece (m : ℕ) where
  X : Set (Quart m)
  Y : Set (Quart m)
  Z : Set (Duo m)
  f : Quart m × Duo m → Bool
  g : Quart m × Duo m → Bool
  measurable_X : MeasurableSet X
  measurable_Y : MeasurableSet Y
  measurable_Z : MeasurableSet Z
  measurable_f : Measurable f
  measurable_g : Measurable g
  support_f : ∀ y z, f (y,z) = true → y ∈ Y ∧ z ∈ Z
  support_g : ∀ x z, g (x,z) = true → x ∈ X ∧ z ∈ Z

noncomputable def BoxPiece.xLaw {m : ℕ} [NeZero m] (B : BoxPiece m) :=
  normalizedRestriction (haarPower m 4) B.X
noncomputable def BoxPiece.yLaw {m : ℕ} [NeZero m] (B : BoxPiece m) :=
  normalizedRestriction (haarPower m 4) B.Y
noncomputable def BoxPiece.zLaw {m : ℕ} [NeZero m] (B : BoxPiece m) :=
  normalizedRestriction (haarPower m 2) B.Z
noncomputable def BoxPiece.df {m : ℕ} [NeZero m] (B : BoxPiece m) :=
  density B.yLaw B.zLaw (bval ∘ B.f)
noncomputable def BoxPiece.dg {m : ℕ} [NeZero m] (B : BoxPiece m) :=
  density B.xLaw B.zLaw (bval ∘ B.g)
noncomputable def BoxPiece.dh {m : ℕ} [NeZero m] (B : BoxPiece m)
    (h : Quart m × Quart m → Bool) := density B.xLaw B.yLaw (bval ∘ h)
noncomputable def BoxPiece.volume {m : ℕ} [NeZero m] (B : BoxPiece m) : ℝ :=
  ((haarPower m 4) B.X).toReal * ((haarPower m 4) B.Y).toReal * ((haarPower m 2) B.Z).toReal
noncomputable def BoxPiece.value {m : ℕ} (B : BoxPiece m)
    (h : Quart m × Quart m → Bool) (u : ContinuousInput m) : ℝ :=
  bval (B.f (u.2.1,u.2.2)) * bval (B.g (u.1,u.2.2)) * bval (h (u.1,u.2.1))

def BoxPiece.Positive {m : ℕ} [NeZero m] (B : BoxPiece m) : Prop :=
  0 < (haarPower m 4) B.X ∧ 0 < (haarPower m 4) B.Y ∧ 0 < (haarPower m 2) B.Z

def BoxPiece.Pseudorandom {m : ℕ} [NeZero m] (B : BoxPiece m) (ε : ℝ) (d : ℕ) : Prop :=
  Regular B.yLaw B.zLaw (bval ∘ B.f) ε d ∧
  Regular B.xLaw B.zLaw (bval ∘ B.g) ε d ∧
  MinDegree B.yLaw B.zLaw B.Y (bval ∘ B.f) ε ∧
  MinDegree B.xLaw B.zLaw B.X (bval ∘ B.g) ε

def UnionOfCells {S : Type*} [MeasurableSpace S] {μ : Measure S}
    (P : EqualPartition S μ) (A : Set S) : Prop :=
  ∃ labels : Finset (Fin P.count), labels.Nonempty ∧ A = P.label ⁻¹' (↑labels : Set (Fin P.count))

def RespectsPartitions {m : ℕ} [NeZero m] {c : Cylinder m}
    (P : CylinderPartitions c) (B : BoxPiece m) : Prop :=
  UnionOfCells P.X B.X ∧ UnionOfCells P.Y B.Y ∧ UnionOfCells P.Z B.Z ∧
  CellConstant P.Y P.Z B.f ∧ CellConstant P.X P.Z B.g

noncomputable def regularIndices {m : ℕ} [NeZero m]
    (pieces : List (BoxPiece m)) (h : Quart m × Quart m → Bool) (ε : ℝ) (d : ℕ) :
    Finset (Fin pieces.length) := by
  classical
  exact Finset.univ.filter (fun i => Real.rpow 2 (-(d : ℝ)) < (pieces.get i).df ∧
    Real.rpow 2 (-(d : ℝ)) < (pieces.get i).dg ∧
    Real.rpow 2 (-ε*d) < (pieces.get i).dh h)

end InterleavedUnitaryNOF.LowerBound


