-- Prove2me | Definitions.Def_sticky_kakeya4_core
-- name    : sticky_kakeya4_core
-- status  : Definition
-- author  : @sensei
-- created : 2026-09-26T03:03:58.834612+00:00
-- url     : https://prove2.me/theorems/89398fcb-2731-4915-998e-37b47bf42624
-- title:
--   Marked lines, packing dimension, and finite-scale source interfaces in R4
-- statement:
--   This module fixes the complete interface used by the mission.  It defines valid marked oriented lines in $\mathbb R^4$, direction selectors, their unit fronts, covering numbers, upper Minkowski dimension, packing dimension, and compact full-direction Sticky data.
--
--   It also defines shaded and weighted finite-scale sources.  Each source retains its affine fibre mark and an arbitrary finite nested carrier tree.  Fractional source restrictions may lower weights and replace shadings by measurable subsets while keeping the lines, marks, and tree; retained descendant restrictions are recorded separately.  The module states three proof interfaces: a coherent normalized discretization of one front probability measure at every small scale, a uniform $L^2$/union estimate for every fractional restriction, and Frostman probability measures on the selector front.
--
--   The collision residual and the matrix-pencil/Lagrangian-incidence model supply the contact--symplectic local geometry used by the finite-scale estimate.
-- source:
--   Chenxi Cai, source manuscript https://cchx0000.github.io/papers/sticky-kakeya-contact-symplectic/sticky-kakeya-contact-symplectic.pdf, Sections 2--9 and the finite-scale/Frostman interfaces in Section 9 and Appendix B.

import Mathlib

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

namespace StickyKakeya4

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev MarkedLine := (E4 × E4) × ℝ

def direction (line : MarkedLine) : E4 := line.1.1
def offset (line : MarkedLine) : E4 := line.1.2
def mark (line : MarkedLine) : ℝ := line.2

def IsValidLine (line : MarkedLine) : Prop :=
  ‖direction line‖ = 1 ∧ inner ℝ (offset line) (direction line) = 0

def lineCarrier (lines : Set MarkedLine) : Set (E4 × E4) :=
  (fun line => (direction line, offset line)) '' lines

def FullDirection (lines : Set MarkedLine) : Prop :=
  ∀ θ : E4, ‖θ‖ = 1 → ∃ line ∈ lines, direction line = θ

def IsDirectionSelector (lines : Set MarkedLine) : Prop :=
  ∀ θ : E4, ‖θ‖ = 1 → ∃! line, line ∈ lines ∧ direction line = θ

def unitFront (lines : Set MarkedLine) : Set E4 :=
  {x | ∃ line ∈ lines, ∃ t ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ),
    x = offset line + (mark line + t) • direction line}

def coversAtRadius {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (r : ℝ) (centers : Finset X) : Prop := by
  classical
  exact s ⊆ ⋃ x ∈ (centers : Set X), Metric.ball x r

def coveringNumber {X : Type*} [PseudoMetricSpace X]
    (s : Set X) (r : ℝ) : ℝ≥0∞ := by
  classical
  exact sInf {n : ℝ≥0∞ | ∃ centers : Finset X,
    coversAtRadius s r centers ∧ n = centers.card}

def upperMinkowskiDim {X : Type*} [PseudoMetricSpace X]
    (s : Set X) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | d ≠ ⊤ ∧ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      coveringNumber s r ≤ C * (ENNReal.ofReal r).rpow (-d.toReal)}

def packingDim {X : Type*} [PseudoMetricSpace X]
    (s : Set X) : ℝ≥0∞ :=
  sInf {d : ℝ≥0∞ | ∃ pieces : ℕ → Set X,
    s ⊆ ⋃ n, pieces n ∧ ∀ n, upperMinkowskiDim (pieces n) ≤ d}

def IsStickyDatum (lines : Set MarkedLine) : Prop :=
  IsCompact lines ∧
  (∀ line ∈ lines, IsValidLine line) ∧
  FullDirection lines ∧
  packingDim (lineCarrier lines) = 3

def collisionTime (α β : E3) : ℝ :=
  -inner ℝ α β / ‖α‖ ^ 2

def collisionResidual (α β : E3) : E3 :=
  β + collisionTime α β • α

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def pencil (A B : Mat3) (s : ℝ) : Mat3 := B + s • A

def graphPlane (A B : Mat3) : Set (E3 × E3) :=
  {(x, y) | ∃ c : E3, x = A.mulVec c ∧ y = B.mulVec c}

def lagrangianPencil (s : ℝ) : Set (E3 × E3) :=
  {(x, y) | y = (-s) • x}

/-!
Finite-scale marked sources.  The tree is part of the data rather than a
cardinality parameter: its cells are nested along parent edges, and the
affine fibre mark is retained separately from the unmarked carrier.
-/

structure NestedCarrierTree (n : ℕ) where
  parent : Fin n → Option (Fin n)
  level : Fin n → ℕ
  parent_level : ∀ {i p}, parent i = some p → level p < level i
  carrierCell : Fin n → Set (E4 × E4)
  nested : ∀ {i p}, parent i = some p → carrierCell i ⊆ carrierCell p

structure FiniteScaleSource (n : ℕ) where
  thickness : ℝ
  line : Fin n → MarkedLine
  shading : Fin n → Set E4
  weight : Fin n → ℝ≥0∞
  fibreMark : Fin n → ℝ
  tree : NestedCarrierTree n
  line_in_carrier : ∀ i, (direction (line i), offset (line i)) ∈ tree.carrierCell i

def sourceFunction {n : ℕ} (D : FiniteScaleSource n) (x : E4) : ℝ≥0∞ := by
  classical
  exact ∑ i, if x ∈ D.shading i then D.weight i else 0

def sourceMass {n : ℕ} (D : FiniteScaleSource n) : ℝ≥0∞ :=
  ∫⁻ x, sourceFunction D x ∂volume

def sourceUnion {n : ℕ} (D : FiniteScaleSource n) : Set E4 :=
  {x | 0 < sourceFunction D x}

def ComesFromSelector {n : ℕ} (D : FiniteScaleSource n)
    (selector : Set MarkedLine) : Prop :=
  ∀ i, D.line i ∈ selector

def IsAdmissibleStickySource {n : ℕ} (D : FiniteScaleSource n)
    (ε : ℝ) (C : ℝ≥0∞) : Prop :=
  0 < D.thickness ∧ D.thickness < 1 ∧
  (∀ i, D.weight i ≤ 1) ∧
  (∀ i, D.fibreMark i = mark (D.line i)) ∧
  (∀ i, IsValidLine (D.line i)) ∧
  (∀ i, MeasurableSet (D.shading i)) ∧
  (∀ i x, x ∈ D.shading i →
    Metric.infDist x (unitFront {D.line i}) ≤ D.thickness) ∧
  (∀ r : ℝ, D.thickness ≤ r → r ≤ 1 →
    coveringNumber (lineCarrier (Set.range D.line)) r ≤
      C * (ENNReal.ofReal r).rpow (-(3 + ε)))

def IsFractionalSourceRestriction {n : ℕ}
    (R D : FiniteScaleSource n) : Prop :=
  R.thickness = D.thickness ∧
  R.line = D.line ∧
  R.fibreMark = D.fibreMark ∧
  R.tree = D.tree ∧
  (∀ i, MeasurableSet (R.shading i)) ∧
  (∀ i, R.shading i ⊆ D.shading i) ∧
  ∀ i, R.weight i ≤ D.weight i

def IsCarrierDescendant {n : ℕ} (T : NestedCarrierTree n)
    (child root : Fin n) : Prop :=
  Relation.ReflTransGen (fun i p => T.parent i = some p) child root

def IsRetainedDescendant {n : ℕ} (R D : FiniteScaleSource n)
    (root : Fin n) : Prop :=
  IsFractionalSourceRestriction R D ∧
  ∀ i, 0 < R.weight i → IsCarrierDescendant D.tree i root

/-!
The coherent form is the Hausdorff-scale interface.  A single probability
measure on the physical front is discretized at every small radius.  For each
ball at that radius there is a measurable shading/weight restriction whose
mass dominates the measure of the ball and whose physical union stays in the
doubled ball.  Thus the source-hereditary union estimate can be applied at the
same radius as the desired Frostman bound.
-/

def HasCoherentFiniteScaleSources (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
    ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      μ (unitFront selector)ᶜ = 0 ∧
      ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        ∃ n : ℕ, ∃ D : FiniteScaleSource n,
          D.thickness = δ ∧
          ComesFromSelector D selector ∧
          IsAdmissibleStickySource D ε C ∧
          C⁻¹ ≤ sourceMass D ∧ sourceMass D ≤ C ∧
          ∀ x : E4, ∃ R : FiniteScaleSource n,
            IsFractionalSourceRestriction R D ∧
            sourceUnion R ⊆ Metric.closedBall x (2 * δ) ∧
            μ (Metric.ball x δ) ≤ C * sourceMass R

def HasUniformMarkedSourceEstimate (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ Cpack : ℝ≥0∞, Cpack ≠ 0 → Cpack ≠ ⊤ →
    ∃ A : ℝ≥0∞, A ≠ 0 ∧ A ≠ ⊤ ∧
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ (n : ℕ) (D R : FiniteScaleSource n),
      D.thickness ≤ δ₀ →
      ComesFromSelector D selector →
      IsAdmissibleStickySource D ε Cpack →
      IsFractionalSourceRestriction R D →
      (∫⁻ x, (sourceFunction R x) ^ 2 ∂volume) ≤
          A * (ENNReal.ofReal D.thickness).rpow (-ε) * sourceMass R ∧
      sourceMass R ≤
          A * (ENNReal.ofReal D.thickness).rpow (-ε) * volume (sourceUnion R)

def HasFrontFrostmanMeasures (selector : Set MarkedLine) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 4 →
    ∃ μ : Measure E4,
      IsProbabilityMeasure μ ∧
      μ (unitFront selector)ᶜ = 0 ∧
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ (x : E4) (r : ℝ), 0 < r → r ≤ 1 →
          μ (Metric.ball x r) ≤
            C * (ENNReal.ofReal r).rpow (4 - ε)

end StickyKakeya4


