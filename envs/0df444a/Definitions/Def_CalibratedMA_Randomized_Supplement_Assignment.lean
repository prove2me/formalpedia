-- Prove2me | Definitions.Def_CalibratedMA_Randomized_Supplement_Assignment
-- name    : CalibratedMA_Randomized_Supplement_Assignment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:24:39.944511+00:00
-- url     : https://prove2.me/theorems/f81b62dc-1010-4b94-8ca7-adf9aa964d55
-- title:
--   Section 5.2 — independent finite category assignments and residual changes
-- statement:
--   Fix a finite nonempty measurable test family $G\subseteq[-1,1]^X$, the signed family $H=G\cup(-G)$, a measurable score $S:X\to[0,1]$, and a finite measurable partition labeled by a cell map. A finite list of distinct private points has singleton cells. Fix integers $K,m\ge1$ and $\lambda>0$. For a tuple $\tau\in H^m$ set
--   $$f_\tau(x)=\frac1m\sum_{\ell=1}^m h_\ell(x),\quad
--   u_j=-1+j\frac{\lambda+2}{K},\quad w=\frac{\lambda+2}{K}.$$
--   The nearest grid point to $f_\tau(x)+\lambda S(x)$ determines the nominal category, with ties broken by smaller index. Private points get distinct categories. For a probability law $\pi$ on $H$, tuples are drawn independently with law $\pi^m$ for each nonprivate cell. Independent unused tuples at private cells do not affect the assignment or its law. Category means are computed from the context law; private points retain $S$ even when their mass is zero, while empty nominal categories receive zero.
--
--   For this actual construction define
--   $$F_h(\omega)=\mathbb E_P[h(X)(S(X)-p_\omega(X))],\quad V(\omega)=\mathbb E_P[(S(X)-p_\omega(X))^2],$$
--   $$d_h(\pi)=\mathbb E_\omega F_h(\omega),\quad\bar V(\pi)=\mathbb E_\omega V(\omega),\quad e_{\rm app}=w/2+1/\sqrt m.$$
--   Mass bounds concern nonprivate assignment cells. A score-diameter bound concerns each category under every assignment. Finite indices enumerate actual signed tests, and never count duplicate functions twice. The structure stores only inputs and validity conditions, with no fixed-point, residual or variance guarantee.
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), pp.23–24, Section 5.2, Eq. (11), Eq. (12); p.47, Lemma A.1

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Categories

open MeasureTheory
open scoped ENNReal

namespace CalibratedMA.Randomized.Supplement

noncomputable def signedTests {X : Type} (G : Finset (X → ℝ)) : Finset (X → ℝ) := by
  classical
  exact G ∪ G.image (fun g x => -g x)

/-- Section 5.2's finite construction, before choosing the test mixture.
The cell map labels a finite measurable partition. Empty cells are harmless.
Each private point has a singleton cell. No distribution or residual guarantee is stored. -/
structure AssignmentConfig (X : Type) [MeasurableSpace X] where
  G : Finset (X → ℝ)
  nonempty_tests : G.Nonempty
  valid_tests : ∀ g ∈ G, Measurable g ∧ ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1
  S : X → ℝ
  valid_score : IsDetPredictor S
  numCells : ℕ
  cell : X → Fin numCells
  measurable_cell : Measurable cell
  numPrivate : ℕ
  privatePoint : Fin numPrivate → X
  private_injective : Function.Injective privatePoint
  private_cell : ∀ i x, cell x = cell (privatePoint i) ↔ x = privatePoint i
  K : ℕ
  positive_K : 0 < K
  m : ℕ
  positive_m : 0 < m
  lam : ℝ
  positive_lam : 0 < lam

/-- Finite indices avoid any measurable-space convention on a type of test functions. -/
noncomputable def testAt {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (i : Fin (signedTests c.G).card) : X → ℝ :=
  (signedTests c.G).equivFin.symm i

noncomputable def sparseAverage {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (τ : Fin c.m → Fin (signedTests c.G).card) (x : X) : ℝ :=
  (c.m : ℝ)⁻¹ * ∑ l : Fin c.m, testAt c (τ l) x

noncomputable def gridValue {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (j : Fin (c.K + 1)) : ℝ := -1 + j.val * ((c.lam + 2) / c.K)

/-- Distance followed by smaller index fixes all grid ties. -/
noncomputable def nearestGrid {X : Type} [MeasurableSpace X]
    (c : AssignmentConfig X) (z : ℝ) : Fin (c.K + 1) := by
  classical
  exact ((Finset.univ : Finset (Fin (c.K + 1))).toList.mergeSort (fun i j =>
    decide (|z - gridValue c i| < |z - gridValue c j| ∨
      (|z - gridValue c i| = |z - gridValue c j| ∧ i.val ≤ j.val)))).headD 0

/-- An independent m-tuple of tests for each cell. Private-cell tuples are ignored. -/
abbrev Assignments {X : Type} [MeasurableSpace X] (c : AssignmentConfig X) :=
  Fin c.numCells → Fin c.m → Fin (signedTests c.G).card

/-- Product test-mixture law, with independence across both cells and tuple positions. -/
noncomputable def assignmentLaw {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (π : Measure (Fin (signedTests c.G).card)) : Measure (Assignments c) :=
  Measure.pi (fun _ : Fin c.numCells => Measure.pi (fun _ : Fin c.m => π))

/-- Private category indices are K+1,…,K+q; nominal indices are 0,…,K. -/
noncomputable def assignmentCategory {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (ω : Assignments c) (x : X) : Fin (c.K + 1 + c.numPrivate) := by
  classical
  exact if h : ∃ i, x = c.privatePoint i then
    ⟨c.K + 1 + (Classical.choose h).val, by omega⟩
  else ⟨(nearestGrid c (sparseAverage c (ω (c.cell x)) x + c.lam * c.S x)).val, by
    have := (nearestGrid c (sparseAverage c (ω (c.cell x)) x + c.lam * c.S x)).isLt
    omega⟩

/-- Category averages, retaining S at private zero-mass singletons as on p.24. -/
noncomputable def assignmentPredictor {X : Type} [MeasurableSpace X]
    (c : AssignmentConfig X) (P : Measure X) (ω : Assignments c) (x : X) : ℝ := by
  classical
  exact if ∃ i, x = c.privatePoint i then c.S x else
    categoryPredictor P c.S (assignmentCategory c ω) x

noncomputable def assignmentF {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (P : Measure X) (h : X → ℝ) (ω : Assignments c) : ℝ :=
  ∫ x, h x * (c.S x - assignmentPredictor c P ω x) ∂P

noncomputable def assignmentV {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (P : Measure X) (ω : Assignments c) : ℝ :=
  ∫ x, (c.S x - assignmentPredictor c P ω x) ^ 2 ∂P

noncomputable def meanChange {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (P : Measure X) (π : Measure (Fin (signedTests c.G).card)) (h : X → ℝ) : ℝ :=
  ∫ ω, assignmentF c P h ω ∂assignmentLaw c π

noncomputable def meanVariance {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (P : Measure X) (π : Measure (Fin (signedTests c.G).card)) : ℝ :=
  ∫ ω, assignmentV c P ω ∂assignmentLaw c π

noncomputable def approximationError {X : Type} [MeasurableSpace X]
    (c : AssignmentConfig X) : ℝ :=
  (c.lam + 2) / c.K / 2 + 1 / Real.sqrt c.m

/-- The bound b concerns nonprivate cells only. -/
def AssignmentMassBound {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (P : Measure X) (b : ℝ) : Prop :=
  ∀ u : Fin c.numCells, (∀ i, u ≠ c.cell (c.privatePoint i)) →
    (P {x | c.cell x = u}).toReal ≤ b

def CategoryDiameterBound {X : Type} [MeasurableSpace X] (c : AssignmentConfig X)
    (Dcat : ℝ) : Prop :=
  ∀ (ω : Assignments c) (x y : X),
    assignmentCategory c ω x = assignmentCategory c ω y → |c.S x - c.S y| ≤ Dcat

end CalibratedMA.Randomized.Supplement


