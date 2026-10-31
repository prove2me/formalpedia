-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P14
-- name    : QAlgorithms_Papers_Independent_Intake100_P14
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:13:12.548568+00:00
-- url     : https://prove2.me/theorems/4e0fdbdc-59ed-459f-8d10-b9f6da065429
-- title:
--   Definitions for Continuity properties of measurable group cohomology
-- statement:
--   The objects the formalized statements of *Continuity properties of measurable group cohomology* (arXiv:1004.4937) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GroupPower`: Cartesian power G^p, with a one-point domain in degree zero (PDF p.12).
--   - `powerMeasure`: Product Haar measure; its empty product has mass one (PDF pp.12--13).
--   - `ModuleAction`: Continuous action by additive automorphisms, with a compatible translation-invariant coefficient metric (PDF p.12). The inverse action follows from the action laws.
--   - `ActionIsometric`: The action-invariant metric convention for compact groups (PDF p.12).
--   - `mergedTuple`: Merge entries j,j+1 of a bar tuple (PDF p.12, equation (2)).
--   - `barDifferential`: Unnormalized inhomogeneous bar differential, including d^0(a)(g)=g.a-a (PDF p.12, equation (2)); also applies to the raw coinduced function module.
--   - `IsCocycle`: Borel cocycle with its identity holding Haar-a.e. (PDF pp.12--13).
--   - `IsMeasurableBoundary`: Borel primitive, with B^0=0 rather than an image from a truncated predecessor (PDF pp.12--13). Borelness of f itself is supplied by IsCocycle at uses.
--   - `SameClass`: Equality of measurable classes means the difference has a Borel primitive (PDF p.13); the two functions are required to be cocycles at each use.
--   - `IsContinuousBoundary`: Continuous bar primitive, including B_cts^0=0 (PDF p.13).
--   - `IsBoundaryIn`: Borel primitive in a specified coefficient subgroup (PDF pp.21--22). Degree zero again means equality to zero.
--   - `Small`: Epsilon-smallness, with strict tail and measure bounds and positive epsilon (PDF p.13).
--   - `probabilityDistance`: Probability metric (PDF p.13), used here only with probability Haar measure, so its infimum set is nonempty (every epsilon>1 works) and bounded below by zero.
--   - `uniformDistance`: Essential uniform distance, retaining infinity for unbounded cochains (PDF p.13).
--   - `dimensionShiftQ`: Q on a degree-(p+1) cochain (PDF p.14). The inverse of the ordered product gives exactly g_p^{-1}...g_1^{-1}; the empty product handles degree one.
--   - `coinducedAction`: Diagonal coinduced action (PDF pp.12,14).
--   - `LocallyTotallyBounded`: Total boundedness of the actual representative's image of every compact set (PDF p.15, Definition 31).
--   - `UniformRegular`: The stronger regularity class from PDF pp.48--49: uniform limits of functions locally constant off closed null sets that may vary with the approximant. No condition is imposed on arbitrary exceptional-set values; the cocycle representatives are separately Borel.
--   - `QuantitativeRegularization`: Fixed-sequence quantitative conclusion (PDF pp.16--17); the theorem below chooses both sequences before the group, module, action, metric, epsilon and cocycle.
--   - `IsAlgebraicCocycle`: Algebraic bar cocycles with trivial action for the discrete-group examples of Section 5.2 (PDF pp.22--23). Every cochain on a discrete group is Borel.
--   - `IsAlgebraicBoundary`: Algebraic bar coboundaries with trivial action and B^0=0 (PDF pp.22--23).
--   - `IsFinitelyGenerated`: Finite generation as generation by a finite subset (PDF p.22, Lemma 56).
--   - `FiniteWindowNontrivial`: The property of the group in Lemma 56: nonzero means a nonzero cohomology class, not merely a nonzero function (PDF pp.22--23).
--   - `IntegerDirectSum`: Finitely supported integer sequences encode the countable direct sum of Z (PDF p.23, Proposition 57).
--   - `HasInitialSupport`: The initial n-coordinate subgroup Z^n of the countable direct sum (PDF p.23).
-- source:
--   Continuity properties of measurable group cohomology, arXiv:1004.4937v4, https://arxiv.org/abs/1004.4937v4

import Mathlib

/-! Austin--Moore, arXiv:1004.4937v4. Local definitions implement the bar formulas on Borel
representatives, with cocycle and coboundary equations modulo Haar-a.e. equality. Theorems A
and C are stated through both surjectivity and injectivity on these representatives. -/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P14

universe u v w

/-- Cartesian power G^p, with a one-point domain in degree zero (PDF p.12). -/
abbrev GroupPower (G : Type u) (p : ℕ) := Fin p → G

/-- Product Haar measure; its empty product has mass one (PDF pp.12--13). -/
def powerMeasure {G : Type u} [MeasurableSpace G] (mu : Measure G) (p : ℕ) :
    Measure (GroupPower G p) := Measure.pi (fun _ : Fin p => mu)

/-- Continuous action by additive automorphisms, with a compatible translation-invariant
coefficient metric (PDF p.12). The inverse action follows from the action laws. -/
structure ModuleAction (G : Type u) (A : Type v) [Group G] [TopologicalSpace G]
    [AddCommGroup A] [MetricSpace A] where
  act : G → A → A
  one_act : ∀ a, act 1 a = a
  mul_act : ∀ g h a, act (g * h) a = act g (act h a)
  act_add : ∀ g a b, act g (a + b) = act g a + act g b
  continuous_act : Continuous (fun z : G × A => act z.1 z.2)
  translation_invariant : ∀ a b c : A, dist (a + c) (b + c) = dist a b

/-- The action-invariant metric convention for compact groups (PDF p.12). -/
def ActionIsometric {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [AddCommGroup A] [MetricSpace A] (T : ModuleAction G A) : Prop :=
  ∀ g a b, dist (T.act g a) (T.act g b) = dist a b

/-- Merge entries j,j+1 of a bar tuple (PDF p.12, equation (2)). -/
def mergedTuple {G : Type u} [Group G] {p : ℕ} (j : Fin p)
    (g : GroupPower G (p + 1)) : GroupPower G p :=
  fun k => if k.val < j.val then g k.castSucc
    else if k = j then g j.castSucc * g j.succ else g k.succ

/-- Unnormalized inhomogeneous bar differential, including d^0(a)(g)=g.a-a
(PDF p.12, equation (2)); also applies to the raw coinduced function module. -/
def barDifferential {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    (act : G → A → A) (p : ℕ) (f : GroupPower G p → A) :
    GroupPower G (p + 1) → A :=
  fun g => act (g 0) (f (fun i => g i.succ)) +
    (∑ j : Fin p, ((-1 : ℤ) ^ (j.val + 1)) • f (mergedTuple j g)) +
    ((-1 : ℤ) ^ (p + 1)) • f (fun i => g i.castSucc)

/-- Borel cocycle with its identity holding Haar-a.e. (PDF pp.12--13). -/
def IsCocycle {G : Type u} {A : Type v} [Group G] [MeasurableSpace G]
    [AddCommGroup A] [MeasurableSpace A] (mu : Measure G) (act : G → A → A)
    (p : ℕ) (f : GroupPower G p → A) : Prop :=
  Measurable f ∧ ∀ᵐ g ∂powerMeasure mu (p + 1), barDifferential act p f g = 0

/-- Borel primitive, with B^0=0 rather than an image from a truncated predecessor
(PDF pp.12--13). Borelness of f itself is supplied by IsCocycle at uses. -/
def IsMeasurableBoundary {G : Type u} {A : Type v} [Group G] [MeasurableSpace G]
    [AddCommGroup A] [MeasurableSpace A] (mu : Measure G) (act : G → A → A) :
    (p : ℕ) → (GroupPower G p → A) → Prop
  | 0, f => ∀ᵐ g ∂powerMeasure mu 0, f g = 0
  | p + 1, f => ∃ b : GroupPower G p → A, Measurable b ∧
      ∀ᵐ g ∂powerMeasure mu (p + 1), f g = barDifferential act p b g

/-- Equality of measurable classes means the difference has a Borel primitive
(PDF p.13); the two functions are required to be cocycles at each use. -/
def SameClass {G : Type u} {A : Type v} [Group G] [MeasurableSpace G]
    [AddCommGroup A] [MeasurableSpace A] (mu : Measure G) (act : G → A → A)
    (p : ℕ) (f h : GroupPower G p → A) : Prop :=
  IsMeasurableBoundary mu act p (fun g => f g - h g)

/-- Continuous bar primitive, including B_cts^0=0 (PDF p.13). -/
def IsContinuousBoundary {G : Type u} {A : Type v} [Group G] [TopologicalSpace G]
    [AddCommGroup A] [TopologicalSpace A] (act : G → A → A) :
    (p : ℕ) → (GroupPower G p → A) → Prop
  | 0, f => ∀ g, f g = 0
  | p + 1, f => ∃ b : GroupPower G p → A, Continuous b ∧
      ∀ g, f g = barDifferential act p b g

/-- Borel primitive in a specified coefficient subgroup (PDF pp.21--22).
Degree zero again means equality to zero. -/
def IsBoundaryIn {G : Type u} {A : Type v} [Group G] [MeasurableSpace G]
    [AddCommGroup A] [MeasurableSpace A] (mu : Measure G) (act : G → A → A)
    (S : AddSubgroup A) : (p : ℕ) → (GroupPower G p → A) → Prop
  | 0, f => ∀ᵐ g ∂powerMeasure mu 0, f g = 0
  | p + 1, f => ∃ b : GroupPower G p → A, Measurable b ∧
      (∀ g, b g ∈ S) ∧ ∀ᵐ g ∂powerMeasure mu (p + 1),
        f g = barDifferential act p b g

/-- Epsilon-smallness, with strict tail and measure bounds and positive epsilon (PDF p.13). -/
def Small {X : Type u} {A : Type v} [MeasurableSpace X] [Zero A] [MetricSpace A]
    (mu : Measure X) (f : X → A) (epsilon : ℝ) : Prop :=
  0 < epsilon ∧ mu {x | epsilon < dist 0 (f x)} < ENNReal.ofReal epsilon

/-- Probability metric (PDF p.13), used here only with probability Haar measure, so its
infimum set is nonempty (every epsilon>1 works) and bounded below by zero. -/
def probabilityDistance {X : Type u} {A : Type v} [MeasurableSpace X]
    [AddCommGroup A] [MetricSpace A] (mu : Measure X) (f h : X → A) : ℝ :=
  sInf {epsilon : ℝ | Small mu (fun x => f x - h x) epsilon}

/-- Essential uniform distance, retaining infinity for unbounded cochains (PDF p.13). -/
def uniformDistance {X : Type u} {A : Type v} [MeasurableSpace X] [MetricSpace A]
    (mu : Measure X) (f h : X → A) : ℝ≥0∞ :=
  essSup (fun x => ENNReal.ofReal (dist (f x) (h x))) mu

/-- Q on a degree-(p+1) cochain (PDF p.14). The inverse of the ordered product gives
exactly g_p^{-1}...g_1^{-1}; the empty product handles degree one. -/
def dimensionShiftQ {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    (p : ℕ) (f : GroupPower G (p + 1) → A) (g : GroupPower G p) (h : G) : A :=
  ((-1 : ℤ) ^ (p + 1)) • f (Fin.snoc g ((List.ofFn g).prod⁻¹ * h))

/-- Diagonal coinduced action (PDF pp.12,14). -/
def coinducedAction {G : Type u} {A : Type v} [Group G]
    (act : G → A → A) (g : G) (f : G → A) (h : G) : A :=
  act g (f (g⁻¹ * h))

/-- Total boundedness of the actual representative's image of every compact set
(PDF p.15, Definition 31). -/
def LocallyTotallyBounded {X : Type u} {A : Type v} [TopologicalSpace X] [MetricSpace A]
    (f : X → A) : Prop := ∀ K : Set X, IsCompact K → TotallyBounded (f '' K)

/-- The stronger regularity class from PDF pp.48--49: uniform limits of functions locally
constant off closed null sets that may vary with the approximant. No condition is imposed on
arbitrary exceptional-set values; the cocycle representatives are separately Borel. -/
def UniformRegular {X : Type u} {A : Type v} [TopologicalSpace X] [MeasurableSpace X]
    [MetricSpace A] (mu : Measure X) (f : X → A) : Prop :=
  ∃ approximants : ℕ → X → A,
    (∀ n, ∃ N : Set X, IsClosed N ∧ mu N = 0 ∧
      IsLocallyConstant (fun x : ↥(Nᶜ) => approximants n x)) ∧
    ∀ epsilon : ℝ, 0 < epsilon → ∃ n0 : ℕ, ∀ n, n0 ≤ n →
      ∀ x, dist (approximants n x) (f x) < epsilon

/-- Fixed-sequence quantitative conclusion (PDF pp.16--17); the theorem below chooses
both sequences before the group, module, action, metric, epsilon and cocycle. -/
def QuantitativeRegularization {G : Type u} {A : Type v} [Group G] [MeasurableSpace G]
    [AddCommGroup A] [MetricSpace A] [MeasurableSpace A]
    (mu : Measure G) (act : G → A → A) (eta C : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ eta (p + 1) →
    ∀ f : GroupPower G (p + 1) → A, IsCocycle mu act (p + 1) f →
    Small (powerMeasure mu (p + 1)) f epsilon →
    ∃ b : GroupPower G p → A, ∃ phi : GroupPower G (p + 1) → A,
      Measurable b ∧ IsCocycle mu act (p + 1) phi ∧
      (∀ᵐ g ∂powerMeasure mu (p + 1),
        f g = phi g + barDifferential act p b g) ∧
      Small (powerMeasure mu p) b
        (C (p + 1) * Real.rpow epsilon (1 / (2 : ℝ) ^ (p + 1))) ∧
      uniformDistance (powerMeasure mu (p + 1)) (fun _ => 0) phi ≤
        ENNReal.ofReal (C (p + 1) * Real.rpow epsilon (1 / (2 : ℝ) ^ (p + 1)))

/-- Sign sanity check for the degree-one Q operator. -/
example {A : Type v} [AddCommGroup A] (a : A) : ((-1 : ℤ) ^ (1 : ℕ)) • a = -a := by simp [neg_one_zsmul]

/-- The empty bar power is a singleton, so its coefficient cochains are canonically A. -/
example {G : Type u} (x y : GroupPower G 0) : x = y := by
  funext i
  exact Fin.elim0 i

/-- The degree-zero bar differential has the source sign, with no normalization. -/
example {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    (act : G → A → A) (a : A) (g : GroupPower G 1) :
    barDifferential act 0 (fun _ => a) g = act (g 0) a - a := by
  simp [barDifferential, sub_eq_add_neg, neg_one_zsmul]

/-- B^0 remains zero for nondiscrete coefficients. -/
example {G : Type u} {A : Type v} [Group G] [MeasurableSpace G]
    [AddCommGroup A] [MeasurableSpace A] (mu : Measure G) (act : G → A → A)
    (f : GroupPower G 0 → A) :
    IsMeasurableBoundary mu act 0 f ↔ ∀ᵐ g ∂powerMeasure mu 0, f g = 0 := Iff.rfl

/-- Constant maps belong to the stated uniform approximation class. -/
example {X : Type u} {A : Type v} [TopologicalSpace X] [MeasurableSpace X]
    [MetricSpace A] (mu : Measure X) (a : A) : UniformRegular mu (fun _ : X => a) := by
  refine ⟨fun _ _ => a, ?_, ?_⟩
  · intro n
    exact ⟨∅, isClosed_empty, measure_empty, (IsLocallyConstant.const (X := ↥((∅ : Set X)ᶜ)) a)⟩
  · intro epsilon hepsilon
    exact ⟨0, fun _ _ _ => by simpa only [dist_self] using hepsilon⟩

section LocallyCompact

variable {G : Type u} [Group G] [TopologicalSpace G]
    [hTG : IsTopologicalGroup G] [hT2 : T2Space G]
    [hLC : LocallyCompactSpace G] [hSC : SecondCountableTopology G]
    [MeasurableSpace G] [hBG : BorelSpace G]
    {A : Type v} [AddCommGroup A] [MetricSpace A] [hTA : IsTopologicalAddGroup A]
    [hPA : PolishSpace A] [MeasurableSpace A] [hBA : BorelSpace A]
    (mu : Measure G) [hHaar : mu.IsHaarMeasure] (T : ModuleAction G A)

include hTG hT2 hLC hSC hBG hTA hPA hBA hHaar

end LocallyCompact

/-- Algebraic bar cocycles with trivial action for the discrete-group examples of
Section 5.2 (PDF pp.22--23). Every cochain on a discrete group is Borel. -/
def IsAlgebraicCocycle {G : Type u} {A : Type v} [Group G] [AddCommGroup A]
    (p : ℕ) (f : GroupPower G p → A) : Prop :=
  ∀ g, barDifferential (fun _ a => a) p f g = 0

/-- Algebraic bar coboundaries with trivial action and B^0=0 (PDF pp.22--23). -/
def IsAlgebraicBoundary {G : Type u} {A : Type v} [Group G] [AddCommGroup A] :
    (p : ℕ) → (GroupPower G p → A) → Prop
  | 0, f => ∀ g, f g = 0
  | p + 1, f => ∃ b : GroupPower G p → A,
      ∀ g, f g = barDifferential (fun _ a => a) p b g

/-- Finite generation as generation by a finite subset (PDF p.22, Lemma 56). -/
def IsFinitelyGenerated (G : Type u) [Group G] : Prop :=
  ∃ S : Finset G, Subgroup.closure (S : Set G) = ⊤

/-- The property of the group in Lemma 56: nonzero means a nonzero cohomology class,
not merely a nonzero function (PDF pp.22--23). -/
def FiniteWindowNontrivial (G : Type u) [Group G] : Prop :=
  ∀ F : Finset G, ∃ f : GroupPower G 2 → ℤ,
    IsAlgebraicCocycle 2 f ∧ ¬ IsAlgebraicBoundary 2 f ∧
      ∀ g : GroupPower G 2, (∀ i, g i ∈ F) → f g = 0

/-- Finitely supported integer sequences encode the countable direct sum of Z
(PDF p.23, Proposition 57). -/
abbrev IntegerDirectSum := ℕ →₀ ℤ

/-- The initial n-coordinate subgroup Z^n of the countable direct sum (PDF p.23). -/
def HasInitialSupport {X : Type u} (n : ℕ) (f : X → IntegerDirectSum) : Prop :=
  ∀ x i, n ≤ i → f x i = 0

/-- Zero has a trivial algebraic primitive in degree one. -/
example {G : Type u} {A : Type v} [Group G] [AddCommGroup A] :
    IsAlgebraicBoundary (G := G) 1 (fun _ => (0 : A)) := by
  refine ⟨fun _ => 0, ?_⟩
  intro g
  simp [barDifferential]

end QAlgorithms.Papers.Independent.Intake100.P14


