-- Prove2me | Definitions.Def_OAIQ2Un000
-- name    : OAIQ2Un000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T02:54:22.475426+00:00
-- url     : https://prove2.me/theorems/946dd114-6a3b-4473-81a2-220bd66a1fcc
-- title:
--   Definitions bundle OAIQ2Un000 of the split of OpenAI, A power saving for planar unit distances
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PlanarUnitDistances.main`, carved from OpenAI's openai/math development (OpenAI, *A power saving for planar unit distances*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 691 declarations of OpenAI's Lean: 539 definitions, 12 inductive types or structures, 29 instances and 111 theorems. The definitions and types are `OAI.PlanarUnitDistances.AccurateBand.kept`, `OAI.PlanarUnitDistances.ActualBudgetIntegral.commonVariation`, `OAI.PlanarUnitDistances.ActualHeights.center`, `OAI.PlanarUnitDistances.ActualHeights.mistake`, `OAI.PlanarUnitDistances.ActualProfiles.Input`, `OAI.PlanarUnitDistances.ActualProfiles.Input.book`, `OAI.PlanarUnitDistances.ActualProfiles.Input.errorAt`, `OAI.PlanarUnitDistances.ActualProfiles.Input.heightAt`, `OAI.PlanarUnitDistances.ActualProfiles.Input.profile`, `OAI.PlanarUnitDistances.ActualProfiles.Input.snap`, `OAI.PlanarUnitDistances.ActualProfiles.Input.threshold`, `OAI.PlanarUnitDistances.ActualRarePair.positive`, `OAI.PlanarUnitDistances.ActualRarePair.score`, `OAI.PlanarUnitDistances.ActualScoreBook.ActualBook`, `OAI.PlanarUnitDistances.ActualScoreBook.make`, `OAI.PlanarUnitDistances.ActualScoreBook.mass`, `OAI.PlanarUnitDistances.ActualSlots.active`, `OAI.PlanarUnitDistances.ActualSlots.frequency`, `OAI.PlanarUnitDistances.ActualSlots.positive`, `OAI.PlanarUnitDistances.ActualSlots.rareException`, `OAI.PlanarUnitDistances.ActualSlots.score`, `OAI.PlanarUnitDistances.AlgebraicObstruction.Hypotheses`, `OAI.PlanarUnitDistances.AlgebraicObstruction.indicator`, `OAI.PlanarUnitDistances.AlgebraicObstruction.w`, `OAI.PlanarUnitDistances.AlgebraicObstruction.z`, `OAI.PlanarUnitDistances.AlgebraicSpecialization.ParameterPolynomial`, `OAI.PlanarUnitDistances.AlgebraicSpecialization.chartValue`, `OAI.PlanarUnitDistances.AlgebraicSpecialization.evaluate`, `OAI.PlanarUnitDistances.BivariateDegree.size`, `OAI.PlanarUnitDistances.BivariateMaps.bimap`, `OAI.PlanarUnitDistances.BookCoercivity.centerLoss`, `OAI.PlanarUnitDistances.BookCoercivity.commonLoss`, `OAI.PlanarUnitDistances.BookCoercivity.loss`, `OAI.PlanarUnitDistances.BookCoercivity.pointLoss`, `OAI.PlanarUnitDistances.BookCoercivity.scaleLoss`, `OAI.PlanarUnitDistances.BookEnvelope.center`, `OAI.PlanarUnitDistances.BookEnvelope.common`, `OAI.PlanarUnitDistances.BookEnvelope.height`, `OAI.PlanarUnitDistances.BookEnvelope.j`, `OAI.PlanarUnitDistances.BookEnvelope.point` and 511 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/UnitDistances, in whole or in part: `UnitDistances_AbsoluteValues`, `UnitDistances_Basic`, `UnitDistances_Blocks`, `UnitDistances_Circles`, `UnitDistances_Cross`, `UnitDistances_Cutting`, `UnitDistances_Derivations`, `UnitDistances_Entropy`, `UnitDistances_Extraction`, `UnitDistances_GenericCurves`, `UnitDistances_Grid`, `UnitDistances_HeightTransfer`, `UnitDistances_Information`, `UnitDistances_Integration`, `UnitDistances_Levels`, `UnitDistances_Loci`, `UnitDistances_Main`, `UnitDistances_Obstruction`, `UnitDistances_Powers`, `UnitDistances_PredictionBudget`, `UnitDistances_Predictions`, `UnitDistances_Preparation`, `UnitDistances_Profiles`, `UnitDistances_Quantization`, `UnitDistances_Radicals`, `UnitDistances_RareBudget`, `UnitDistances_RareEvents`, `UnitDistances_Regularization`, `UnitDistances_Sampling`, `UnitDistances_Scale`, `UnitDistances_Scores`, `UnitDistances_Sequence`, `UnitDistances_Slots`, `UnitDistances_SmallHeight`, `UnitDistances_States`, `UnitDistances_Sweep`, `UnitDistances_Tails`, `UnitDistances_Transfer`, `UnitDistances_Valuations`, `UnitDistances_Wedges`.
--
--   **Imports.** It imports the published bundle `Def_PlanarUnitDistances`.
--
--   **Imported by** (directly, in this split): the statements `OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve`, `OAI.PlanarUnitDistances.AlgebraicObstruction.curve_plane`, `OAI.PlanarUnitDistances.AlgebraicObstruction.no_rectangles`, `OAI.PlanarUnitDistances.IncidenceBand.choose`, `OAI.PlanarUnitDistances.IncidenceBook.constants`, `OAI_PlanarUnitDistances_IncidenceDiagonal_exists_data`, `OAI.PlanarUnitDistances.IncidenceEstimates.upper`, `OAI.PlanarUnitDistances.IncidenceNoise.limit`, `OAI.PlanarUnitDistances.IncidenceScale.scale_limit` and `OAI.PlanarUnitDistances.IncidenceSequence.diagonal_sequence`; the proofs of `OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve`, `OAI.PlanarUnitDistances.AlgebraicObstruction.curve_plane`, `OAI.PlanarUnitDistances.AlgebraicObstruction.no_rectangles`, `OAI.PlanarUnitDistances.IncidenceBand.choose`, `OAI.PlanarUnitDistances.IncidenceBook.constants`, `OAI_PlanarUnitDistances_IncidenceDiagonal_exists_data`, `OAI.PlanarUnitDistances.IncidenceEstimates.upper`, `OAI.PlanarUnitDistances.IncidenceNoise.limit`, `OAI.PlanarUnitDistances.IncidenceScale.scale_limit`, `OAI.PlanarUnitDistances.IncidenceSequence.diagonal_sequence` and `OAI.PlanarUnitDistances.main`.
-- source:
--   OpenAI, A power saving for planar unit distances, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/UnitDistances at commit adc7f12

import Mathlib
import Definitions.Def_PlanarUnitDistances

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances

def MainClaim : Prop := ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
    ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β

@[simp] theorem isUnitPair_mk (x y : Plane) :
    IsUnitPair s(x, y) ↔ dist x y = 1 := Iff.rfl

@[simp] theorem not_isUnitPair_diag (x : Plane) :
    ¬ IsUnitPair (Sym2.diag x) := by
  simp [IsUnitPair, Sym2.diag]

@[simp] theorem unitPairCount_singleton (p : Plane) : unitPairCount {p} = 0 := by
  classical
  simp [unitPairCount]

end PlanarUnitDistances

namespace PlanarUnitDistances.AlgebraicSpecialization
open Set Filter Polynomial
open scoped Topology

abbrev ParameterPolynomial (ι : Type*) := Polynomial (MvPolynomial ι ℚ)

noncomputable def evaluate {ι : Type*} (F : ParameterPolynomial ι)
    (u : ι → ℝ) (θ : ℝ) : ℝ :=
  F.eval₂ (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u) θ

noncomputable def chartValue {ι κ : Type*} (N D : κ → ParameterPolynomial ι)
    (p : (ι → ℝ) × ℝ) (i : κ) : ℝ := evaluate (N i) p.1 p.2 / evaluate (D i) p.1 p.2

end PlanarUnitDistances.AlgebraicSpecialization

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

noncomputable abbrev ParameterField {ι : Type*} (u : ι → ℝ) :=
  IntermediateField.adjoin ℚ (Set.range u)

noncomputable def parameterMap {ι : Type*} (u : ι → ℝ) :
    MvPolynomial ι ℚ →ₐ[ℚ] ParameterField u :=
  MvPolynomial.aeval (fun i =>
    ⟨u i,IntermediateField.subset_adjoin ℚ (Set.range u) (mem_range_self i)⟩)

@[simp] theorem coe_parameterMap {ι : Type*} (u : ι → ℝ) (p : MvPolynomial ι ℚ) :
    ((parameterMap u p : ParameterField u) : ℝ) = MvPolynomial.aeval u p := by
  have he : (IntermediateField.val (ParameterField u)).comp (parameterMap u) =
      MvPolynomial.aeval u := by
    ext i
    change ((parameterMap u (MvPolynomial.X i) : ParameterField u) : ℝ) =
      MvPolynomial.aeval u (MvPolynomial.X i)
    simp only [parameterMap,MvPolynomial.aeval_X]
  exact AlgHom.congr_fun he p

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

noncomputable def unitRelation {ι κ : Type*}
    (N D : κ × Fin 2 → ParameterPolynomial ι) (i j : κ) : ParameterPolynomial ι :=
  (N (i,0)*D (j,0)-N (j,0)*D (i,0))^2 * (D (i,1)*D (j,1))^2 +
    (N (i,1)*D (j,1)-N (j,1)*D (i,1))^2 * (D (i,0)*D (j,0))^2 -
    (D (i,0)*D (j,0))^2 * (D (i,1)*D (j,1))^2

def unitEquation {κ : Type*} (x : κ × Fin 2 → ℝ) (i j : κ) : Prop :=
  (x (i,0)-x (j,0))^2+(x (i,1)-x (j,1))^2 = 1

end PlanarUnitDistances.PrimitiveChart

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cutting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.CircleCutting
open Set Polynomial

abbrev Plane := EuclideanSpace ℝ (Fin 2)

lemma finite_circle_intersection (c d : Plane) (hcd : c ≠ d) :
    {p : Plane | dist p c = 1 ∧ dist p d = 1}.Finite := by
  let S : Set Plane := {p | dist p c = 1 ∧ dist p d = 1}
  by_cases hs : S.Subsingleton
  · exact hs.finite
  obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hs
  apply (Set.toFinite ({a,b} : Set Plane)).subset
  intro p hp
  apply Set.mem_insert_iff.mpr
  have h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (by simp : Module.finrank ℝ Plane = 2) hcd hab ha.1 hb.1 hp.1 ha.2 hb.2 hp.2
  exact h.imp_right (fun h => Set.mem_singleton_iff.mpr h)

noncomputable def circleIntersections (Q : Finset Plane) : Finset Plane := by
  classical
  exact ((Q ×ˢ Q).biUnion fun cd => if h : cd.1 = cd.2 then ∅ else
    (finite_circle_intersection cd.1 cd.2 h).toFinset)

noncomputable def direction (t : ℝ) : Plane :=
  WithLp.toLp 2 ![(1-t^2)/(1+t^2), 2*t/(1+t^2)]

noncomputable def projection (e p : Plane) : ℝ := e 0*p 0+e 1*p 1

noncomputable def directionPolynomial (a b c : ℝ) : Polynomial ℝ :=
  C a*(1-X^2)+C b*(2*X)-C c*(1+X^2)

noncomputable def rotate (e p : Plane) : Plane :=
  WithLp.toLp 2 ![projection e p,-e 1*p 0+e 0*p 1]

noncomputable def branch (c : Plane) (upper : Bool) (x : ℝ) : ℝ :=
  c 1 + if upper then Real.sqrt (1-(x-c 0)^2) else -Real.sqrt (1-(x-c 0)^2)

def active (c : Plane) (x : ℝ) : Prop := c 0-1 < x ∧ x < c 0+1

noncomputable def graphPoint (c : Plane) (b : Bool) (x : ℝ) : Plane :=
  WithLp.toLp 2 ![x,branch c b x]

noncomputable def eventAbscissas (Q : Finset Plane) : Finset ℝ :=
  (Q.biUnion fun c => {c 0-1,c 0+1}) ∪ (circleIntersections Q).image (· 0)

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.Sweep
open Finset Classical

variable {α : Type*} [DecidableEq α]

def links (x : Option α) : List α → Finset (Option α × Option α)
  | [] => {(x,none)}
  | a::L => insert (x,some a) (links (some a) L)

def gaps (L : List α) : Finset (Option α × Option α) := links none L

def touches (C : Finset α) (g : Option α × Option α) : Prop :=
  (∃ a ∈ C, g.1 = some a) ∨ (∃ a ∈ C, g.2 = some a)

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.SweepIntervals
open Finset Set Classical

def span {n : ℕ} (a : Fin n → ℝ) (lo hi : ℕ) : Set ℝ :=
  {x | (∀ i, i.val < lo → a i < x) ∧ (∀ i, hi ≤ i.val → x < a i)}

abbrev slab {n : ℕ} (a : Fin n → ℝ) (k : ℕ) := span a k k

end PlanarUnitDistances.SweepIntervals

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

abbrev Label := Plane × Bool
noncomputable def labels (Q : Finset Plane) : Finset Label := Q ×ˢ Finset.univ
noncomputable def height (b : Label) : ℝ → ℝ := branch b.1 b.2
noncomputable def activeLabels (Q : Finset Plane) (x : ℝ) : Finset Label :=
  (labels Q).filter (fun b => active b.1 x)

noncomputable def circleEvents (Q : Finset Plane) (c : Plane) : Finset ℝ :=
  {c 0-1,c 0+1} ∪ Q.biUnion (fun d => if h : c=d then ∅ else
    ((finite_circle_intersection c d h).toFinset.image (· 0)))

noncomputable def critical (Q : Finset Plane) (x : ℝ) : Finset Label :=
  (labels Q).filter (fun b => x ∈ circleEvents Q b.1)

end PlanarUnitDistances.CircleCutting

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.Sweep
open Finset Classical
variable {α : Type*} [DecidableEq α]

def Lower (f : α → ℝ) (x : Option α) (y : ℝ) : Prop :=
  ∀ a, x=some a → f a<y

def GapBand (f : α → ℝ) (g : Option α × Option α) (y : ℝ) : Prop :=
  Lower f g.1 y ∧ ∀ a, g.2=some a → y<f a

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.SweepRuns
open Finset Classical
variable {α : Type*}

def Reach (G : ℕ → Finset α) (bad : ℕ → α → Prop) (g : α) (lo hi : ℕ) : Prop :=
  lo ≤ hi ∧ (∀ k, lo ≤ k → k ≤ hi → g ∈ G k) ∧
    (∀ k, lo ≤ k → k < hi → ¬bad k g)

noncomputable def starts (G : ℕ → Finset α) (bad : ℕ → α → Prop) (k : ℕ) :=
  (G k).filter (fun g => k=0 ∨ g ∉ G (k-1) ∨ bad (k-1) g)

noncomputable def last (G : ℕ → Finset α) (bad : ℕ → α → Prop) (n : ℕ)
    (g : α) (lo : ℕ) := Nat.findGreatest (Reach G bad g lo) n

noncomputable def runs (G : ℕ → Finset α) (bad : ℕ → α → Prop) (n : ℕ) :
    Finset (α × ℕ × ℕ) :=
  (range (n+1)).biUnion fun lo => (starts G bad lo).image (fun g => (g,lo,last G bad n g lo))

end PlanarUnitDistances.SweepRuns

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

abbrev Gap := Option Label × Option Label

noncomputable def region {n : ℕ} (a : Fin n → ℝ) (g : Gap) (lo hi : ℕ) : Set Plane :=
  {p | p 0 ∈ SweepIntervals.span a lo hi ∧ Sweep.GapBand (fun b => height b (p 0)) g (p 1)}

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

structure Arrangement (Q : Finset Plane) where
  n : ℕ
  a : Fin n → ℝ
  strict : StrictMono a
  events : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z
  L : ℕ → List Label
  nodup : ∀ k, (L k).Nodup
  mem : ∀ k x, x ∈ SweepIntervals.slab a k → ∀ b, b ∈ L k ↔ b ∈ activeLabels Q x
  order : ∀ k x, x ∈ SweepIntervals.slab a k → (L k).Pairwise (fun b d => height b x<height d x)

namespace Arrangement
variable {Q : Finset Plane} (d : Arrangement Q)

noncomputable def criticalAt (k : ℕ) : Finset Label :=
  if h : k<d.n then critical Q (d.a ⟨k,h⟩) else ∅

noncomputable def G (k : ℕ) := Sweep.gaps (d.L k)

noncomputable def pieces := SweepRuns.runs d.G (fun k g => Sweep.touches (d.criticalAt k) g) d.n

end Arrangement
end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

noncomputable def endpoints (Q : Finset Plane) : Finset (Option ℝ) :=
  insert none ((eventAbscissas Q).image some)

noncomputable def boundaries (Q : Finset Plane) : Finset (Option Label) :=
  insert none ((labels Q).image some)

abbrev RegionCode := (Option ℝ × Option ℝ) × Gap

noncomputable def codeRegion (r : RegionCode) : Set Plane :=
  {p | Sweep.GapBand id r.1 (p 0) ∧ Sweep.GapBand (fun b => height b (p 0)) r.2 (p 1)}

noncomputable def candidateCodes (Q : Finset Plane) : Finset RegionCode :=
  (endpoints Q ×ˢ endpoints Q) ×ˢ (boundaries Q ×ˢ boundaries Q)

end PlanarUnitDistances.CircleCutting

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteSampling
open Finset Classical

noncomputable def sampleSize (R : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (R*Real.log (10*((N : ℝ)+1)))

end PlanarUnitDistances.FiniteSampling

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

noncomputable def conflicts (Q : Finset Plane) (U : Set Plane) : Finset Plane :=
  Q.filter (fun c => ∃ p ∈ U, dist p c=1)

noncomputable def cuttingLog (l : ℕ) : ℝ := Real.log (10*(81*(1+(l : ℝ))^6+1))

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleIncidence
open Finset Classical
open CircleCutting

noncomputable def degree (P : Finset Plane) (q : Plane) : ℝ :=
  ((P.filter (fun p => dist p q=1)).card : ℝ)

noncomputable def incidences (P Q : Finset Plane) : ℝ := ∑ q ∈ Q, degree P q

lemma degree_sum (P : Finset Plane) (q : Plane) :
    degree P q = ∑ p ∈ P, if dist p q=1 then (1 : ℝ) else 0 := by
  simp [degree,Finset.sum_boole]

lemma degree_le (P : Finset Plane) (q : Plane) : degree P q ≤ P.card :=
  Nat.cast_le.mpr (Finset.card_filter_le _ _)

lemma incidences_le (P Q : Finset Plane) : incidences P Q ≤ (P.card : ℝ)*Q.card := by
  apply (Finset.sum_le_sum (fun q _ => degree_le P q)).trans_eq
  simp [mul_comm]

noncomputable def common (Q : Finset Plane) (p r : Plane) : ℝ :=
  ((Q.filter (fun q => dist p q=1 ∧ dist r q=1)).card : ℝ)

noncomputable def retained (P T : Finset Plane) : Finset Plane :=
  P.filter (fun p => ∀ c ∈ T, dist p c≠1)

noncomputable def deleted (P T : Finset Plane) : Finset Plane :=
  P.filter (fun p => ∃ c ∈ T, dist p c=1)

end PlanarUnitDistances.CircleIncidence

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PowerGrowth
open Filter

def Lower {ι : Type*} (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ i in F, t i ^ (a-ε) ≤ f i

def Upper {ι : Type*} (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ i in F, f i ≤ t i ^ (a+ε)

end PlanarUnitDistances.PowerGrowth

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Regularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceRegularization
open Finset Real

noncomputable def mass {A : Type*} (μ : A → ℝ) (s : Finset A) : ℝ := ∑ a ∈ s, μ a
noncomputable def rect {P Q : Type*} (w : P → Q → ℝ)
    (F : Finset P) (G : Finset Q) : ℝ := ∑ p ∈ F, ∑ q ∈ G, w p q

section Optimizer
variable {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
variable (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)

noncomputable def objective (γ : ℝ) (F : Finset P) (G : Finset Q) : ℝ :=
  rect w F G / (mass μ F * mass ν G)^γ

def IsMaximizing (τ γ : ℝ) (F : Finset P) (G : Finset Q) : Prop :=
  τ ≤ mass μ F ∧ τ ≤ mass ν G ∧
    ∀ A B, τ ≤ mass μ A → τ ≤ mass ν B →
      objective μ ν w γ A B ≤ objective μ ν w γ F G

end Optimizer

end PlanarUnitDistances.IncidenceRegularization

namespace PlanarUnitDistances.GeometricExpansion
open CircleIncidence CircleCutting IncidenceRegularization
open scoped Classical
noncomputable section

def factor (m n e L dP dQ t a : ℝ) : ℝ :=
  1+1000*L^2*(m*n)^(2/3:ℝ)/e+1000*L^2*n*t^a/e+
    1000*L^2*m*t/e+dP*m/e+dQ*n/e

end
end PlanarUnitDistances.GeometricExpansion

namespace PlanarUnitDistances.GeometricOptimizer
open CircleIncidence CircleCutting IncidenceRegularization GeometricExpansion
open scoped Classical
noncomputable section

def lift (P : Finset Plane) (A : Finset P) : Finset Plane := A.map (Function.Embedding.subtype _)

def counting (P : Finset Plane) : P → ℝ := fun _ => 1/(P.card:ℝ)
def weight (P Q : Finset Plane) : P → Q → ℝ := fun p q =>
  (if dist (p:Plane) (q:Plane)=1 then (1:ℝ) else 0)/incidences P Q
end
end PlanarUnitDistances.GeometricOptimizer

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section

structure Law (X : Type*) [Fintype X] where
  val : X  →  ℝ
  nonneg : ∀ x, 0  ≤  val x
  total : ∑ x, val x = 1

variable {X Y : Type*} [Fintype X] [Fintype Y]

def avg (μ : Law X) (f : X  →  ℝ) : ℝ := ∑ x,μ.val x*f x

def event (μ : Law X) (P : X  →  Prop) : ℝ := by
  classical
  exact avg μ (fun x => if P x then 1 else 0)

lemma avg_nonneg (μ : Law X) {f : X  →  ℝ} (h : ∀ x,0 ≤ f x) : 0 ≤ avg μ f :=
  sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (h x)
lemma event_nonneg (μ : Law X) (P : X  →  Prop) : 0 ≤ event μ P := by
  classical
  apply avg_nonneg; intro x; split <;> norm_num

def pair (μ : Law X) (ν : Law Y) : Law (X×Y) where
  val x := μ.val x.1*ν.val x.2
  nonneg x := mul_nonneg (μ.nonneg _) (ν.nonneg _)
  total := by simp [Fintype.sum_prod_type,← mul_sum,ν.total,μ.total]

end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.StrictCross
open Set
variable {A B : Type*}

def Adj (x y : A × B) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (x.1 ≠ y.1 ∧ x.2 = y.2)

noncomputable def coefficient (r : ℝ) : ℝ :=
  if |r-1/2| ≤ (1/100:ℝ) then 1+1/20000 else 1-1/20000

end PlanarUnitDistances.StrictCross

namespace PlanarUnitDistances.StarScore
open FiniteLaw StrictCross
noncomputable section
variable {X A B : Type*} [Fintype X]

def frequency (μ : Law X) (bit : X  →  Bool) : ℝ := event μ (fun x => bit x=true)
def variation (μ : Law X) (bit : X  →  Bool) : ℝ := 2*frequency μ bit*(1-frequency μ bit)

def slot (r : ℝ) (bit : X  →  Bool) (state : X  →  A×B) (x y : X) : ℝ := by
  classical
  exact if bit x ≠ bit y then -1 else
    if bit x then (if (state x).2=(state y).2 then coefficient r else 0)
    else (if (state x).1=(state y).1 then coefficient r else 0)

def score (μ : Law X) (bit : X  →  Bool) (state : X  →  A×B) : ℝ :=
  avg (pair μ μ) (fun xy => slot (frequency μ bit) bit state xy.1 xy.2)

end
end PlanarUnitDistances.StarScore

namespace PlanarUnitDistances.FiniteLaw
open Finset
noncomputable section
open scoped Classical
variable {X Y : Type*} [Fintype X] [Fintype Y]

def fiberMass (μ : Law X) (φ : X → Y) (y : Y) : ℝ := event μ (fun x => φ x=y)

omit [Fintype Y] in
lemma fiberMass_eq (μ : Law X) (φ : X → Y) (y : Y) :
    fiberMass μ φ y = ∑ x, if φ x=y then μ.val x else 0 := by
  classical
  unfold fiberMass event avg
  apply sum_congr rfl
  intro x _
  split_ifs <;> simp_all
omit [Fintype Y] in
lemma fiberMass_nonneg (μ : Law X) (φ : X → Y) (y : Y) : 0 ≤ fiberMass μ φ y :=
  event_nonneg _ _
lemma fiberMass_total (μ : Law X) (φ : X → Y) : ∑ y, fiberMass μ φ y = 1 := by
  classical
  simp_rw [fiberMass_eq]
  rw [sum_comm]
  simp [μ.total]

def push (μ : Law X) (φ : X → Y) : Law Y where
  val := fiberMass μ φ
  nonneg := fiberMass_nonneg μ φ
  total := fiberMass_total μ φ

def cond (μ : Law X) (φ : X → Y) (y : Y) : Law X := by
  classical
  exact if h : 0 < fiberMass μ φ y then
    { val := fun x => if φ x=y then μ.val x/fiberMass μ φ y else 0
      nonneg := fun x => by
        have := μ.nonneg x
        split_ifs <;> positivity
      total := by
        have hf := fiberMass_eq μ φ y
        calc
          _ = (∑ x, if φ x=y then μ.val x else 0) / fiberMass μ φ y := by
            rw [sum_div]
            apply sum_congr rfl
            intro x _
            split_ifs <;> simp
          _ = 1 := by rw [← hf,div_self h.ne'] }
    else μ

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.RestrictedTransfer
open Finset

noncomputable def mass {X : Type*} (ν : X → ℝ) (s : Finset X) : ℝ := ∑ x ∈ s, ν x

section Supports
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def row (a : A) : Finset (A × B) := univ.filter (fun x => x.1 = a)
def col (b : B) : Finset (A × B) := univ.filter (fun x => x.2 = b)

def Permitted (U : Finset (A × B)) : Prop :=
  (∃ a, U = row a) ∨ (∃ b, U = col b) ∨ U.card ≤ 2

noncomputable def rowException (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) := by
  classical
  exact if h : ∃ a, 1-η ≤ mass ν (row a) then (row h.choose)ᶜ else ∅
noncomputable def colException (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) := by
  classical
  exact if h : ∃ b, 1-η ≤ mass ν (col b) then (col h.choose)ᶜ else ∅
noncomputable def smallException (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) := by
  classical
  exact if ∃ U : Finset (A × B), U.card ≤ 2 ∧ 1-η ≤ mass ν U
    then univ.filter (fun x => ν x ≤ η) else ∅
noncomputable def exception (ν : A × B → ℝ) (η : ℝ) : Finset (A × B) :=
  rowException ν η ∪ colException ν η ∪ smallException ν η

end Supports

section Posterior
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]
  [DecidableEq H] [DecidableEq A] [DecidableEq B]

noncomputable def historyMass (μ : P → ℝ) (h : P → H) (a : H) : ℝ :=
  ∑ p, if h p = a then μ p else 0
noncomputable def posterior (μ : P → ℝ) (h : P → H) (a : H) (p : P) : ℝ :=
  (if h p = a then μ p else 0) / historyMass μ h a
noncomputable def statePosterior (μ : P → ℝ) (h : P → H)
    (X : P → A × B) (a : H) (x : A × B) : ℝ := ∑ p, if X p = x then posterior μ h a p else 0

end Posterior

section EdgeTemplate
variable {P Q H A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype Θ] [DecidableEq H] [DecidableEq A] [DecidableEq B]

noncomputable def centerMixture (μ : P → ℝ) (h : P → H) (X : P → A × B)
    (edge : P → Q → ℝ) (q : Q) (x : A × B) : ℝ :=
  ∑ p, edge p q / (∑ r, edge r q) * statePosterior μ h X (h p) x

end EdgeTemplate

end PlanarUnitDistances.RestrictedTransfer

namespace PlanarUnitDistances.CrossStructure
open Finset StrictCross RestrictedTransfer
open scoped Classical
noncomputable section
variable {A B : Type*}

def Consistent (b : Bool) (x y : A×B) : Prop :=
  if b then x.1=y.1 ∧ x.2≠y.2 else x.1≠y.1 ∧ x.2=y.2

def Shape (Y U : Finset (A×B)) : Prop :=
  (∀ y∈Y,∀ z∈Y,y=z) ∨ (∀ x∈U,∀ z∈U,x=z) ∨
  (∃ b : Bool,∀ x∈U,∀ y∈Y,∀ c,Consistent c x y → c=b) ∨
  ((∀ x∈U,∀ y∈Y,∀ z∈Y,∀ b,Consistent b x y → Consistent b x z → y=z) ∧
   (∀ y∈Y,∀ x∈U,∀ z∈U,∀ b,Consistent b x y → Consistent b z y → x=z))

end
end PlanarUnitDistances.CrossStructure

namespace PlanarUnitDistances.FiniteStarCoupling
open Finset FiniteLaw StarScore CrossStructure
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

def left (π : Law (P×Q)) : Law P := push π Prod.fst
def right (π : Law (P×Q)) : Law Q := push π Prod.snd
def row (π : Law (P×Q)) (p : P) : Law Q := push (cond π Prod.fst p) Prod.snd
def col (π : Law (P×Q)) (q : Q) : Law P := push (cond π Prod.snd q) Prod.fst

def DP (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×B) : ℝ :=
  avg (left π) (fun p => score (row π p) (bit p) y)
def DQ (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) : ℝ :=
  avg (right π) (fun q => score (col π q) (fun p => bit p q) x)
def VP (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  avg (left π) (fun p => variation (row π p) (bit p))
def VQ (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  avg (right π) (fun q => variation (col π q) (fun p => bit p q))
def bad (π : Law (P×Q)) (good : P → Q → Prop) : ℝ := event π (fun pq => ¬good pq.1 pq.2)

end
end PlanarUnitDistances.FiniteStarCoupling

namespace PlanarUnitDistances.RareScore
open FiniteLaw CrossStructure
open scoped Classical
noncomputable section
variable {A B X : Type*}

def exceptional (r : Bool) (l x : A×B) : Prop :=
  if r then x.2≠l.2 else x.1≠l.1

def nonshared (b : Bool) (y z : A×B) : Prop :=
  if b then y.2=z.2 else y.1=z.1

def ind (h : Prop) : ℝ := if h then 1 else 0

def slot (r : Bool) (l x y z : A×B) (b c : Bool) : ℝ :=
  2*ind (exceptional r l x ∧ b=r ∧ c=r ∧ nonshared r y z)-ind (b≠c)

end
end PlanarUnitDistances.RareScore

namespace PlanarUnitDistances.WedgeProfiles
open RareScore CrossStructure FiniteLaw
open scoped Classical
noncomputable section
variable {A B : Type*}

def value (b : Bool) : ℝ := if b then 1 else 0
def sign (r : Bool) : ℝ := if r then 1 else -1

end
end PlanarUnitDistances.WedgeProfiles

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

def independent (μ : Law X) (I : Type*) [Fintype I] [DecidableEq I] : Law (I → X) where
  val x := ∏ i,μ.val (x i)
  nonneg x := prod_nonneg fun i _ => μ.nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [μ.total]

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Wedges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

def dependent (μ : Law X) (ν : X → Law Y) : Law (X×Y) where
  val xy := μ.val xy.1*(ν xy.1).val xy.2
  nonneg xy := mul_nonneg (μ.nonneg _) ((ν _).nonneg _)
  total := by simp [Fintype.sum_prod_type,← mul_sum,Law.total]

def mix (μ : Law X) (ν : X → Law Y) : Law Y where
  val y := avg μ (fun x => (ν x).val y)
  nonneg _ := avg_nonneg _ (fun x => (ν x).nonneg _)
  total := by
    simp only [avg]
    rw [sum_comm]
    simp [← mul_sum,Law.total]

def tensor (μ : I → Law X) : Law (I → X) where
  val x := ∏ i,(μ i).val (x i)
  nonneg x := prod_nonneg fun i _ => (μ i).nonneg _
  total := by
    classical
    rw [← Fintype.prod_sum]
    simp [Law.total]

end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.WedgeLaw
open FiniteLaw FiniteStarCoupling WedgeProfiles
open scoped Classical
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

def law (π : Law (P×Q)) : Law (Q×(P×P)) :=
  dependent (right π) (fun q => pair (col π q) (col π q))

end
end PlanarUnitDistances.WedgeLaw

namespace PlanarUnitDistances.TemplateCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q Θ : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

def joint (π : Law (P×Q)) (a : Q → Law Θ) : Law ((P×Q)×Θ) := dependent π (fun pq => a pq.2)
def templates (π : Law (P×Q)) (a : Q → Law Θ) : Law Θ := push (joint π a) Prod.snd
def slice (π : Law (P×Q)) (a : Q → Law Θ) (θ : Θ) : Law (P×Q) :=
  push (cond (joint π a) Prod.snd θ) Prod.fst

end
end PlanarUnitDistances.TemplateCoupling

namespace PlanarUnitDistances.CrossSampling
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B I : Type*} [Fintype A] [Fintype B] [Fintype I] [DecidableEq I]

def crossMass (ν : Law (A×B)) (y : A×B) : ℝ := event ν (fun x => Adj x y)
def rowMass (ν : Law (A×B)) (a : A) : ℝ := event ν (fun x => x.1=a)
def colMass (ν : Law (A×B)) (b : B) : ℝ := event ν (fun x => x.2=b)

def Bad (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ y,crossMass ν y < 1-α ∧ ∀ i,Adj (xs i) y

def Corner (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) (i j : I) : Prop :=
  i≠j ∧ crossMass ν ((xs i).1,(xs j).2)<1-α ∧
    ∀ l,Adj (xs l) ((xs i).1,(xs j).2)
def LowRow (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ a,rowMass ν a ≤ 1-α/2 ∧ ∀ i,(xs i).1=a
def LowCol (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ b,colMass ν b ≤ 1-α/2 ∧ ∀ i,(xs i).2=b
def HeavyAvoid (ν : Law (A×B)) (α : ℝ) (xs : I → A×B) : Prop :=
  ∃ y,α/2<ν.val y ∧ ∀ i,xs i≠y

abbrev Rest (i j : I) (hij : i≠j) := {l : {l : I // l≠i} // l≠⟨j,hij.symm⟩}
def fillTwo {X : Type*} (i j : I) (hij : i≠j) (a b : X) (xs : Rest i j hij → X) : I → X :=
  (Equiv.piSplitAt i (fun _ => X)).symm (a,
    (Equiv.piSplitAt (⟨j,hij.symm⟩ : {l : I // l≠i}) (fun _ => X)).symm (b,xs))

end
end PlanarUnitDistances.CrossSampling

namespace PlanarUnitDistances.CrossTemplates
open Finset FiniteLaw StrictCross CrossSampling
open scoped Classical
noncomputable section
variable {H A B I : Type*} [Fintype H] [Fintype A] [Fintype B] [Fintype I]

def Candidates (ν : H → Law (A×B)) (ε : ℝ) (h : I → H) : Finset (A×B) :=
  univ.filter fun y => ∀i,1-ε≤crossMass (ν (h i)) y

def Failure (μ : Law H) (ν : H → Law (A×B)) (ε α : ℝ) (h : I → H) : Prop :=
  ∃y∈Candidates ν ε h,crossMass (mix μ ν) y<1-α

end
end PlanarUnitDistances.CrossTemplates

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossTemplates CrossStructure
open scoped Classical
noncomputable section
variable {P Q H A B Θ : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype Θ]

def posteriorState (π : Law (P×Q)) (h : P → H) (x : P → A×B) (v : H) : Law (A×B) :=
  push (cond (left π) h v) x

def historyLaw (π : Law (P×Q)) (h : P → H) (q : Q) : Law H := push (col π q) h

end
end PlanarUnitDistances.CommonTemplate

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteInformation
open scoped InnerProductSpace
open Finset Real

noncomputable def KL {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ a, p a * log (p a / q a)

noncomputable def TV {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (∑ a, |p a - q a|) / 2

noncomputable def push {α β : Type*} [Fintype α] [DecidableEq β]
    (p : α → ℝ) (f : α → β) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

noncomputable def row {α β : Type*} [Fintype β] (p : α × β → ℝ) (a : α) : ℝ :=
  ∑ b, p (a,b)

noncomputable def cond {α β : Type*} [Fintype β] (p : α × β → ℝ)
    (a : α) (b : β) : ℝ := p (a,b) / row p a

section Features
variable {H C V : Type*} [Fintype H] [Fintype C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def mean (x : H × C → ℝ) (v : C → V) (h : H) : V :=
  ∑ c, cond x h c • v c

noncomputable def paired (x : H × C → ℝ) : (H × H) × (C × C) → ℝ :=
  fun a => x (a.1.1,a.2.1)*x (a.1.2,a.2.2)

end Features

section Observation
variable {P H C : Type*} [Fintype P] [Fintype H] [Fintype C]
  [DecidableEq H] [DecidableEq C]

def observation (h : P → H) (c : P → C) (pr : P × P) : (H × H) × (C × C) :=
  ((h pr.1,h pr.2),(c pr.1,c pr.2))

end Observation

section Wedges
variable {P Q V : Type*} [Fintype P] [Fintype Q]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def wedge (κ : Q → ℝ) (w : Q → P → ℝ) (pr : P × P) : ℝ :=
  ∑ q, κ q * w q pr.1 * w q pr.2

end Wedges

universe u
def History (C : Type u) : ℕ → Type u
  | 0 => PUnit
  | n+1 => History C n × C

instance historyFintype (C : Type*) [Fintype C] : (n : ℕ) → Fintype (History C n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n+1 => by
      letI : Fintype (History C n) := historyFintype C n
      exact inferInstanceAs (Fintype (History C n × C))

instance historyDecidableEq (C : Type*) [DecidableEq C] :
    (n : ℕ) → DecidableEq (History C n)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | n+1 => @instDecidableEqProd (History C n) C (historyDecidableEq C n) inferInstance

def transcript {P C : Type*} (c : ℕ → P → C) : (n : ℕ) → P → History C n
  | 0, _ => PUnit.unit
  | n+1, p => (transcript c n p,c n p)

noncomputable def transcriptKL {P C : Type*} [Fintype P] [Fintype C] [DecidableEq C]
    (p q : P × P → ℝ) (c : ℕ → P → C) (n : ℕ) : ℝ :=
  KL (push p (fun pr => (transcript c n pr.1,transcript c n pr.2)))
    (push q (fun pr => (transcript c n pr.1,transcript c n pr.2)))

section Marginal
variable {P Q : Type*} [Fintype P] [Fintype Q]
noncomputable def marginal (κ : Q → ℝ) (w : Q → P → ℝ) (p : P) : ℝ :=
  ∑ q, κ q * w q p

end Marginal

section FrozenPrediction
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def residual (μ : P → ℝ) (c : ℕ → P → C) (v : ℕ → C → V)
    (n : ℕ) (p : P) : V :=
  v n (c n p) - mean (push μ (fun p => (transcript c n p,c n p))) (v n) (transcript c n p)

noncomputable def discrepancy (κ : Q → ℝ) (w : Q → P → ℝ)
    (c : ℕ → P → C) (v : ℕ → C → V) (g : ℕ → Q → V) (n : ℕ) : ℝ :=
  |∑ q, κ q * ⟪∑ p, w q p • residual (marginal κ w) c v n p,g n q⟫_ℝ|

end FrozenPrediction

section Posterior
variable {P H C V : Type*} [Fintype P] [Fintype H] [Fintype C]
  [DecidableEq H] [DecidableEq C] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def posterior (μ : P → ℝ) (h : P → H) (x : H) (p : P) : ℝ :=
  (if h p = x then μ p else 0) / push μ h x

end Posterior

section HistoriesMeasurable
open MeasureTheory ProbabilityTheory
universe uC
variable {C : Type uC} [MeasurableSpace C]

instance historyMeasurable : (n : ℕ) → MeasurableSpace (History C n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => by
    letI : MeasurableSpace (History C n) := historyMeasurable n
    exact inferInstanceAs (MeasurableSpace (History C n × C))

end HistoriesMeasurable

section RandomDevice
open MeasureTheory ProbabilityTheory
variable {P Q C V : Type*} [Fintype P] [Fintype Q] [Fintype C] [DecidableEq C]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def testDiscrepancy {H : Type*} [Fintype H] [DecidableEq H]
    (κ : Q → ℝ) (w : Q → P → ℝ) (h : P → H) (c : P → C) (v : C → V) (g : Q → V) : ℝ :=
  |∑ q, κ q * ⟪∑ p, w q p •
    (v (c p) - mean (push (marginal κ w) (fun p => (h p,c p))) v (h p)),g q⟫_ℝ|

end RandomDevice

end PlanarUnitDistances.FiniteInformation

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

noncomputable def entropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  - ∑ a, p a * log (p a)

noncomputable def indicator (E : P → Q → Prop) (p : P) (q : Q) : ℝ := by
  classical
  exact if E p q then 1 else 0
noncomputable def degree (E : P → Q → Prop) (q : Q) : ℝ := ∑ p, indicator E p q
noncomputable def edgeCount (E : P → Q → Prop) : ℝ := ∑ q, degree E q
noncomputable def wedge (E : P → Q → Prop) (x : P × P) : ℝ :=
  ∑ q, indicator E x.1 q * indicator E x.2 q / (edgeCount E * degree E q)
noncomputable def pointLaw (E : P → Q → Prop) (p : P) : ℝ :=
  (∑ q, indicator E p q) / edgeCount E

omit [Fintype P] [Fintype Q] in
lemma indicator_nonneg (E : P → Q → Prop) (p : P) (q : Q) : 0 ≤ indicator E p q := by
  classical
  unfold indicator
  split_ifs <;> norm_num

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

noncomputable def centerPolynomial (p r : ℂ) : ℂ[X] :=
  (X-C p)*(C (p*conj p-r*conj r-(p-r)*conj p)-C (conj p-conj r)*X)-C (p-r)

noncomputable def zCoordinate : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

lemma zCoordinate_apply (x : EuclideanSpace ℝ (Fin 2)) :
    zCoordinate x = x 0 + x 1 * Complex.I := rfl

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.UniformGraphLaw
open Finset FiniteLaw FiniteStarCoupling IncidenceEntropy
open scoped Classical BigOperators
noncomputable section
variable {P Q : Type*} [Fintype P] [Fintype Q]

def law (E : P → Q → Prop) (hE : 0<edgeCount E) : Law (P×Q) where
  val pq := indicator E pq.1 pq.2/edgeCount E
  nonneg pq := div_nonneg (indicator_nonneg E _ _) hE.le
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [←sum_div]
    rw [sum_comm]
    exact div_self hE.ne'

end
end PlanarUnitDistances.UniformGraphLaw

namespace PlanarUnitDistances.GeometricLaw
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def E (P Q : Finset Plane) (p : P) (q : Q) : Prop := dist (p:Plane) (q:Plane)=1
lemma degree_eq (P Q : Finset Plane) (q : Q) :
    IncidenceEntropy.degree (E P Q) q=CircleIncidence.degree P q := by
  rw [CircleIncidence.degree_sum]
  exact Finset.sum_coe_sort P (fun p => if dist p (q:Plane)=1 then (1:ℝ) else 0)
lemma edgeCount_eq (P Q : Finset Plane) :
    IncidenceEntropy.edgeCount (E P Q)=CircleIncidence.incidences P Q := by
  simp only [IncidenceEntropy.edgeCount,degree_eq,Finset.sum_coe_sort,CircleIncidence.incidences]
lemma card_pos (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) :
    0<P.card ∧ 0<Q.card := by
  have h := he.trans_le (CircleIncidence.incidences_le P Q)
  have hP : (0:ℝ)<P.card := pos_of_mul_pos_left h (Nat.cast_nonneg _)
  have hQ : (0:ℝ)<Q.card := pos_of_mul_pos_right h (Nat.cast_nonneg _)
  exact ⟨Nat.cast_pos.mp hP,Nat.cast_pos.mp hQ⟩
def graph (P Q : Finset Plane) (he : 0<CircleIncidence.incidences P Q) : Law (P×Q) :=
  UniformGraphLaw.law (E P Q) (by rw [edgeCount_eq]; exact he)

def counting (P : Finset Plane) (hp : 0<P.card) : Law P where
  val _ := 1/(P.card:ℝ)
  nonneg _ := by positivity
  total := by simp [ne_of_gt hp]

def image {P : Finset Plane} (A : Finset P) : Finset Plane := A.image Subtype.val
end
end PlanarUnitDistances.GeometricLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def information (P Q : Finset Plane) : ℝ :=
  FiniteInformation.KL (IncidenceEntropy.wedge (GeometricLaw.E P Q))
    (fun pr => IncidenceEntropy.pointLaw (GeometricLaw.E P Q) pr.1*
      IncidenceEntropy.pointLaw (GeometricLaw.E P Q) pr.2)

structure Good (t δ R : ℝ) (P Q : Finset Plane) (ξ : ℝ) : Prop where
  algebraicP : ∀p∈P,∀k,IsAlgebraic ℚ (p k)
  algebraicQ : ∀q∈Q,∀k,IsAlgebraic ℚ (q k)
  positive : 0 < incidences P Q
  error_nonneg : 0 ≤ ξ
  error_le : ξ ≤ δ
  expansion : ∀A ⊆ P,∀B ⊆ Q,incidences A B/incidences P Q  ≤
    Real.sqrt ((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))*
      (((A.card:ℝ)/P.card*((B.card:ℝ)/Q.card))^(1/25:ℝ)+ξ)
  atomP : ∀p∈P,(27/50:ℝ)/(P.card:ℝ) ≤ degree Q p/incidences P Q
  atomQ : ∀q∈Q,(27/50:ℝ)/(Q.card:ℝ) ≤ degree P q/incidences P Q
  cardP : (P.card:ℝ) ≤ t^(1+δ)
  atomUpper : ∀p∈P,degree Q p/incidences P Q ≤ t^(-1/2:ℝ)
  degreeP : t^(1/2:ℝ) ≤ (27/50:ℝ)*incidences P Q/P.card
  degreeQ : R ≤ (27/50:ℝ)*incidences P Q/Q.card
  wedgeBound : t^(2-δ) ≤ incidences P Q*((27/50:ℝ)*incidences P Q/Q.card)/2
  info : information P Q/Real.log t ≤ δ

structure Sequence where
  t : ℕ → ℝ
  P : ℕ → Finset Plane
  Q : ℕ → Finset Plane
  ξ : ℕ → ℝ
  large : ∀i : ℕ,(i:ℝ)+2 ≤ t i
  good : ∀i : ℕ,Good (t i) (1/((i:ℝ)+1)) ((i:ℝ)+1) (P i) (Q i) (ξ i)

end
end PlanarUnitDistances.IncidenceSequence

namespace PlanarUnitDistances.CommonField
open Polynomial

theorem exists_normal_field (S : Finset ℂ) (halg : ∀ z∈S, IsAlgebraic ℚ z) :
    ∃ F : IntermediateField ℚ ℂ, (∀ z∈S,z∈F) ∧ FiniteDimensional ℚ F ∧ Normal ℚ F := by
  classical
  let A := IntermediateField.adjoin ℚ (S : Set ℂ)
  let : FiniteDimensional ℚ A := IntermediateField.finiteDimensional_adjoin
    (fun z hz => (halg z hz).isIntegral)
  let F := IntermediateField.normalClosure ℚ A ℂ
  let : IsNormalClosure ℚ A F := Algebra.IsAlgebraic.isNormalClosure_normalClosure
    (fun _ => IsAlgClosed.splits _)
  let : Normal ℚ F := IsNormalClosure.normal (F := ℚ) (K := A) (L := F)
  refine ⟨F,?_,inferInstance,inferInstance⟩
  intro z hz
  exact (A.val.fieldRange_le_normalClosure (K := A))
    ⟨⟨z,IntermediateField.subset_adjoin ℚ _ hz⟩,rfl⟩

lemma integral_I : IsIntegral ℚ Complex.I := by
  refine ⟨X^2+1,?_,?_⟩
  · exact monic_X_pow_add_C 1 (by decide : 2 ≠ 0)
  · simp

lemma algebraic_ofReal {x : ℝ} (hx : IsAlgebraic ℚ x) : IsAlgebraic ℚ (x : ℂ) :=
  (hx.isIntegral.map (IsScalarTower.toAlgHom ℚ ℝ ℂ)).isAlgebraic

lemma algebraic_coordinates (x : EuclideanSpace ℝ (Fin 2))
    (hx : ∀ i,IsAlgebraic ℚ (x i)) :
    IsAlgebraic ℚ ((x 0 : ℂ)+(x 1 : ℂ)*Complex.I) ∧
    IsAlgebraic ℚ ((x 0 : ℂ)-(x 1 : ℂ)*Complex.I) := by
  have h0 := (algebraic_ofReal (hx 0)).isIntegral
  have h1 := (algebraic_ofReal (hx 1)).isIntegral
  exact ⟨(h0.add (h1.mul integral_I)).isAlgebraic,(h0.sub (h1.mul integral_I)).isAlgebraic⟩
end PlanarUnitDistances.CommonField

namespace PlanarUnitDistances.CommonFieldModel
open scoped Classical
noncomputable section
abbrev Plane := EuclideanSpace ℝ (Fin 2)
variable (P Q : Finset Plane)
def location : P ⊕ Q → Plane := Sum.elim Subtype.val Subtype.val

structure Model where
  field : IntermediateField ℚ ℂ
  finite : FiniteDimensional ℚ field
  normal : Normal ℚ field
  z : P ⊕ Q → field
  w : P ⊕ Q → field
  z_eq : ∀v,(z v:ℂ)=UnitCodegree.zCoordinate (location P Q v)
  w_eq : ∀v,(w v:ℂ)=star (UnitCodegree.zCoordinate (location P Q v))

variable {P Q}
instance instFiniteDimensionalRatSubtypeComplexMemIntermediateFieldField (M : Model P Q) : FiniteDimensional ℚ M.field := M.finite
instance instNormalRatSubtypeComplexMemIntermediateFieldField (M : Model P Q) : Normal ℚ M.field := M.normal
instance instNumberFieldSubtypeComplexMemIntermediateFieldRatField (M : Model P Q) : NumberField M.field := ⟨⟩
instance instIsGaloisRatSubtypeComplexMemIntermediateFieldField (M : Model P Q) : IsGalois ℚ M.field := ⟨⟩

theorem exists_model
    (hP : ∀p∈P,∀i,IsAlgebraic ℚ (p i))
    (hQ : ∀q∈Q,∀i,IsAlgebraic ℚ (q i)) : Nonempty (Model P Q) := by
  let Z := fun v : P⊕Q => UnitCodegree.zCoordinate (location P Q v)
  let W := fun v : P⊕Q => star (Z v)
  have ha (v : P⊕Q) : IsAlgebraic ℚ (Z v) ∧ IsAlgebraic ℚ (W v) := by
    have h : ∀i,IsAlgebraic ℚ (location P Q v i) := by
      cases v with
      | inl p => exact hP p p.property
      | inr q => exact hQ q q.property
    have hh := CommonField.algebraic_coordinates (location P Q v) h
    constructor
    · exact hh.1
    · convert hh.2 using 1
      simp [W,Z,UnitCodegree.zCoordinate_apply,sub_eq_add_neg]
  let S : Finset ℂ := Finset.univ.image Z ∪ Finset.univ.image W
  have halg : ∀z∈S,IsAlgebraic ℚ z := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact (ha v).1
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz
      exact (ha v).2
  obtain ⟨F,hF,hfin,hnorm⟩ := CommonField.exists_normal_field S halg
  refine ⟨⟨F,hfin,hnorm,fun v => ⟨Z v,hF _ ?_⟩,fun v => ⟨W v,hF _ ?_⟩,
    fun _ => rfl,fun _ => rfl⟩⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)

namespace Model
variable (M : Model P Q)

def support : Finset M.field :=
  (Finset.univ.image (fun vr : (P⊕Q)×(P⊕Q) => M.z vr.1-M.z vr.2) ∪
  Finset.univ.image (fun vr : (P⊕Q)×(P⊕Q) => M.w vr.1-M.w vr.2)) ∪
  Finset.univ.image (fun vrs : (P⊕Q)×(P⊕Q)×(P⊕Q) =>
    ((M.z vrs.1-M.z vrs.2.1)-(M.z vrs.1-M.z vrs.2.2))*
    ((M.z vrs.1-M.z vrs.2.1)⁻¹-(M.z vrs.1-M.z vrs.2.2)⁻¹))
end Model
end
end PlanarUnitDistances.CommonFieldModel

namespace PlanarUnitDistances.ExpansionConsequences
open Finset Real

noncomputable def mass {A : Type*} (μ : A → ℝ) (s : Finset A) : ℝ := ∑ a ∈ s, μ a
noncomputable def rect {P Q : Type*} (w : P → Q → ℝ)
    (F : Finset P) (G : Finset Q) : ℝ := ∑ p ∈ F, ∑ q ∈ G, w p q

section FiniteLaw
variable {P Q : Type*} [Fintype P] [Fintype Q]
variable (w : P → Q → ℝ)
noncomputable def left (p : P) : ℝ := ∑ q, w p q
noncomputable def right (q : Q) : ℝ := ∑ p, w p q
noncomputable def conditional (F : Finset P) (q : Q) : ℝ :=
  (∑ p ∈ F, w p q) / right w q

noncomputable def wedgeMass (F : Finset P) : ℝ :=
  ∑ q, right w q * (conditional w F q)^2

end FiniteLaw

section LabelMatching
variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def mismatch (w : A → A → ℝ) : ℝ :=
  ∑ p, ∑ q, if p ≠ q then w p q else 0

def outside (a : A) : Finset A := univ.filter (fun p => p ≠ a)

end LabelMatching

universe u

end PlanarUnitDistances.ExpansionConsequences

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset
noncomputable section

section Rational

def badPrimes (q : ℚ) : Finset ℕ := q.num.natAbs.primeFactors ∪ q.den.primeFactors

lemma padic_nat_eq (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    (padicNorm p (n : ℚ) : ℝ) = ((p : ℝ)^n.factorization p)⁻¹ := by
  rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat,
    ← Nat.factorization_def n hp]
  norm_cast
  simp

lemma prod_padic_nat {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) {n : ℕ}
    (hn : n ≠ 0) (hsn : n.primeFactors ⊆ s) :
    (∏ p ∈ s, (padicNorm p (n : ℚ) : ℝ)) = (n : ℝ)⁻¹ := by
  have heq : (∏ p ∈ s, p^n.factorization p) = n := by
    have hh := Finsupp.prod_of_support_subset n.factorization
      (s := s) (by simpa only [Nat.support_factorization] using hsn)
      (fun p e => p^e) (by simp)
    rw [Nat.prod_factorization_pow_eq_self hn] at hh
    exact hh.symm
  have heqR : (∏ p ∈ s, (p : ℝ)^n.factorization p) = (n : ℝ) := by
    exact_mod_cast heq
  calc
    (∏ p ∈ s, (padicNorm p (n : ℚ) : ℝ)) =
        ∏ p ∈ s, ((p : ℝ)^n.factorization p)⁻¹ :=
      prod_congr rfl (fun p hp => padic_nat_eq p n (hs p hp) hn)
    _ = (∏ p ∈ s, (p : ℝ)^n.factorization p)⁻¹ := by rw [prod_inv_distrib]
    _ = (n : ℝ)⁻¹ := by rw [heqR]

lemma padic_int_natAbs (p : ℕ) (z : ℤ) :
    padicNorm p (z : ℚ) = padicNorm p (z.natAbs : ℚ) := by
  cases z with
  | ofNat n => simp
  | negSucc n => simpa only [Int.cast_negSucc, Int.natAbs_negSucc, Nat.cast_add,
      Nat.cast_one, Nat.cast_succ] using padicNorm.neg (p := p) ((n:ℚ)+1)

lemma padic_rat_outside {q : ℚ} (hq : q ≠ 0) {p : ℕ} (hp : p.Prime)
    (hps : p ∉ badPrimes q) : padicNorm p q = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : q.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hq)
  have hnd : ¬ p ∣ q.num.natAbs := by
    intro h
    exact hps (mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp,h,hn⟩))
  have hdd : ¬ p ∣ q.den := by
    intro h
    exact hps (mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp,h,q.den_ne_zero⟩))
  conv_lhs => rw [← q.num_div_den]
  rw [padicNorm.div, padic_int_natAbs, (padicNorm.nat_eq_one_iff _).mpr hnd,
    (padicNorm.nat_eq_one_iff _).mpr hdd, div_one]

theorem rational_product_formula {q : ℚ} (hq : q ≠ 0) :
    |(q : ℝ)| * ∏ p ∈ badPrimes q, (padicNorm p q : ℝ) = 1 := by
  have hn : q.num.natAbs ≠ 0 := by simpa using (Rat.num_ne_zero.mpr hq)
  have hp : ∀ p ∈ badPrimes q, p.Prime := by
    intro p hp
    rcases mem_union.mp hp with hp | hp <;> exact Nat.prime_of_mem_primeFactors hp
  have hprod : (∏ p ∈ badPrimes q, (padicNorm p q : ℝ)) =
      (q.num.natAbs : ℝ)⁻¹/(q.den : ℝ)⁻¹ := by
    calc
      (∏ p ∈ badPrimes q, (padicNorm p q : ℝ)) =
          ∏ p ∈ badPrimes q, (padicNorm p (q.num.natAbs:ℚ) : ℝ) /
            (padicNorm p (q.den:ℚ) : ℝ) := by
        apply prod_congr rfl
        intro p hps
        let : Fact p.Prime := ⟨hp p hps⟩
        conv_lhs => rw [← q.num_div_den]
        rw [padicNorm.div, padic_int_natAbs, Rat.cast_div]
      _ = _ := by
        rw [prod_div_distrib, prod_padic_nat hp hn (subset_union_left),
          prod_padic_nat hp q.den_ne_zero (subset_union_right)]
  have hval : |(q : ℝ)| = (q.num.natAbs:ℝ)/(q.den:ℝ) := by
    have hdabs : |(q.den:ℝ)| = (q.den:ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    rw [Rat.cast_def, abs_div, hdabs, Nat.cast_natAbs, Int.cast_abs]
  rw [hprod,hval]
  have hnR : (q.num.natAbs:ℝ) ≠ 0 := by exact_mod_cast hn
  have hdR : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  field_simp

end Rational

section Entries
variable (K : Type*) [Field K] [NumberField K]

def primeEmbedding (p : ℕ) [Fact p.Prime] : K →ₐ[ℚ] PadicAlgCl p :=
  IsAlgClosed.lift

def primeAbsoluteValue (p : ℕ) [Fact p.Prime] : AbsoluteValue K ℝ :=
  (NormedField.toAbsoluteValue (PadicAlgCl p)).comp (primeEmbedding K p).injective

@[simp] lemma primeAbsoluteValue_apply (p : ℕ) [Fact p.Prime] (u : K) :
    primeAbsoluteValue K p u = ‖primeEmbedding K p u‖ := rfl

@[simp] theorem primeAbsoluteValue_rat (p : ℕ) [Fact p.Prime] (q : ℚ) :
    primeAbsoluteValue K p (algebraMap ℚ K q) = (padicNorm p q : ℝ) := by
  rw [primeAbsoluteValue_apply, AlgHom.commutes]
  change ‖(q : PadicAlgCl p)‖ = _
  have hh : (q : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) (q:ℚ_[p]) := by simp
  rw [hh, PadicAlgCl.norm_extends, Padic.eq_padicNorm]

theorem primeAbsoluteValue_nonarch (p : ℕ) [Fact p.Prime] :
    IsNonarchimedean (primeAbsoluteValue K p) := by
  intro x y
  change ‖primeEmbedding K p (x+y)‖ ≤ _
  rw [map_add]
  exact PadicAlgCl.isNonarchimedean p _ _

def finiteEntry (p : Nat.Primes) (σ : Gal(K/ℚ)) : AbsoluteValue K ℝ := by
  letI : Fact p.val.Prime := ⟨p.property⟩
  exact (primeAbsoluteValue K p.val).comp (f := σ.toRingHom) σ.injective

def infiniteEntry (σ : K →ₐ[ℚ] ℂ) : AbsoluteValue K ℝ :=
  (NormedField.toAbsoluteValue ℂ).comp σ.injective

@[simp] theorem infiniteEntry_apply (σ : K →ₐ[ℚ] ℂ) (u : K) :
    infiniteEntry K σ u = ‖σ u‖ := rfl

lemma finiteEntry_nonarch (p : Nat.Primes) (σ : Gal(K/ℚ)) :
    IsNonarchimedean (finiteEntry K p σ) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  intro x y
  change primeAbsoluteValue K p.val (σ (x+y)) ≤ _
  rw [map_add]
  exact primeAbsoluteValue_nonarch K p.val _ _

@[simp] lemma finiteEntry_rat (p : Nat.Primes) (σ : Gal(K/ℚ)) (q : ℚ) :
    finiteEntry K p σ (algebraMap ℚ K q) = (padicNorm p.val q : ℝ) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  change primeAbsoluteValue K p.val (σ (algebraMap ℚ K q)) = _
  rw [AlgEquiv.commutes, primeAbsoluteValue_rat]

def rootDenominators (x : K) : Finset ℕ :=
  (range (minpoly ℚ x).natDegree).biUnion fun i => ((minpoly ℚ x).coeff i).den.primeFactors

end Entries

lemma nonarch_root_one {L : Type*} [Field L] (v : AbsoluteValue L ℝ)
    (hv : IsNonarchimedean v) {m : ℕ} (hm : 0 < m)
    (a : Fin m → L) (x : L) (hcoeff : ∀ i, v (a i) ≤ 1)
    (hrel : x^m = ∑ i, a i * x^(i:ℕ)) : v x ≤ 1 := by
  by_contra h
  have hx : 1 < v x := lt_of_not_ge h
  have : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have hs : (v x)^m ≤ (v x)^(m-1) := by
    calc
      (v x)^m = v (∑ i, a i * x^(i:ℕ)) := by rw [← hrel,map_pow]
      _ ≤ ⨆ i, v (a i * x^(i:ℕ)) := hv.apply_sum_univ_le
      _ ≤ (v x)^(m-1) := by
        apply ciSup_le
        intro i
        rw [map_mul,map_pow]
        have hi : (v x)^(i:ℕ) ≤ (v x)^(m-1) := pow_le_pow_right₀ hx.le (by omega)
        exact (mul_le_mul (hcoeff i) hi (pow_nonneg (v.nonneg x) _) zero_le_one).trans_eq (one_mul _)
  have heq : (v x)^m = v x * (v x)^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hpos : 0 < (v x)^(m-1) := pow_pos (lt_trans zero_lt_one hx) _
  rw [heq] at hs
  have hh : v x ≤ 1 := (mul_le_mul_iff_left₀ hpos).mp (by simpa using hs)
  exact h hh

section Support
variable (K : Type*) [Field K] [NumberField K]

lemma finiteEntry_le_one_off_denominators (x : K) (p : Nat.Primes) (σ : Gal(K/ℚ))
    (hp : p.val ∉ rootDenominators K x) : finiteEntry K p σ x ≤ 1 := by
  classical
  let : Fact p.val.Prime := ⟨p.property⟩
  let f := minpoly ℚ x
  have hf : f.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hroot : Polynomial.aeval x f = 0 := minpoly.aeval ℚ x
  have hm : 0 < f.natDegree :=
    Polynomial.natDegree_pos_of_aeval_root hf.ne_zero hroot (fun a ha => by simpa using ha)
  apply nonarch_root_one (finiteEntry K p σ) (finiteEntry_nonarch K p σ) hm
    (fun i => -algebraMap ℚ K (f.coeff (i:ℕ))) x
  · intro i
    rw [AbsoluteValue.map_neg, finiteEntry_rat]
    have hden : ¬ p.val ∣ (f.coeff (i:ℕ)).den := by
      intro hd
      apply hp
      apply mem_biUnion.mpr
      refine ⟨(i:ℕ), mem_range.mpr i.isLt, ?_⟩
      exact Nat.mem_primeFactors.mpr ⟨p.property, hd, (f.coeff (i:ℕ)).den_ne_zero⟩
    simpa only [Padic.eq_padicNorm] using (Padic.norm_rat_le_one (p := p.val) hden)
  · have hh := congrArg (Polynomial.aeval x) hf.as_sum
    rw [hroot] at hh
    simp only [map_add,map_sum,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C] at hh
    rw [← Fin.sum_univ_eq_sum_range] at hh
    simp only [neg_mul, sum_neg_distrib]
    exact eq_neg_of_add_eq_zero_left hh.symm

lemma finiteEntry_eq_one_off_support {x : K} (hx : x ≠ 0)
    (p : Nat.Primes) (σ : Gal(K/ℚ))
    (hp : p.val ∉ rootDenominators K x ∪ rootDenominators K x⁻¹) :
    finiteEntry K p σ x = 1 := by
  have hu := finiteEntry_le_one_off_denominators K x p σ (fun h => hp (mem_union_left _ h))
  have hi := finiteEntry_le_one_off_denominators K x⁻¹ p σ (fun h => hp (mem_union_right _ h))
  have hpos : 0 < finiteEntry K p σ x := (finiteEntry K p σ).pos hx
  have hh := mul_le_mul_of_nonneg_left hi hpos.le
  rw [map_inv₀, mul_inv_cancel₀ (ne_of_gt hpos), mul_one] at hh
  exact le_antisymm hu hh

theorem finiteEntry_hasFiniteMulSupport {x : K} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport (fun v : Nat.Primes × Gal(K/ℚ) => finiteEntry K v.1 v.2 x) := by
  classical
  let S := (rootDenominators K x ∪ rootDenominators K x⁻¹).subtype Nat.Prime
  apply (S ×ˢ (univ : Finset Gal(K/ℚ))).finite_toSet.subset
  intro v hv
  apply mem_product.mpr
  refine ⟨?_,mem_univ _⟩
  apply Finset.mem_subtype.mpr
  by_contra hn
  exact hv (finiteEntry_eq_one_off_support K hx v.1 v.2 hn)

end Support

section Product
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma finiteEntry_block (p : Nat.Primes) (x : K) :
    (∏ σ : Gal(K/ℚ), finiteEntry K p σ x) =
      (padicNorm p.val (Algebra.norm ℚ x) : ℝ) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  change (∏ σ : Gal(K/ℚ), primeAbsoluteValue K p.val (σ x)) = _
  rw [← map_prod, ← Algebra.norm_eq_prod_automorphisms ℚ, primeAbsoluteValue_rat]

lemma infiniteEntry_block (x : K) :
    (∏ σ : K →ₐ[ℚ] ℂ, infiniteEntry K σ x) = |(Algebra.norm ℚ x : ℝ)| := by
  simp only [infiniteEntry_apply]
  rw [← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ]
  simp only [eq_ratCast, Complex.norm_ratCast]

lemma rational_product_formula_on {q : ℚ} (hq : q ≠ 0) (s : Finset Nat.Primes)
    (hs : ∀ p ∈ badPrimes q, ∃ hp : p.Prime, (⟨p,hp⟩ : Nat.Primes) ∈ s) :
    |(q : ℝ)| * (∏ p ∈ s, (padicNorm p.val q : ℝ)) = 1 := by
  classical
  have heq : (∏ p ∈ s, (padicNorm p.val q : ℝ)) =
      ∏ p ∈ badPrimes q, (padicNorm p q : ℝ) := by
    let t := s.map ⟨Subtype.val, Subtype.val_injective⟩
    have hsub : badPrimes q ⊆ t := by
      intro p hp
      obtain ⟨hpr,hps⟩ := hs p hp
      exact mem_map.mpr ⟨⟨p,hpr⟩,hps,rfl⟩
    have he : (∏ p ∈ t, (padicNorm p q : ℝ)) =
        ∏ p ∈ badPrimes q, (padicNorm p q : ℝ) := by
      exact (prod_subset hsub (by
        intro p hpt hp
        obtain ⟨r,hr,he⟩ := mem_map.mp hpt
        subst p
        change (padicNorm r.val q : ℝ) = 1
        exact_mod_cast (padic_rat_outside hq r.property hp))).symm
    change (∏ p ∈ s.map (⟨Subtype.val, Subtype.val_injective⟩ : Nat.Primes ↪ ℕ),
      (padicNorm p q : ℝ)) = _ at he
    rw [Finset.prod_map] at he
    exact he
  rw [heq]
  exact rational_product_formula hq

theorem product_formula {x : K} (hx : x ≠ 0) :
    (∏ σ : K →ₐ[ℚ] ℂ, infiniteEntry K σ x) *
      (∏ᶠ v : Nat.Primes × Gal(K/ℚ), finiteEntry K v.1 v.2 x) = 1 := by
  classical
  let q := Algebra.norm ℚ x
  have hq : q ≠ 0 := Algebra.norm_ne_zero_iff.mpr hx
  let S := rootDenominators K x ∪ rootDenominators K x⁻¹ ∪ badPrimes q
  let s : Finset Nat.Primes := S.subtype Nat.Prime
  have hsup : Function.mulSupport (fun v : Nat.Primes × Gal(K/ℚ) =>
      finiteEntry K v.1 v.2 x) ⊆ (↑(s ×ˢ (univ : Finset Gal(K/ℚ))) : Set (Nat.Primes × Gal(K/ℚ))) := by
    intro v hv
    apply mem_product.mpr
    refine ⟨?_,mem_univ _⟩
    apply Finset.mem_subtype.mpr
    by_contra hn
    apply hv
    apply finiteEntry_eq_one_off_support K hx
    intro h
    exact hn (mem_union_left _ h)
  rw [finprod_eq_prod_of_mulSupport_subset _ hsup, Finset.prod_product]
  simp_rw [finiteEntry_block K]
  rw [infiniteEntry_block K]
  apply rational_product_formula_on hq
  intro p hp
  have hpr : p.Prime := by
    rcases mem_union.mp hp with h | h <;> exact Nat.prime_of_mem_primeFactors h
  refine ⟨hpr,?_⟩
  apply Finset.mem_subtype.mpr
  exact mem_union_right _ hp

theorem weighted_log_product_formula {x : K} (hx : x ≠ 0) :
    ((∑ σ : K →ₐ[ℚ] ℂ, Real.log (infiniteEntry K σ x)) +
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), Real.log (finiteEntry K v.1 v.2 x))) /
        (Module.finrank ℚ K : ℝ) = 0 := by
  have hp : ∀ σ : K →ₐ[ℚ] ℂ, 0 < infiniteEntry K σ x :=
    fun σ => (infiniteEntry K σ).pos hx
  have hfin : ∀ v : Nat.Primes × Gal(K/ℚ), 0 < finiteEntry K v.1 v.2 x :=
    fun v => (finiteEntry K v.1 v.2).pos hx
  have h1 : (∏ σ : K →ₐ[ℚ] ℂ, infiniteEntry K σ x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun σ _ => (hp σ).ne')
  have h2 : (∏ᶠ v : Nat.Primes × Gal(K/ℚ), finiteEntry K v.1 v.2 x) ≠ 0 := by
    rw [finprod_eq_prod _ (finiteEntry_hasFiniteMulSupport K hx)]
    exact Finset.prod_ne_zero_iff.mpr (fun v _ => (hfin v).ne')
  have hh := congrArg Real.log (product_formula K hx)
  rw [Real.log_mul h1 h2, Real.log_prod (fun σ _ => (hp σ).ne'),
    Real.log_finprod hfin, Real.log_one] at hh
  rw [hh, zero_div]

end Product
end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
lemma finiteEntry_composed_support (g : ℝ → ℝ) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (x : K) : Function.HasFiniteSupport
      (fun v : Nat.Primes × Gal(K/ℚ) => g (finiteEntry K v.1 v.2 x)) := by
  by_cases hx : x = 0
  · subst x
    simpa only [map_zero,h0] using (Function.hasFiniteSupport_zero :
      Function.HasFiniteSupport (0 : Nat.Primes × Gal(K/ℚ) → ℝ))
  · apply (finiteEntry_hasFiniteMulSupport K hx).subset
    intro v hv he
    change finiteEntry K v.1 v.2 x = 1 at he
    apply hv
    change g (finiteEntry K v.1 v.2 x) = 0
    rw [he,h1]

omit [IsGalois ℚ K] in
lemma finite_posLog_support (x : K) : Function.HasFiniteSupport
    (fun v : Nat.Primes × Gal(K/ℚ) => log⁺ (finiteEntry K v.1 v.2 x)) :=
  finiteEntry_composed_support K _ posLog_zero posLog_one x

def exactHeight (x : K) : ℝ :=
  ((∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
    (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x))) /
      (Module.finrank ℚ K : ℝ)

omit [IsGalois ℚ K] in
lemma finrank_pos : 0 < (Module.finrank ℚ K : ℝ) := by
  exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)

omit [IsGalois ℚ K] in
lemma exactHeight_nonneg (x : K) : 0 ≤ exactHeight K x := by
  apply div_nonneg _ (finrank_pos K).le
  exact add_nonneg (sum_nonneg (fun _ _ => posLog_nonneg))
    (finsum_nonneg (fun _ => posLog_nonneg))

omit [IsGalois ℚ K] in
@[simp] lemma exactHeight_zero : exactHeight K (0 : K) = 0 := by
  simp [exactHeight]

omit [IsGalois ℚ K] in
@[simp] lemma exactHeight_one : exactHeight K (1 : K) = 0 := by
  simp [exactHeight]

omit [IsGalois ℚ K] in
@[simp] lemma exactHeight_neg (x : K) : exactHeight K (-x) = exactHeight K x := by
  simp only [exactHeight,AbsoluteValue.map_neg]

@[simp] lemma exactHeight_inv (x : K) : exactHeight K x⁻¹ = exactHeight K x := by
  by_cases hx : x = 0
  · simp [hx]
  have he : exactHeight K x - exactHeight K x⁻¹ = 0 := by
    unfold exactHeight
    rw [← sub_div]
    have hs :
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) -
          (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x⁻¹)) =
        ∑ σ : K →ₐ[ℚ] ℂ, log (infiniteEntry K σ x) := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro σ hσ
      rw [map_inv₀,posLog_sub_posLog_inv]
    have hf :
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) -
          (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x⁻¹)) =
        ∑ᶠ v : Nat.Primes × Gal(K/ℚ), log (finiteEntry K v.1 v.2 x) := by
      rw [← finsum_sub_distrib (finite_posLog_support K x) (finite_posLog_support K x⁻¹)]
      apply finsum_congr
      intro v
      rw [map_inv₀,posLog_sub_posLog_inv]
    rw [show ∀ a b c d : ℝ, (a+b)-(c+d)=(a-c)+(b-d) by intros; ring, hs,hf]
    exact weighted_log_product_formula K hx
  exact (sub_eq_zero.mp he).symm

omit [IsGalois ℚ K] in
lemma exactHeight_mul_le (x y : K) :
    exactHeight K (x*y) ≤ exactHeight K x + exactHeight K y := by
  unfold exactHeight
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (finrank_pos K).le
  have harch :
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (x*y))) ≤
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ y)) := by
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro σ _
    rw [map_mul]
    exact posLog_mul
  have hfin :
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (x*y))) ≤
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 y)) := by
    rw [← finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K y)]
    apply finsum_le_finsum' (finite_posLog_support K (x*y))
      ((finite_posLog_support K x).add (finite_posLog_support K y))
    intro v
    dsimp only
    rw [map_mul]
    exact posLog_mul
  linarith

lemma exactHeight_add_le (x y : K) :
    exactHeight K (x+y) ≤ log 2 + exactHeight K x + exactHeight K y := by
  have harch :
      (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (x+y))) ≤
        (Module.finrank ℚ K : ℝ) * log 2 +
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) +
        (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ y)) := by
    calc
      _ ≤ ∑ σ : K →ₐ[ℚ] ℂ,
          (log 2 + log⁺ (infiniteEntry K σ x) + log⁺ (infiniteEntry K σ y)) := by
        apply sum_le_sum
        intro σ _
        exact (posLog_le_posLog (id ((infiniteEntry K σ).nonneg _))
          ((infiniteEntry K σ).add_le x y)).trans posLog_add
      _ = _ := by simp [sum_add_distrib]
  have hfin :
      (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (x+y))) ≤
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) +
        (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 y)) := by
    rw [← finsum_add_distrib (finite_posLog_support K x) (finite_posLog_support K y)]
    apply finsum_le_finsum' (finite_posLog_support K (x+y))
      ((finite_posLog_support K x).add (finite_posLog_support K y))
    intro v
    dsimp only
    apply (posLog_le_posLog (id ((finiteEntry K v.1 v.2).nonneg _))
      (finiteEntry_nonarch K v.1 v.2 x y)).trans
    rcases le_total (finiteEntry K v.1 v.2 x) (finiteEntry K v.1 v.2 y) with h|h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left posLog_nonneg
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right posLog_nonneg
  unfold exactHeight
  have hh := div_le_div_of_nonneg_right (add_le_add harch hfin) (finrank_pos K).le
  simp only [add_div, mul_div_cancel_left₀ _ (finrank_pos K).ne'] at hh ⊢
  linarith

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_HeightTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def mismatch (x y u : ℝ) : ℝ := if ⌊x+u⌋ = ⌊y+u⌋ then 0 else 1

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.GridShift
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def unitShift : Measure ℝ := volume.restrict (Icc 0 1)
instance instIsProbabilityMeasureRealUnitShift : IsProbabilityMeasure unitShift := ⟨by simp [unitShift]⟩
def squareShift : Measure (ℝ × ℝ) := unitShift.prod unitShift
instance instIsProbabilityMeasureProdRealSquareShift : IsProbabilityMeasure squareShift := by unfold squareShift; infer_instance

def gridLabel (r : ℝ) (z : ℂ) (u : ℝ × ℝ) : ℤ × ℤ :=
  (⌊z.re/r+u.1⌋,⌊z.im/r+u.2⌋)

def gridMismatch (r : ℝ) (z w : ℂ) (u : ℝ × ℝ) : ℝ :=
  if gridLabel r z u = gridLabel r w u then 0 else 1

end
end PlanarUnitDistances.GridShift

namespace PlanarUnitDistances.LocalHeightTransfer
open MeasureTheory Set Real Finset
open PlanarUnitDistances.GridShift
noncomputable section
variable {P Q : Type} [Fintype P] [Fintype Q]

def left (w : P → Q → ℝ) (p : P) : ℝ := ∑ q, w p q

def dis {A : Type*} [DecidableEq A] (a b : A) : ℝ := if a=b then 0 else 1

def LabelControl (C : ℝ) (w : P → Q → ℝ) : Prop :=
  ∀ L : P ⊕ Q → ℕ,
    (∑ p, ∑ p', left w p * left w p' * dis (L (.inl p)) (L (.inl p'))) ≤
      C * ∑ p, ∑ q, w p q * dis (L (.inl p)) (L (.inr q))

end
end PlanarUnitDistances.LocalHeightTransfer

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_States
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.StateConsistency
open MeasureTheory Set Real
open PlanarUnitDistances.GridShift
noncomputable section
abbrev Shifts := (ℝ × ℝ) × (ℝ × ℝ)
def shiftLaw : Measure Shifts := squareShift.prod squareShift
instance instIsProbabilityMeasureShiftsShiftLaw : IsProbabilityMeasure shiftLaw := by unfold shiftLaw; infer_instance

def consistent (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) : Prop :=
  if s < n then
    gridLabel (exp (-s)) z u.1 = gridLabel (exp (-s)) z' u.1 ∧
    gridLabel (exp s) w u.2 ≠ gridLabel (exp s) w' u.2
  else
    gridLabel (exp (-s)) z u.1 ≠ gridLabel (exp (-s)) z' u.1 ∧
    gridLabel (exp s) w u.2 = gridLabel (exp s) w' u.2

def error (n s : ℝ) (z z' w w' : ℂ) (u : Shifts) : ℝ :=
  by classical exact if consistent n s z z' w w' u then 0 else 1

def envelope (n s : ℝ) : ℝ :=
  (Icc (n-log 2) (n+log 2)).indicator (fun _ => (1:ℝ)) s+2*exp (-|s-n|)

variable {E : Type*} [Fintype E]

def fractionalShifts (u : Shifts) : Shifts :=
  ((Int.fract u.1.1,Int.fract u.1.2),(Int.fract u.2.1,Int.fract u.2.2))

def Fractional (u : Shifts) : Prop :=
  u.1.1 ∈ Ico (0:ℝ) 1 ∧ u.1.2 ∈ Ico (0:ℝ) 1 ∧
  u.2.1 ∈ Ico (0:ℝ) 1 ∧ u.2.2 ∈ Ico (0:ℝ) 1

def localSetoid {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) : Setoid K :=
  { r := fun x y => v (x-y) ≤ exp s
    iseqv := ⟨by intro x; simpa using (exp_pos s).le,
      by intro x y h; rwa [v.map_sub],
      by
        intro x y z h₁ h₂
        have he : x-z = (x-y)+(y-z) := by ring
        rw [he]; exact (hv _ _).trans (max_le h₁ h₂)⟩ }

def nonarchConsistent {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (n s : ℝ) (z z' w w' : K) : Prop :=
  if s < n then
    Quotient.mk (localSetoid v hv (-s)) z = Quotient.mk _ z' ∧
    Quotient.mk (localSetoid v hv s) w ≠ Quotient.mk _ w'
  else
    Quotient.mk (localSetoid v hv (-s)) z ≠ Quotient.mk _ z' ∧
    Quotient.mk (localSetoid v hv s) w = Quotient.mk _ w'

end
end PlanarUnitDistances.StateConsistency

namespace PlanarUnitDistances.FiniteStates
open MeasureTheory Set Real
open scoped Classical
noncomputable section
variable {V : Type*}

def label (r : Setoid V) (x : V) : V → Bool := fun y => decide (r.r x y)

lemma measurable_label {Ω : Type*} [MeasurableSpace Ω]
    (r : Ω → Setoid V) (hr : ∀x y,MeasurableSet {s | (r s).r x y}) (x : V) :
    Measurable (fun s => label (r s) x) := by
  apply measurable_pi_iff.mpr
  intro y
  show Measurable (fun s => decide ((r s).r x y))
  have he : (fun s => decide ((r s).r x y)) =
      (fun s => if (r s).r x y then true else false) := by
    funext s; split_ifs <;> simp_all
  rw [he]
  exact Measurable.ite (hr x y) measurable_const measurable_const

def archRel (z : V → ℂ) (u : ℝ×ℝ) (s : ℝ) : Setoid V :=
  Setoid.ker (fun v => GridShift.gridLabel (exp s) (z v) u)

def archState (z w : V → ℂ) (u : StateConsistency.Shifts) (s : ℝ) (v : V) :
    (V → Bool)×(V → Bool) := (label (archRel z u.1 (-s)) v,label (archRel w u.2 s) v)

lemma archRel_measurable (z : V → ℂ) (u : ℝ×ℝ) :
    ∀x y,MeasurableSet {s | (archRel z u s).r x y} := by
  intro x y
  have hm (v : V) : Measurable (fun s => GridShift.gridLabel (exp s) (z v) u) := by
    apply Measurable.prodMk
    · exact ((measurable_const.div measurable_exp).add_const _).floor
    · exact ((measurable_const.div measurable_exp).add_const _).floor
  exact measurableSet_eq_fun (hm x) (hm y)
lemma archState_measurable (z w : V → ℂ) (u : StateConsistency.Shifts) (v : V) :
    Measurable (fun s => archState z w u s v) :=
  ((measurable_label _ (archRel_measurable z u.1) v).comp measurable_neg).prodMk
    (measurable_label _ (archRel_measurable w u.2) v)

def finiteRel {K : Type*} [Field K] (z : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) : Setoid V :=
  Setoid.comap z (StateConsistency.localSetoid v hv s)

def finiteState {K : Type*} [Field K] (z w : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (s : ℝ) (x : V) : (V → Bool)×(V → Bool) :=
  (label (finiteRel z v hv (-s)) x,label (finiteRel w v hv s) x)

lemma finiteRel_measurable {K : Type*} [Field K] (z : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) : ∀x y,MeasurableSet {s | (finiteRel z v hv s).r x y} := by
  intro x y
  exact measurableSet_le measurable_const measurable_exp
lemma finiteState_measurable {K : Type*} [Field K] (z w : V → K) (v : AbsoluteValue K ℝ)
    (hv : IsNonarchimedean v) (x : V) : Measurable (fun s => finiteState z w v hv s x) :=
  ((measurable_label _ (finiteRel_measurable z v hv) x).comp measurable_neg).prodMk
    (measurable_label _ (finiteRel_measurable w v hv) x)
end
end PlanarUnitDistances.FiniteStates

namespace PlanarUnitDistances.FiniteLevels
open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
noncomputable section
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

def measure (weight : ℝ≥0) (l u : J → ℝ) : Measure (J × ℝ) :=
  ∑ j, weight • Measure.map (fun s : ℝ => (j,s))
    (volume.restrict (Icc (l j) (u j)))

instance measure_finite (weight : ℝ≥0) (l u : J → ℝ) :
    IsFiniteMeasure (measure weight l u) := by
  unfold measure
  infer_instance

lemma measurable_pieces {Y : Type*} [MeasurableSpace Y] (f : J → ℝ → Y) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun x : J × ℝ => f x.1 x.2) := by
  exact measurable_from_prod_countable_right (fun j => hf j)

end
end PlanarUnitDistances.FiniteLevels

namespace PlanarUnitDistances.BudgetPlaces
open Real Finset
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]

def threshold (v : AbsoluteValue K ℝ) (d : K) : ℝ := -log (v d)
def alpha (v : AbsoluteValue K ℝ) (d d' : K) : ℝ :=
  threshold v (d-d')-min (threshold v d) (threshold v d')
def differenceProduct (d d' : K) : K := (d-d')*(d⁻¹-d'⁻¹)

end
end PlanarUnitDistances.BudgetPlaces

namespace PlanarUnitDistances.PlaceLevels
open Finset Real WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def finiteSupport (S : Finset K) : Finset (Nat.Primes × Gal(K/ℚ)) :=
  S.biUnion fun x => ((rootDenominators K x ∪ rootDenominators K x⁻¹).subtype Nat.Prime) ×ˢ univ

abbrev Place (S : Finset K) := (K →ₐ[ℚ] ℂ) ⊕ ↥(finiteSupport K S)
instance instFintypePlace (S : Finset K) : Fintype (Place K S) := inferInstanceAs (Fintype (_ ⊕ _))
instance instMeasurableSpacePlace (S : Finset K) : MeasurableSpace (Place K S) := ⊤
instance instMeasurableSingletonClassPlace (S : Finset K) : MeasurableSingletonClass (Place K S) := ⟨fun _ => trivial⟩

def av {S : Finset K} : Place K S → AbsoluteValue K ℝ
  | .inl σ => infiniteEntry K σ
  | .inr v => finiteEntry K v.val.1 v.val.2

def radius (S : Finset K) (v : Place K S) : ℝ := ∑x∈S, |log (av K v x)|
end
end PlanarUnitDistances.PlaceLevels

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Levels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelStates
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels FiniteStates CrossStructure
open scoped Classical NNReal ENNReal
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

def state (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) (x : V) :
    (V → Bool)×(V → Bool) := match a.1 with
  | .inl σ => archState (fun x => σ (z x)) (fun x => σ (w x)) (u σ) a.2 x
  | .inr v => finiteState z w (WeightedAbsoluteValues.finiteEntry K v.val.1 v.val.2)
      (WeightedAbsoluteValues.finiteEntry_nonarch K v.val.1 v.val.2) a.2 x

omit [Fintype V] in
lemma state_measurable (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x : V) :
    Measurable (fun a => state S z w u a x) := by
  change Measurable (fun a : Place K S × ℝ => (fun v s => state S z w u (v,s) x) a.1 a.2)
  refine FiniteLevels.measurable_pieces (J := Place K S) (fun v s => state S z w u (v,s) x) ?_
  intro v
  cases v with
  | inl σ => exact archState_measurable _ _ _ _
  | inr v => exact finiteState_measurable _ _ _ _ _

def bit (S : Finset K) (z : V → K) (src tgt : E → V) (a : Place K S × ℝ) (e : E) : Bool :=
  decide (a.2 < -log (av K a.1 (z (src e)-z (tgt e))))

omit [Fintype V] [Fintype E] in
lemma bit_measurable (S : Finset K) (z : V → K) (src tgt : E → V) (e : E) :
    Measurable (fun a => bit S z src tgt a e) := by
  have he : (fun a => bit S z src tgt a e) =
      (fun a => if a.2 < -log (av K a.1 (z (src e)-z (tgt e))) then true else false) := by
    funext a; unfold bit; split_ifs <;> simp_all
  rw [he]
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_lt measurable_snd ((measurable_of_finite (fun v : Place K S => -log (av K v (z (src e)-z (tgt e))))).comp measurable_fst)

def edgeError (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) (e : E) : ℝ :=
  if Consistent (bit S z src tgt a e) (state S z w u a (src e)) (state S z w u a (tgt e)) then 0 else 1

def meanError (μ : Law E) (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S × ℝ) : ℝ :=
  avg μ (edgeError S z w src tgt u a)
end
end PlanarUnitDistances.LevelStates

namespace PlanarUnitDistances.ThresholdProfiles
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def bit (a s : ℝ) : ℝ := if s < a then 1 else 0

variable {E : Type*} [Fintype E]

def frequency (p : E → ℝ) (a : E → ℝ) (s : ℝ) : ℝ := ∑ e, p e * bit (a e) s

def minority (p : E → ℝ) (a : E → ℝ) (s : ℝ) : ℝ :=
  min (frequency p a s) (1-frequency p a s)

end
end PlanarUnitDistances.ThresholdProfiles

namespace PlanarUnitDistances.WeightedAbsoluteValues
open MeasureTheory Set Finset Real
open scoped BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable {E : Type*} [Fintype E]

def archThreshold (d : E → K) (σ : K →ₐ[ℚ] ℂ) (e : E) : ℝ :=
  -log (infiniteEntry K σ (d e))
def finiteThreshold (d : E → K) (v : Nat.Primes × Gal(K/ℚ)) (e : E) : ℝ :=
  -log (finiteEntry K v.1 v.2 (d e))

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.LevelScale
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels
open scoped Classical NNReal
noncomputable section
variable {K E : Type*} [Field K] [NumberField K] [Fintype E]

def weight (K : Type*) [Field K] [NumberField K] : ℝ≥0 :=
  ⟨(Module.finrank ℚ K : ℝ)⁻¹,inv_nonneg.mpr (Nat.cast_nonneg _)⟩
def measure (S : Finset K) : Measure (Place K S × ℝ) :=
  FiniteLevels.measure (weight K) (fun v => -radius K S v) (radius K S)
instance instIsFiniteMeasureProdPlaceRealMeasure (S : Finset K) : IsFiniteMeasure (measure S) := by unfold measure; infer_instance

def cut (S : Finset K) (d : E → K) (v : Place K S) (e : E) := -log (av K v (d e))
def prob (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) : ℝ :=
  ThresholdProfiles.frequency μ.val (cut S d a.1) a.2
def minority (μ : Law E) (S : Finset K) (d : E → K) (a : Place K S × ℝ) : ℝ :=
  min (prob μ S d a) (1-prob μ S d a)
def scale (μ : Law E) (S : Finset K) (d : E → K) : ℝ :=
  ∫a,minority μ S d a ∂measure S

end
end PlanarUnitDistances.LevelScale

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]

def support (μ : Law X) : Law {x : X // 0<μ.val x} where
  val := fun x => μ.val x.val
  nonneg := fun x => μ.nonneg x.val
  total := by
    rw [←sum_subtype (univ.filter (fun x => 0<μ.val x)) (fun x => by simp)]
    rw [sum_filter]
    convert μ.total using 1
    apply sum_congr rfl
    intro x _
    split_ifs with hx
    · rfl
    · exact (le_antisymm (le_of_not_gt hx) (μ.nonneg x)).symm

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Predictions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteLaw
open Finset MeasureTheory
open scoped Classical
noncomputable section
variable {X Y C : Type*} [Fintype X] [Fintype Y] [Fintype C]

def uniform (X : Type*) [Fintype X] [Nonempty X] : Law X where
  val _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [Fintype.card_ne_zero]

def Law.pmf (μ : Law X) : PMF X := PMF.ofFintype (fun x => ENNReal.ofReal (μ.val x)) (by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => μ.nonneg x),μ.total,ENNReal.ofReal_one])

@[simp] lemma Law.pmf_apply (μ : Law X) (x : X) : μ.pmf x = ENNReal.ofReal (μ.val x) := rfl

end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.EmbeddingTails
open Finset FiniteLaw WeightedAbsoluteValues Real
open scoped Classical
noncomputable section
variable {K Ω I : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype Ω] [Fintype I]

abbrev Embeddings (K : Type*) [Field K] [NumberField K] := K →ₐ[ℚ] ℂ

instance instNonemptyEmbeddings : Nonempty (Embeddings K) := ⟨IsAlgClosed.lift⟩

end
end PlanarUnitDistances.EmbeddingTails

namespace PlanarUnitDistances.FiniteMarginalScore
open Finset FiniteLaw StrictCross CrossStructure CrossSampling StarScore
open scoped Classical
noncomputable section
variable {A B Q : Type*} [Fintype A] [Fintype B] [Fintype Q]

def collision {X Y : Type*} [Fintype X] [Fintype Y] (ν : Law X) (φ : X → Y) : ℝ :=
  ∑ y,(event ν (fun x => φ x=y))^2

def tau (ν : Law (A×B)) : ℝ := collision ν Prod.fst+collision ν Prod.snd-1

end
end PlanarUnitDistances.FiniteMarginalScore

namespace PlanarUnitDistances.PredictionCoupling
open Finset FiniteLaw FiniteMarginalScore
open scoped Classical
noncomputable section
variable {P H A B : Type*} [Fintype P] [Fintype H] [Fintype A] [Fintype B]

def coupling (μ : Law P) (h : P → H) : Law (P×P) :=
  mix (push μ h) (fun j => pair (cond μ h j) (cond μ h j))

end
end PlanarUnitDistances.PredictionCoupling

namespace PlanarUnitDistances.HashFeatures
open Finset Real
open scoped RealInnerProductSpace Classical
noncomputable section
variable {A B : Type*} [Fintype A] [Fintype B]

abbrev Index (A B : Type*) := A ⊕ (B ⊕ A×B)
abbrev V (A B : Type*) [Fintype A] [Fintype B] := EuclideanSpace ℝ (Index A B)

def vector (x : A×B) (a b c : ℝ) : V A B := by
  classical
  exact WithLp.toLp 2 (Sum.elim (Pi.single x.1 a)
    (Sum.elim (Pi.single x.2 b) (Pi.single x c)))

end
end PlanarUnitDistances.HashFeatures

namespace PlanarUnitDistances.Hashing
open Finset FiniteLaw StrictCross
open scoped Classical
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [Nonempty C]

abbrev Hash (A B C : Type*) := (A → C) × (B → C)
def law : Law (Hash A B C) := pair (uniform (A → C)) (uniform (B → C))
def state (h : Hash A B C) (x : A×B) : C×C := (h.1 x.1,h.2 x.2)

def indicator (x y : A×B) : ℝ := if Adj x y then 1 else 0

end
end PlanarUnitDistances.Hashing

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def mixture (μ : Law X) (ν : X → Law Y) : Law Y where
  val y := avg μ (fun x => (ν x).val y)
  nonneg y := avg_nonneg μ (fun x => (ν x).nonneg y)
  total := by
    simp only [avg]
    rw [sum_comm]
    simp_rw [← mul_sum,Law.total,mul_one]
    exact μ.total

end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.CrossPrediction
open Finset FiniteLaw
open scoped Classical
noncomputable section
variable {P Q H A B C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype C] [Fintype T]
  [DecidableEq H] [DecidableEq A] [DecidableEq B] [Nonempty C]

def actual (κ : Law Q) (w : Q → Law P) (X : P → A×B) (Z : Q → A×B) : ℝ :=
  avg κ (fun q => avg (w q) (fun p => Hashing.indicator (X p) (Z q)))

def predicted (κ : Law Q) (w : Q → Law P) (h : P → H) (X : P → A×B) (Z : Q → A×B) : ℝ :=
  avg κ (fun q => avg (w q) (fun p =>
    avg (cond (mixture κ w) h (h p)) (fun r => Hashing.indicator (X r) (Z q))))

open MeasureTheory Real
end
end PlanarUnitDistances.CrossPrediction

namespace PlanarUnitDistances.FiniteLaw
open MeasureTheory Finset Set
open scoped Classical
noncomputable section
variable {S : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
lemma sum_real_atoms (μ : Measure S) [IsFiniteMeasure μ] : ∑s,μ.real {s}=μ.real Set.univ := by
  have hi := integral_fintype (f := fun _ : S => (1:ℝ)) (μ := μ) (integrable_const 1)
  simpa only [integral_const,smul_eq_mul,mul_one] using hi.symm

def fromMeasure (μ : Measure S) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ) : Law S where
  val s := μ.real {s}/μ.real Set.univ
  nonneg s := div_nonneg ENNReal.toReal_nonneg hμ.le
  total := by rw [←sum_div,sum_real_atoms,div_self hμ.ne']

variable {Ω : Type*} [MeasurableSpace Ω]
omit [Fintype S] [MeasurableSingletonClass S] in
lemma map_real_univ (μ : Measure Ω) (c : Ω → S) (hc : Measurable c) :
    (μ.map c).real Set.univ=μ.real Set.univ := by
  simp only [Measure.real,Measure.map_apply hc MeasurableSet.univ,Set.preimage_univ]

def compress (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : 0<μ.real Set.univ)
    (c : Ω → S) (hc : Measurable c) : Law S :=
  fromMeasure (μ.map c) (by rwa [map_real_univ μ c hc])

end
end PlanarUnitDistances.FiniteLaw

namespace PlanarUnitDistances.FiniteLaw
open Finset
open scoped Classical
noncomputable section
variable {X : Type*} [Fintype X]

def triple (μ : Law X) : Law (X×(X×X)) := pair μ (pair μ μ)
def entry (x : X×(X×X)) (i : Fin 3) : X := ![x.1,x.2.1,x.2.2] i

end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Quantization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.TripleCoupling
open Finset FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {P Q H : Type*} [Fintype P] [Fintype Q] [Fintype H]

abbrev Outcome (P Q : Type*) := P×(P×(Q×(Q×Q)))

def law (π : Law (P×Q)) (h : P → H) : Law (Outcome P Q) :=
  dependent (left π) (fun p => pair (cond (left π) h (h p)) (triple (row π p)))

def point (a : Outcome P Q) : P := a.1
def prediction (a : Outcome P Q) : P := a.2.1
def neighbor (a : Outcome P Q) (i : Fin 3) : Q := entry a.2.2 i

end
end PlanarUnitDistances.TripleCoupling

namespace PlanarUnitDistances.FiniteQuantization
open scoped Classical
noncomputable section

def radius (B τ : ℝ) : ℕ := ⌈B/τ⌉₊
abbrev Cell (B τ : ℝ) := ↥(Finset.Icc (-(radius B τ : ℤ)) (radius B τ : ℤ))
abbrev Axis (B τ : ℝ) := Option (Cell B τ)
abbrev Alphabet (B τ : ℝ) := (Axis B τ×Axis B τ)×(Axis B τ×Axis B τ)

def axis (B τ x : ℝ) : Axis B τ :=
  if h : ⌊x/τ⌋ ∈ Finset.Icc (-(radius B τ : ℤ)) (radius B τ : ℤ) then
    some ⟨⌊x/τ⌋,h⟩ else none

def code (B τ : ℝ) (Z W : ℂ) : Alphabet B τ :=
  ((axis B τ Z.re,axis B τ Z.im),(axis B τ W.re,axis B τ W.im))

end
end PlanarUnitDistances.FiniteQuantization

namespace PlanarUnitDistances.BoundedGeometricCover
open FiniteLaw FiniteStarCoupling TripleCoupling FiniteQuantization
open scoped Classical
noncomputable section
variable {P Q K : Type*} [Field K] [NumberField K]

abbrev BigIndex := Bool ⊕ (Fin 3 × (Bool ⊕ Unit))
abbrev SmallIndex := Unit ⊕ (Fin 3 × Fin 3)

def big (Z W : P → K) (a b : Q → K) (x : Outcome P Q) : BigIndex → K
  | .inl false => Z (prediction x)
  | .inl true => W (prediction x)
  | .inr (i,.inl false) => a (neighbor x i)
  | .inr (i,.inl true) => b (neighbor x i)
  | .inr (i,.inr ()) => Z (point x)-a (neighbor x i)

def small (Z : P → K) (a : Q → K) (x : Outcome P Q) : SmallIndex → K
  | .inl () => Z (prediction x)-Z (point x)
  | .inr (i,j) => (Z (point x)-a (neighbor x i))-(Z (point x)-a (neighbor x j))

def accept (Z W : P → K) (E : P → Q → Prop) (B τ : ℝ) (σ : K →ₐ[ℚ] ℂ)
    (r : P) (q : Q) : Prop :=
  ∃s,E s q ∧ code B τ (σ (Z r)) (σ (W r))=code B τ (σ (Z s)) (σ (W s))

def bad (Z W : P → K) (a b : Q → K) (E : P → Q → Prop) (B τ δ : ℝ) :
    Fin 6 → (Outcome P Q × (K →ₐ[ℚ] ℂ)) → Prop
  | 0,x => ∃i,B < ‖x.2 (big Z W a b x.1 i)‖
  | 1,x => ∃i,small Z a x.1 i ≠ 0 ∧ ‖x.2 (small Z a x.1 i)‖ < δ
  | 2,x => point x.1=prediction x.1
  | 3,x => ∃ij : Fin 3 × Fin 3,ij.1 < ij.2 ∧ neighbor x.1 ij.1=neighbor x.1 ij.2
  | 4,x => ∃i,¬E (point x.1) (neighbor x.1 i)
  | 5,x => ∃i,¬accept Z W E B τ x.2 (prediction x.1) (neighbor x.1 i)

end
end PlanarUnitDistances.BoundedGeometricCover

namespace PlanarUnitDistances.BoundedProbabilities
open Finset FiniteLaw FiniteStarCoupling TripleCoupling BoundedGeometricCover
open WeightedAbsoluteValues EmbeddingTails
open scoped Classical
noncomputable section
variable {P Q H K : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Field K] [NumberField K] [IsGalois ℚ K]

def failure (π : Law (P×Q)) (h : P → H) (Z W : P → K)
    (E : P → Q → Prop) (B τ : ℝ) : ℝ :=
  avg (uniform (Embeddings K)) (fun σ => avg (right π) (fun q => avg (col π q) (fun p =>
    event (cond (left π) h (h p)) (fun r => ¬accept Z W E B τ σ r q))))

end
end PlanarUnitDistances.BoundedProbabilities

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteAcceptance
open Finset FiniteLaw CrossPrediction Real MeasureTheory
open scoped Classical
noncomputable section
variable {P Q H C T : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype C] [Fintype T] [DecidableEq H]

def feature (c : C) : EuclideanSpace ℝ C := WithLp.toLp 2 (Pi.single c 1)
def test (A : C → Prop) : EuclideanSpace ℝ C := WithLp.toLp 2 (fun c => if A c then 1 else 0)

omit [Fintype H] [Fintype T] [DecidableEq H] in
def actual (κ : Law Q) (w : Q → Law P) (c : P → C) (A : Q → C → Prop) : ℝ :=
  avg κ (fun q => event (w q) (fun p => A q (c p)))

omit [Fintype T] [DecidableEq H] in
def predicted (κ : Law Q) (w : Q → Law P) (h : P → H) (c : P → C) (A : Q → C → Prop) : ℝ :=
  avg κ (fun q => avg (w q) (fun p => event (cond (mixture κ w) h (h p)) (fun r => A q (c r))))

end
end PlanarUnitDistances.FiniteAcceptance

namespace PlanarUnitDistances.BoundedScaleFinite
open Finset FiniteLaw FiniteStarCoupling TripleCoupling BoundedGeometricCover
open WeightedAbsoluteValues BoundedProbabilities FiniteQuantization EmbeddingTails
open scoped Classical
noncomputable section
variable {P Q H K : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Field K] [NumberField K] [IsGalois ℚ K]

omit [Fintype H] in
def information (π : Law (P×Q)) : ℝ :=
  FiniteInformation.KL (FiniteInformation.wedge (right π).val (fun q => (col π q).val))
    (fun pp : P×P => (left π).val pp.1*(left π).val pp.2)

end
end PlanarUnitDistances.BoundedScaleFinite

namespace PlanarUnitDistances.LogHistory
open Filter
noncomputable section

def length (M : ℕ) (t : ℝ) : ℕ := ⌊Real.log t/(4*(Real.log M+1))⌋₊+1

end
end PlanarUnitDistances.LogHistory

namespace PlanarUnitDistances.IncidenceScale
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence
open scoped Classical
noncomputable section
variable (s : Sequence)
def graph (n : ℕ) := GeometricLaw.graph (s.P n) (s.Q n) (s.good n).positive
def model (n : ℕ) : CommonFieldModel.Model (s.P n) (s.Q n) :=
  Classical.choice (CommonFieldModel.exists_model (s.good n).algebraicP (s.good n).algebraicQ)

def scale (n : ℕ) : ℝ := LevelScale.scale (graph s n) (model s n).support
  (fun pq => (model s n).z (.inl pq.1)-(model s n).z (.inr pq.2))

end
end PlanarUnitDistances.IncidenceScale

namespace PlanarUnitDistances.CommonTemplate
open Finset FiniteLaw FiniteStarCoupling TemplateCoupling StrictCross CrossSampling CrossTemplates CrossStructure
open scoped Classical
noncomputable section
variable {P Q H A B I : Type*} [Fintype P] [Fintype Q] [Fintype H]
  [Fintype A] [Fintype B] [Fintype I]

def templateLaw (π : Law (P×Q)) (h : P → H) (q : Q) : Law (I → H) :=
  independent (historyLaw π h q) I

def predictionError (π : Law (P×Q)) (h : P → H) (x : P → A×B) (y : Q → A×B) : ℝ :=
  avg π (fun pq => 1-crossMass (posteriorState π h x (h pq.1)) (y pq.2))

def samplingError (k : ℕ) (α : ℝ) : ℝ :=
  (k:ℝ)^2*(1-α)^(k-2)+2*(1-α/2)^(k-1)+(2/α)*(1-α/2)^k

end
end PlanarUnitDistances.CommonTemplate

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Slots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LevelGeometry
open MeasureTheory Set Real FiniteStates PlaceLevels LevelStates BudgetPlaces
open scoped Classical
noncomputable section
variable {K V : Type*} [Field K] [NumberField K]

def allowance {S : Finset K} : Place K S → ℝ
  | .inl _ => log 2
  | .inr _ => 0

end
end PlanarUnitDistances.LevelGeometry

namespace PlanarUnitDistances.BudgetIntervals
open Finset Set
open scoped BigOperators
noncomputable section

def overlap (a b l r : ℝ) : ℝ := max 0 (min b r-max a l)

variable {E : Type*} [Fintype E]

def tail (μ : E → ℝ) (x : E → ℝ) (s : ℝ) : ℝ :=
  ∑ e, μ e * if s < x e then 1 else 0

def interiorMass (μ : E → ℝ) (x : E → ℝ) (l r : ℝ) : ℝ :=
  ∑ e, μ e * if l < x e ∧ x e < r then 1 else 0

end
end PlanarUnitDistances.BudgetIntervals

namespace PlanarUnitDistances.PlaceScore
open MeasureTheory Set Real BudgetIntervals StrictCross
open scoped Classical
noncomputable section

def common (ε p : ℝ) : Prop := ε ≤ p ∧ p ≤ 1-ε

def reward (ε p ρ : ℝ) (one : Bool) : ℝ :=
  if common ε p then coefficient ρ
  else if (if one then p<ε else 1-ε<p) then 2 else 0

def ind (A : Set ℝ) (s : ℝ) : ℝ := A.indicator (fun _ => 1) s

def cap (ε : ℝ) (g ρ : ℝ → ℝ) (b b' T s : ℝ) : ℝ :=
  reward ε (g s) (ρ s) true*ind (Icc (b-T) b ∩ Iio b) s+
  reward ε (g s) (ρ s) false*ind (Icc b' (b'+T)) s

end
end PlanarUnitDistances.PlaceScore

namespace PlanarUnitDistances.LevelScores
open FiniteLaw StrictCross CrossStructure RareScore PlaceScore
open scoped Classical
noncomputable section
variable {A B : Type*}

def minority (p : ℝ) : Bool := decide (p<1/2)

def positive (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) : ℝ :=
  if common ε p then coefficient ρ*RareScore.ind (b=c ∧ nonshared b y z)
  else if good then 2*RareScore.ind (exceptional (minority p) l base ∧
    b=minority p ∧ c=minority p ∧ nonshared (minority p) y z) else 0

def score (ε p ρ : ℝ) (good : Prop) (l base y z : A×B) (b c : Bool) : ℝ :=
  positive ε p ρ good l base y z b c-RareScore.ind (b≠c)

end
end PlanarUnitDistances.LevelScores

namespace PlanarUnitDistances.RareRows
open FiniteLaw FiniteStarCoupling RareScore LevelScores
open scoped Classical
noncomputable section
variable {P Q A B : Type*} [Fintype P] [Fintype Q]

def frequency (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ := event π (fun pq => bit pq.1 pq.2=true)
def scoreP (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : ℝ :=
  avg (left π) (fun p => avg (pair (row π p) (row π p)) (fun qq =>
    LevelScores.score ε f (event (row π p) (fun q => bit p q=true)) good l (x p)
      (y qq.1) (y qq.2) (bit p qq.1) (bit p qq.2)))
def scoreQ (ε f : ℝ) (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×B) (y : Q → A×B)
    (good : Prop) (l : A×B) : ℝ :=
  avg (right π) (fun q => avg (pair (col π q) (col π q)) (fun pp =>
    LevelScores.score ε f (event (col π q) (fun p => bit p q=true)) good l (y q)
      (x pp.1) (x pp.2) (bit pp.1 q) (bit pp.2 q)))

end
end PlanarUnitDistances.RareRows

namespace PlanarUnitDistances.RareRows
open FiniteLaw FiniteStarCoupling TemplateCoupling LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q Θ A B : Type*} [Fintype P] [Fintype Q] [Fintype Θ]

def scoreT (ε f : ℝ) (π : Law (P×Q)) (a : Q → Law Θ) (bit : P → Q → Bool)
    (x : P → A×B) (y : Q → A×B) (good : Prop) (l : A×B) : ℝ :=
  avg (templates π a) (fun θ => scoreP ε f (slice π a θ) bit x y good l)

end
end PlanarUnitDistances.RareRows

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.RareMass
open FiniteLaw CrossStructure RareScore LevelScores
open scoped Classical
noncomputable section
variable {A B E : Type*} [Fintype E]

def nonsharedCoord {D : Type*} (r : Bool) (x : D×D) : D := if r then x.2 else x.1

end
end PlanarUnitDistances.RareMass

namespace PlanarUnitDistances.RareLabels
open FiniteLaw FiniteStarCoupling LevelScores RareScore RareMass
open scoped Classical
noncomputable section
variable {P Q A : Type*} [Fintype P] [Fintype Q] [Fintype A]

def minorityMass (π : Law (P×Q)) (bit : P → Q → Bool) : ℝ :=
  min (event π (fun pq => bit pq.1 pq.2=true)) (1-event π (fun pq => bit pq.1 pq.2=true))
def error (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : ℝ :=
  event π (fun pq => ¬CrossStructure.Consistent (bit pq.1 pq.2) (x pq.1) (y pq.2))
end
end PlanarUnitDistances.RareLabels

namespace PlanarUnitDistances.RareMoments
open Finset FiniteLaw FiniteStarCoupling RareLabels LevelScores RareScore
open scoped Classical
noncomputable section
variable {P Q A : Type} [Fintype P] [Fintype Q] [Fintype A]

def hp (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (l : A×A) : ℝ :=
  event (left π) (fun p => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (x p))
def hq (π : Law (P×Q)) (bit : P → Q → Bool) (y : Q → A×A) (l : A×A) : ℝ :=
  event (right π) (fun q => exceptional (minority (event π (fun pq => bit pq.1 pq.2=true))) l (y q))
def joint (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (y : Q → A×A) (l : A×A) : ℝ :=
  event π (fun pq => exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x pq.1) ∧
    exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (y pq.2))
def wedge (π : Law (P×Q)) (bit : P → Q → Bool) (x : P → A×A) (l : A×A) : ℝ :=
  avg (right π) (fun q => event (pair (col π q) (col π q)) (fun pp =>
    exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x pp.1) ∧
    exceptional (minority (event π (fun rs => bit rs.1 rs.2=true))) l (x pp.2)))

end
end PlanarUnitDistances.RareMoments

namespace PlanarUnitDistances.LevelBookkeeping
open Finset FiniteLaw FiniteStarCoupling RareLabels RareMoments RareScore
open scoped Classical
noncomputable section
variable {D P Q A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype A]

def goodRare (ε τ : ℝ) (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : Prop :=
  ¬PlaceScore.common ε (event π (fun pq => b pq.1 pq.2=true)) ∧ error π b x y ≤ τ

def damaged (ε τ : ℝ) (π : Law (P×Q)) (b : P → Q → Bool) (x : P → A×A) (y : Q → A×A) : Prop :=
  ¬PlaceScore.common ε (event π (fun pq => b pq.1 pq.2=true)) ∧ τ < error π b x y

end
end PlanarUnitDistances.LevelBookkeeping

namespace PlanarUnitDistances.FiniteLaw
open scoped Classical
noncomputable section
variable {D : Type*} [Fintype D]
def cut (σ : Law D) (c : D → Prop) (f : D → ℝ) : ℝ := avg σ (fun s => if c s then f s else 0)
end
end PlanarUnitDistances.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Scores
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GlobalScores
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows LevelScores RareScore RareMoments
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

def common (ε : ℝ) (π : Law (P×Q)) (b : D → P → Q → Bool) (s : D) : Prop :=
  PlaceScore.common ε (event π (fun pq => b s pq.1 pq.2=true))

def bad (c g : D → Prop) (s : D) : Prop := ¬c s ∧ ¬g s

end
end PlanarUnitDistances.GlobalScores

namespace PlanarUnitDistances.ScoreBook
open FiniteLaw FiniteStarCoupling TemplateCoupling CommonTemplate RareRows RareMoments GlobalScores
open scoped Classical
noncomputable section

structure Book (D P Q H A : Type) [Fintype D] [Fintype P] [Fintype Q] where
  levels : Law D
  graph : Law (P×Q)
  bit : D → P → Q → Bool
  point : D → P → A×A
  center : D → Q → A×A
  history : P → H
  epsilon : ℝ
  good : D → Prop
  label : D → A×A

namespace Book
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A] [Fintype I]

def C (B : Book D P Q H A) : D → Prop := common B.epsilon B.graph B.bit
def R (B : Book D P Q H A) : D → Prop := fun s => ¬B.C s ∧ B.good s
def S (B : Book D P Q H A) := avg B.levels (fun s => RareLabels.minorityMass B.graph (B.bit s))
def M (B : Book D P Q H A) := avg B.levels (fun s => RareLabels.error B.graph (B.bit s) (B.point s) (B.center s))
def WC (B : Book D P Q H A) := event B.levels B.C
def WB (B : Book D P Q H A) := event B.levels (GlobalScores.bad B.C B.good)
def HP (B : Book D P Q H A) := cut B.levels B.R (fun s => hp B.graph (B.bit s) (B.point s) (B.label s))
def HQ (B : Book D P Q H A) := cut B.levels B.R (fun s => hq B.graph (B.bit s) (B.center s) (B.label s))
def J (B : Book D P Q H A) := cut B.levels B.R (fun s => RareMoments.joint B.graph (B.bit s) (B.point s) (B.center s) (B.label s))
def EP (B : Book D P Q H A) := cut B.levels B.C (fun s => predictionError B.graph B.history (B.point s) (B.center s))
def CP (B : Book D P Q H A) := cut B.levels B.C (fun s => VP B.graph (B.bit s))
def CQ (B : Book D P Q H A) := cut B.levels B.C (fun s => VQ B.graph (B.bit s))
def CT (B : Book D P Q H A) := cut B.levels B.C (fun s => avg
  (templates B.graph (templateLaw (I := I) B.graph B.history))
  (fun θ => VP (slice B.graph (templateLaw (I := I) B.graph B.history) θ) (B.bit s)))
def DP (B : Book D P Q H A) := avg B.levels (fun s => scoreP B.epsilon (frequency B.graph (B.bit s))
  B.graph (B.bit s) (B.point s) (B.center s) (B.good s) (B.label s))
def DQ (B : Book D P Q H A) := avg B.levels (fun s => scoreQ B.epsilon (frequency B.graph (B.bit s))
  B.graph (B.bit s) (B.point s) (B.center s) (B.good s) (B.label s))
def DT (B : Book D P Q H A) := avg B.levels (fun s => scoreT B.epsilon (frequency B.graph (B.bit s))
  B.graph (templateLaw (I := I) B.graph B.history) (B.bit s) (B.point s) (B.center s) (B.good s) (B.label s))
def T (B : Book D P Q H A) := cut B.levels B.C (fun s => avg (left B.graph)
  (fun p => FiniteMarginalScore.tau (posteriorState B.graph B.history (B.point s) (B.history p))))

end Book
end
end PlanarUnitDistances.ScoreBook

namespace PlanarUnitDistances.BookCoercivity
open FiniteLaw ScoreBook FiniteStarCoupling RareMoments
open scoped Classical
noncomputable section
variable {D P Q H A I : Type} [Fintype D] [Fintype P] [Fintype Q]
  [Fintype H] [Fintype A] [Fintype I]

def commonLoss (B : Book D P Q H A) (ζ η : ℝ) : ℝ :=
  12*B.M+(12*(Fintype.card I:ℝ)/ζ)*B.EP+
    (12*(CommonTemplate.samplingError (Fintype.card I) (η^2)/(1-(Fintype.card I:ℝ)*ζ)+8*η))*B.WC+
    8*B.J+2*B.WB
omit [Fintype I] in
def centerLoss (B : Book D P Q H A) : ℝ := 4*B.J+6*B.M+B.WB
omit [Fintype I] in
def pointLoss (B : Book D P Q H A) (δ : ℝ) : ℝ :=
  4*B.J+26*B.M+(20/δ)*B.EP+(20*δ)*B.WC+B.WB
omit [Fintype I] in
def scaleLoss (B : Book D P Q H A) : ℝ := B.M+B.WB/2

def loss (B : Book D P Q H A) (ζ η δ eP eQ eT ePred : ℝ) : ℝ :=
  |commonLoss (I := I) B ζ η|+|centerLoss B|+|pointLoss B δ|+|scaleLoss B|+
    |eP|+|eQ|+|eT|+|ePred|

end
end PlanarUnitDistances.BookCoercivity

namespace PlanarUnitDistances.LevelSnapshot
open MeasureTheory Set Finset FiniteLaw LevelStates PlaceLevels
open scoped Classical
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

abbrev Data (V E : Type*) := (E → Bool)×(V → ((V → Bool)×(V → Bool)))

def snapshot (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (a : Place K S×ℝ) : Data V E :=
  (bit S z src tgt a,state S z w u a)

omit [Fintype V] [Fintype E] in
lemma measurable_snapshot (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) : Measurable (snapshot S z w src tgt u) := by
  exact (Measurable.of_eval (fun e => bit_measurable S z src tgt e)).prodMk
    (Measurable.of_eval (fun x => state_measurable S z w u x))

end
end PlanarUnitDistances.LevelSnapshot

namespace PlanarUnitDistances.ActualSlots
open MeasureTheory Set Finset FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot LevelScores RareScore
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

def frequency (μ : Law E) (a : Data V E) : ℝ := event μ (fun e => a.1 e=true)
def rareException (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x : V) (a : Data V E) : Prop :=
  ¬PlaceScore.common ε (frequency μ a) ∧ good a ∧ exceptional (minority (frequency μ a)) (label a) (a.2 x)
def active (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x : V) (a : Data V E) : ℝ :=
  ind (PlaceScore.common ε (frequency μ a))+ind (rareException ε μ good label x a)

def positive (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (a : Data V E) : ℝ :=
  LevelScores.positive ε (frequency μ a) (event ν (fun j => a.1 (edge j)=true)) (good a)
    (label a) (a.2 x) (a.2 (y e)) (a.2 (y f)) (a.1 (edge e)) (a.1 (edge f))
def score (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (a : Data V E) : ℝ :=
  positive ε μ ν edge y x good label e f a-ind (a.1 (edge e)≠a.1 (edge f))

end
end PlanarUnitDistances.ActualSlots

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Integration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.TailWindows
open Finset Set FiniteLaw
open scoped Classical
noncomputable section
variable {E : Type*} [Fintype E]

def tail (μ : Law E) (x : E → ℝ) (s : ℝ) : ℝ := event μ (fun e => s<x e)

end
end PlanarUnitDistances.TailWindows

namespace PlanarUnitDistances.WindowVariation
open MeasureTheory Set Real FiniteLaw TailWindows PlaceScore
open scoped Classical
noncomputable section
variable {E F : Type*} [Fintype E] [Fintype F]

def variation (ε : ℝ) (g ρ : ℝ → ℝ) (s : ℝ) : ℝ :=
  if common ε (g s) then 2*ρ s*(1-ρ s) else 0

end
end PlanarUnitDistances.WindowVariation

namespace PlanarUnitDistances.ExpectedBudget
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces
  LevelGeometry PlaceScore TailWindows WindowVariation
open scoped Classical
noncomputable section
variable {K E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K] [Fintype E] [Fintype F]

def pairScore (S : Finset K) (d : F → K) (f : F → F → Place K S → ℝ → ℝ) (a : F×F) : ℝ :=
  (∑v : Place K S,((∫s,f a.1 a.2 v s)-|threshold (av K v) (d a.1)-threshold (av K v) (d a.2)|)) /
    (Module.finrank ℚ K:ℝ)

def excess (S : Finset K) (d : F → K) (l r : Place K S → ℝ) (v : Place K S) (a : F×F) : ℝ :=
  (1/20000:ℝ)*max 0 (r v-l v)*
    (if l v < min (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2)) ∧
        min (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2))<r v ∧
        l v < max (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2)) ∧
        max (threshold (av K v) (d a.1)) (threshold (av K v) (d a.2))<r v then 1 else 0)

end
end PlanarUnitDistances.ExpectedBudget

namespace PlanarUnitDistances.SlotIntegration
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E] [Fintype F]

def truncatedPositive (S : Finset K) (z w : V → K) (src tgt : E → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts)
    (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (y : F → V) (x : V)
    (good : Data V E → Prop) (label : Data V E → (V → Bool)×(V → Bool))
    (e f : F) (v : Place K S) (s : ℝ) : ℝ :=
  (Icc (-radius K S v) (radius K S v)).indicator
    (fun s => positive ε μ ν edge y x good label e f (snapshot S z w src tgt u (v,s))) s

end
end PlanarUnitDistances.SlotIntegration

namespace PlanarUnitDistances.ActualBudgetIntegral
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical
noncomputable section
variable {K V E F : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype E] [Fintype F]

def commonVariation (ε : ℝ) (μ : Law E) (ν : Law F) (edge : F → E) (a : Data V E) : ℝ :=
  if PlaceScore.common ε (frequency μ a) then StarScore.variation ν (fun j => a.1 (edge j)) else 0

end
end PlanarUnitDistances.ActualBudgetIntegral

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Preparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.ActualScoreBook
open MeasureTheory FiniteLaw LevelSnapshot ActualSlots ScoreBook FiniteStarCoupling RareRows RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

abbrev ActualBook (V P Q H : Type) [Fintype V] [Fintype P] [Fintype Q] :=
  Book (Data V (P×Q)) P Q H (V → Bool)

def mass (S : Finset K) := (LevelScale.measure S).real Set.univ

def make (S : Finset K) (z w : V → K) (x : P → V) (y : Q → V)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (π : Law (P×Q)) (h : P → H)
    (ε : ℝ) (good : Data V (P×Q) → Prop) (label : Data V (P×Q) → (V → Bool)×(V → Bool))
    (hm : 0 < mass S) : ActualBook V P Q H where
  levels := compress (LevelScale.measure S) hm
    (snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
    (measurable_snapshot S z w (fun pq : P×Q => x pq.1) (fun pq : P×Q => y pq.2) u)
  graph := π
  bit := fun a p q => a.1 (p,q)
  point := fun a p => a.2 (x p)
  center := fun a q => a.2 (y q)
  history := h
  epsilon := ε
  good := good
  label := label

end
end PlanarUnitDistances.ActualScoreBook

namespace PlanarUnitDistances.LawStable
open Finset FiniteLaw StarScore FiniteStarCoupling
open scoped Classical
noncomputable section
variable {X P Q : Type*} [Fintype X] [Fintype P] [Fintype Q]

def majority (μ : Law X) (b : X → Bool) : Bool := !(LevelScores.minority (frequency μ b))
def minorityFrequency (μ : Law X) (b : X → Bool) : ℝ := min (frequency μ b) (1-frequency μ b)

end
end PlanarUnitDistances.LawStable

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LocalProfiles
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore RareMoments ScoreBook LevelScores
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

def rareBit (B : Book D P Q H A) (s : D) := minority (RareRows.frequency B.graph (B.bit s))
def exceptional (B : Book D P Q H A) (s : D) (a : A×A) : Prop := RareScore.exceptional (rareBit B s) (B.label s) a

def X (B : Book D P Q H A) (s : D) (p : P) : ℝ :=
  if B.R s then ind (exceptional B s (B.point s p)) else 0

def signed (B : Book D P Q H A) (s : D) (p : P) : ℝ := sign (rareBit B s)*X B s p

def jfirst (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (exceptional B s (B.point s a.2.1) ∧ exceptional B s (B.center s a.1))
def jsecond (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (exceptional B s (B.point s a.2.2) ∧ exceptional B s (B.center s a.1))
def jpoints (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (exceptional B s (B.point s a.2.1) ∧ exceptional B s (B.point s a.2.2))
def ifirst (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (¬CrossStructure.Consistent (B.bit s a.2.1 a.1) (B.point s a.2.1) (B.center s a.1))
def isecond (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  ind (¬CrossStructure.Consistent (B.bit s a.2.2 a.1) (B.point s a.2.2) (B.center s a.1))
def bits (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  value (B.bit s a.2.1 a.1)-value (B.bit s a.2.2 a.1)

def error1 (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  (if B.C s then |bits B s a| else 0)+ind (¬B.C s ∧ ¬B.good s)+
  (if B.R s then 2*(jfirst B s a+jsecond B s a+ifirst B s a+isecond B s a) else 0)
def error2 (B : Book D P Q H A) (s : D) (a : Q×(P×P)) : ℝ :=
  if B.R s then 2*(jpoints B s a+jfirst B s a+jsecond B s a+ifirst B s a+isecond B s a) else 0

end
end PlanarUnitDistances.LocalProfiles

namespace PlanarUnitDistances.WedgeSummary
open FiniteLaw FiniteStarCoupling WedgeProfiles RareScore ScoreBook LevelScores LocalProfiles
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q]

def JW (B : Book D P Q H A) := cut B.levels B.R (fun s => RareMoments.wedge B.graph (B.bit s) (B.point s) (B.label s))

end
end PlanarUnitDistances.WedgeSummary

namespace PlanarUnitDistances.ActualProfiles
open MeasureTheory Set FiniteLaw LevelSnapshot ScoreBook ActualScoreBook PlaceLevels
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]

structure Input (K : Type*) (V P Q H : Type) [Field K] [NumberField K]
    [Fintype V] [Fintype P] [Fintype Q] where
  support : Finset K
  z : V → K
  w : V → K
  point : P → V
  center : Q → V
  shifts : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts
  graph : Law (P×Q)
  history : P → H
  epsilon : ℝ
  good : Data V (P×Q) → Prop
  label : Data V (P×Q) → (V → Bool)×(V → Bool)
  mass_pos : 0 < mass support

namespace Input
variable (G : Input K V P Q H)
def book : ActualBook V P Q H := make G.support G.z G.w G.point G.center G.shifts
  G.graph G.history G.epsilon G.good G.label G.mass_pos
def snap (a : Place K G.support×ℝ) := snapshot G.support G.z G.w
  (fun pq : P×Q => G.point pq.1) (fun pq : P×Q => G.center pq.2) G.shifts a
def threshold (v : Place K G.support) (p : P) (q : Q) :=
  -Real.log (av K v (G.z (G.point p)-G.z (G.center q)))
def profile (p : P) (v : Place K G.support) :=
  ∫s in Icc (-radius K G.support v) (radius K G.support v), LocalProfiles.signed G.book (G.snap (v,s)) p
def heightAt (p : P) (v : Place K G.support) :=
  ∫s in Icc (-radius K G.support v) (radius K G.support v), LocalProfiles.X G.book (G.snap (v,s)) p
def errorAt (i : Bool) (a : Q×(P×P)) (v : Place K G.support) :=
  ∫s in Icc (-radius K G.support v) (radius K G.support v),
    (if i then LocalProfiles.error1 else LocalProfiles.error2) G.book (G.snap (v,s)) a

end Input
end
end PlanarUnitDistances.ActualProfiles

namespace PlanarUnitDistances.BudgetParameters
open Filter CommonTemplate
noncomputable section

def vanishing (n : ℕ) : ℝ := 1/((n:ℝ)+1)

structure Params where
  epsilon : ℝ
  delta : ℝ
  eta : ℝ
  d : ℝ
  k : ℕ
  m : ℕ
  epsilon_pos : 0 < epsilon
  epsilon_lt : epsilon < 1/2
  delta_pos : 0 < delta
  eta_pos : 0 < eta
  eta_lt : eta < 1/2
  d_pos : 0 < d
  k_pos : 0 < k
  m_pos : 0 < m

def Params.zeta (a : Params) : ℝ := 1/(2*a.k)

def joint (C γ η ε ξ : ℝ) : ℝ := ((C*(ε+ε)/γ)^η+ξ)/γ

def leading (a : Params) (C γ η : ℝ) : ℝ :=
  8*joint C γ η a.epsilon 0*C+
    (96*a.eta+20*a.delta+24*samplingError a.k (a.eta^2)+
      (12*(a.k:ℝ)/a.zeta+20/a.delta)*4/(a.m:ℝ))/a.epsilon

def wedge (a : Params) (C γ η : ℝ) : ℝ :=
  (a.d+joint C γ η a.epsilon 0/Real.sqrt a.d)*C

end
end PlanarUnitDistances.BudgetParameters

namespace PlanarUnitDistances.IncidenceBook
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale ActualScoreBook LevelSnapshot BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params) (i : ℕ)
def capacity : ℕ := a.m^(2*a.k)
def length : ℕ := LogHistory.length (capacity a) (s.t i)
structure Realization where
  depth : ℕ
  depth_lt : depth < length s a i
  mass_pos : 0 < mass (model s i).support
  shifts : ((model s i).field →ₐ[ℚ] ℂ) → StateConsistency.Shifts
  history : s.P i → FiniteInformation.History (Fin a.m×Fin a.m) depth
  label : Data (s.P i⊕s.Q i) (s.P i×s.Q i) →
    ((s.P i⊕s.Q i) → Bool)×((s.P i⊕s.Q i) → Bool)

variable {s a i}
local instance instFintypeSumSubtypePlaneMemFinsetPQ : Fintype (s.P i⊕s.Q i) := inferInstance
@[instance_reducible] def labelFintype (V : Type) [Fintype V] : Fintype (V→Bool) := inferInstance
local instance instFintypeForallSumSubtypePlaneMemFinsetPQBool : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
local instance instFintypeProdSubtypePlaneMemFinsetPQ_rfc8304_1 : Fintype (s.P i×s.Q i) := inferInstance
@[instance_reducible] def snapshotFintype (V P Q : Type) [Fintype V] [Fintype P] [Fintype Q] : Fintype (Data V (P×Q)) := inferInstance
local instance : Fintype (Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := snapshotFintype _ _ _
def Realization.good (_R : Realization s a i) (d : Data (s.P i⊕s.Q i) (s.P i×s.Q i)) : Prop :=
  error (graph s i) (fun p q => d.1 (p,q)) (fun p => d.2 (.inl p))
    (fun q => d.2 (.inr q)) ≤ a.epsilon

def Realization.input (R : Realization s a i) : ActualProfiles.Input (model s i).field
    (s.P i⊕s.Q i) (s.P i) (s.Q i) (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) where
  support := (model s i).support
  z := (model s i).z
  w := (model s i).w
  point := Sum.inl
  center := Sum.inr
  shifts := R.shifts
  graph := graph s i
  history := R.history
  epsilon := a.epsilon
  good := R.good
  label := R.label
  mass_pos := R.mass_pos

def Realization.book (R : Realization s a i) : ActualBook (s.P i⊕s.Q i) (s.P i) (s.Q i)
    (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) := R.input.book

set_option maxHeartbeats 1000000 in
def Realization.fractional (R : Realization s a i) : Prop :=
  ∀σ,StateConsistency.Fractional (R.shifts σ)
set_option maxHeartbeats 1000000 in
def Realization.scale_eq (R : Realization s a i) : Prop :=
  mass (model s i).support*R.book.S=scale s i
set_option maxHeartbeats 1000000 in
def Realization.mistake_bound (R : Realization s a i) : Prop :=
  mass (model s i).support*R.book.M ≤ 2*Real.log 2+4
set_option maxHeartbeats 1000000 in
def Realization.history_bound (R : Realization s a i) : Prop :=
  Fintype.card (FiniteInformation.History (Fin a.m×Fin a.m) R.depth) ≤ a.m^(2*length s a i)
def Realization.stable (R : Realization s a i) (L : ℝ) : Prop :=
  ∀d,minorityMass (graph s i) (R.book.bit d) ≤ L*(VP (graph s i) (R.book.bit d)+VQ (graph s i) (R.book.bit d))
def Realization.rare (R : Realization s a i) : Prop :=
  ∀d,R.book.R d → minorityMass (graph s i) (R.book.bit d) ≤ hp (graph s i) (R.book.bit d) (R.book.point d) (R.label d)+
    hq (graph s i) (R.book.bit d) (R.book.center d) (R.label d)+error (graph s i) (R.book.bit d) (R.book.point d) (R.book.center d)
def Realization.common_bound (R : Realization s a i) : Prop := R.book.WC ≤ R.book.S/a.epsilon
def Realization.bad_bound (R : Realization s a i) : Prop := R.book.WB ≤ R.book.M/a.epsilon
def Realization.height_bound (R : Realization s a i) (C : ℝ) : Prop := R.book.HP+R.book.HQ ≤ C*(R.book.S+R.book.M)
def Realization.joint_bound (R : Realization s a i) (C : ℝ) : Prop :=
  R.book.J ≤ joint C (27/50) (1/25) a.epsilon (s.ξ i)/2*(R.book.HP+R.book.HQ)
def Realization.wedge_bound (R : Realization s a i) (C : ℝ) : Prop :=
  WedgeSummary.JW R.book ≤ (a.d+joint C (27/50) (1/25) a.epsilon (s.ξ i)/Real.sqrt a.d)*R.book.HP
def Realization.prediction_bound (R : Realization s a i) : Prop :=
  R.book.EP ≤ R.book.M+R.book.WC*(4/(a.m:ℝ)+18*(IncidenceSequence.information (s.P i) (s.Q i)/(length s a i:ℝ))^(1/4:ℝ))
def Realization.Valid (R : Realization s a i) (C L : ℝ) : Prop :=
  R.fractional ∧ R.scale_eq ∧ R.mistake_bound ∧ R.history_bound ∧ R.stable L ∧ R.rare ∧
  R.common_bound ∧ R.bad_bound ∧ R.height_bound C ∧ R.joint_bound C ∧ R.wedge_bound C ∧ R.prediction_bound

end
end PlanarUnitDistances.IncidenceBook

namespace PlanarUnitDistances.BookEnvelope
open Filter FiniteLaw ScoreBook BookCoercivity BudgetParameters
open scoped Classical
noncomputable section

variable (a : Params) (C γ η ξ r : ℝ)
def height : ℝ := C*(1+r)
def j : ℝ := joint C γ η a.epsilon ξ/2*height C r
def pred : ℝ := r+(4/(a.m:ℝ)+18*r)/a.epsilon
def star : ℝ := r+2*r*(1/a.epsilon+height C r)
def prediction : ℝ := r+r/a.epsilon+r/a.epsilon
def common : ℝ := 12*r+(12*(a.k:ℝ)/a.zeta)*pred a r+
  (12*(CommonTemplate.samplingError a.k (a.eta^2)/(1-(a.k:ℝ)*a.zeta)+8*a.eta))/a.epsilon+
  8*j a C γ η ξ r+2*(r/a.epsilon)
def center : ℝ := 4*j a C γ η ξ r+6*r+r/a.epsilon
def point : ℝ := 4*j a C γ η ξ r+26*r+(20/a.delta)*pred a r+20*a.delta/a.epsilon+r/a.epsilon
def sc : ℝ := r+r/a.epsilon/2
def total : ℝ := common a C γ η ξ r+center a C γ η ξ r+point a C γ η ξ r+sc a r+
  3*star a C r+prediction a r

end
end PlanarUnitDistances.BookEnvelope

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_PredictionBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PredictionPairBudget
open MeasureTheory Set Finset Real PlaceLevels LevelGeometry PlaceScore
open scoped Classical
noncomputable section

variable {K V : Type*} [Field K] [NumberField K] [Fintype V]

def score (S : Finset K) (z w : V → K)
    (u : (K →ₐ[ℚ] ℂ) → StateConsistency.Shifts) (x y : V) (a : Place K S×ℝ) : ℝ :=
  (if (LevelStates.state S z w u a x).1=(LevelStates.state S z w u a y).1 then 1 else 0)+
  (if (LevelStates.state S z w u a x).2=(LevelStates.state S z w u a y).2 then 1 else 0)-1

end
end PlanarUnitDistances.PredictionPairBudget

namespace PlanarUnitDistances.PredictionCut
open Finset MeasureTheory FiniteLaw RareScore PredictionCoupling
open scoped Classical
noncomputable section
variable {P H A B Ω : Type*} [Fintype P] [Fintype H]

def pairScore (x y : A×B) : ℝ :=
  (if x.1=y.1 then 1 else 0)+(if x.2=y.2 then 1 else 0)-1
end
end PlanarUnitDistances.PredictionCut

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_RareBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceNoise
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params)
def dp (i : ℕ) : ℝ := s.t i^(-1/2:ℝ)
def collision (i : ℕ) : ℝ := (capacity a:ℝ)^(length s a i)*dp s i
def rootInfo (i : ℕ) : ℝ := (IncidenceSequence.information (s.P i) (s.Q i)/(length s a i:ℝ))^(1/4:ℝ)
def noise (i : ℕ) : ℝ := |(2*Real.log 2+4)/scale s i|+collision s a i+vanishing i+rootInfo s a i
end
end PlanarUnitDistances.IncidenceNoise

namespace PlanarUnitDistances.IncidenceEstimates
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
local instance instFintypeSumSubtypePlaneMemFinsetPQ : Fintype (s.P i⊕s.Q i) := inferInstance
local instance instFintypeForallSumSubtypePlaneMemFinsetPQBool : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
end
end PlanarUnitDistances.IncidenceEstimates

namespace PlanarUnitDistances.EnvelopeCoercivity
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook BudgetParameters
  BookEnvelope BookCoercivity
open scoped Classical
noncomputable section
variable {D P Q H A : Type} [Fintype D] [Fintype P] [Fintype Q] [Fintype H] [Fintype A]
variable (B : Book D P Q H A) (a : Params) {C L ξ r : ℝ}

def pointConstant (L : ℝ) : ℝ := 400000*L+2
def lossConstant (L : ℝ) : ℝ := 23000000000*L+130001

end
end PlanarUnitDistances.EnvelopeCoercivity

namespace PlanarUnitDistances.ProfileBudget
open MeasureTheory Set Finset FiniteLaw FiniteStarCoupling LevelSnapshot
  ScoreBook ActualScoreBook PlaceLevels ActualProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

def weighted (f : Place K G.support → ℝ) : ℝ := (LevelScale.weight K : ℝ)*∑v,f v
def l1 (f : Place K G.support → ℝ) : ℝ := weighted G (fun v => |f v|)
def height (p : P) : ℝ := weighted G (G.heightAt p)
def error (i : Bool) (a : Q×(P×P)) : ℝ := weighted G (G.errorAt i a)

end
end PlanarUnitDistances.ProfileBudget

namespace PlanarUnitDistances.RarePairBudget
open MeasureTheory Set Real FiniteLaw PlaceScore RareScore
open scoped Classical
noncomputable section
variable {A B : Type*}

def cap (ε : ℝ) (g : ℝ → ℝ) (b b' T s : ℝ) : ℝ :=
  (if g s<ε then 2 else 0)*PlaceScore.ind (Icc (b-T) b ∩ Iio b) s+
  (if 1-ε<g s then 2 else 0)*PlaceScore.ind (Icc b' (b'+T)) s

end
end PlanarUnitDistances.RarePairBudget

namespace PlanarUnitDistances.ActualRarePair
open MeasureTheory Set Finset Real FiniteLaw PlaceLevels BudgetPlaces LevelSnapshot ActualSlots
open scoped Classical BigOperators
noncomputable section
variable {K V E : Type*} [Field K] [NumberField K] [Fintype V] [Fintype E]

def positive (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) : ℝ :=
  if PlaceScore.common ε (frequency μ a) then 0 else
    LevelScores.positive ε (frequency μ a) 0 (good a) (label a) (a.2 x) (a.2 y) (a.2 y') (a.1 e) (a.1 f)
def score (ε : ℝ) (μ : Law E) (good : Data V E → Prop)
    (label : Data V E → (V → Bool)×(V → Bool)) (x y y' : V) (e f : E) (a : Data V E) : ℝ :=
  positive ε μ good label x y y' e f a-RareScore.ind (a.1 e≠a.1 f)

end
end PlanarUnitDistances.ActualRarePair

namespace PlanarUnitDistances.ActualHeights
open MeasureTheory FiniteLaw FiniteStarCoupling ActualProfiles ActualScoreBook LevelSnapshot
  ProfileBudget ScoreBook RareScore
open scoped Classical
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)
def center (q : Q) : ℝ := mass G.support*avg G.book.levels
  (fun d => if G.book.R d then ind (LocalProfiles.exceptional G.book d (G.book.center d q)) else 0)
def mistake (p : P) (q : Q) : ℝ := mass G.support*avg G.book.levels
  (fun d => ind (¬CrossStructure.Consistent (G.book.bit d p q) (G.book.point d p) (G.book.center d q)))
end
end PlanarUnitDistances.ActualHeights

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Tails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceCoercivity
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
  EnvelopeCoercivity
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
local instance instFintypeSumSubtypePlaneMemFinsetPQ : Fintype (s.P i⊕s.Q i) := inferInstance
local instance instFintypeForallSumSubtypePlaneMemFinsetPQBool : Fintype ((s.P i⊕s.Q i)→Bool) := labelFintype _
variable (R : Realization s a i)

def errorCoefficient (a : Params) (C ξ r : ℝ) : ℝ :=
  250000*BookEnvelope.total a C (27/50) (1/25) ξ r+r/a.epsilon+
  8*BookEnvelope.j a C (27/50) (1/25) ξ r+8*r+
  2*(a.d+BudgetParameters.joint C (27/50) (1/25) a.epsilon ξ/Real.sqrt a.d)*BookEnvelope.height C r

end
end PlanarUnitDistances.IncidenceCoercivity

namespace PlanarUnitDistances.IncidenceRare
open Filter FiniteLaw FiniteStarCoupling ScoreBook IncidenceSequence IncidenceScale
  IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters EnvelopeCoercivity
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}

local instance instFintypeSumSubtypePlaneMemFinsetPQ_rfc8304_1 : Fintype (s.P i⊕s.Q i) := inferInstance
local instance instFintypeProdSubtypePlaneMemFinsetPQ_rfc8304_2 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := IncidenceBook.snapshotFintype _ _ _
def Ready (R : Realization s a i) (c C τ : ℝ) : Prop :=
  R.fractional ∧ R.scale_eq ∧ R.mistake_bound ∧ R.common_bound ∧ R.bad_bound ∧
  c*scale s i ≤ mass (model s i).support*R.book.HP ∧
  mass (model s i).support*(R.book.HP+R.book.HQ) ≤ C*scale s i ∧
  mass (model s i).support*(R.book.CQ+R.book.WB+8*R.book.J+8*R.book.M+2*WedgeSummary.JW R.book) ≤ τ*scale s i

end
end PlanarUnitDistances.IncidenceRare

namespace PlanarUnitDistances.IncidenceHeights
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare ActualScoreBook ActualProfiles ProfileBudget
open scoped Classical
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
variable (R : Realization s a i)

local instance instFintypeSumSubtypePlaneMemFinsetPQ_rfc8304_2 : Fintype (s.P i⊕s.Q i) := inferInstance
def Z (x : s.Q i×(s.P i×s.P i)) : ℝ := error R.input true x+error R.input false x
end
end PlanarUnitDistances.IncidenceHeights

namespace PlanarUnitDistances.TailControl
open Finset MeasureTheory Set
open scoped BigOperators

noncomputable def layer (a t : ℝ) : ℝ := (Ioc 0 a).indicator (fun _ => 1) t

noncomputable def mass {P : Type*} (μ : P → ℝ) (F : Finset P) : ℝ := ∑ p ∈ F, μ p

section Finite
variable {P Q : Type*} [Fintype P] [Fintype Q]

noncomputable def tails (μ a : P → ℝ) (t : ℝ) : ℝ := ∑ p, μ p * layer (a p) t

noncomputable def pairTails (w : P → Q → ℝ) (a : P → ℝ) (b : Q → ℝ) (t : ℝ) : ℝ :=
  ∑ p, ∑ q, w p q * layer (min (a p) (b q)) t

noncomputable def capped (a : P → ℝ) (T : Finset P) (p : P) : ℝ := by
  classical
  exact if p ∈ T then a p else 0

end Finite
end PlanarUnitDistances.TailControl

namespace PlanarUnitDistances.AccurateBand
open FiniteLaw Finset
open scoped Classical BigOperators
noncomputable section
variable {X : Type*} [Fintype X]

def kept (W Z : X → ℝ) (L U δ : ℝ) (x : X) : Prop :=
  L ≤ W x ∧ W x ≤ U ∧ Z x ≤ δ*W x

end
end PlanarUnitDistances.AccurateBand

namespace PlanarUnitDistances.TailParameters
open Filter
noncomputable section

def coefficient (C R ξ : ℝ) : ℝ := 144*((((C/R)/(27/50:ℝ))^(1/25:ℝ)+ξ)/(27/50:ℝ))^2*C
end
end PlanarUnitDistances.TailParameters

namespace PlanarUnitDistances.IncidenceBand
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceRare IncidenceHeights ActualProfiles ProfileBudget BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}

local instance instFintypeSumSubtypePlaneMemFinsetPQ_rfc8304_3 : Fintype (s.P i⊕s.Q i) := inferInstance
def band (R : Realization s a i) (J δ : ℝ) (x : s.Q i×(s.P i×s.P i)) : Prop :=
  J≤height R.input x.2.1+height R.input x.2.2 ∧
  height R.input x.2.1+height R.input x.2.2≤2*J ∧
  Z R x≤δ*(height R.input x.2.1+height R.input x.2.2)

end
end PlanarUnitDistances.IncidenceBand

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Circles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PopularCircles
open Finset UnitCodegree
open scoped Classical BigOperators
noncomputable section

def neighbors (S : Finset ℂ) (q : ℂ) : Finset ℂ := S.filter (fun p => dist p q=1)
def candidates (S : Finset ℂ) : Finset ℂ :=
  S.biUnion (fun p => S.biUnion (fun r => if p=r then ∅ else (centerPolynomial p r).roots.toFinset))
def popular (S : Finset ℂ) (k : ℕ) : Finset ℂ :=
  (candidates S).filter (fun q => k≤(neighbors S q).card)
def multiple (S C : Finset ℂ) : Finset ℂ :=
  S.filter (fun p => 2≤(C.filter (fun q => dist p q=1)).card)

end
end PlanarUnitDistances.PopularCircles

namespace PlanarUnitDistances.IncidencePopular
open Filter Finset FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale PowerGrowth
open scoped Classical
noncomputable section
variable (s : Sequence)
def points (i : ℕ) : Finset ℂ := (s.P i).image UnitCodegree.zCoordinate
def k (i : ℕ) : ℕ := ⌈s.t i^(9/10:ℝ)⌉₊
def centers (i : ℕ) : Finset ℂ := PopularCircles.popular (points s i) (k s i)
def bad (i : ℕ) (a : s.Q i×(s.P i×s.P i)) : Prop :=
  ∃c∈centers s i,dist (UnitCodegree.zCoordinate a.2.1.val) c=1 ∧
    dist (UnitCodegree.zCoordinate a.2.2.val) c=1
end
end PlanarUnitDistances.IncidencePopular

namespace PlanarUnitDistances.LawDeletion
open FiniteLaw FiniteStarCoupling
open scoped Classical
noncomputable section
variable {X P Q : Type*} [Fintype X] [Fintype P] [Fintype Q]
def keep (μ : Law X) (A B : X → Prop) (x : X) : Prop := 0<μ.val x ∧ A x ∧ ¬B x
end
end PlanarUnitDistances.LawDeletion

namespace PlanarUnitDistances.PlaceLogGeometry
open Finset PlaceLevels WeightedAbsoluteValues
open scoped BigOperators Classical
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

def supported (S : Finset K) (x : K) : Prop :=
  ∀v : Nat.Primes×Gal(K/ℚ),v∉finiteSupport K S → Real.log (finiteEntry K v.1 v.2 x)=0

end
end PlanarUnitDistances.PlaceLogGeometry

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Extraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.OrganizedProfiles
open Finset PlaceLevels WeightedAbsoluteValues ActualProfiles ProfileBudget PlaceLogGeometry
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H)

def jump (p : P) (q : Q) : K := G.z (G.point p)-G.z (G.center q)
def ratio (a : Q×(P×P)) : K := jump G a.2.1 a.1/jump G a.2.2 a.1

end
end PlanarUnitDistances.OrganizedProfiles

namespace PlanarUnitDistances.OrganizedGraph
open Finset PlaceLevels WeightedAbsoluteValues ActualProfiles ProfileBudget PlaceLogGeometry OrganizedProfiles
open scoped Classical BigOperators
noncomputable section
variable {K : Type*} {V P Q H : Type} [Field K] [NumberField K] [IsGalois ℚ K]
  [Fintype V] [Fintype P] [Fintype Q]
variable (G : Input K V P Q H) (A : Q×(P×P) → Prop)

def edge (p r : P) : Prop := ∃q,A (q,(p,r))
def label (p r : P) : K := if h : edge A p r then ratio G (h.choose,(p,r)) else 1

end
end PlanarUnitDistances.OrganizedGraph

namespace PlanarUnitDistances.IncidenceSelected
open Filter Finset FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook
  IncidenceHeights OrganizedProfiles WeightedAbsoluteValues
open scoped Classical BigOperators
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
local instance instFintypeProdSubtypePlaneMemFinsetPQ_rfc8304_3 : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
def kept (R : Realization s a i) (J δ : ℝ) :=
  LawDeletion.keep (WedgeLaw.law (graph s i)) (IncidenceBand.band R J δ) (IncidencePopular.bad s i)
def edge (R : Realization s a i) (J δ : ℝ) := OrganizedGraph.edge (kept R J δ)
local instance instFintypeSumSubtypePlaneMemFinsetPQ_rfc8304_4 : Fintype (s.P i⊕s.Q i) := inferInstance
def label (R : Realization s a i) (J δ : ℝ) := OrganizedGraph.label R.input (kept R J δ)
def pairs (R : Realization s a i) (J δ : ℝ) := univ.filter (fun pr : s.P i×s.P i => edge R J δ pr.1 pr.2)

end
end PlanarUnitDistances.IncidenceSelected

namespace PlanarUnitDistances.ImageRelation
open Finset
open scoped Classical
noncomputable section
variable {α β K : Type*}
variable (P : Finset α) (f : α → β) (hf : Function.Injective f)
def image : Finset β := P.image f
def equiv : P ≃ image P f where
  toFun p := ⟨f p,mem_image.mpr ⟨p,p.property,rfl⟩⟩
  invFun p := ⟨(mem_image.mp p.property).choose,(mem_image.mp p.property).choose_spec.1⟩
  left_inv p := Subtype.ext (hf (mem_image.mp (show f p∈P.image f from mem_image.mpr ⟨p,p.property,rfl⟩)).choose_spec.2)
  right_inv p := Subtype.ext (mem_image.mp p.property).choose_spec.2
variable (E : P → P → Prop) (l : P → P → K) [One K]
def edge (p r : β) : Prop := ∃hp : p∈image P f,∃hr : r∈image P f,
  E ((equiv P f hf).symm ⟨p,hp⟩) ((equiv P f hf).symm ⟨r,hr⟩)
def label (p r : β) : K := if hp : p∈image P f then if hr : r∈image P f then
  l ((equiv P f hf).symm ⟨p,hp⟩) ((equiv P f hf).symm ⟨r,hr⟩) else 1 else 1
end
end PlanarUnitDistances.ImageRelation

namespace PlanarUnitDistances.IncidenceComplex
open Finset IncidenceSequence IncidenceScale IncidenceBook IncidenceSelected
open scoped Classical
noncomputable section
variable {s : Sequence} {a : BudgetParameters.Params} {i : ℕ}
def pull (p : IncidencePopular.points s i) : s.P i :=
  (ImageRelation.equiv (s.P i) UnitCodegree.zCoordinate UnitCodegree.zCoordinate.injective).symm p

def edge (R : Realization s a i) (J δ : ℝ) : ℂ → ℂ → Prop :=
  ImageRelation.edge (s.P i) UnitCodegree.zCoordinate UnitCodegree.zCoordinate.injective (IncidenceSelected.edge R J δ)
def label (R : Realization s a i) (J δ : ℝ) : ℂ → ℂ → (model s i).field :=
  ImageRelation.label (s.P i) UnitCodegree.zCoordinate UnitCodegree.zCoordinate.injective (IncidenceSelected.label R J δ)
end
end PlanarUnitDistances.IncidenceComplex

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Radicals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

def SquareIndependent {K : Type u} [CommMonoid K] (ds : List K) : Prop :=
  ∀ s : List K, s.Sublist ds → s ≠ [] → ∀ c : K, s.prod ≠ c ^ 2

section Quadratic

variable {K : Type u} [Field K] [CharZero K] (a b : K)

theorem square_in_quadratic_iff :
    (∃ z : QuadraticAlgebra K a 0, z ^ 2 = algebraMap K _ b) ↔
      (∃ x : K, x ^ 2 = b) ∨ (∃ y : K, a * y ^ 2 = b) := by
  constructor
  · rintro ⟨z, hz⟩
    have hr := congrArg QuadraticAlgebra.re hz
    have hi := congrArg QuadraticAlgebra.im hz
    simp only [pow_two, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re] at hr
    simp only [pow_two, QuadraticAlgebra.im_mul, zero_mul, add_zero,
      QuadraticAlgebra.algebraMap_im, mul_comm z.im z.re] at hi
    have hi' : z.re * z.im = 0 := by linear_combination hi / 2
    rcases mul_eq_zero.mp hi' with hx | hy
    · right; exact ⟨z.im, by simpa [hx, pow_two, mul_assoc] using hr⟩
    · left; exact ⟨z.re, by simpa [hy, pow_two] using hr⟩
  · rintro (⟨x, hx⟩ | ⟨y, hy⟩)
    · refine ⟨⟨x, 0⟩, ?_⟩
      ext <;> simp [pow_two, ← hx]
    · refine ⟨⟨0, y⟩, ?_⟩
      ext <;> simp [pow_two, ← hy, mul_assoc]

def quadraticFlip : QuadraticAlgebra K a 0 ≃+* QuadraticAlgebra K a 0 where
  toFun z := ⟨z.re, -z.im⟩
  invFun z := ⟨z.re, -z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp; ring
  map_add' z w := by ext <;> simp; ring

omit [CharZero K] in
@[simp] theorem quadraticFlip_cast (x : K) :
    quadraticFlip a (algebraMap K _ x) = algebraMap K _ x := by
  ext <;> simp [quadraticFlip]

omit [CharZero K] in
@[simp] theorem quadraticFlip_omega :
    quadraticFlip a (QuadraticAlgebra.omega : QuadraticAlgebra K a 0) =
      -QuadraticAlgebra.omega := by
  ext <;> simp [quadraticFlip, QuadraticAlgebra.omega]

def quadraticLift (σ : K ≃+* K) (ha : σ a = a) :
    QuadraticAlgebra K a 0 ≃+* QuadraticAlgebra K a 0 where
  toFun z := ⟨σ z.re, σ z.im⟩
  invFun z := ⟨σ.symm z.re, σ.symm z.im⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp [ha]
  map_add' z w := by ext <;> simp

@[simp] theorem quadraticLift_cast (σ : K ≃+* K) (ha : σ a = a) (x : K) :
    quadraticLift a σ ha (algebraMap K _ x) = algebraMap K _ (σ x) := by
  ext <;> simp [quadraticLift]

@[simp] theorem quadraticLift_omega (σ : K ≃+* K) (ha : σ a = a) :
    quadraticLift a σ ha (QuadraticAlgebra.omega : QuadraticAlgebra K a 0) =
      QuadraticAlgebra.omega := by
  ext <;> simp [quadraticLift, QuadraticAlgebra.omega]

def quadraticEval {L : Type u} [Field L] (f : K →+* L)
    (r : L) (hr : r ^ 2 = f a) : QuadraticAlgebra K a 0 →+* L where
  toFun z := f z.re + f z.im * r
  map_zero' := by simp
  map_one' := by change f 1 + f 0 * r = 1; simp
  map_add' z w := by simp; ring
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      map_add, map_mul, zero_mul, add_zero]
    rw [← hr]
    ring

omit [CharZero K] in
@[simp] theorem quadraticEval_cast {L : Type u} [Field L] (f : K →+* L)
    (r : L) (hr : r ^ 2 = f a) (x : K) :
    quadraticEval a f r hr (algebraMap K _ x) = f x := by
  simp [quadraticEval]

omit [CharZero K] in
@[simp] theorem quadraticEval_omega {L : Type u} [Field L] (f : K →+* L)
    (r : L) (hr : r ^ 2 = f a) :
    quadraticEval a f r hr QuadraticAlgebra.omega = r := by
  simp [quadraticEval, QuadraticAlgebra.omega]

end Quadratic

structure RadicalModel {K : Type u} [Field K] (ds : List K) where
  Carrier : Type u
  field : Field Carrier
  charZero : CharZero Carrier
  incl : K →+* Carrier
  roots : Fin ds.length → Carrier
  roots_sq : ∀ i, roots i ^ 2 = incl (ds.get i)
  flips : Fin ds.length → (Carrier ≃+* Carrier)
  flips_base : ∀ i x, flips i (incl x) = incl x
  flips_roots : ∀ i j, flips i (roots j) = if i = j then -roots j else roots j
  square_descends : ∀ b : K, (∃ z : Carrier, z ^ 2 = incl b) ↔
    ∃ s : List K, s.Sublist ds ∧ ∃ c : K, b = c ^ 2 * s.prod
  evaluate : ∀ (L : Type u) [Field L] (f : K →+* L) (r : Fin ds.length → L),
    (∀ i, r i ^ 2 = f (ds.get i)) →
    ∃ φ : Carrier →+* L, (∀ x, φ (incl x) = f x) ∧ ∀ i, φ (roots i) = r i

attribute [instance] RadicalModel.field RadicalModel.charZero

section Construction

variable {K : Type u} [Field K] [CharZero K]

def emptyModel : RadicalModel ([] : List K) where
  Carrier := K
  field := inferInstance
  charZero := inferInstance
  incl := RingHom.id K
  roots := Fin.elim0
  roots_sq := fun i => Fin.elim0 i
  flips := Fin.elim0
  flips_base := fun i => Fin.elim0 i
  flips_roots := fun i => Fin.elim0 i
  square_descends b := by
    simp only [RingHom.id_apply, List.sublist_nil]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨[], rfl, c, by simpa using hc.symm⟩
    · rintro ⟨s, rfl, c, hc⟩
      exact ⟨c, by simpa using hc.symm⟩
  evaluate L _ f r _ := ⟨f, fun _ => rfl, fun i => Fin.elim0 i⟩

omit [CharZero K] in
theorem head_not_square {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) (m : RadicalModel ds) :
    ∀ z : m.Carrier, z ^ 2 ≠ m.incl a := by
  intro z hz
  obtain ⟨s, hs, c, hc⟩ := (m.square_descends a).mp ⟨z, hz⟩
  apply h (a :: s) (hs.cons_cons a) (List.cons_ne_nil _ _) (c * s.prod)
  simp only [List.prod_cons, hc]
  ring

omit [CharZero K] in
theorem head_ne_zero {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) : a ≠ 0 := by
  intro ha
  apply h [a] (List.nil_sublist ds |>.cons_cons a) (List.cons_ne_nil _ _) 0
  simp [ha]

omit [CharZero K] in
theorem extend_square_descends {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) (m : RadicalModel ds) (b : K) :
    (∃ z : QuadraticAlgebra m.Carrier (m.incl a) 0,
      z ^ 2 = algebraMap m.Carrier _ (m.incl b)) ↔
    ∃ s : List K, s.Sublist (a :: ds) ∧ ∃ c : K, b = c ^ 2 * s.prod := by
  rw [square_in_quadratic_iff]
  have ha := head_ne_zero h
  have hma : m.incl a ≠ 0 := (map_ne_zero m.incl).mpr ha
  constructor
  · rintro (hb | ⟨y, hy⟩)
    · obtain ⟨s, hs, c, hc⟩ := (m.square_descends b).mp hb
      exact ⟨s, hs.cons a, c, hc⟩
    · have hy' : y ^ 2 = m.incl (b / a) := by
        rw [map_div₀, eq_div_iff hma, mul_comm]
        exact hy
      obtain ⟨s, hs, c, hc⟩ := (m.square_descends (b / a)).mp ⟨y, hy'⟩
      refine ⟨a :: s, hs.cons_cons a, c, ?_⟩
      calc
        b = (b / a) * a := (div_mul_cancel₀ b ha).symm
        _ = c ^ 2 * (a :: s).prod := by rw [hc, List.prod_cons]; ring
  · rintro ⟨s, hs, c, hc⟩
    rcases List.sublist_cons_iff.mp hs with hs | ⟨r, rfl, hr⟩
    · exact Or.inl ((m.square_descends b).mpr ⟨s, hs, c, hc⟩)
    · obtain ⟨y, hy⟩ := (m.square_descends (c ^ 2 * r.prod)).mpr ⟨r, hr, c, rfl⟩
      refine Or.inr ⟨y, ?_⟩
      rw [hy, ← map_mul]
      congr 1
      rw [hc, List.prod_cons]
      ring

def extendModel {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) (m : RadicalModel ds) :
    RadicalModel (a :: ds) := by
  letI : Fact (∀ z : m.Carrier, z ^ 2 ≠ m.incl a + 0 * z) :=
    ⟨by simpa using head_not_square h m⟩
  let E := QuadraticAlgebra m.Carrier (m.incl a) 0
  let cast : m.Carrier →+* E := algebraMap m.Carrier E
  refine
    { Carrier := E
      field := inferInstance
      charZero := inferInstance
      incl := cast.comp m.incl
      roots := Fin.cases QuadraticAlgebra.omega (fun i => cast (m.roots i))
      roots_sq := ?_
      flips := Fin.cases (quadraticFlip (m.incl a))
        (fun i => quadraticLift (m.incl a) (m.flips i) (m.flips_base i a))
      flips_base := ?_
      flips_roots := ?_
      square_descends := extend_square_descends h m
      evaluate := ?_ }
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [cast, E, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap]
    · change cast (m.roots i) ^ 2 = cast (m.incl (ds.get i))
      simpa only [map_pow] using congrArg cast (m.roots_sq i)
  · intro i x
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [cast, E]
    · simp [cast, E, m.flips_base]
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp [cast, E, Fin.succ_ne_zero, eq_comm]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [cast, E, Fin.succ_ne_zero]
      · by_cases hij : i = j <;> simp [cast, E, m.flips_roots, hij]
  · intro L _ f r hr
    obtain ⟨φ, hφbase, hφroot⟩ := m.evaluate L f (fun i => r i.succ)
      (fun i => hr i.succ)
    have hr0 : r 0 ^ 2 = φ (m.incl a) := by
      rw [hφbase]
      exact hr 0
    refine ⟨quadraticEval (m.incl a) φ (r 0) hr0, ?_, ?_⟩
    · intro x
      simpa [cast, E] using hφbase x
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [E]
      · simpa [cast, E] using hφroot i

end Construction

end PlanarUnitDistances.Radicals

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Valuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

open WithZero Multiplicative

section RootValuation

open Polynomial IsDedekindDomain

variable {K : Type u} [Field K]

noncomputable def pointPrime (a : K) : HeightOneSpectrum K[X] where
  asIdeal := Ideal.span {X - C a}
  isPrime := by
    rw [Ideal.span_singleton_prime (X_sub_C_ne_zero a)]
    exact prime_X_sub_C a
  ne_bot := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero a

noncomputable def pointValuation (a : K) : Valuation (RatFunc K) ℤᵐ⁰ :=
  (pointPrime a).valuation (RatFunc K)

end RootValuation

section Plane

open Polynomial

variable {K : Type u} [Field K] [CharZero K]

noncomputable def planePrivateRoot (a b : K) : RatFunc K :=
  (RatFunc.C b * (RatFunc.X - RatFunc.C a) + 4) /
    (RatFunc.X - RatFunc.C a)

noncomputable def planeDistancePoly (a b : K) : (RatFunc K)[X] :=
  C (RatFunc.X - RatFunc.C a) * (X - C (RatFunc.C b))

noncomputable def planeRadicandPoly (a b : K) : (RatFunc K)[X] :=
  planeDistancePoly a b * (planeDistancePoly a b - 4)

end Plane

section GenericLine

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable {ι : Type*} {a : ι → K}

noncomputable def lineDistancePoly (e a : K) : K[X] := C e * (X - C a) ^ 2

noncomputable def lineRadicandPoly (e a : K) : K[X] :=
  lineDistancePoly e a * (lineDistancePoly e a - 4)

end GenericLine

section GenericCircle

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable [CharZero B] [CharZero K]
variable {ι : Type*} {a : ι → K}

noncomputable def circleNumerator (b a : K) : K[X] := -C b * (X - C a) ^ 2
noncomputable def circleDenominator (u a : K) : K[X] := (X - C u) * C (a - u)
noncomputable def circleDifference (b u a : K) : K[X] :=
  circleNumerator b a - 4 * circleDenominator u a
noncomputable def circleRadicandNumerator (b u a : K) : K[X] :=
  circleNumerator b a * circleDifference b u a

noncomputable def circleDistance (b u a : K) : RatFunc K :=
  algebraMap K[X] (RatFunc K) (circleNumerator b a) /
    algebraMap K[X] (RatFunc K) (circleDenominator u a)
noncomputable def circleRadicand (b u a : K) : RatFunc K :=
  circleDistance b u a * (circleDistance b u a - 4)

end GenericCircle
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.GenericCurve
open Polynomial
open scoped nonZeroDivisors
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

noncomputable def ratEval (z : U) (hz : Transcendental K z) : RatFunc K →ₐ[K] U :=
  IsFractionRing.liftAlgHom (transcendental_iff_injective.mp hz)

end PlanarUnitDistances.GenericCurve

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_GenericCurves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GenericNoncoincidence
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

noncomputable def poleTest (f : K[X][X]) (a b k : K) : K[X] :=
  (f.scaleRoots (X - C a)).eval (C b * (X - C a) + C k)

end PlanarUnitDistances.GenericNoncoincidence

namespace PlanarUnitDistances.BivariateMaps
open Polynomial
variable {B K L : Type*} [Field B] [Field K] [Field L]

noncomputable abbrev bimap (φ : B →+* K) : B[X][X] →+* K[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

end PlanarUnitDistances.BivariateMaps

namespace PlanarUnitDistances.CurveValuations

universe u
variable {K : Type u} [Field K]

open Polynomial

open scoped LaurentSeries nonZeroDivisors

noncomputable def shiftPowerSeries (a : K) : K[X] →+* PowerSeries K :=
  Polynomial.coeToPowerSeries.ringHom.comp (algEquivAevalXAddC a).toRingHom

lemma shiftPowerSeries_injective (a : K) : Function.Injective (shiftPowerSeries a) :=
  (Polynomial.coe_injective K).comp (algEquivAevalXAddC a).injective

@[simp] lemma shiftPowerSeries_C (a c : K) :
    shiftPowerSeries a (C c) = PowerSeries.C c := by
  simp [shiftPowerSeries, algEquivAevalXAddC_apply]

@[simp] lemma shiftPowerSeries_X (a : K) :
    shiftPowerSeries a X = PowerSeries.X + PowerSeries.C a := by
  simp [shiftPowerSeries, algEquivAevalXAddC_apply]

noncomputable def shiftLaurent (a : K) : K[X] →+* K⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ K).comp (shiftPowerSeries a)

lemma shiftLaurent_injective (a : K) : Function.Injective (shiftLaurent a) :=
  HahnSeries.ofPowerSeries_injective.comp (shiftPowerSeries_injective a)

lemma shiftLaurent_regular (a : K) :
    K[X]⁰ ≤ (K⸨X⸩)⁰.comap (shiftLaurent a) := by
  intro p hp
  change shiftLaurent a p ∈ (K⸨X⸩)⁰
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro he
  apply (mem_nonZeroDivisors_iff_ne_zero.mp hp)
  apply shiftLaurent_injective a
  simpa using he

noncomputable def shiftRatFunc (a : K) : RatFunc K →+* K⸨X⸩ :=
  RatFunc.liftRingHom (shiftLaurent a) (shiftLaurent_regular a)

@[simp] lemma shiftRatFunc_polynomial (a : K) (p : K[X]) :
    shiftRatFunc a (algebraMap K[X] (RatFunc K) p) = shiftLaurent a p :=
  RatFunc.liftRingHom_algebraMap _ _ _

abbrev CurveField (f : K[X][X]) := AdjoinRoot (f.map (algebraMap K[X] (RatFunc K)))

open WithZero Multiplicative

noncomputable def curveZ (f : K[X][X]) : CurveField f :=
  AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) X)

noncomputable def curveC (f : K[X][X]) (c : K) : CurveField f :=
  AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) (C c))

noncomputable def curveL (f : K[X][X]) (a c : K) : CurveField f :=
  (curveZ f - curveC f a) * (AdjoinRoot.root _ - curveC f c)

noncomputable def curveD (f : K[X][X]) (a c : K) : CurveField f :=
  curveL f a c * (curveL f a c - 4)

end PlanarUnitDistances.CurveValuations

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Derivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.BivariateDegree
open Polynomial
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

noncomputable def size (f : K[X][X]) : ℕ := f.natDegree+(Bivariate.swap f).natDegree

end PlanarUnitDistances.BivariateDegree

namespace UnitDistances.DerivationObstruction

open TensorProduct

section Etale
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]

noncomputable def extendDerivation (d : Derivation R S T) : Derivation R T T :=
  ((d.liftKaehlerDifferential.liftBaseChange T).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer
      (KaehlerDifferential.D R T)

@[simp] theorem extendDerivation_algebraMap (d : Derivation R S T) (s : S) :
    extendDerivation d (algebraMap S T s) = d s := by
  simp [extendDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]

end Etale

end UnitDistances.DerivationObstruction

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.CoefficientField
universe u
variable {B U : Type u} [Field B] [Field U] [Algebra B U]

abbrev FieldOf (y : Fin 4 × Fin 5 → U) :=
  algebraicClosure (IntermediateField.adjoin B (Set.range y)) U

noncomputable def entry (y : Fin 4 × Fin 5 → U) (i : Fin 4 × Fin 5) :
    FieldOf (B := B) y :=
  ⟨y i, by
    rw [mem_algebraicClosure_iff]
    let a : IntermediateField.adjoin B (Set.range y) :=
      ⟨y i,IntermediateField.subset_adjoin B _ ⟨i,rfl⟩⟩
    exact isAlgebraic_algebraMap a⟩

@[simp] theorem entry_val (y : Fin 4 × Fin 5 → U) (i : Fin 4 × Fin 5) :
    (entry (B := B) y i : U)=y i := rfl

variable {k : Type u} [Field k] [Algebra k U]

def parameters (D : Derivation k U U) (a b t : Fin 4 → U) : Fin 4 × Fin 5 → U :=
  fun ij => ![a ij.1,b ij.1,D (a ij.1),D (b ij.1),t ij.1] ij.2

@[simp] theorem parameters_zero (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,0)=a i := rfl
@[simp] theorem parameters_one (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,1)=b i := rfl
@[simp] theorem parameters_two (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,2)=D (a i) := rfl
@[simp] theorem parameters_three (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,3)=D (b i) := rfl
@[simp] theorem parameters_four (D : Derivation k U U) (a b t : Fin 4 → U) (i : Fin 4) :
    parameters D a b t (i,4)=t i := rfl
end PlanarUnitDistances.CoefficientField

namespace UnitDistances.UltraField
open Filter

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i, Field (K i)]

def zeroIdeal : Ideal (∀ i, K i) where
  carrier := {f | ∀ᶠ i in U, f i = 0}
  zero_mem' := Eventually.of_forall fun _ => rfl
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg] with i hi hj
    simp [hi, hj]
  smul_mem' := by
    intro f g hg
    filter_upwards [hg] with i hi
    simp [hi]

@[simp] theorem mem_zeroIdeal (f : ∀ i, K i) :
    f ∈ zeroIdeal U K ↔ ∀ᶠ i in U, f i = 0 := Iff.rfl

instance zeroIdeal_maximal : (zeroIdeal U K).IsMaximal := by
  rw [Ideal.isMaximal_iff]
  constructor
  · simpa using U.neBot.ne
  intro I f hle hf hfI
  have hn : ∀ᶠ i in U, f i ≠ 0 := Ultrafilter.eventually_not.mpr hf
  have hdiff : (1 - (fun i => (f i)⁻¹) * f) ∈ zeroIdeal U K := by
    filter_upwards [hn] with i hi
    simp [hi]
  have hinv : (fun i => (f i)⁻¹) * f ∈ I := I.mul_mem_left _ hfI
  simpa using I.add_mem (hle hdiff) hinv

abbrev FieldProduct := (∀ i, K i) ⧸ zeroIdeal U K

noncomputable instance instFieldFieldProduct : Field (FieldProduct U K) := Ideal.Quotient.field (zeroIdeal U K)

abbrev mk : (∀ i, K i) →+* FieldProduct U K := Ideal.Quotient.mk (zeroIdeal U K)

@[simp] theorem mk_eq_mk (f g : ∀ i, K i) : mk U K f = mk U K g ↔ ∀ᶠ i in U, f i = g i := by
  rw [Ideal.Quotient.eq]
  simp only [mem_zeroIdeal, Pi.sub_apply, sub_eq_zero]

@[simp] theorem mk_eq_zero (f : ∀ i, K i) : mk U K f = 0 ↔ ∀ᶠ i in U, f i = 0 := by
  rw [← (mk U K).map_zero, mk_eq_mk]
  rfl

instance instCharZeroFieldProduct [∀ i, CharZero (K i)] : CharZero (FieldProduct U K) := by
  constructor
  intro m n h
  have hh : mk U K (m : ∀ i, K i) = mk U K n := by simpa using h
  have he := (mk_eq_mk U K _ _).mp hh
  obtain ⟨i, hi⟩ := he.exists
  exact Nat.cast_injective hi

@[simp] theorem mk_inv (f : ∀ i, K i) : mk U K (fun i => (f i)⁻¹) = (mk U K f)⁻¹ := by
  by_cases h : mk U K f = 0
  · rw [h, inv_zero]
    apply (mk_eq_zero U K _).mpr
    filter_upwards [(mk_eq_zero U K _).mp h] with i hi
    simp [hi]
  · apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    change mk U K ((fun i => (f i)⁻¹) * f) = mk U K 1
    apply (mk_eq_mk U K _ _).mpr
    have hn := Ultrafilter.eventually_not.mpr (by simpa using h : ¬ ∀ᶠ i in U, f i = 0)
    filter_upwards [hn] with i hi
    simp [hi]

end UnitDistances.UltraField

namespace PlanarUnitDistances.UltraPolynomial
open Polynomial Filter
open UnitDistances.UltraField

noncomputable abbrev bimapping {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) :
    R[X][X] →+* S[X][X] := Polynomial.mapRingHom (Polynomial.mapRingHom φ)

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i,Field (K i)]

noncomputable def pack (f : ∀ i,(K i)[X][X]) (D : ℕ) : (∀ i,K i)[X][X] :=
  ∑ m ∈ Finset.range (D+1),monomial m
    (∑ n ∈ Finset.range (D+1),monomial n (fun i => ((f i).coeff m).coeff n))

end PlanarUnitDistances.UltraPolynomial

namespace PlanarUnitDistances.CountableCoefficients
open Polynomial
variable {U : Type*} [Field U]

noncomputable def field (f g : U[X][X]) : Subfield U :=
  Subfield.closure (Set.range (fun mn : ℕ × ℕ => (f.coeff mn.1).coeff mn.2) ∪
    Set.range (fun mn : ℕ × ℕ => (g.coeff mn.1).coeff mn.2))

instance instCountableSubtypeMemSubfieldField (f g : U[X][X]) : Countable (field f g) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply (Subfield.cardinalMk_closure_le_max _).trans
  apply max_le _ le_rfl
  exact Cardinal.le_aleph0_iff_set_countable.mpr
    ((Set.countable_range _).union (Set.countable_range _))

noncomputable def descend (B : Subfield U) (f : U[X][X])
    (h : ∀ m n, (f.coeff m).coeff n ∈ B) : B[X][X] :=
  ∑ m ∈ f.support, monomial m
    (∑ n ∈ (f.coeff m).support, monomial n ⟨(f.coeff m).coeff n,h m n⟩)

end PlanarUnitDistances.CountableCoefficients

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Loci
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LocusAvoidance
open Polynomial Filter PowerGrowth
attribute [local instance] Classical.propDecidable
variable {K α ι : Type*} [Field K]

noncomputable def zeros (S : Finset α) (z w : α → K) (f : K[X][X]) : Finset α :=
  S.filter fun a => f.eval₂ (evalRingHom (z a)) (w a)=0

end PlanarUnitDistances.LocusAvoidance

namespace PlanarUnitDistances.RealCurveSymmetry
open Polynomial Filter LocusAvoidance PowerGrowth
attribute [local instance] Classical.propDecidable

noncomputable def conjugate (f : ℂ[X][X]) : ℂ[X][X] :=
  f.map (Polynomial.mapRingHom (starRingEnd ℂ))

noncomputable def reflect (f : ℂ[X][X]) : ℂ[X][X] := Bivariate.swap (conjugate f)

end PlanarUnitDistances.RealCurveSymmetry

namespace PlanarUnitDistances.UltraCurve
open Polynomial Filter UnitDistances.UltraField UltraPolynomial
variable {ι : Type*} (U : Ultrafilter ι)
abbrev CU := FieldProduct U (fun _ => ℂ)

noncomputable def locus (f : ι → ℂ[X][X]) (D : ℕ) : (CU U)[X][X] :=
  bimapping (mk U (fun _ => ℂ)) (pack (fun _ => ℂ) f D)

end PlanarUnitDistances.UltraCurve

namespace PlanarUnitDistances.CirclePolynomial
open Polynomial
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

noncomputable def circle (u v : B) : B[X][X] :=
  (C X-C (C u))*(X-C (C v))-1

@[simp] lemma eval_circle (u v : B) (z w : K) :
    (circle u v).eval₂ (aeval z).toRingHom w=
      (z-algebraMap B K u)*(w-algebraMap B K v)-1 := by
  simp [circle]

end PlanarUnitDistances.CirclePolynomial

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_SmallHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UnitDistances.ExactHeightObstruction
open PlanarUnitDistances.WeightedAbsoluteValues
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
noncomputable abbrev height (x : K) : ℝ := exactHeight K x
omit [IsGalois ℚ K] in
lemma height_nonneg (x : K) : 0 ≤ height x := exactHeight_nonneg K x
omit [IsGalois ℚ K] in
@[simp] lemma height_zero : height (0 : K) = 0 := exactHeight_zero K
omit [IsGalois ℚ K] in
@[simp] lemma height_one : height (1 : K) = 0 := exactHeight_one K
omit [IsGalois ℚ K] in
@[simp] lemma height_neg (x : K) : height (-x) = height x := exactHeight_neg K x
@[simp] lemma height_inv (x : K) : height x⁻¹ = height x := exactHeight_inv K x
omit [IsGalois ℚ K] in
lemma height_mul_le (x y : K) : height (x*y) ≤ height x + height y := exactHeight_mul_le K x y
lemma height_add_le (x y : K) : height (x+y) ≤ Real.log 2 + height x + height y := exactHeight_add_le K x y
end UnitDistances.ExactHeightObstruction

namespace UnitDistances.ExactSmallHeightField
open Filter Asymptotics
open scoped BigOperators
open ExactHeightObstruction UltraField

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)] (J : ι → ℝ)

def Negligible (f : ∀ i, K i) : Prop :=
  (fun i => height (f i)) =o[(U : Filter ι)] J

variable {U K J}

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.zero : Negligible U K J 0 := by
  simp [Negligible]

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.one : Negligible U K J 1 := by
  simp [Negligible]

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.neg {f : ∀ i, K i} (hf : Negligible U K J f) :
    Negligible U K J (-f) := by simpa [Negligible] using hf

theorem Negligible.inv {f : ∀ i, K i} (hf : Negligible U K J f) :
    Negligible U K J (fun i => (f i)⁻¹) := by simpa [Negligible] using hf

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.mul {f g : ∀ i, K i} (hf : Negligible U K J f)
    (hg : Negligible U K J g) : Negligible U K J (f * g) := by
  have hb : (fun i => height ((f * g) i)) =O[(U : Filter ι)]
      (fun i => height (f i) + height (g i)) := by
    apply IsBigO.of_bound'
    apply Eventually.of_forall
    intro i
    simp only [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _),
      abs_of_nonneg (add_nonneg (height_nonneg _) (height_nonneg _))]
    exact height_mul_le _ _
  exact hb.trans_isLittleO (hf.add hg)

theorem Negligible.add (hJ : Tendsto J U atTop) {f g : ∀ i, K i}
    (hf : Negligible U K J f) (hg : Negligible U K J g) :
    Negligible U K J (f + g) := by
  have hb : (fun i => height ((f + g) i)) =O[(U : Filter ι)]
      (fun i => Real.log 2 + height (f i) + height (g i)) := by
    apply IsBigO.of_bound'
    apply Eventually.of_forall
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (add_nonneg (Real.log_nonneg (by norm_num))
        (height_nonneg _)) (height_nonneg _))]
    exact height_add_le _ _
  exact hb.trans_isLittleO (((isLittleO_const_id_atTop (Real.log 2)).comp_tendsto hJ).add hf |>.add hg)

noncomputable def constants (hJ : Tendsto J U atTop) : Subfield (FieldProduct U K) where
  carrier := {x | ∃ f, mk U K f = x ∧ Negligible U K J f}
  zero_mem' := ⟨0, map_zero _, Negligible.zero⟩
  one_mem' := ⟨1, map_one _, Negligible.one⟩
  add_mem' := by
    rintro x y ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f + g, map_add _ _ _, hf.add hJ hg⟩
  neg_mem' := by
    rintro x ⟨f, rfl, hf⟩
    exact ⟨-f, map_neg _ _, hf.neg⟩
  mul_mem' := by
    rintro x y ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
    exact ⟨f * g, map_mul _ _ _, hf.mul hg⟩
  inv_mem' := by
    rintro x ⟨f, rfl, hf⟩
    exact ⟨fun i => (f i)⁻¹, mk_inv U K f, hf.inv⟩

end UnitDistances.ExactSmallHeightField

namespace UnitDistances.UltraField
open Filter
variable {ι : Type*} (U : Ultrafilter ι) (K L : ι → Type*)
  [∀ i, Field (K i)] [∀ i, Field (L i)]

noncomputable def map (f : ∀ i, K i →+* L i) : FieldProduct U K →+* FieldProduct U L :=
  Ideal.Quotient.lift (zeroIdeal U K)
    ((mk U L).comp (RingHom.pi fun i => (f i).comp (Pi.evalRingHom K i))) (by
      intro x hx
      apply (mk_eq_zero U L _).mpr
      filter_upwards [hx] with i hi
      change f i (x i)=0
      rw [hi,map_zero])

@[simp] lemma map_mk (f : ∀ i, K i →+* L i) (x : ∀ i, K i) :
    map U K L f (mk U K x)=mk U L (fun i => f i (x i)) := rfl

end UnitDistances.UltraField

namespace PlanarUnitDistances.UltraHeightGrid
open Filter Asymptotics UnitDistances.UltraField UnitDistances.ExactSmallHeightField
open UnitDistances.ExactHeightObstruction
variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)]
  {J : ι → ℝ} (hJ : Tendsto J U atTop)

noncomputable def complexMap (e : ∀ i,K i →+* ℂ) :
    FieldProduct U K →+* FieldProduct U (fun _ => ℂ) := map U K (fun _ => ℂ) e

@[instance_reducible] noncomputable def complexAlgebra (e : ∀ i,K i →+* ℂ) :
    Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) :=
  ((complexMap U K e).comp (constants (K := K) hJ).subtype).toAlgebra

end PlanarUnitDistances.UltraHeightGrid

namespace PlanarUnitDistances.EdgeLabels
open Filter Asymptotics UnitDistances.UltraField UnitDistances.ExactSmallHeightField
open UnitDistances.ExactHeightObstruction UltraHeightGrid
variable (U : Ultrafilter ℕ) (K : ℕ → Type)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)]
  (J : ℕ → ℝ) (hJ : Tendsto J U atTop) (e : ∀ i,K i →+* ℂ)
variable [Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ))]
    (hcomm : ∀ r : constants (K := K) hJ,
      complexMap U K e r=algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r)
variable (ell : ∀ n,ℂ → ℂ → K n)

noncomputable def label (p r : ℕ → ℂ) : FieldProduct U (fun _ => ℂ) :=
  mk U (fun _ => ℂ) (fun n => e n (ell n (p n) (r n)))

end PlanarUnitDistances.EdgeLabels

namespace UnitDistances.GridCount
open scoped BigOperators
open Finset

def grids {α β : Type*} [Fintype α] [Fintype β] (E : α → β → Prop)
    [DecidableRel E] (N j : ℕ) : Finset ((Fin N → α) × (Fin j → β)) :=
  univ.filter fun pr => ∀ i l, E (pr.1 i) (pr.2 l)

end UnitDistances.GridCount

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

def Saving (F : Filter ι) (t f : ι → ℝ) (a : ℝ) : Prop :=
  ∃ b < a, Upper F t f b

end PlanarUnitDistances.PowerGrowth

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GenericGrid
open Filter Finset PowerGrowth
open UnitDistances.GridCount

variable {ι : Type*} {F : Filter ι} (t : ι → ℝ)
variable {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

noncomputable def edges (E : ∀ i, A i → B i → Prop) (i : ι) : Finset (A i × B i) := by
  classical
  exact univ.filter fun ab => E i ab.1 ab.2

end PlanarUnitDistances.GenericGrid

namespace UnitDistanceBlockAvoidance
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {F σ τ : Type*} [Field F]

universe u

abbrev BlockVars (σ : Type u) : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => BlockVars σ n ⊕ σ

abbrev BlockTuples (A : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => BlockTuples A n × A

instance blockTuplesFintype (A : Type*) [Fintype A] (n : ℕ) :
    Fintype (BlockTuples A n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact @instFintypeProd (BlockTuples A n) A ih inferInstance

def blockEval {A : Type*} (x : A → σ → F) :
    (n : ℕ) → BlockTuples A n → BlockVars σ n → F
  | 0, _ => PEmpty.elim
  | n + 1, u => Sum.elim (blockEval x n u.1) (x u.2)

def zeroCap (m a : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => zeroCap m a n * m + m ^ n * a

end UnitDistanceBlockAvoidance

namespace UnitDistanceBlockAvoidance
open MvPolynomial
open scoped BigOperators
variable {K A σ : Type*} [Field K] [Fintype A]

noncomputable def zeroSet (x : A → σ → K) (p : MvPolynomial σ K) : Finset A := by
  classical
  exact Finset.univ.filter fun i => eval (x i) p = 0

noncomputable def maxZeros (x : A → σ → K) (D : ℕ) : ℕ :=
  sSup {m | ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = m}

def tupleEquiv (A : Type*) : (n : ℕ) → BlockTuples A n ≃ (Fin n → A)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := fun u => by cases u; rfl
      right_inv := fun f => by funext i; exact Fin.elim0 i }
  | n+1 => (Equiv.prodCongr (tupleEquiv A n) (Equiv.refl A)).trans
      ((Equiv.prodComm _ _).trans (Fin.consEquiv fun _ : Fin (n+1) => A))

noncomputable def blockGrids {B : Type*} [Fintype B] (E : A → B → Prop) (N j : ℕ) :
    Finset (BlockTuples A N × BlockTuples B j) := by
  classical
  exact (UnitDistances.GridCount.grids E N j).map
    (Equiv.prodCongr (tupleEquiv A N) (tupleEquiv B j)).symm.toEmbedding

end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance
variable {ι : Type*} {F : Filter ι} {t : ι → ℝ}
variable {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable {K σ τ : Type*} [Field K]

def UniformBlocks (F : Filter ι) (t : ι → ℝ) {A : ι → Type*} [∀ i, Fintype (A i)]
    (x : ∀ i, A i → σ → K) : Prop :=
  ∀ D, Saving F t (fun i => maxZeros (x i) D) 1

end PlanarUnitDistances.GenericGrid

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance
variable {K σ τ : Type*} [Field K]
variable {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]

def optionalCoordinates (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K) (N j n : ℕ)
    (u : Option (BlockTuples (A n) N × BlockTuples (B n) j)) :
    (BlockVars σ N ⊕ BlockVars τ j) → K :=
  u.elim (fun _ => 0) (fun v => Sum.elim (blockEval (x n) N v.1) (blockEval (y n) j v.2))

end PlanarUnitDistances.GenericGrid

namespace UnitDistanceBlockAvoidance
instance blockVars_countable {σ : Type*} [Countable σ] (n : ℕ) : Countable (BlockVars σ n) := by
  induction n with
  | zero => exact inferInstanceAs (Countable PEmpty)
  | succ n ih => exact @instCountableSum (BlockVars σ n) σ ih inferInstance
end UnitDistanceBlockAvoidance

namespace UnitDistanceBlockAvoidance
variable {A σ F : Type*}

def varIndex (σ : Type*) : (n : ℕ) → Fin n × σ → BlockVars σ n
  | 0, ij => Fin.elim0 ij.1
  | n+1, ij => Fin.cases (Sum.inr ij.2) (fun j => Sum.inl (varIndex σ n (j,ij.2))) ij.1

end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {K σ τ L : Type*} [Field K] [Field L]
variable {A B : ℕ → Type*}

def leftCoords (x : ∀ n, A n → σ → K) (N j n : ℕ)
    (u : Option (BlockTuples (A n) N × BlockTuples (B n) j)) (is : Fin N × σ) : K :=
  match u with
  | none => 0
  | some v => x n (tupleEquiv (A n) N v.1 is.1) is.2

def rightCoords (y : ∀ n, B n → τ → K) (N j n : ℕ)
    (u : Option (BlockTuples (A n) N × BlockTuples (B n) j)) (is : Fin j × τ) : K :=
  match u with
  | none => 0
  | some v => y n (tupleEquiv (B n) j v.2 is.1) is.2

end PlanarUnitDistances.GenericGrid

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PolynomialBlocks
open MvPolynomial
open scoped BigOperators

noncomputable abbrev bivar {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :=
  (Polynomial.Bivariate.equivMvPolynomial K).symm p

end PlanarUnitDistances.PolynomialBlocks

namespace PlanarUnitDistances.FiniteGraphPruning
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def mass {α β : Type*} (w : α → β → ℝ) (P : Finset α) (Q : Finset β) : ℝ :=
  ∑ p ∈ P,∑ q ∈ Q,w p q

end PlanarUnitDistances.FiniteGraphPruning

namespace PlanarUnitDistances.DenseLoci
open Filter PowerGrowth FiniteGraphPruning LocusAvoidance Polynomial
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*}

variable {K : Type*} [Field K]

def Uniform (U : Ultrafilter ι) (t : ι → ℝ) (P : ι → Finset α) (z v : α → K) : Prop :=
  ∀ D : ℕ,∃ b : ℝ,0<b ∧ ∀ᶠ i in U,∀ f : K[X][X],f ≠ 0 → BivariateDegree.size f ≤ D →
    ((zeros (P i) z v f).card : ℝ) ≤ t i^(1-b)

def OnCurve (U : Ultrafilter ι) (P : ι → Finset α) (z v : α → K) : Prop :=
  ∃ D : ℕ,∃ f : ι → K[X][X],
    (∀ i,Irreducible (f i) ∧ BivariateDegree.size (f i) ≤ D) ∧
    ∀ᶠ i in U,∀ p ∈ P i,(f i).eval₂ (evalRingHom (z p)) (v p)=0

def Controlled (U : Ultrafilter ι) (t : ι → ℝ) (P : ι → Finset α) (z v : α → K) : Prop :=
  Uniform U t P z v ∨ OnCurve U P z v

end PlanarUnitDistances.DenseLoci

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Asymptotics Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth FiniteGraphPruning BivariateMaps

noncomputable def indicator (E : ℂ → ℂ → Prop) (a b : ℂ) : ℝ := by
  classical
  exact if E a b then 1 else 0

noncomputable abbrev z (U : Ultrafilter ℕ) (p : ℕ → ℂ) := mk U (fun _ => ℂ) p
noncomputable abbrev w (U : Ultrafilter ℕ) (p : ℕ → ℂ) :=
  mk U (fun _ => ℂ) (fun n => star (p n))

variable (U : Ultrafilter ℕ) (t J : ℕ → ℝ) (P : ℕ → Finset ℂ)
  (E : ℕ → ℂ → ℂ → Prop) (K : ℕ → Type)
  [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)

structure Hypotheses : Prop where
  nonzero : ∀ n,∀ p∈P n, ∀ r∈P n,E n p r → ell n p r≠0
  distance : ∀ n,∀ p∈P n, ∀ r∈P n,E n p r →
    (p-r)*(star p-star r)=2-e n (ell n p r)-(e n (ell n p r))⁻¹
  large : ∃ c : ℝ,0<c ∧ ∀ n,∀ p∈P n, ∀ r∈P n,E n p r → c*J n≤height (ell n p r)
  rectangle : ∃ b : ℕ → ℝ,b=o[(U : Filter ℕ)] J ∧
    ∀ n,∀ p∈P n, ∀ p'∈P n,∀ r∈P n,∀ r'∈P n,
      E n p r → E n p r' → E n p' r → E n p' r' →
      height (ell n p r*ell n p' r'/(ell n p r'*ell n p' r))≤b n
  no_circle : ∀ n,∀ p∈P n, ∀ r∈P n,E n p r → ∀ a : ℂ,
    t n^((9:ℝ)/10)≤((P n).filter (fun v => ‖v-a‖=1)).card →
    ¬(‖p-a‖=1 ∧ ‖r-a‖=1)

end PlanarUnitDistances.AlgebraicObstruction

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceDiagonal
open Filter Finset IncidenceSequence IncidenceScale IncidenceBook PowerGrowth
open scoped Classical
noncomputable section

def delta (n : ℕ) : ℝ := 1/(3*((n:ℝ)+1))

structure Data (s : Sequence) where
  f : ℕ → ℕ
  cofinal : Tendsto f atTop atTop
  a : ℕ → BudgetParameters.Params
  R : ∀n,Realization s (a n) (f n)
  J : ℕ → ℝ
  positive : ∀n,0<J n
  large : ∀n : ℕ,(n:ℝ)+1≤J n
  dense : ∀n,s.t (f n)^(2-1/((n:ℝ)+1))≤(IncidenceSelected.pairs (R n) (J n) (delta n)).card
  popular : ∀n,2≤IncidencePopular.k s (f n)

namespace Data
variable {s : Sequence} (D : Data s)
def t (n : ℕ) := s.t (D.f n)
def P (n : ℕ) := IncidencePopular.points s (D.f n)
def E (n : ℕ) := IncidenceComplex.edge (D.R n) (D.J n) (delta n)
def K (n : ℕ) : Type := (model s (D.f n)).field
instance instFieldK (n : ℕ) : Field (D.K n) := inferInstanceAs (Field (model s (D.f n)).field)
instance instNumberFieldK (n : ℕ) : NumberField (D.K n) := inferInstanceAs (NumberField (model s (D.f n)).field)
instance instIsGaloisRatK (n : ℕ) : IsGalois ℚ (D.K n) := inferInstanceAs (IsGalois ℚ (model s (D.f n)).field)
def e (n : ℕ) : D.K n →+* ℂ := (model s (D.f n)).field.val.toRingHom
def ell (n : ℕ) : ℂ → ℂ → D.K n := IncidenceComplex.label (D.R n) (D.J n) (delta n)
end Data
end
end PlanarUnitDistances.IncidenceDiagonal

end OAI
end


