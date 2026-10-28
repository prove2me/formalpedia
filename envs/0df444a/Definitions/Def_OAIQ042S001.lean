-- Prove2me | Definitions.Def_OAIQ042S001
-- name    : OAIQ042S001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:29:41.741399+00:00
-- url     : https://prove2.me/theorems/943bb773-7a45-4389-bf91-53255d86917a
-- title:
--   Definitions bundle OAIQ042S001 of the split of OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CriticalStrip.critical_strip_mass`, carved from OpenAI's openai/math development (OpenAI, *Critical strip-crossing mass on the honeycomb lattice (result family 237)*, OpenAI Math Release, September 26, 2026, result family 237, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 723 declarations of OpenAI's Lean: 352 definitions, 7 inductive types or structures, 14 instances and 350 theorems. The definitions and types are `OAI.CriticalStrip.Diagram.ArchRootIndex`, `OAI.CriticalStrip.Diagram.ArchShiftIndex`, `OAI.CriticalStrip.Diagram.BoundaryInsert.fresh`, `OAI.CriticalStrip.Diagram.BoundaryInsert.old`, `OAI.CriticalStrip.Diagram.BoundaryInsert.unionGraph`, `OAI.CriticalStrip.Diagram.BoundarySew.graph`, `OAI.CriticalStrip.Diagram.BoundarySew.project`, `OAI.CriticalStrip.Diagram.CompactGate.boundary`, `OAI.CriticalStrip.Diagram.CompactGate.core`, `OAI.CriticalStrip.Diagram.CompactGate.localEnd`, `OAI.CriticalStrip.Diagram.CompactGate.project`, `OAI.CriticalStrip.Diagram.ConnectivityCertificate`, `OAI.CriticalStrip.Diagram.CutPatch.boundary`, `OAI.CriticalStrip.Diagram.CutPatch.boundaryAdj`, `OAI.CriticalStrip.Diagram.CutPatch.boundarySupport`, `OAI.CriticalStrip.Diagram.FixedZero`, `OAI.CriticalStrip.Diagram.FreshGate.Ports`, `OAI.CriticalStrip.Diagram.FreshGate.Ports.boundary`, `OAI.CriticalStrip.Diagram.FreshGate.Ports.core`, `OAI.CriticalStrip.Diagram.FreshGate.Ports.project`, `OAI.CriticalStrip.Diagram.GateExterior`, `OAI.CriticalStrip.Diagram.Graph.Attached.contraction`, `OAI.CriticalStrip.Diagram.Graph.Attached.project`, `OAI.CriticalStrip.Diagram.Graph.Attached.wiring`, `OAI.CriticalStrip.Diagram.Graph.BoundaryEquiv`, `OAI.CriticalStrip.Diagram.Graph.BoundaryEquiv.ofEquiv`, `OAI.CriticalStrip.Diagram.Graph.BoundaryEquiv.symm`, `OAI.CriticalStrip.Diagram.Graph.DrainsBoundary`, `OAI.CriticalStrip.Diagram.Graph.Used`, `OAI.CriticalStrip.Diagram.Graph.WireContraction`, `OAI.CriticalStrip.Diagram.Graph.boundaryConstant`, `OAI.CriticalStrip.Diagram.LaurentInterval`, `OAI.CriticalStrip.Diagram.Pairing.arcTurn`, `OAI.CriticalStrip.Diagram.Pairing.gateBoundary`, `OAI.CriticalStrip.Diagram.Pairing.gateTurn`, `OAI.CriticalStrip.Diagram.Pairing.turnOrder`, `OAI.CriticalStrip.Diagram.PartialColumn.position`, `OAI.CriticalStrip.Diagram.PartialColumn.prev`, `OAI.CriticalStrip.Diagram.PartialColumn.rowPosition`, `OAI.CriticalStrip.Diagram.PartialColumn.rowTriple` and 319 more.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/StripMass, in whole or in part: `StripMass_ArchRoots`, `StripMass_AugmentedTail`, `StripMass_Basic`, `StripMass_BlockPfaffian`, `StripMass_BottomPadding`, `StripMass_BoundaryTree`, `StripMass_CauchyMatrices`, `StripMass_CollisionLeaf`, `StripMass_CollisionSubstitutions`, `StripMass_ColumnGeometry`, `StripMass_ColumnSweep`, `StripMass_CoordinateBoxes`, `StripMass_CutPatch`, `StripMass_CutStateSound`, `StripMass_DeficitBounds`, `StripMass_DensityExhaustion`, `StripMass_DiagonalFactors`, `StripMass_FiniteEnds`, `StripMass_FirstFlatSpecialization`, `StripMass_FluxWindow`, `StripMass_FreshGate`, `StripMass_HoneycombClip`, `StripMass_HoneycombTiles`, `StripMass_InterpolantCovariance`, `StripMass_InverseIntegrability`, `StripMass_InverseMoments`, `StripMass_LaguerreNormalization`, `StripMass_LaguerreScaling`, `StripMass_LaguerreTails`, `StripMass_LaurentBox`, `StripMass_LaurentNumerator`, `StripMass_LocalPadding`, `StripMass_MirrorExterior`, `StripMass_MomentGrowth`, `StripMass_NodalEmpty`, `StripMass_NodalExchange`, `StripMass_NodalNodes`, `StripMass_NodalRegularity`, `StripMass_NodalScalarDeletion`, `StripMass_NodalTorusValue`, `StripMass_PairCoordinates`, `StripMass_PairSelfNode`, `StripMass_PatchReplacement`, `StripMass_PfaffianConfluentLimit`, `StripMass_PfaffianEvaluation`, `StripMass_PfaffianIntegration`, `StripMass_PfaffianMatrices`, `StripMass_PfaffianRecursion`, `StripMass_PhaseAlgebra`, `StripMass_PhysicalPorts`, `StripMass_PolynomialDegrees`, `StripMass_PositiveAssociation`, `StripMass_QuarterMoments`, `StripMass_QuarticIntegrals`, `StripMass_RealEvaluation`, `StripMass_ResidualEvaluation`, `StripMass_ResidualParityCoefficients`, `StripMass_RibbonGlobal`, `StripMass_RibbonLocal`, `StripMass_RibbonWalk`, `StripMass_RootOfUnityPowers`, `StripMass_ScalarDegree`, `StripMass_ScalarDeleteContinuation`, `StripMass_ScalarMergeTrig`, `StripMass_SchurIdentity`, `StripMass_SewnAssignment`, `StripMass_Specialization`, `StripMass_SpecializationPolynomial`, `StripMass_SpectralComponents`, `StripMass_SplitGluing`, `StripMass_StepComplete`, `StripMass_StepToCut`, `StripMass_StieltjesLimits`, `StripMass_SwapVacancy`, `StripMass_TailIntegrals`, `StripMass_ThreeBoxProfiles`, `StripMass_ThreeBoxSplitPolynomial`, `StripMass_ThreeBoxWeights`, `StripMass_Trigonometry`, `StripMass_TripleCircuit`, `StripMass_TriplePatch`, `StripMass_TurnDisk`, `StripMass_TurnEvolution`, `StripMass_TurnGate`, `StripMass_TurnRectangleMatching`, `StripMass_TurnRhombus`, `StripMass_TurnWideGate`, `StripMass_WeightComparison`, `StripMass_WireContraction`.
--
--   **Imports.** It imports the published bundle `Def_CriticalStripMass`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ042S002`, `OAIQ042S003` and `OAIQ042S004`; the statements `OAI.CriticalStrip.HoneycombBranch.step_turn`, `OAI.CriticalStrip.HoneycombBranch.strip_turn`, `OAI.CriticalStrip.laguerre_inverseQuarterSum_upper` and `OAI.CriticalStrip.laguerre_least_inverseQuarter_lower`; the proofs of `OAI.CriticalStrip.laguerre_inverseQuarterSum_upper` and `OAI.CriticalStrip.laguerre_least_inverseQuarter_lower`.
-- source:
--   OpenAI, Critical strip-crossing mass on the honeycomb lattice (result family 237), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 237; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-strip-crossing-mass-on-the-honeycomb-lattice-September-26-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/StripMass at commit adc7f12

import Mathlib
import Definitions.Def_CriticalStripMass

section
-- module Solutions.OAIQ042_SS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
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
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory


def homogeneousQ (N : ℕ) (g : Polynomial ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C C) ^ (2 * N + 1) *
    (Polynomial.X - Polynomial.C c) ^ N * g

def harmonicCoordinate : Polynomial ℝ := Polynomial.X ^ 2 * (1 - Polynomial.X ^ 2)

def HasProjection (N : ℕ) (Q : Polynomial ℝ) : Prop :=
  ∃ P J E : Polynomial ℝ,
    P.natDegree ≤ N ∧ J.natDegree ≤ N ∧ E.degree < (N : WithBot ℕ) ∧
    Q = P.comp harmonicCoordinate + Polynomial.X * J.comp harmonicCoordinate +
      Polynomial.X ^ 2 * E.comp harmonicCoordinate

def MonicProblem (N : ℕ) (g : Polynomial ℝ) : Prop :=
  g.Monic ∧ g.natDegree = N ∧ HasProjection N (homogeneousQ N g)


def pairKernel (x y : ℝ) : ℝ := (y - x) ^ 2 / (y + x)

def orderedDomain (N : ℕ) : Set (Fin N → ℝ) :=
  {y | StrictMono y ∧ ∀ i, y i ∈ Ioo 0 1}

def reflectionProduct (N : ℕ) (x : ℝ) (y : Fin N → ℝ) : ℝ :=
  ∏ i, (y i - x) / (y i + x)


def inverseHalfSum (N : ℕ) (y : Fin N → ℝ) : ℝ := ∑ i, (y i) ^ (-(1 / 2 : ℝ))

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

abbrev Vec (n : ℕ) := Fin n → ℂ
abbrev Grassmann (n : ℕ) := ExteriorAlgebra ℂ (Vec n)

def standardBasis (n : ℕ) : Module.Basis (Fin n) ℂ (Vec n) := Pi.basisFun ℂ (Fin n)
def generator (n : ℕ) (i : Fin n) : Grassmann n :=
  ExteriorAlgebra.ι ℂ (standardBasis n i)
def twoForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Grassmann n :=
  ∑ i, ∑ j ∈ Finset.Ioi i, A i j • (generator n i * generator n j)
def pfaffian (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ((standardBasis n).ExteriorAlgebra.repr ((twoForm A) ^ (n / 2))) Finset.univ /
    (Nat.factorial (n / 2) : ℂ)

def d : ℂ := (Real.cos (2 * (Real.pi / 8)) : ℝ)
def rho : ℂ := (1 / Real.sqrt (2 + Real.sqrt 2) : ℝ)
def D (a b : ℂ) : ℂ := a ^ 2 + b ^ 2 + 2 * d * a * b - d ^ 2
def kernel (a b : ℂ) : ℂ := (a - b) * (a + b + rho) / D a b

def pfSize (N : ℕ) : ℕ := 2 * ((N + 1) / 2)
def augmentedKernel (N : ℕ) (a : Fin N → ℂ) : Matrix (Fin (pfSize N)) (Fin (pfSize N)) ℂ :=
  fun i j => if hi : i.val < N then
    if hj : j.val < N then kernel (a ⟨i.val, hi⟩) (a ⟨j.val, hj⟩) else 1
    else if j.val < N then -1 else 0

def p (N : ℕ) (a : Fin N → ℂ) : ℂ :=
  (∏ i, ∏ j ∈ Finset.Ioi i, D (a i) (a j) / (a i - a j)) *
    pfaffian (pfSize N) (augmentedKernel N a)



def topWedge (n : ℕ) : Grassmann n := ExteriorAlgebra.ιMulti ℂ n (standardBasis n)
def topCoord (n : ℕ) : Grassmann n →ₗ[ℂ] ℂ :=
  (standardBasis n).ExteriorAlgebra.coord Finset.univ

def permMap (n : ℕ) (σ : Equiv.Perm (Fin n)) : Vec n →ₗ[ℂ] Vec n :=
  (standardBasis n).constr ℂ (fun i => standardBasis n (σ i))

@[simp] lemma permMap_basis (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permMap n σ (standardBasis n i) = standardBasis n (σ i) := by
  simp [permMap]

@[simp] lemma permMap_generator (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ExteriorAlgebra.map (permMap n σ) (generator n i) = generator n (σ i) := by
  simp [generator]

def embedMap (n : ℕ) : Vec n →ₗ[ℂ] Vec (n + 1) :=
  (standardBasis n).constr ℂ (fun i => standardBasis (n + 1) i.castSucc)

@[simp] lemma embedMap_basis (n : ℕ) (i : Fin n) :
    embedMap n (standardBasis n i) = standardBasis (n + 1) i.castSucc := by
  simp [embedMap]

@[simp] lemma embedMap_generator (n : ℕ) (i : Fin n) :
    ExteriorAlgebra.map (embedMap n) (generator n i) = generator (n + 1) i.castSucc := by
  simp [generator]

def border {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun i j => Fin.lastCases (Fin.lastCases 0 (fun j => -u j) j)
    (fun i => Fin.lastCases (u i) (fun j => A i j) j) i

@[simp] lemma border_old_old {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) (i j : Fin n) :
    border A u i.castSucc j.castSucc = A i j := by simp [border]
@[simp] lemma border_old_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) (i : Fin n) :
    border A u i.castSucc (Fin.last n) = u i := by simp [border]
@[simp] lemma border_last_old {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) (i : Fin n) :
    border A u (Fin.last n) i.castSucc = -u i := by simp [border]
@[simp] lemma border_last_last {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Vec n) :
    border A u (Fin.last n) (Fin.last n) = 0 := by simp [border]

def borderLinear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Vec n →ₗ[ℂ] ℂ where
  toFun u := topCoord (n + 1) (ExteriorAlgebra.map (embedMap n) (twoForm A) ^ (n / 2) *
    (ExteriorAlgebra.ι ℂ (embedMap n u) * generator (n + 1) (Fin.last n))) / (n / 2).factorial
  map_add' u v := by simp [mul_add, add_mul, add_div]
  map_smul' t u := by simp [smul_eq_mul, mul_div_assoc]

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BottomPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open Finset


theorem det_one_sub_zero_rows {𝕜 α β : Type*} [CommRing 𝕜]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) 𝕜)
    (h : ∀ i j, M (.inr i) j = 0) :
    (1-M).det = (1-M.toBlocks₁₁).det := by
  have hm : 1-M = Matrix.fromBlocks (1-M.toBlocks₁₁) (-M.toBlocks₁₂) 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, h]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

 
theorem det_one_sub_zero_cols {𝕜 α β : Type*} [CommRing 𝕜]
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) 𝕜)
    (h : ∀ i j, M i (.inr j) = 0) :
    (1-M).det = (1-M.toBlocks₁₁).det := by
  have hm : 1-M = Matrix.fromBlocks (1-M.toBlocks₁₁) 0 (-M.toBlocks₂₁) 1 := by
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, h]
  rw [hm, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DiagonalFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram







noncomputable section
open scoped LaurentPolynomial Classical

variable {K : Type*} [Field K]

def LaurentInterval (f : LaurentPolynomial K) (a b : ℤ) : Prop :=
  ∀ e, f.coeff e ≠ 0 → a ≤ e ∧ e ≤ b

lemma laurent_trunc_coeff (f : LaurentPolynomial K) (k : ℕ) :
    (LaurentPolynomial.trunc f).coeff k=f.coeff (k:ℤ) := rfl

lemma laurent_toLaurent_coeff (p : Polynomial K) (k : ℕ) :
    p.toLaurent.coeff (k:ℤ)=p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.cast_injective p.toFinsupp.coeff k

lemma laurent_toLaurent_negative (p : Polynomial K) (e : ℤ) (he : e<0) :
    p.toLaurent.coeff e=0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n,hn⟩
  have : (0:ℤ)≤n := Int.natCast_nonneg _
  change (n:ℤ)=e at hn
  omega

lemma laurent_toLaurent_trunc (f : LaurentPolynomial K)
    (h : ∀ e,e<0 → f.coeff e=0) :
    (LaurentPolynomial.trunc f).toLaurent=f := by
  ext e
  by_cases he:0≤e
  · lift e to ℕ using he
    rw [laurent_toLaurent_coeff,laurent_trunc_coeff]
  · rw [laurent_toLaurent_negative _ _ (by omega),h _ (by omega)]

lemma laurent_shift_coeff (f : LaurentPolynomial K) (a e : ℤ) :
    (f*LaurentPolynomial.T a).coeff e=f.coeff (e-a) := by
  simp only [LaurentPolynomial.T,AddMonoidAlgebra.coeff_mul_single_apply,mul_one]
  rfl

lemma LaurentInterval.shift {f : LaurentPolynomial K} {a b : ℤ}
    (h : LaurentInterval f a b) (c : ℤ) :
    LaurentInterval (f*LaurentPolynomial.T c) (a+c) (b+c) := by
  intro e he
  rw [laurent_shift_coeff] at he
  have := h (e-c) he
  omega

lemma LaurentInterval.shift_trunc {f : LaurentPolynomial K} {m : ℕ} {b : ℤ}
    (h : LaurentInterval f (-(m:ℤ)) b) :
    (LaurentPolynomial.trunc (f*LaurentPolynomial.T m)).toLaurent=
      f*LaurentPolynomial.T m := by
  apply laurent_toLaurent_trunc
  intro e he
  by_contra hh
  have := h.shift m e hh
  omega

 

theorem laurent_root_saturation (f : LaurentPolynomial K) (m : ℕ)
    (hb : LaurentInterval f (-(m:ℤ)) m) (htop : f.coeff (m:ℤ)=0)
    (s : Finset K) (hc : s.card=2*m) (hz : ∀ z∈s,z≠0)
    (he : ∀ z (h:z∈s),
      LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z h)) f=0) : f=0 := by
  let p := LaurentPolynomial.trunc (f*LaurentPolynomial.T m)
  have hp : p.degree<(2*m:ℕ) := by
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [laurent_trunc_coeff,laurent_shift_coeff]
    by_cases hh:k=2*m
    · subst k
      convert htop using 2
      all_goals try with_reducible_and_instances rfl
      push_cast
      ring
    · by_contra hn
      have := hb ((k:ℤ)-m) hn
      omega
  have hev (z : K) (hs:z∈s) : p.eval z=0 := by
    have h:=congrArg (LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs)))
      hb.shift_trunc
    rw [LaurentPolynomial.eval₂_toLaurent] at h
    change p.eval z = _ at h
    rw [(LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs))).map_mul,
      he z hs,zero_mul] at h
    exact h
  have hp0 : p=0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
    · simpa [hc] using hp
    · exact hev
  have hh:=hb.shift_trunc
  change p.toLaurent=_ at hh
  rw [hp0,map_zero] at hh
  have hunit:=LaurentPolynomial.isUnit_T (R:=K) (m:ℤ)
  exact (hunit.mul_left_eq_zero.mp hh.symm)

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped LaurentPolynomial Classical

variable {K : Type*} [Field K]

lemma laurent_mul_top_coeff (f g : LaurentPolynomial K) (a b : ℤ)
    (hf : ∀ e,f.coeff e≠0 → e≤a) (hg : ∀ e,g.coeff e≠0 → e≤b) :
    (f*g).coeff (a+b)=f.coeff a*g.coeff b := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ e ∈ f.coeff.support, f.coeff e*g.coeff (-e+(a+b)))=_
  rw [Finset.sum_eq_single a]
  · congr 1
    congr 1
    ring
  · intro e he hea
    have hle:=hf e (Finsupp.mem_support_iff.mp he)
    have hz:g.coeff (-e+(a+b))=0 := by
      by_contra hh
      have := hg _ hh
      omega
    rw [hz,mul_zero]
  · intro ha
    rw [Finsupp.notMem_support_iff.mp ha,zero_mul]

lemma laurent_mul_bottom_coeff (f g : LaurentPolynomial K) (a b : ℤ)
    (hf : ∀ e,f.coeff e≠0 → a≤e) (hg : ∀ e,g.coeff e≠0 → b≤e) :
    (f*g).coeff (a+b)=f.coeff a*g.coeff b := by
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  change (∑ e ∈ f.coeff.support, f.coeff e*g.coeff (-e+(a+b)))=_
  rw [Finset.sum_eq_single a]
  · congr 1
    congr 1
    ring
  · intro e he hea
    have hle:=hf e (Finsupp.mem_support_iff.mp he)
    have hz:g.coeff (-e+(a+b))=0 := by
      by_contra hh
      have := hg _ hh
      omega
    rw [hz,mul_zero]
  · intro ha
    rw [Finsupp.notMem_support_iff.mp ha,zero_mul]

 

theorem LaurentInterval.quotient {f g : LaurentPolynomial K} {a b c d : ℤ}
    (h : LaurentInterval (f*g) a b) (hg : LaurentInterval g c d)
    (hc : g.coeff c≠0) (hd : g.coeff d≠0) : LaurentInterval f (a-c) (b-d) := by
  intro e he
  have hs : f.coeff.support.Nonempty := ⟨e,Finsupp.mem_support_iff.mpr he⟩
  let lo:=f.coeff.support.min' hs
  let hi:=f.coeff.support.max' hs
  have hlo : f.coeff lo≠0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ hs)
  have hhi : f.coeff hi≠0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ hs)
  have hlow (k : ℤ) (hk:f.coeff k≠0) : lo≤k :=
    Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hk)
  have hhigh (k : ℤ) (hk:f.coeff k≠0) : k≤hi :=
    Finset.le_max' _ _ (Finsupp.mem_support_iff.mpr hk)
  have hl : (f*g).coeff (lo+c)≠0 := by
    rw [laurent_mul_bottom_coeff f g lo c hlow (fun k hk => (hg k hk).1)]
    exact mul_ne_zero hlo hc
  have hh : (f*g).coeff (hi+d)≠0 := by
    rw [laurent_mul_top_coeff f g hi d hhigh (fun k hk => (hg k hk).2)]
    exact mul_ne_zero hhi hd
  have h₁ := (h (lo+c) hl).1
  have h₂ := (h (hi+d) hh).2
  have h₃ := hlow e he
  have h₄ := hhigh e he
  omega

end





noncomputable section
open scoped LaurentPolynomial Classical

 

lemma laurent_linear_dvd {R : Type*} [CommRing R] (f : LaurentPolynomial R) (u : Rˣ)
    (h : LaurentPolynomial.eval₂ (RingHom.id R) u f=0) :
    LaurentPolynomial.T 1-LaurentPolynomial.C (u:R) ∣ f := by
  obtain ⟨m,p,hp⟩:=LaurentPolynomial.exists_T_pow f
  have he:p.eval (u:R)=0 := by
    have hh:=congrArg (LaurentPolynomial.eval₂ (RingHom.id R) u) hp
    rw [LaurentPolynomial.eval₂_toLaurent,map_mul,h,zero_mul] at hh
    exact hh
  obtain ⟨q,hq⟩:=Polynomial.dvd_iff_isRoot.mpr he
  refine ⟨q.toLaurent*LaurentPolynomial.T (-(m:ℤ)),?_⟩
  have hh:=congrArg (fun g : LaurentPolynomial R => g*LaurentPolynomial.T (-(m:ℤ))) hp
  rw [hq,map_mul,map_sub,Polynomial.toLaurent_X,Polynomial.toLaurent_C] at hh
  simpa only [mul_assoc,←LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,mul_one]
    using hh.symm

lemma laurent_eval_linear {R : Type*} [CommRing R] (u v : Rˣ) :
    LaurentPolynomial.eval₂ (RingHom.id R) u
      (LaurentPolynomial.T 1-LaurentPolynomial.C (v:R))=(u:R)-(v:R) := by
  simp [LaurentPolynomial.eval₂_T,LaurentPolynomial.eval₂_C]

 

lemma laurent_prod_linear_dvd {R : Type*} [CommRing R] [IsDomain R]
    (f : LaurentPolynomial R) (s : Finset Rˣ)
    (h : ∀ u∈s,LaurentPolynomial.eval₂ (RingHom.id R) u f=0) :
    (∏ u∈s,(LaurentPolynomial.T 1-LaurentPolynomial.C (u:R))) ∣ f := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert a s ha ih =>
    obtain ⟨g,hg⟩:=laurent_linear_dvd f a (h a (Finset.mem_insert_self a s))
    have hs (u : Rˣ) (hu:u∈s) : LaurentPolynomial.eval₂ (RingHom.id R) u g=0 := by
      have hh:=h u (Finset.mem_insert_of_mem hu)
      rw [hg,map_mul,laurent_eval_linear] at hh
      apply (mul_eq_zero.mp hh).resolve_left
      apply sub_ne_zero.mpr
      intro e
      have eu:u=a := Units.ext e
      exact ha (eu ▸ hu)
    obtain ⟨q,hq⟩:=ih g hs
    rw [Finset.prod_insert ha]
    refine ⟨q,?_⟩
    rw [hg,hq,mul_assoc]

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

 

theorem prod_dvd_of_evaluation_packets {R K ι κ : Type*}
    [CommRing R] [CommRing K] [IsDomain K]
    (s : Finset ι) (D : ι → R) (φ : ι → κ → R →+* K)
    (hker : ∀ i∈s, ∀ f:R, (∀ k,φ i k f=0) → D i ∣ f)
    (hcross : ∀ i∈s, ∀ j∈s, i≠j → ∀ k,φ i k (D j)≠0)
    (f : R) (hf : ∀ i∈s, ∀ k,φ i k f=0) : (∏ i∈s,D i) ∣ f := by
  induction s using Finset.induction_on generalizing f with
  | empty => simp
  | @insert i s hi ih =>
    obtain ⟨g,hg⟩:=hker i (Finset.mem_insert_self _ _) f (hf i (Finset.mem_insert_self _ _))
    have hsg (j : ι) (hj:j∈s) (k : κ) : φ j k g=0 := by
      have hh:=hf j (Finset.mem_insert_of_mem hj) k
      rw [hg,map_mul] at hh
      apply (mul_eq_zero.mp hh).resolve_left
      exact hcross j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
        (fun he => hi (he ▸ hj)) k
    obtain ⟨q,hq⟩:=ih (fun j hj => hker j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      g hsg
    refine ⟨q,?_⟩
    rw [Finset.prod_insert hi,hg,hq,mul_assoc]

lemma laurent_prod_linear_indexed_dvd {R ι : Type*} [CommRing R] [IsDomain R]
    [Fintype ι] (u : ι → Rˣ) (hu : Function.Injective u)
    (f : LaurentPolynomial R) (h : ∀ i,LaurentPolynomial.eval₂ (RingHom.id R) (u i) f=0) :
    (∏ i,(LaurentPolynomial.T 1-LaurentPolynomial.C ((u i):R))) ∣ f := by
  have hh:=laurent_prod_linear_dvd f (Finset.univ.image u) (by
    intro v hv
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hv
    exact h i)
  simpa only [Finset.prod_image (fun i _ j _ hij => hu hij)] using hh

end

 

 

noncomputable section
open scoped LaurentPolynomial Classical


def cosineCollisionRoots {R : Type*} [CommRing R] (a u : Rˣ) : Fin 4 → Rˣ :=
  ![u,-u,a⁻¹*u⁻¹,-(a⁻¹*u⁻¹)]

def cosineCollisionPacket {R : Type*} [CommRing R] (a u : Rˣ) : LaurentPolynomial R :=
  LaurentPolynomial.C (a:R)*LaurentPolynomial.T 2+
    LaurentPolynomial.C ((a⁻¹:Rˣ):R)*LaurentPolynomial.T (-2)-
    LaurentPolynomial.C ((a:R)*(u:R)^2+((a⁻¹:Rˣ):R)*((u⁻¹:Rˣ):R)^2)

lemma cosineCollision_factorization {R : Type*} [CommRing R] (a u : Rˣ) :
    (∏ k:Fin 4, (LaurentPolynomial.T 1-LaurentPolynomial.C ((cosineCollisionRoots a u k):R)))=
      (LaurentPolynomial.C ((a⁻¹:Rˣ):R)*LaurentPolynomial.T 2)*cosineCollisionPacket a u := by
  simp only [cosineCollisionRoots,Fin.prod_univ_succ,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one,Units.val_neg,Units.val_mul,
    map_neg,map_mul,cosineCollisionPacket,map_add,map_pow]
  have h2 : (LaurentPolynomial.T (1:ℤ) : LaurentPolynomial R)^2=LaurentPolynomial.T 2 := by
    rw [pow_two,←LaurentPolynomial.T_add]; rfl
  have h4 : (LaurentPolynomial.T (1:ℤ) : LaurentPolynomial R)^4=LaurentPolynomial.T 2*LaurentPolynomial.T 2 := by
    rw [←h2]; ring
  have haa : LaurentPolynomial.C ((a⁻¹:Rˣ):R)*LaurentPolynomial.C (a:R)=1 := by
    rw [←map_mul]; simp
  have huu : LaurentPolynomial.C ((u⁻¹:Rˣ):R)*LaurentPolynomial.C (u:R)=1 := by
    rw [←map_mul]; simp
  have hT : (LaurentPolynomial.T (2:ℤ) : LaurentPolynomial R)*LaurentPolynomial.T (-2)=1 := by
    rw [←LaurentPolynomial.T_add]; rfl
  linear_combination
    ((LaurentPolynomial.T 1)^2+LaurentPolynomial.T 2)*h2 +
    (LaurentPolynomial.C (u:R)^2+LaurentPolynomial.C ((a⁻¹:Rˣ):R)^2*LaurentPolynomial.C ((u⁻¹:Rˣ):R)^2)*(-h2) -
    (LaurentPolynomial.T 2)^2*haa +
    (LaurentPolynomial.C (u:R)^2*LaurentPolynomial.T 2)*haa +
    LaurentPolynomial.C ((a⁻¹:Rˣ):R)^2*((LaurentPolynomial.C ((u⁻¹:Rˣ):R)*LaurentPolynomial.C (u:R)+1)*huu-hT)

lemma cosineCollisionPacket_dvd {R : Type*} [CommRing R] [IsDomain R]
    (a u : Rˣ) (hi:Function.Injective (cosineCollisionRoots a u)) (f : LaurentPolynomial R)
    (h:∀ k,LaurentPolynomial.eval₂ (RingHom.id R) (cosineCollisionRoots a u k) f=0) :
    cosineCollisionPacket a u ∣ f := by
  have hh:=laurent_prod_linear_indexed_dvd (cosineCollisionRoots a u) hi f h
  rw [cosineCollision_factorization] at hh
  exact dvd_trans (dvd_mul_left _ _) hh

end

 

 

noncomputable section
open Finset


def repairFirstDenominator {R : Type*} [One R] {m : ℕ}
    (D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) :
    Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R := fun i j =>
  if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then 1 else D i j

 
def isolateFirstNumerator {R : Type*} [Zero R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) :
    Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R := fun i j =>
  if (i = 0 ∧ j ≠ 1) ∨ (j = 0 ∧ i ≠ 1) then 0 else N i j

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PatchReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram.Patch
noncomputable section

variable {A B I : Type*}

 
def glued (r : A → A → Prop) (s : B → B → Prop) (a : I → A) (b : I → B)
    (active : I → Prop) : Sum A B → Sum A B → Prop
  | .inl x, .inl y => r x y
  | .inr x, .inr y => s x y
  | .inl x, .inr y => ∃ i, active i ∧ x = a i ∧ y = b i
  | .inr x, .inl y => ∃ i, active i ∧ x = b i ∧ y = a i

 

def compressed (r : A → A → Prop) (s : B → B → Prop) (a : I → A) (b : I → B)
    (active : I → Prop) (x y : B) : Prop :=
  s x y ∨ ∃ i j, active i ∧ active j ∧
    Relation.ReflTransGen r (a i) (a j) ∧ x = b i ∧ y = b j

variable (r : A → A → Prop) (s : B → B → Prop) (a : I → A) (b : I → B)
  (active : I → Prop)

theorem reach_to_exterior {x : Sum A B} {y : B}
    (h : Relation.ReflTransGen (glued r s a b active) x (.inr y)) :
    match x with
    | .inr x => Relation.ReflTransGen (compressed r s a b active) x y
    | .inl x => ∃ i, active i ∧ Relation.ReflTransGen r x (a i) ∧
        Relation.ReflTransGen (compressed r s a b active) (b i) y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | @head x w h hpath ih =>
    cases x with
    | inl x =>
      cases w with
      | inl w =>
        obtain ⟨i,hi,hr,hs⟩ := ih
        exact ⟨i,hi,hr.head h,hs⟩
      | inr w =>
        obtain ⟨i,hi,rfl,rfl⟩ := h
        exact ⟨i,hi,.refl,ih⟩
    | inr x =>
      cases w with
      | inl w =>
        obtain ⟨i,hi,rfl,rfl⟩ := h
        obtain ⟨j,hj,hr,hs⟩ := ih
        exact hs.head (Or.inr ⟨i,j,hi,hj,hr,rfl,rfl⟩)
      | inr w => exact ih.head (Or.inl h)

theorem lift_local_reach {x y : A} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen (glued r s a b active) (.inl x) (.inl y) :=
  h.lift Sum.inl (fun _ _ h => h)

theorem lift_compressed_reach {x y : B}
    (h : Relation.ReflTransGen (compressed r s a b active) x y) :
    Relation.ReflTransGen (glued r s a b active) (.inr x) (.inr y) := by
  apply h.lift' Sum.inr
  intro x y he
  rcases he with he | ⟨i,j,hi,hj,hr,rfl,rfl⟩
  · exact .single he
  · exact ((lift_local_reach r s a b active hr).head ⟨i,hi,rfl,rfl⟩).tail
      ⟨j,hj,rfl,rfl⟩

theorem exterior_reach_iff {x y : B} :
    Relation.ReflTransGen (glued r s a b active) (.inr x) (.inr y) ↔
      Relation.ReflTransGen (compressed r s a b active) x y :=
  ⟨reach_to_exterior r s a b active, lift_compressed_reach r s a b active⟩

theorem interior_reach_iff {x : A} {y : B} :
    Relation.ReflTransGen (glued r s a b active) (.inl x) (.inr y) ↔
      ∃ i, active i ∧ Relation.ReflTransGen r x (a i) ∧
        Relation.ReflTransGen (compressed r s a b active) (b i) y := by
  refine ⟨reach_to_exterior r s a b active, ?_⟩
  rintro ⟨i,hi,hr,hs⟩
  have hc : Relation.ReflTransGen (glued r s a b active) (.inl x) (.inr (b i)) :=
    (lift_local_reach r s a b active hr).tail ⟨i,hi,rfl,rfl⟩
  exact hc.trans (lift_compressed_reach r s a b active hs)

 

def drains {V : Type*} (r : V → V → Prop) (out : V → Prop) : Prop :=
  ∀ v w, r v w → ∃ j, out j ∧ Relation.ReflTransGen r v j

def exteriorOutput (out : B → Prop) : Sum A B → Prop
  | .inl _ => False
  | .inr x => out x

 

theorem drains_glued_iff (out : B → Prop) :
    drains (glued r s a b active) (exteriorOutput out) ↔
      (∀ x y, r x y → ∃ i, active i ∧ Relation.ReflTransGen r x (a i)) ∧
      drains (compressed r s a b active) out := by
  constructor
  · intro h
    constructor
    · intro x y hxy
      obtain ⟨z,hz,hr⟩ := h (.inl x) (.inl y) hxy
      cases z with
      | inl z => exact hz.elim
      | inr z =>
        obtain ⟨i,hi,hr,_⟩ := reach_to_exterior r s a b active hr
        exact ⟨i,hi,hr⟩
    · intro x y hxy
      rcases hxy with hxy | ⟨i,j,hi,hj,hr,rfl,rfl⟩
      · obtain ⟨z,hz,hr⟩ := h (.inr x) (.inr y) hxy
        cases z with
        | inl z => exact hz.elim
        | inr z => exact ⟨z,hz,reach_to_exterior r s a b active hr⟩
      · obtain ⟨z,hz,hr⟩ := h (.inr (b i)) (.inl (a i)) ⟨i,hi,rfl,rfl⟩
        cases z with
        | inl z => exact hz.elim
        | inr z => exact ⟨z,hz,reach_to_exterior r s a b active hr⟩
  · rintro ⟨hl,he⟩ v w hvw
    cases v with
    | inl x =>
      have hx : ∃ i, active i ∧ Relation.ReflTransGen r x (a i) := by
        cases w with
        | inl y => exact hl x y hvw
        | inr y => obtain ⟨i,hi,rfl,rfl⟩ := hvw; exact ⟨i,hi,.refl⟩
      obtain ⟨i,hi,hr⟩ := hx
      obtain ⟨z,hz,hs⟩ := he (b i) (b i) (Or.inr ⟨i,i,hi,hi,.refl,rfl,rfl⟩)
      refine ⟨.inr z,hz,?_⟩
      exact (interior_reach_iff r s a b active).mpr ⟨i,hi,hr,hs⟩
    | inr x =>
      have hx : ∃ y, compressed r s a b active x y := by
        cases w with
        | inl y =>
          obtain ⟨i,hi,rfl,rfl⟩ := hvw
          exact ⟨b i,Or.inr ⟨i,i,hi,hi,.refl,rfl,rfl⟩⟩
        | inr y => exact ⟨y,Or.inl hvw⟩
      obtain ⟨y,hxy⟩ := hx
      obtain ⟨z,hz,hr⟩ := he x y hxy
      exact ⟨.inr z,hz,lift_compressed_reach r s a b active hr⟩

end
end CriticalStrip.Diagram.Patch

 

 

 

namespace CriticalStrip.Diagram
noncomputable section

structure ConnectivityCertificate {V : Type*} (r : V → V → Prop) where
  root : V → V
  parent : V → V
  rank : V → ℕ
  edge_root : ∀ x y, r x y → root x = root y
  parent_edge : ∀ x, x ≠ root x → r x (parent x)
  parent_rank : ∀ x, x ≠ root x → rank (parent x) < rank x

namespace ConnectivityCertificate
variable {V : Type*} {r : V → V → Prop} (c : ConnectivityCertificate r)

theorem reaches_root (x : V) : Relation.ReflTransGen r x (c.root x) := by
  classical
  generalize hk : c.rank x = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hx : x = c.root x
    · rw [← hx]
    · have hp := c.parent_edge x hx
      have hr := ih (c.rank (c.parent x)) (by rw [← hk]; exact c.parent_rank x hx)
        (c.parent x) rfl
      rw [← c.edge_root _ _ hp] at hr
      exact hr.head hp

theorem reach_root_eq {x y : V} (h : Relation.ReflTransGen r x y) : c.root x = c.root y := by
  induction h with
  | refl => rfl
  | @tail y z h he ih => exact ih.trans (c.edge_root _ _ he)

theorem reach_symm (hs : Std.Symm r) {x y : V} (h : Relation.ReflTransGen r x y) :
    Relation.ReflTransGen r y x := by
  induction h with
  | refl => exact .refl
  | tail hp he ih => exact ih.head (hs.symm _ _ he)

theorem reach_iff (hs : Std.Symm r) (x y : V) :
    Relation.ReflTransGen r x y ↔ c.root x = c.root y := by
  refine ⟨c.reach_root_eq, ?_⟩
  intro he
  have hx := c.reaches_root x
  rw [he] at hx
  exact hx.trans (reach_symm hs (c.reaches_root y))

end ConnectivityCertificate

end
end CriticalStrip.Diagram

 

 

 

namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

def row (v : Fin 12) : Fin 3 := ⟨v.val/4, by have := v.isLt; omega⟩
def port (v : Fin 12) : Fin 4 := ⟨v.val%4, Nat.mod_lt _ (by decide)⟩

def wireEdge (a b v w : Fin 12) : Prop := (v=a ∧ w=b) ∨ (v=b ∧ w=a)

instance wireEdgeDecidable (a b : Fin 12) : DecidableRel (wireEdge a b) := by
  intro v w; unfold wireEdge; infer_instance

theorem wireEdge_symm {a b v w : Fin 12} (h : wireEdge a b v w) : wireEdge a b w v := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩


def boundary : Fin 6 → Fin 12 := ![4,0,1,6,10,11]

def boundaryAdj (d : Finset (Fin 6 × Fin 6)) (i j : Fin 6) : Prop :=
  (i,j) ∈ d ∨ (j,i) ∈ d

def boundarySupport (d : Finset (Fin 6 × Fin 6)) (i : Fin 6) : Prop :=
  ∃ j, boundaryAdj d i j



end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CutPatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.CutPatch
noncomputable section
open Finset

def boundary : Fin 4 → Fin 6 := ![2,3,4,5]

def boundaryAdj (d : Finset (Fin 4 × Fin 4)) (i j : Fin 4) : Prop :=
  (i,j) ∈ d ∨ (j,i) ∈ d

def boundarySupport (d : Finset (Fin 4 × Fin 4)) (i : Fin 4) : Prop :=
  ∃ j, boundaryAdj d i j

instance instDecidableBoundaryAdj (d : Finset (Fin 4 × Fin 4)) (i j : Fin 4) : Decidable (boundaryAdj d i j) := by
  unfold boundaryAdj; infer_instance
instance instDecidableBoundarySupport (d : Finset (Fin 4 × Fin 4)) (i : Fin 4) : Decidable (boundarySupport d i) := by
  unfold boundarySupport; infer_instance

end
end CriticalStrip.Diagram.CutPatch





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CutStateSound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section






namespace Graph

def Used {V : Type*} (r : V → V → Prop) (v : V) : Prop := ∃ w, r v w

theorem map_reach {V W : Type*} {r : V → V → Prop} {s : W → W → Prop}
    (f : V → W) (hf : ∀ v w, r v w → Relation.ReflTransGen s (f v) (f w))
    {v w : V} (h : Relation.ReflTransGen r v w) : Relation.ReflTransGen s (f v) (f w) := by
  induction h with
  | refl => exact .refl
  | @tail y z h hyz ih => exact ih.trans (hf y z hyz)

 

structure BoundaryEquiv {V W : Type*} {n : ℕ} (r : V → V → Prop) (s : W → W → Prop)
    (a : Fin n → V) (b : Fin n → W) where
  toFun : V → W
  invFun : W → V
  map_edge : ∀ v w, r v w → Relation.ReflTransGen s (toFun v) (toFun w)
  inv_edge : ∀ v w, s v w → Relation.ReflTransGen r (invFun v) (invFun w)
  map_boundary : ∀ i, toFun (a i) = b i
  inv_boundary : ∀ i, invFun (b i) = a i
  map_used : ∀ v, Used r v → Used s (toFun v)
  inv_used : ∀ v, Used s v → Used r (invFun v)
  retract : ∀ v, Used r v → Relation.ReflTransGen r v (invFun (toFun v))
  inv_retract : ∀ v, Used s v → Relation.ReflTransGen s v (toFun (invFun v))

namespace BoundaryEquiv
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  {a : Fin n → V} {b : Fin n → W}

protected def symm (e : BoundaryEquiv r s a b) : BoundaryEquiv s r b a :=
  ⟨e.invFun,e.toFun,e.inv_edge,e.map_edge,e.inv_boundary,e.map_boundary,
    e.inv_used,e.map_used,e.inv_retract,e.retract⟩

end BoundaryEquiv
end Graph

 

 

open Finset
open scoped Classical

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepToCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical

namespace Graph

theorem used_of_reach_ne {V : Type*} {r : V → V → Prop} {v w : V}
    (h : Relation.ReflTransGen r v w) (hne : v ≠ w) : Used r v := by
  rcases h.cases_head with h | ⟨x,hx,_⟩
  · exact (hne h).elim
  · exact ⟨x,hx⟩

end Graph

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StepComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical






namespace Graph

def BoundaryEquiv.ofEquiv {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} (e : V ≃ W)
    (hr : ∀ v w, r v w ↔ s (e v) (e w)) (ha : ∀ i, e (a i)=b i) :
    BoundaryEquiv r s a b where
  toFun := e
  invFun := e.symm
  map_edge := fun v w h => .single ((hr v w).mp h)
  inv_edge := fun v w h => .single ((hr (e.symm v) (e.symm w)).mpr (by simpa using h))
  map_boundary := ha
  inv_boundary := fun i => by rw [←ha i]; exact e.symm_apply_apply _
  map_used := fun v ⟨w,h⟩ => ⟨e w,(hr v w).mp h⟩
  inv_used := fun v ⟨w,h⟩ => ⟨e.symm w,(hr (e.symm v) (e.symm w)).mpr (by simpa using h)⟩
  retract := fun v _ => by rw [e.symm_apply_apply]
  inv_retract := fun v _ => by rw [e.apply_symm_apply]

end Graph

abbrev GateExterior (n : ℕ) := Sum (Fin 4) (Fin n)

def gateInput {n : ℕ} (a b : Fin n) (i : Fin n) : GateExterior n :=
  if i=a then .inl 0 else if i=b then .inl 1 else .inr i

@[simp] theorem gateInput_eq_box {n : ℕ} (a b i : Fin n) (hab : a≠b) (k : Fin 4) :
    gateInput a b i = .inl k ↔ (i=a ∧ k=0) ∨ (i=b ∧ k=1) := by
  by_cases hia : i=a <;> by_cases hib : i=b <;> simp_all [gateInput,eq_comm]

@[simp] theorem gateInput_eq_out {n : ℕ} (a b i j : Fin n) :
    gateInput a b i = .inr j ↔ i=j ∧ i≠a ∧ i≠b := by
  by_cases hia : i=a <;> by_cases hib : i=b <;> simp_all [gateInput]







namespace Graph

def DrainsBoundary {V I : Type*} (r : V → V → Prop) (a : I → V) : Prop :=
  ∀ v w, r v w → ∃ i, Relation.ReflTransGen r v (a i)

theorem BoundaryEquiv.drains {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
    {a : Fin n → V} {b : Fin n → W} (e : BoundaryEquiv r s a b)
    (h : DrainsBoundary r a) : DrainsBoundary s b := by
  intro v w hvw
  obtain ⟨x,hx⟩ := e.inv_used v ⟨w,hvw⟩
  obtain ⟨i,hi⟩ := h (e.invFun v) x hx
  refine ⟨i,?_⟩
  have hmap := Graph.map_reach e.toFun e.map_edge hi
  rw [e.map_boundary] at hmap
  exact (e.inv_retract v ⟨w,hvw⟩).trans hmap

theorem drains_glued_exterior_iff {V W I J : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (c : J → W) :
    DrainsBoundary (Patch.glued r s a b active) (fun i => .inr (c i)) ↔
      Patch.drains (Patch.glued r s a b active) (Patch.exteriorOutput (fun x => ∃ i, x=c i)) := by
  constructor
  · intro h v w hvw
    obtain ⟨i,hi⟩ := h v w hvw
    exact ⟨.inr (c i),⟨i,rfl⟩,hi⟩
  · intro h v w hvw
    obtain ⟨x,hx,hr⟩ := h v w hvw
    cases x with
    | inl x => exact hx.elim
    | inr x => obtain ⟨i,rfl⟩ := hx; exact ⟨i,hr⟩

theorem glued_drains_local {V W I J : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (c : J → W)
    (h : DrainsBoundary (Patch.glued r s a b active) (fun i => .inr (c i))) :
    DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨j,hj⟩ := h (.inl v) (.inl w) hvw
  obtain ⟨i,_,hi,_⟩ := Patch.reach_to_exterior r s a b active hj
  exact ⟨i,hi⟩

end Graph

end

 

 

noncomputable section
open Finset
open scoped Classical

structure Position (n : ℕ) where
  left : Fin n
  right : Fin n
  adjacent : left.val+1=right.val

def optionMatrix {K P Q : Type*} [Zero K] [One K] (f : P → Option Q) : Matrix Q P K :=
  fun q p => if f p=some q then 1 else 0

theorem optionMatrix_mul {K P Q R : Type*} [Semiring K] [Fintype Q]
    (f : P → Option Q) (g : Q → Option R) :
    (optionMatrix g : Matrix R Q K) * (optionMatrix f : Matrix Q P K) = optionMatrix (fun p => (f p).bind g) := by
  ext r p
  simp only [Matrix.mul_apply,optionMatrix]
  rcases Option.eq_none_or_eq_some (f p) with he | ⟨q,he⟩
  · simp [he]
  · simp only [he,Option.bind_some]
    rw [sum_eq_single q]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_WireContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

namespace Graph

 

structure WireContraction {V W : Type*} {n : ℕ} (r : V → V → Prop) (s : W → W → Prop)
    (a : Fin n → V) (b : Fin n → W) where
  project : V → W
  core : W → V
  section_eq : ∀ v, project (core v)=v
  map_edge : ∀ v w, r v w → Relation.ReflTransGen s (project v) (project w)
  core_edge : ∀ v w, s v w → r (core v) (core w)
  map_boundary : ∀ i, project (a i)=b i
  boundary_injective : Function.Injective b
  map_used : ∀ v, Used r v → Used s (project v)
  retract : ∀ v, Used r v → Relation.ReflTransGen r v (core (project v))
  boundary_retract : ∀ i, Used s (b i) → Relation.ReflTransGen r (core (b i)) (a i)

namespace WireContraction
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  {a : Fin n → V} {b : Fin n → W} [Std.Symm r] [Std.Symm s]

theorem lift_boundary_reach (e : WireContraction r s a b) {i j : Fin n}
    (hij : i≠j) (h : Relation.ReflTransGen s (b i) (b j)) :
    Relation.ReflTransGen r (a i) (a j) := by
  have hne : b i≠b j := fun hh => hij (e.boundary_injective hh)
  have hi := Graph.used_of_reach_ne h hne
  have hj := Graph.used_of_reach_ne (symm h) hne.symm
  have hm := Graph.map_reach e.core (fun v w hvw => .single (e.core_edge v w hvw)) h
  exact ((symm (e.boundary_retract i hi)).trans hm).trans (e.boundary_retract j hj)

end WireContraction
end Graph

 

 

section LocalContractions
open scoped Classical

namespace CompactGate
variable {V : Type*} {n : ℕ}

def boundary (old : Fin n → V) (a b : Fin n) (i : Fin n) : Sum V (Fin 4) :=
  if i=a then .inr 2 else if i=b then .inr 3 else .inl (old i)

def project (old : Fin n → V) (a b : Fin n) : Sum V (GateExterior n) → Sum V (Fin 4)
  | .inl v => .inl v
  | .inr (.inl k) => .inr k
  | .inr (.inr i) => boundary old a b i

def core : Sum V (Fin 4) → Sum V (GateExterior n)
  | .inl v => .inl v
  | .inr k => .inr (.inl k)

@[simp] theorem project_core (old : Fin n → V) (a b : Fin n) (v : Sum V (Fin 4)) :
    project old a b (core v)=v := by cases v <;> rfl

@[simp] theorem boundary_left (old : Fin n → V) (a b : Fin n) : boundary old a b a=.inr 2 := by
  simp [boundary]
@[simp] theorem boundary_right (old : Fin n → V) (a b : Fin n) (hab : a≠b) :
    boundary old a b b=.inr 3 := by simp [boundary,hab.symm]

theorem boundary_injective (old : Fin n → V) (h : Function.Injective old)
    (a b : Fin n) : Function.Injective (boundary old a b) := by
  intro i j hij
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    by_cases hja : j=a <;> by_cases hjb : j=b <;>
    simp_all [boundary]
  exact h hij

end CompactGate

namespace Patch
instance glued_symm {A B I : Type*} (r : A → A → Prop) (s : B → B → Prop)
    [Std.Symm r] [Std.Symm s] (a : I → A) (b : I → B) (active : I → Prop) :
    Std.Symm (glued r s a b active) := by
  constructor
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => change r _ _ at h ⊢; exact symm h
    | inr w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
  | inr v =>
    cases w with
    | inl w => obtain ⟨i,hi,rfl,rfl⟩ := h; exact ⟨i,hi,rfl,rfl⟩
    | inr w => change s _ _ at h ⊢; exact symm h
end Patch

end LocalContractions

namespace Graph
variable {V W : Type*} {n : ℕ} {r : V → V → Prop} {s : W → W → Prop}
  [Std.Symm r] [Std.Symm s] {a : Fin n → V} {b : Fin n → W}

lemma used_of_reach {v w : V} (h : Relation.ReflTransGen r v w) (hv : Used r v) : Used r w := by
  by_cases he : v=w
  · exact he ▸ hv
  · exact used_of_reach_ne (symm h) (Ne.symm he)

omit [Std.Symm r] in
lemma WireContraction.drains_inv (e : WireContraction r s a b) (h : DrainsBoundary s b) :
    DrainsBoundary r a := by
  intro v w hvw
  obtain ⟨x,hx⟩ := e.map_used v ⟨w,hvw⟩
  obtain ⟨i,hr⟩ := h (e.project v) x hx
  have hm := Graph.map_reach e.core (fun v w hvw => .single (e.core_edge v w hvw)) hr
  exact ⟨i,((e.retract v ⟨w,hvw⟩).trans hm).trans
    (e.boundary_retract i (used_of_reach hr ⟨x,hx⟩))⟩

end Graph

 

 

open scoped Classical

namespace CompactGate
variable {V : Type*}
  {n : ℕ}
  (r : V → V → Prop)
  (old : Fin n → V)
  (active : Fin n → Prop)
  (a b : Fin n)

def localEnd (v : V) : Sum V (Fin 4) → Prop
  | .inl w => Relation.ReflTransGen r v w
  | .inr _ => False

end CompactGate

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FreshGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace FreshGate
variable {V : Type*} {n : ℕ}

 
structure Ports (r : V → V → Prop) (old : Fin n → V) where
  port : Fin 4 → V
  select : V → Option (Fin 4)
  select_port : ∀ k, select (port k)=some k
  of_some : ∀ v k, select v=some k → v=port k
  old_none : ∀ i, select (old i)=none
  edge_none : ∀ v w, r v w → select v=none

namespace Ports
variable {r : V → V → Prop} {old : Fin n → V} (f : Ports r old)

def project : Sum V (Fin 4) → V
  | .inl v => v
  | .inr k => f.port k

def core (v : V) : Sum V (Fin 4) :=
  match f.select v with | none => .inl v | some k => .inr k

@[simp] theorem project_core (v : V) : f.project (f.core v)=v := by
  cases h : f.select v with
  | none => simp [core,h,project]
  | some k => simpa [core,h,project] using (f.of_some v k h).symm

@[simp] theorem core_port (k : Fin 4) : f.core (f.port k)=.inr k := by simp [core,f.select_port]
@[simp] theorem core_old (i : Fin n) : f.core (old i)=.inl (old i) := by simp [core,f.old_none]

def boundary (a b : Fin n) (i : Fin n) : V := f.project (CompactGate.boundary old a b i)

lemma core_boundary (a b i : Fin n) : f.core (f.boundary a b i)=CompactGate.boundary old a b i := by
  by_cases hia : i=a <;> by_cases hib : i=b <;>
    simp_all [boundary,CompactGate.boundary,project]

end Ports
end FreshGate
namespace PartialColumn

section RowTransitions
variable {n : ℕ}
  (row : Fin n)

 def prev (h : 0 < row.val) : Fin n := ⟨row.val-1,by omega⟩

lemma prev_val_add (h : 0 < row.val) : (prev row h).val+1=row.val := by
  simp only [prev]
  omega

end RowTransitions

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnSweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
namespace PartialColumn

open Finset
open scoped Classical
variable {K : Type*} [CommRing K] {n : ℕ}

def position (i : Fin n) : Position (n+1) := ⟨i.castSucc,i.succ,by simp⟩

end PartialColumn
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BlockPfaffian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

def blockFirst {m : ℕ} (i : Fin m) : Fin (2*m) := ⟨2*i.val, by omega⟩
def blockSecond {m : ℕ} (i : Fin m) : Fin (2*m) := ⟨2*i.val+1, by omega⟩

theorem blockFirst_injective {m : ℕ} : Function.Injective (@blockFirst m) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [blockFirst] at this
  omega

theorem blockSecond_injective {m : ℕ} : Function.Injective (@blockSecond m) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [blockSecond] at this
  omega

@[simp] theorem blockFirst_ne_second {m : ℕ} (i j : Fin m) : blockFirst i ≠ blockSecond j := by
  intro h
  have := congrArg Fin.val h
  dsimp [blockFirst,blockSecond] at this
  omega

@[simp] theorem blockSecond_ne_first {m : ℕ} (i j : Fin m) : blockSecond i ≠ blockFirst j :=
  (blockFirst_ne_second j i).symm

@[simp] theorem blockFirst_zero (m : ℕ) : blockFirst (0 : Fin (m+1)) = 0 := rfl
@[simp] theorem blockSecond_zero (m : ℕ) : blockSecond (0 : Fin (m+1)) = 1 := rfl

def blockSummand {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*m)) (Fin (2*m)) K) (σ : Equiv.Perm (Fin (2*m))) : K :=
  (Equiv.Perm.sign σ : ℤ) * ∏ i : Fin m, M (σ (blockFirst i)) (σ (blockSecond i))

def blockSwap {m : ℕ} (k : Fin (m+1)) : Equiv.Perm (Fin (2*(m+1))) :=
  Equiv.swap (blockFirst 0) (blockFirst k) * Equiv.swap (blockSecond 0) (blockSecond k)

theorem blockSwap_first {m : ℕ} (k i : Fin (m+1)) :
    blockSwap k (blockFirst i) = blockFirst (Equiv.swap 0 k i) := by
  simp only [blockSwap, Equiv.Perm.coe_mul, Function.comp_apply,
    Equiv.swap_apply_of_ne_of_ne (blockFirst_ne_second i 0) (blockFirst_ne_second i k)]
  exact (blockFirst_injective.map_swap 0 k i).symm

theorem blockSwap_second {m : ℕ} (k i : Fin (m+1)) :
    blockSwap k (blockSecond i) = blockSecond (Equiv.swap 0 k i) := by
  change Equiv.swap (blockFirst 0) (blockFirst k)
    (Equiv.swap (blockSecond 0) (blockSecond k) (blockSecond i)) = _
  rw [← blockSecond_injective.map_swap 0 k i]
  exact Equiv.swap_apply_of_ne_of_ne (blockSecond_ne_first _ 0) (blockSecond_ne_first _ k)

@[simp] theorem blockSwap_sign {m : ℕ} (k : Fin (m+1)) : Equiv.Perm.sign (blockSwap k) = 1 := by
  by_cases hk : k = 0
  · simp [blockSwap,hk]
  · rw [blockSwap, map_mul,
      Equiv.Perm.sign_swap (blockFirst_injective.ne (Ne.symm hk)),
      Equiv.Perm.sign_swap (blockSecond_injective.ne (Ne.symm hk))]
    simp

theorem blockSummand_swap {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (σ : Equiv.Perm (Fin (2*(m+1)))) (k : Fin (m+1)) :
    blockSummand M (σ*blockSwap k) = blockSummand M σ := by
  simp only [blockSummand, map_mul, blockSwap_sign, mul_one, Equiv.Perm.coe_mul,
    Function.comp_apply, blockSwap_first, blockSwap_second]
  congr 1
  exact Equiv.prod_comp (Equiv.swap 0 k) (fun i => M (σ (blockFirst i)) (σ (blockSecond i)))

def blockFlip (m : ℕ) : Equiv.Perm (Fin (2*(m+1))) := Equiv.swap 0 1

@[simp] theorem blockFlip_first_zero (m : ℕ) : blockFlip m (blockFirst 0) = blockSecond 0 := by
  simp [blockFlip]

@[simp] theorem blockFlip_second_zero (m : ℕ) : blockFlip m (blockSecond 0) = blockFirst 0 := by
  simp [blockFlip]

@[simp] theorem blockFlip_first_succ {m : ℕ} (i : Fin m) :
    blockFlip m (blockFirst i.succ) = blockFirst i.succ := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp only [blockFirst, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one] at hv <;> omega

@[simp] theorem blockFlip_second_succ {m : ℕ} (i : Fin m) :
    blockFlip m (blockSecond i.succ) = blockSecond i.succ := by
  apply Equiv.swap_apply_of_ne_of_ne <;> intro h <;>
    have hv := congrArg Fin.val h <;> simp only [blockSecond, Fin.val_mk, Fin.val_succ, Fin.val_zero, Fin.val_one] at hv <;> omega

@[simp] theorem blockFlip_sign (m : ℕ) : Equiv.Perm.sign (blockFlip m) = -1 := by
  exact Equiv.Perm.sign_swap (by intro h; have := congrArg Fin.val h; simp at this)

theorem blockSummand_flip {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (σ : Equiv.Perm (Fin (2*(m+1)))) :
    blockSummand M (σ*blockFlip m) = blockSummand M σ := by
  simp only [blockSummand, map_mul, blockFlip_sign, Units.val_mul, Int.cast_mul,
    Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, Equiv.Perm.coe_mul,
    Function.comp_apply]
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [blockFlip_first_zero, blockFlip_second_zero,
    blockFlip_first_succ, blockFlip_second_succ, hM (σ (blockFirst 0)) (σ (blockSecond 0))]
  ring

 
def blockSection {m : ℕ} (p : Fin (2*(m+1))) : Equiv.Perm (Fin (2*(m+1))) :=
  let k : Fin (m+1) := ⟨p.val/2, by omega⟩
  if p.val%2 = 0 then blockSwap k else blockSwap k * blockFlip m

@[simp] theorem blockSection_zero {m : ℕ} (p : Fin (2*(m+1))) : blockSection p 0 = p := by
  unfold blockSection
  split_ifs with hp
  · rw [← blockFirst_zero m, blockSwap_first, Equiv.swap_apply_left]
    apply Fin.ext
    dsimp [blockFirst]
    omega
  · change blockSwap _ (blockFlip m 0) = p
    rw [← blockFirst_zero m, blockFlip_first_zero, blockSwap_second, Equiv.swap_apply_left]
    apply Fin.ext
    dsimp [blockSecond]
    omega

theorem blockSummand_section {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (σ : Equiv.Perm (Fin (2*(m+1))))
    (p : Fin (2*(m+1))) : blockSummand M (σ*blockSection p) = blockSummand M σ := by
  unfold blockSection
  split_ifs
  · exact blockSummand_swap M σ _
  · rw [← mul_assoc, blockSummand_flip M hM, blockSummand_swap]


 

 


abbrev FixedZero (n : ℕ) := {σ : Equiv.Perm (Fin (n+1)) // σ 0 = 0}

instance instFintypeFixedZero (n : ℕ) : Fintype (FixedZero n) := by classical exact Subtype.fintype _

def fixedZeroEquiv (n : ℕ) : FixedZero n ≃ Equiv.Perm (Fin n) where
  toFun σ := (Equiv.Perm.decomposeFin σ.val).2
  invFun σ := ⟨Equiv.Perm.decomposeFin.symm (0,σ), by simp⟩
  left_inv σ := by
    apply Subtype.ext
    have hp : (Equiv.Perm.decomposeFin σ.val).1 = 0 := by
      have h := congrArg (fun e : Equiv.Perm (Fin (n+1)) => e 0)
        (Equiv.Perm.decomposeFin.symm_apply_apply σ.val)
      change Equiv.Perm.decomposeFin.symm ((Equiv.Perm.decomposeFin σ.val).1,
        (Equiv.Perm.decomposeFin σ.val).2) 0 = σ.val 0 at h
      rw [Equiv.Perm.decomposeFin_symm_apply_zero, σ.property] at h
      exact h
    change Equiv.Perm.decomposeFin.symm (0,(Equiv.Perm.decomposeFin σ.val).2) = σ.val
    conv_rhs => rw [← Equiv.Perm.decomposeFin.symm_apply_apply σ.val]
    congr 1
    exact Prod.ext hp.symm rfl
  right_inv σ := by simp

 

def blockPermutationEquiv (m : ℕ) : Equiv.Perm (Fin (2*(m+1))) ≃
    Fin (2*(m+1)) × FixedZero (2*m+1) where
  toFun σ := (σ⁻¹ 0, ⟨σ * blockSection (σ⁻¹ 0), by
    change σ (blockSection (m := m) (σ⁻¹ 0) 0) = 0
    rw [blockSection_zero (m := m)]
    exact σ.apply_symm_apply 0⟩)
  invFun p := p.2.val * (blockSection p.1)⁻¹
  left_inv σ := by simp
  right_inv p := by
    rcases p with ⟨p,ρ⟩
    have hi : ρ.val⁻¹ 0 = 0 := by
      apply ρ.val.injective
      change ρ.val (ρ.val.symm 0) = ρ.val 0
      rw [ρ.val.apply_symm_apply]
      exact ρ.property.symm
    have hp : (ρ.val * (blockSection p)⁻¹)⁻¹ 0 = p := by
      simp only [mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, hi]
      exact blockSection_zero (m := m) p
    apply Prod.ext hp
    apply Subtype.ext
    change (ρ.val * (blockSection p)⁻¹) *
      blockSection ((ρ.val * (blockSection p)⁻¹)⁻¹ 0) = ρ.val
    rw [hp, mul_assoc, inv_mul_cancel, mul_one]

theorem blockSummand_section_inv {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (σ : Equiv.Perm (Fin (2*(m+1))))
    (p : Fin (2*(m+1))) : blockSummand M (σ*(blockSection p)⁻¹) = blockSummand M σ := by
  have h := blockSummand_section M hM (σ*(blockSection p)⁻¹) p
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm

theorem blockSummand_sum_fixedZero {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) :
    ∑ σ, blockSummand M σ = (2*(m+1) : K) *
      ∑ τ : Equiv.Perm (Fin (2*m+1)),
        blockSummand M (Equiv.Perm.decomposeFin.symm (0,τ)) := by
  classical
  rw [← Equiv.sum_comp (blockPermutationEquiv m).symm]
  simp only [Fintype.sum_prod_type, blockPermutationEquiv, Equiv.coe_fn_symm_mk,
    blockSummand_section_inv M hM]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  · norm_cast
  · exact (Equiv.sum_comp (fixedZeroEquiv (2*m+1)).symm
      (fun σ => blockSummand M σ.val)).symm

@[simp] theorem blockFirst_succ {m : ℕ} (i : Fin m) :
    blockFirst i.succ = (blockFirst i).succ.succ := by
  apply Fin.ext
  simp [blockFirst]
  omega

@[simp] theorem blockSecond_succ {m : ℕ} (i : Fin m) :
    blockSecond i.succ = (blockSecond i).succ.succ := by
  apply Fin.ext
  simp [blockSecond]
  omega

 

theorem blockSummand_fixTwo {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (σ : Equiv.Perm (Fin (2*m))) :
    blockSummand M (Equiv.Perm.decomposeFin.symm
      (0,Equiv.Perm.decomposeFin.symm (0,σ))) =
      M 0 1 * blockSummand (fun i j => M i.succ.succ j.succ.succ) σ := by
  change Fin (2*m+2) → Fin (2*m+2) → K at M
  unfold blockSummand
  rw [Fin.prod_univ_succ]
  simp only [blockFirst_zero, blockSecond_zero, blockFirst_succ, blockSecond_succ]
  change ((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm
      (0, Equiv.Perm.decomposeFin.symm (0, σ))) : ℤ) : K) *
    (M (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ)) 0)
      (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ)) 1) *
      ∏ index : Fin m,
        M (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ))
          (blockFirst index).succ.succ)
          (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0, σ))
            (blockSecond index).succ.succ)) = _
  simp only [Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, Equiv.swap_self, Equiv.refl_apply,
    Fin.succ_zero_eq_one,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  ring

theorem blockSummand_isolated_zero {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hzero : ∀ j, j ≠ 1 → M 0 j = 0)
    (p : Fin (2*m+1)) (hp : p ≠ 0) (σ : Equiv.Perm (Fin (2*m))) :
    blockSummand M (Equiv.Perm.decomposeFin.symm
      (0,Equiv.Perm.decomposeFin.symm (p,σ))) = 0 := by
  change Fin (2*m+2) → Fin (2*m+2) → K at M
  unfold blockSummand
  rw [Fin.prod_univ_succ]
  simp only [blockFirst_zero, blockSecond_zero]
  change ((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm
      (0, Equiv.Perm.decomposeFin.symm (p, σ))) : ℤ) : K) *
    (M (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (p, σ)) 0)
      (Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (p, σ)) 1) * _) = 0
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, Equiv.swap_self, Equiv.refl_apply]
  rw [hzero p.succ (by
    change p.succ ≠ (0 : Fin (2*m+1)).succ
    exact (Fin.succ_injective (2*m+1)).ne hp),
    zero_mul, mul_zero]

theorem blockSummand_sum_isolated {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (hM : ∀ i j, M j i = -M i j) (hzero : ∀ j, j ≠ 1 → M 0 j = 0) :
    ∑ σ, blockSummand M σ = (2*(m+1) : K) * M 0 1 *
      ∑ σ, blockSummand (fun i j => M i.succ.succ j.succ.succ) σ := by
  classical
  rw [blockSummand_sum_fixedZero M hM]
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := 2*m)).symm]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single 0]
  · have sum_eq : (∑ σ : Equiv.Perm (Fin (2*m)),
        blockSummand M (Equiv.Perm.decomposeFin.symm
          (0, Equiv.Perm.decomposeFin.symm (0, σ)))) =
        M 0 1 * ∑ σ, blockSummand (fun i j => M i.succ.succ j.succ.succ) σ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      exact blockSummand_fixTwo M σ
    exact (congrArg (fun value : K => (2*(m+1) : K) * value) sum_eq).trans
      (mul_assoc _ _ _).symm
  · intro p _ hp
    exact Finset.sum_eq_zero (fun σ _ => blockSummand_isolated_zero M hzero p hp σ)
  · simp








theorem blockSummand_fixZero {K : Type*} [CommRing K] {m : ℕ}
    (M : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) K)
    (τ : Equiv.Perm (Fin (2*m+1))) :
    blockSummand M (Equiv.Perm.decomposeFin.symm (0,τ)) =
      (Equiv.Perm.sign τ : ℤ) * M 0 (τ 0).succ *
      ∏ i : Fin m, M (τ (blockFirst i).succ).succ (τ (blockSecond i).succ).succ := by
  change Fin (2*m+2) → Fin (2*m+2) → K at M
  unfold blockSummand
  rw [Fin.prod_univ_succ]
  simp only [blockFirst_zero, blockSecond_zero, blockFirst_succ, blockSecond_succ]
  change ((Equiv.Perm.sign (Equiv.Perm.decomposeFin.symm (0, τ)) : ℤ) : K) *
    (M (Equiv.Perm.decomposeFin.symm (0, τ) 0)
      (Equiv.Perm.decomposeFin.symm (0, τ) 1) *
      ∏ index : Fin m,
        M (Equiv.Perm.decomposeFin.symm (0, τ) (blockFirst index).succ.succ)
          (Equiv.Perm.decomposeFin.symm (0, τ) (blockSecond index).succ.succ)) = _
  simp only [Equiv.Perm.decomposeFin.symm_sign, ite_true, one_mul,
    Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_one, Equiv.swap_self, Equiv.refl_apply,
    Equiv.Perm.decomposeFin_symm_apply_succ]
  ring



theorem repairFirstDenominator_symm {R : Type*} [One R] {m : ℕ}
    (D : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) (hD : ∀ i j, D i j = D j i) :
    ∀ i j, repairFirstDenominator D i j = repairFirstDenominator D j i := by
  intro i j
  unfold repairFirstDenominator
  have h : ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) ↔
      ((j = 0 ∧ i = 1) ∨ (j = 1 ∧ i = 0)) := by tauto
  simp only [h, hD i j]

theorem isolateFirstNumerator_skew {R : Type*} [AddGroup R] {m : ℕ}
    (N : Matrix (Fin (2*(m+1))) (Fin (2*(m+1))) R) (hN : ∀ i j, N j i = -N i j) :
    ∀ i j, isolateFirstNumerator N j i = -isolateFirstNumerator N i j := by
  intro i j
  unfold isolateFirstNumerator
  have h : ((j = 0 ∧ i ≠ 1) ∨ (i = 0 ∧ j ≠ 1)) ↔
      ((i = 0 ∧ j ≠ 1) ∨ (j = 0 ∧ i ≠ 1)) := by tauto
  simp only [h]
  split_ifs
  · exact neg_zero.symm
  · exact hN i j



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_AugmentedTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

def twoCons {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) : Fin (n+2) → R :=
  Fin.cons x (Fin.cons y a)

@[simp] theorem twoCons_zero {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) :
    twoCons x y a 0 = x := by simp [twoCons]

@[simp] theorem twoCons_one {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) :
    twoCons x y a 1 = y := by
  rw [← Fin.succ_zero_eq_one]
  simp only [twoCons, Fin.cons_succ, Fin.cons_zero]

@[simp] theorem twoCons_succ_succ {R : Type*} {n : ℕ} (x y : R) (a : Fin n → R) (i : Fin n) :
    twoCons x y a i.succ.succ = a i := by simp [twoCons]



def augmentTwoIndex (n : ℕ) : Fin ((n+n%2)+2) ≃ Fin ((n+2)+(n+2)%2) :=
  finCongr (by omega)

@[simp] theorem augmentTwoIndex_val {n : ℕ} (i : Fin ((n+n%2)+2)) :
    (augmentTwoIndex n i).val = i.val := rfl

@[simp] theorem augmentTwoIndex_zero (n : ℕ) : augmentTwoIndex n 0 = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem augmentTwoIndex_one (n : ℕ) : augmentTwoIndex n 1 = 1 := by
  apply Fin.ext
  simp [augmentTwoIndex, Nat.mod_eq_of_lt (by omega : 1 < n+2+n%2)]


theorem prod_pad_one {R : Type*} [CommMonoid R] {n m : ℕ} (h : n ≤ m)
    (f : Fin n → R) :
    (∏ i : Fin m, if hi : i.val < n then f ⟨i.val,hi⟩ else 1) = ∏ i : Fin n, f i := by
  classical
  symm
  apply Fintype.prod_of_injective (fun i : Fin n => i.castLE h) (Fin.castLE_injective h)
  · intro i hi
    split_ifs with hlt
    · exfalso
      exact hi ⟨⟨i.val,hlt⟩, Fin.ext rfl⟩
    · rfl
  · intro i
    simp only [Fin.val_castLE, i.isLt, dite_true]

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalNodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical LaurentPolynomial

lemma LaurentInterval.mul {K:Type*} [Field K] {f g:LaurentPolynomial K} {a b c d:ℤ}
    (hf:LaurentInterval f a b) (hg:LaurentInterval g c d) : LaurentInterval (f*g) (a+c) (b+d) := by
  intro e he
  have hs:=AddMonoidAlgebra.support_coeff_mul_subset f g (Finsupp.mem_support_iff.mpr he)
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.mem_add.mp hs
  have hx:=hf x (Finsupp.mem_support_iff.mp hx)
  have hy:=hg y (Finsupp.mem_support_iff.mp hy)
  omega

lemma LaurentInterval.prod_exact {K:Type*} [Field K] {ι:Type*} (s:Finset ι)
    (f:ι → LaurentPolynomial K) (a b:ι → ℤ)
    (h:∀ i∈s,LaurentInterval (f i) (a i) (b i) ∧ (f i).coeff (a i)≠0 ∧ (f i).coeff (b i)≠0) :
    LaurentInterval (∏ i∈s,f i) (∑ i∈s,a i) (∑ i∈s,b i) ∧
      (∏ i∈s,f i).coeff (∑ i∈s,a i)≠0 ∧ (∏ i∈s,f i).coeff (∑ i∈s,b i)≠0 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    refine ⟨?_,?_,?_⟩
    · intro e he
      have : e=0 := by
        by_contra hh
        apply he
        change (Finsupp.single (0:ℤ) (1:K)) e=0
        exact Finsupp.single_eq_of_ne hh
      simp [this]
    · simp
    · simp
  | @insert i s hi ih =>
    specialize ih (fun j hj => h j (by simp [hj]))
    have hj:=h i (by simp)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]
    refine ⟨hj.1.mul ih.1,?_,?_⟩
    · rw [laurent_mul_bottom_coeff _ _ _ _ (fun e he => (hj.1 e he).1) (fun e he => (ih.1 e he).1)]
      exact mul_ne_zero hj.2.1 ih.2.1
    · rw [laurent_mul_top_coeff _ _ _ _ (fun e he => (hj.1 e he).2) (fun e he => (ih.1 e he).2)]
      exact mul_ne_zero hj.2.2 ih.2.2

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RootOfUnityPowers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram

theorem eighthRoot_power {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) (k : ℕ) :
    q^k = (-1)^(k/8) * q^(k%8) := by
  calc
    q^k = q^(8*(k/8)+k%8) := congrArg (q^·) (by omega)
    _ = (q^8)^(k/8) * q^(k%8) := by rw [pow_add, pow_mul]
    _ = _ := by rw [h]

theorem eighthRoot_power_8 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^8 = -(1) := by
  have ht := eighthRoot_power h 8
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_9 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^9 = -(q^1) := by
  have ht := eighthRoot_power h 9
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_10 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^10 = -(q^2) := by
  have ht := eighthRoot_power h 10
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_11 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^11 = -(q^3) := by
  have ht := eighthRoot_power h 11
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_12 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^12 = -(q^4) := by
  have ht := eighthRoot_power h 12
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_13 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^13 = -(q^5) := by
  have ht := eighthRoot_power h 13
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_14 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^14 = -(q^6) := by
  have ht := eighthRoot_power h 14
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_15 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^15 = -(q^7) := by
  have ht := eighthRoot_power h 15
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_16 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^16 = (1) := by
  have ht := eighthRoot_power h 16
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_17 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^17 = (q^1) := by
  have ht := eighthRoot_power h 17
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_18 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^18 = (q^2) := by
  have ht := eighthRoot_power h 18
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_19 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^19 = (q^3) := by
  have ht := eighthRoot_power h 19
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_20 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^20 = (q^4) := by
  have ht := eighthRoot_power h 20
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_21 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^21 = (q^5) := by
  have ht := eighthRoot_power h 21
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_22 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^22 = (q^6) := by
  have ht := eighthRoot_power h 22
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_23 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^23 = (q^7) := by
  have ht := eighthRoot_power h 23
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_24 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^24 = -(1) := by
  have ht := eighthRoot_power h 24
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_25 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^25 = -(q^1) := by
  have ht := eighthRoot_power h 25
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_26 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^26 = -(q^2) := by
  have ht := eighthRoot_power h 26
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_27 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^27 = -(q^3) := by
  have ht := eighthRoot_power h 27
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_28 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^28 = -(q^4) := by
  have ht := eighthRoot_power h 28
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_29 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^29 = -(q^5) := by
  have ht := eighthRoot_power h 29
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_30 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^30 = -(q^6) := by
  have ht := eighthRoot_power h 30
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_31 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^31 = -(q^7) := by
  have ht := eighthRoot_power h 31
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_32 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^32 = (1) := by
  have ht := eighthRoot_power h 32
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_33 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^33 = (q^1) := by
  have ht := eighthRoot_power h 33
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_34 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^34 = (q^2) := by
  have ht := eighthRoot_power h 34
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_35 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^35 = (q^3) := by
  have ht := eighthRoot_power h 35
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_36 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^36 = (q^4) := by
  have ht := eighthRoot_power h 36
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_37 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^37 = (q^5) := by
  have ht := eighthRoot_power h 37
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_38 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^38 = (q^6) := by
  have ht := eighthRoot_power h 38
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_39 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^39 = (q^7) := by
  have ht := eighthRoot_power h 39
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_40 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^40 = -(1) := by
  have ht := eighthRoot_power h 40
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_41 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^41 = -(q^1) := by
  have ht := eighthRoot_power h 41
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_42 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^42 = -(q^2) := by
  have ht := eighthRoot_power h 42
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_43 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^43 = -(q^3) := by
  have ht := eighthRoot_power h 43
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_44 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^44 = -(q^4) := by
  have ht := eighthRoot_power h 44
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_45 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^45 = -(q^5) := by
  have ht := eighthRoot_power h 45
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_46 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^46 = -(q^6) := by
  have ht := eighthRoot_power h 46
  norm_num at ht
  simpa only [pow_one] using ht

theorem eighthRoot_power_47 {K : Type*} [CommRing K] {q : K} (h : q^8 = -1) :
    q^47 = -(q^7) := by
  have ht := eighthRoot_power h 47
  norm_num at ht
  simpa only [pow_one] using ht

end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset

 

def diagram : Fin 51 → Finset (Fin 6 × Fin 6) := ![
  ∅,
  {(0,1)},
  {(0,1),(2,3)},
  {(0,1),(2,3),(4,5)},
  {(0,1),(2,4)},
  {(0,1),(2,5)},
  {(0,1),(2,5),(3,4)},
  {(0,1),(3,4)},
  {(0,1),(3,5)},
  {(0,1),(4,5)},
  {(0,2)},
  {(0,2),(3,4)},
  {(0,2),(3,5)},
  {(0,2),(4,5)},
  {(0,3)},
  {(0,3),(1,2)},
  {(0,3),(1,2),(4,5)},
  {(0,3),(1,4)},
  {(0,3),(1,4),(2,5)},
  {(0,3),(1,5)},
  {(0,3),(2,4)},
  {(0,3),(2,5)},
  {(0,3),(4,5)},
  {(0,4)},
  {(0,4),(1,2)},
  {(0,4),(1,5)},
  {(0,4),(2,5)},
  {(0,5)},
  {(0,5),(1,2)},
  {(0,5),(1,2),(3,4)},
  {(0,5),(3,4)},
  {(1,2)},
  {(1,2),(3,4)},
  {(1,2),(3,5)},
  {(1,2),(4,5)},
  {(1,3)},
  {(1,3),(2,4)},
  {(1,3),(2,5)},
  {(1,3),(4,5)},
  {(1,4)},
  {(1,4),(2,5)},
  {(1,5)},
  {(1,5),(3,4)},
  {(2,3)},
  {(2,3),(4,5)},
  {(2,4)},
  {(2,5)},
  {(2,5),(3,4)},
  {(3,4)},
  {(3,5)},
  {(4,5)}]

instance boundaryAdjDecidable (d : Finset (Fin 6 × Fin 6)) (i j : Fin 6) :
    Decidable (boundaryAdj d i j) := by unfold boundaryAdj; infer_instance
instance boundarySupportDecidable (d : Finset (Fin 6 × Fin 6)) (i : Fin 6) :
    Decidable (boundarySupport d i) := by unfold boundarySupport; infer_instance

theorem diagram_injective : Function.Injective diagram := by decide

theorem diagram_upper (k : Fin 51) : ∀ e ∈ diagram k, e.1 < e.2 := by
  fin_cases k <;> decide

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section
open Finset
open scoped Classical

def mirrorIndex : Fin 51 → Fin 51 := ![0,31,28,29,24,15,16,34,33,32,10,13,12,11,46,5,6,40,18,37,26,21,47,45,4,36,20,43,2,3,44,1,9,8,7,41,25,19,42,39,17,35,38,27,30,23,14,22,50,49,48]

theorem mirrorIndex_involutive : Function.Involutive mirrorIndex := by
  unfold Function.Involutive
  decide

def reverseSlots : Fin 6 → Fin 6 := ![2,1,0,5,4,3]

theorem diagram_mirror (k : Fin 51) (i j : Fin 6) :
    boundaryAdj (diagram (mirrorIndex k)) i j ↔
      boundaryAdj (diagram k) (reverseSlots i) (reverseSlots j) := by
  fin_cases k <;> decide +revert



end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ThreeBoxSplitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

def commonNumerator {K : Type*} [CommRing K] (q z : K) : K :=
  (q^4*z^2-1)*(q^6*z^2-1)






open Finset

 

def diagramExterior {B : Type*} (d : Finset (Fin 6 × Fin 6))
    (s : B → B → Prop) (b : Fin 6 → B) (active : Fin 6 → Prop) (x y : B) : Prop :=
  s x y ∨ ∃ i j, active i ∧ active j ∧ (i=j ∨ boundaryAdj d i j) ∧ x=b i ∧ y=b j



def exteriorTest {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop)
    (test : (B → B → Prop) → Prop) (k : Fin 51) : Prop :=
  (∀ i, active i ↔ boundarySupport (diagram k) i) ∧
  Patch.drains (diagramExterior (diagram k) s b active) out ∧
  test (Relation.ReflTransGen (diagramExterior (diagram k) s b active))

end
end CriticalStrip.Diagram.ThreeBox

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhaseAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip.Diagram
noncomputable section


lemma eighthRoot_two_add_one_ne_zero {K : Type*} [Field K] [CharZero K] {q : K}
    (hq : q^8 = -1) : q^2+1≠0 := by
  intro h
  have h2 : q^2 = -1 := by linear_combination h
  have h8 : q^8 = 1 := by calc
    q^8 = (q^2)^4 := by ring
    _ = 1 := by rw [h2]; norm_num
  have : (1 : K) = -1 := h8.symm.trans hq
  norm_num at this

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TripleCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

structure TriplePosition (n : ℕ) where
  a : Fin n
  b : Fin n
  c : Fin n
  hab : a.val+1=b.val
  hbc : b.val+1=c.val

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

lemma ab : s.a≠s.b := by intro he; have:=congrArg Fin.val he; have:=s.hab; omega
lemma bc : s.b≠s.c := by intro he; have:=congrArg Fin.val he; have:=s.hbc; omega
lemma ac : s.a≠s.c := by intro he; have:=congrArg Fin.val he; have:=s.hab; have:=s.hbc; omega

def left : Position n := ⟨s.a,s.b,s.hab⟩
def right : Position n := ⟨s.b,s.c,s.hbc⟩

def vertexEquiv : (((Fin n ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4) ≃ (Fin n ⊕ Fin 12) :=
  (Equiv.sumAssoc _ _ _).trans ((Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)).trans
      (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv)))

def boundary (i : Fin n) : Fin n ⊕ Fin 12 :=
  if i=s.a then .inr 6 else if i=s.b then .inr 10 else if i=s.c then .inr 11 else .inl i

@[simp] lemma vertex_old (i : Fin n) : vertexEquiv (.inl (.inl (.inl i)))=.inl i := rfl
@[simp] lemma vertex_zero (i : Fin 4) : (vertexEquiv (n:=n) (.inl (.inl (.inr i))))=
    .inr ⟨i.val,by omega⟩ := rfl
@[simp] lemma vertex_one (i : Fin 4) : (vertexEquiv (n:=n) (.inl (.inr i)))=
    .inr ⟨4+i.val,by omega⟩ := rfl
@[simp] lemma vertex_two (i : Fin 4) : (vertexEquiv (n:=n) (.inr i))=
    .inr ⟨4+(4+i.val),by omega⟩ := rfl

end TriplePosition





end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.Diagram.Graph
noncomputable section
namespace Attached
variable {V : Type*} {n : ℕ}

def wiring (r : V → V → Prop) (old : Fin n → V) (active : Fin n → Prop) :
    (V ⊕ Fin n) → (V ⊕ Fin n) → Prop
  | .inl v,.inl w => r v w
  | .inl v,.inr i | .inr i,.inl v => v=old i ∧ active i
  | .inr _,.inr _ => False

def project (old : Fin n → V) : V ⊕ Fin n → V
  | .inl v => v
  | .inr i => old i

instance wiring_symm (r : V → V → Prop) [Std.Symm r] (old : Fin n → V) (active : Fin n → Prop) :
    Std.Symm (wiring r old active) := by
  constructor
  rintro (v|i) (w|j) h
  · change r v w at h; change r w v; exact symm h
  all_goals exact h

variable (r : V → V → Prop) (old : Fin n → V) (active : Fin n → Prop)
  (ha : ∀ i, active i ↔ Used r (old i))

include ha in
lemma map_used (v : V ⊕ Fin n) (h : Used (wiring r old active) v) : Used r (project old v) := by
  obtain ⟨w,hw⟩ := h
  rcases v with v | i <;> rcases w with w | j
  · exact ⟨w,hw⟩
  · obtain ⟨rfl,hj⟩ := hw; exact (ha j).mp hj
  · exact (ha i).mp hw.2
  · exact hw.elim

def contraction (hi : Function.Injective old) :
    WireContraction (wiring r old active) r Sum.inr old where
  project := project old
  core := Sum.inl
  section_eq := fun _ => rfl
  map_edge := by
    rintro (v|i) (w|j) h
    · exact .single h
    · rw [h.1]; exact .refl
    · rw [h.1]; exact .refl
    · exact h.elim
  core_edge := fun _ _ h => h
  map_boundary := fun _ => rfl
  boundary_injective := hi
  map_used := map_used r old active ha
  retract := by
    rintro (v|i) ⟨w,hw⟩
    · exact .refl
    · cases w with
      | inl w => exact .single ⟨rfl,hw.2⟩
      | inr j => exact hw.elim
  boundary_retract := fun i hu => .single ⟨rfl,(ha i).mpr hu⟩

end Attached
end
end CriticalStrip.Diagram.Graph

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def interface : Fin 6 → Fin n ⊕ Fin n :=
  ![.inl s.a,.inl s.b,.inl s.c,.inr s.a,.inr s.b,.inr s.c]

def exteriorEquiv : ((Fin n ⊕ Fin 12) ⊕ Fin n) ≃ (Fin 12 ⊕ (Fin n ⊕ Fin n)) where
  toFun
    | .inl (.inl i) => .inr (.inl i)
    | .inl (.inr v) => .inl v
    | .inr i => .inr (.inr i)
  invFun
    | .inl v => .inl (.inr v)
    | .inr (.inl i) => .inl (.inl i)
    | .inr (.inr i) => .inr i
  left_inv := by rintro ((i|v)|i) <;> rfl
  right_inv := by rintro (v|(i|i)) <;> rfl

lemma boundary_old (i j : Fin n) :
    ((.inl i : Fin n ⊕ Fin 12)=s.boundary j) ↔
      i=j ∧ i≠s.a ∧ i≠s.b ∧ i≠s.c := by
  by_cases ha : j=s.a <;> by_cases hb : j=s.b <;> by_cases hc : j=s.c <;>
    simp_all [boundary]

lemma boundary_new (v : Fin 12) (j : Fin n) :
    ((.inr v : Fin n ⊕ Fin 12)=s.boundary j) ↔
      (j=s.a ∧ v=6) ∨ (j=s.b ∧ v=10) ∨ (j=s.c ∧ v=11) := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : j=s.a <;> by_cases hb : j=s.b <;> by_cases hc : j=s.c <;>
    simp_all [boundary]

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TriplePatch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical





namespace Tile

def mirrorPort : Fin 4 → Fin 4 := ![1,0,3,2]
lemma mirrorPort_involutive : Function.Involutive mirrorPort := by intro i; fin_cases i <;> rfl

def mirrorPortEquiv : Fin 4 ≃ Fin 4 :=
  ⟨mirrorPort,mirrorPort,mirrorPort_involutive,mirrorPort_involutive⟩

end Tile

 

 

namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorVertexEquiv : (((Fin n ⊕ Fin 4) ⊕ Fin 4) ⊕ Fin 4) ≃ (Fin n ⊕ Fin 12) :=
  (Equiv.sumCongr (Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _) Tile.mirrorPortEquiv)
    Tile.mirrorPortEquiv) Tile.mirrorPortEquiv).trans vertexEquiv

def mirrorBoundary (i : Fin n) : Fin n ⊕ Fin 12 :=
  if i=s.c then .inr 6 else if i=s.b then .inr 10 else if i=s.a then .inr 11 else .inl i

@[simp] lemma mirror_vertex_old (i : Fin n) :
    mirrorVertexEquiv (.inl (.inl (.inl i)))=.inl i := rfl
@[simp] lemma mirror_vertex_zero (i : Fin 4) :
    (mirrorVertexEquiv (n:=n) (.inl (.inl (.inr i))))=
      .inr ⟨(Tile.mirrorPort i).val,by omega⟩ := rfl
@[simp] lemma mirror_vertex_one (i : Fin 4) :
    (mirrorVertexEquiv (n:=n) (.inl (.inr i)))=
      .inr ⟨4+(Tile.mirrorPort i).val,by omega⟩ := rfl
@[simp] lemma mirror_vertex_two (i : Fin 4) :
    (mirrorVertexEquiv (n:=n) (.inr i))=
      .inr ⟨4+(4+(Tile.mirrorPort i).val),by omega⟩ := rfl

end TriplePosition
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MirrorExterior
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

def mirrorInterface : Fin 6 → Fin n ⊕ Fin n :=
  ![.inl s.c,.inl s.b,.inl s.a,.inr s.c,.inr s.b,.inr s.a]

def mirrorExteriorEquiv : ((Fin n ⊕ Fin 12) ⊕ Fin n) ≃ (Fin 12 ⊕ (Fin n ⊕ Fin n)) where
  toFun
    | .inl (.inl i) => .inr (.inl i)
    | .inl (.inr v) => .inl v
    | .inr i => .inr (.inr i)
  invFun
    | .inl v => .inl (.inr v)
    | .inr (.inl i) => .inl (.inl i)
    | .inr (.inr i) => .inr i
  left_inv := by rintro ((i|v)|i) <;> rfl
  right_inv := by rintro (v|(i|i)) <;> rfl

lemma mirror_boundary_old (i j : Fin n) :
    ((.inl i : Fin n ⊕ Fin 12)=s.mirrorBoundary j) ↔
      i=j ∧ i≠s.c ∧ i≠s.b ∧ i≠s.a := by
  by_cases ha : j=s.c <;> by_cases hb : j=s.b <;> by_cases hc : j=s.a <;>
    simp_all [mirrorBoundary]

lemma mirror_boundary_new (v : Fin 12) (j : Fin n) :
    ((.inr v : Fin n ⊕ Fin 12)=s.mirrorBoundary j) ↔
      (j=s.c ∧ v=6) ∨ (j=s.b ∧ v=10) ∨ (j=s.a ∧ v=11) := by
  have hab:=s.ab; have hbc:=s.bc; have hac:=s.ac
  by_cases ha : j=s.c <;> by_cases hb : j=s.b <;> by_cases hc : j=s.a <;>
    simp_all [mirrorBoundary]

end TriplePosition
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.Diagram.ThreeBox
noncomputable section

lemma reverseSlots_involutive : Function.Involutive reverseSlots := by intro i; fin_cases i <;> rfl

@[simp] lemma reverseSlots_twice (i : Fin 6) : reverseSlots (reverseSlots i)=i := reverseSlots_involutive i

def reverseEquiv : Fin 6 ≃ Fin 6 :=
  ⟨reverseSlots,reverseSlots,reverseSlots_involutive,reverseSlots_involutive⟩

lemma support_mirror (k : Fin 51) (i : Fin 6) :
    boundarySupport (diagram (mirrorIndex k)) i ↔
      boundarySupport (diagram k) (reverseSlots i) := by
  unfold boundarySupport
  simp only [diagram_mirror]
  exact reverseEquiv.surjective.exists.symm

lemma exterior_mirror {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (k : Fin 51) :
    diagramExterior (diagram k) s (b∘reverseSlots) (active∘reverseSlots) =
      diagramExterior (diagram (mirrorIndex k)) s b active := by
  funext x y
  apply propext
  unfold diagramExterior
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨i,j,hi,hj,h,he,hf⟩
    refine ⟨reverseSlots i,reverseSlots j,hi,hj,?_,he,hf⟩
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr ((diagram_mirror k _ _).mpr (by simpa only [reverseSlots_twice] using h))
  · rintro ⟨i,j,hi,hj,h,he,hf⟩
    refine ⟨reverseSlots i,reverseSlots j,?_,?_,?_,?_,?_⟩
    · simpa only [Function.comp_apply,reverseSlots_twice] using hi
    · simpa only [Function.comp_apply,reverseSlots_twice] using hj
    · exact h.elim (fun he => Or.inl (congrArg _ he)) (fun hh => Or.inr ((diagram_mirror k i j).mp hh))
    · simpa only [Function.comp_apply,reverseSlots_twice] using he
    · simpa only [Function.comp_apply,reverseSlots_twice] using hf

lemma exteriorTest_mirror {B : Type*} (s : B → B → Prop) (b : Fin 6 → B)
    (active : Fin 6 → Prop) (out : B → Prop) (test : (B → B → Prop) → Prop) (k : Fin 51) :
    exteriorTest s (b∘reverseSlots) (active∘reverseSlots) out test k ↔
      exteriorTest s b active out test (mirrorIndex k) := by
  unfold exteriorTest
  rw [exterior_mirror]
  refine and_congr ?_ Iff.rfl
  simp only [support_mirror,Function.comp_apply]
  constructor
  · intro h i
    simpa only [reverseSlots_twice] using h (reverseSlots i)
  · intro h i
    simpa only [reverseSlots_twice] using h (reverseSlots i)

end
end CriticalStrip.Diagram.ThreeBox

 

 

namespace CriticalStrip.Diagram





noncomputable section
namespace TriplePosition
variable {n : ℕ} (s : TriplePosition n)

lemma mirror_interface : s.mirrorInterface=s.interface ∘ ThreeBox.reverseSlots := by
  funext i; fin_cases i <;> rfl

end TriplePosition

 

 

open scoped Classical
open Finset

end

 

 

noncomputable section
open scoped Classical





namespace Position
variable {n : ℕ}

def Disjoint (a b : Position n) : Prop :=
  a.left≠b.left ∧ a.left≠b.right ∧ a.right≠b.left ∧ a.right≠b.right

def exchangeEquiv : ((Fin n ⊕ Fin 4) ⊕ Fin 4) ≃ ((Fin n ⊕ Fin 4) ⊕ Fin 4) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr k) => .inr k
    | .inr k => .inl (.inr k)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr k) => .inr k
    | .inr k => .inl (.inr k)
  left_inv := by rintro ((i|k)|k) <;> rfl
  right_inv := by rintro ((i|k)|k) <;> rfl

end Position

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LocalPadding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical
open Finset
namespace Position
variable {n : ℕ}
def padTop (a : Position n) : Position (n+1) :=
  ⟨a.left.castSucc,a.right.castSucc,a.adjacent⟩
def padBottom (a : Position n) : Position (n+1) :=
  ⟨a.left.succ,a.right.succ,by have:=a.adjacent; simp only [Fin.val_succ]; omega⟩
end Position

lemma optionMatrix_map {K P Q : Type*} [Zero K] [One K] (e : P → Q) (he : Function.Injective e)
    (f : P → Option P) (g : Q → Option Q) (h : ∀ p, g (e p)=(f p).map e) (p q : P) :
    (optionMatrix g : Matrix Q Q K) (e q) (e p) = optionMatrix f q p := by
  unfold optionMatrix
  rw [h]
  cases hf : f p <;> simp [he.eq_iff]

end





noncomputable section
open scoped Classical
namespace PartialColumn
variable {n m : ℕ}

def rowPosition (r : ℕ) (hr : r+2≤n) : Position n :=
  ⟨⟨r,by omega⟩,⟨r+1,by omega⟩,rfl⟩

def rowTriple (r : ℕ) (hr : r+2≤n) : TriplePosition (n+1) :=
  ⟨⟨r,by omega⟩,⟨r+1,by omega⟩,⟨r+2,by omega⟩,rfl,rfl⟩

lemma row_disjoint_low (r : ℕ) (hr : r+2≤n) (i : Fin n) (hi : i.val < r) :
    (position i).Disjoint (rowPosition r hr).padBottom := by
  have hid := i.isLt
  dsimp [Position.Disjoint,position,rowPosition,Position.padBottom]
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> have hh:=congrArg Fin.val he <;> simp at hh <;> omega

lemma row_disjoint_high (r : ℕ) (hr : r+2≤n) (i : Fin n) (hi : r + 1 < i.val) :
    (position i).Disjoint (rowPosition r hr).padTop := by
  dsimp [Position.Disjoint,position,rowPosition,Position.padTop]
  refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> have hh:=congrArg Fin.val he <;> simp at hh <;> omega



end PartialColumn
end

 

 

noncomputable section
open scoped Classical
open Finset

variable {K : Type*} [CommRing K]

def functionMatrix {P Q : Type*} (f : P → Q) : Matrix Q P K := optionMatrix (some ∘ f)

lemma mul_functionMatrix {P Q R : Type*} [Fintype Q] (f : P → Q) (M : Matrix R Q K)
    (r : R) (p : P) : (M * functionMatrix (K := K) f) r p = M r (f p) := by
  simp only [Matrix.mul_apply,functionMatrix,optionMatrix,Function.comp_apply,Option.some.injEq]
  rw [sum_eq_single (f p)]
  · simp
  · intro q _ hq; simp [Ne.symm hq]
  · simp

lemma optionMatrix_natural {P Q : Type*} [Fintype P] [Fintype Q]
    (f : P → Q) (a : P → Option P) (b : Q → Option Q)
    (h : ∀ p, b (f p)=(a p).map f) :
    (optionMatrix b : Matrix Q Q K) * functionMatrix (K := K) f = functionMatrix (K := K) f * optionMatrix a := by
  calc
    _ = optionMatrix (fun p => ((some ∘ f) p).bind b) :=
      optionMatrix_mul (some ∘ f) b
    _ = optionMatrix (fun p => (a p).bind (some ∘ f)) := by
      congr 1
      funext p
      simp only [Function.comp_apply, Option.bind_some]
      rw [h p]
      cases a p <;> rfl
    _ = _ := (optionMatrix_mul a (some ∘ f)).symm

end
end CriticalStrip.Diagram

 

 

namespace Fin
open scoped _root_.Fin
lemma swap_succAbove_adjacent {n : ℕ} (a b : Fin (n+1)) (hab : a.val+1=b.val)
    (i : Fin n) : Equiv.swap a b (b.succAbove i)=a.succAbove i := by
  by_cases hi : i.val<a.val
  · have hia : i.castSucc≠a := by intro he; have:=congrArg Fin.val he; simp at this; omega
    have hib : i.castSucc≠b := by intro he; have:=congrArg Fin.val he; simp at this; omega
    simp only [Fin.succAbove, show i.castSucc<a from hi, show i.castSucc<b from (by change i.val<b.val; omega),
      ite_true,Equiv.swap_apply_of_ne_of_ne hia hib]
  · by_cases he : i.val=a.val
    · have ha : i.castSucc=a := Fin.ext he
      have hb : i.succ=b := Fin.ext (by simp only [Fin.val_succ]; omega)
      simp only [Fin.succAbove,ha,lt_self_iff_false,ite_false,hb,
        show a<b from (by change a.val<b.val; omega),ite_true,Equiv.swap_apply_left]
    · have hia : i.succ≠a := by intro hh; have:=congrArg Fin.val hh; simp at this; omega
      have hib : i.succ≠b := by intro hh; have:=congrArg Fin.val hh; simp at this; omega
      simp only [Fin.succAbove,show ¬i.castSucc<a from hi,
        show ¬i.castSucc<b from (by change ¬i.val<b.val; omega),ite_false,
        Equiv.swap_apply_of_ne_of_ne hia hib]
end Fin

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SwapVacancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical





namespace Pairing

lemma omit_last {n : ℕ} (r : Fin (n+1)) :
    (Fin.succAboveOrderEmb r.castSucc) (Fin.last n)=Fin.last (n+1) := by
  change r.castSucc.succAbove (Fin.last n)=Fin.last (n+1)
  rw [Fin.succAbove_of_le_castSucc _ _ (by change r.val≤n; omega)]
  rfl

end Pairing
end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical







lemma Fin.insertNth_swap_adjacent {α : Type*} {n : ℕ} (a b : Fin (n+1))
    (hab : a.val+1=b.val) (x : α) (w : Fin n → α) :
    (Fin.insertNth b x w) ∘ Equiv.swap a b=Fin.insertNth a x w := by
  rw [Fin.eq_insertNth_iff]
  constructor
  · simp
  · funext i
    have h : Equiv.swap a b (a.succAbove i)=b.succAbove i := by
      rw [←Fin.swap_succAbove_adjacent a b hab i,Equiv.swap_apply_self]
    simp only [Fin.removeNth,Function.comp_apply,h,Fin.insertNth_apply_succAbove]







def topPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  σ.viaEmbedding Fin.castSuccEmb

@[simp] lemma topPerm_cast {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    topPerm σ i.castSucc=(σ i).castSucc :=
  Equiv.Perm.viaEmbedding_apply σ Fin.castSuccEmb i

@[simp] lemma topPerm_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    topPerm σ (Fin.last n)=Fin.last n := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨i,hi⟩
  exact Fin.castSucc_ne_last i hi

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalScalarDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical

variable {K L ι : Type*} [CommRing K] [CommRing L] [Fintype ι] [DecidableEq ι]

def matrixPrefix {n : ℕ} (A : Fin n → Matrix ι ι K) : ℕ → Matrix ι ι K
  | 0 => 1
  | k+1 => if h:k<n then A ⟨k,h⟩*matrixPrefix A k else matrixPrefix A k

lemma matrixPrefix_map (f : K →+* L) {n : ℕ} (A : Fin n → Matrix ι ι K) (k : ℕ) :
    (matrixPrefix A k).map f=matrixPrefix (fun i => (A i).map f) k := by
  induction k with
  | zero => simp [matrixPrefix]
  | succ k ih =>
    rw [matrixPrefix,matrixPrefix]
    split_ifs with hk
    · rw [Matrix.map_mul,ih]
    · exact ih

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaurentNumerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma matrix_map_ring_smul {K L α β : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (c : K) (A : Matrix α β K) :
    (c • A).map f=f c • A.map f := by
  ext i j
  exact f.map_mul c (A i j)









def interpolationNumerator {R : Type*} [CommRing R] {n : ℕ}
    (b y : Fin n → R) (k : Fin n) : R :=
  ((Matrix.vandermonde b).updateCol k y).det

lemma vandermonde_mulVec_coeff {R : Type*} [CommRing R] {n : ℕ}
    (b : Fin n → R) (p : Polynomial R) (hp:p.degree<n) :
    (Matrix.vandermonde b).mulVec (fun k : Fin n => p.coeff k)=fun i => p.eval (b i) := by
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.vandermonde_apply]
  rw [show (∑ x : Fin n, b i ^ (x:ℕ) * p.coeff (x:ℕ)) =
    ∑ x ∈ Finset.range n, b i ^ x * p.coeff x from
    Fin.sum_univ_eq_sum_range (fun x => b i ^ x * p.coeff x) n]
  by_cases hz:p=0
  · simp [hz]
  · rw [Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp)]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

lemma interpolationNumerator_eq_det_mul_coeff {K : Type*} [Field K] {n : ℕ}
    (b y : Fin n → K) (hb:Function.Injective b) (k : Fin n) :
    interpolationNumerator b y k=(Matrix.vandermonde b).det*
      (Lagrange.interpolate Finset.univ b y).coeff k := by
  let p:=Lagrange.interpolate Finset.univ b y
  have hp:p.degree<n := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Lagrange.degree_interpolate_lt (s:=Finset.univ) y hb.injOn
  have hev : (Matrix.vandermonde b).mulVec (fun k : Fin n => p.coeff k)=y := by
    rw [vandermonde_mulVec_coeff b p hp]
    funext i
    exact Lagrange.eval_interpolate_at_node y hb.injOn (Finset.mem_univ i)
  have h:=congrArg (Matrix.mulVec (Matrix.vandermonde b).adjugate) hev
  rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,
    ←Matrix.cramer_eq_adjugate_mulVec] at h
  exact (congrFun h k).symm

lemma interpolationNumerator_map {R K : Type*} [CommRing R] [CommRing K]
    (f : R →+* K) {n : ℕ} (b y : Fin n → R) (k : Fin n) :
    f (interpolationNumerator b y k)=interpolationNumerator (fun i => f (b i)) (fun i => f (y i)) k := by
  unfold interpolationNumerator
  rw [RingHom.map_det]
  congr 1
  change ((Matrix.vandermonde b).updateCol k y).map f = _
  ext i j
  simp only [Matrix.map_apply,Matrix.updateCol_apply,Matrix.vandermonde_apply]
  split_ifs <;> simp only [map_pow]

lemma interpolationNumerator_collision {R : Type*} [CommRing R] {n : ℕ}
    (b y : Fin n → R) (i j : Fin n) (hij:i≠j) (hb:b i=b j) (hy:y i=y j) (k : Fin n) :
    interpolationNumerator b y k=0 := by
  apply Matrix.det_zero_of_row_eq hij
  funext a
  simp only [Matrix.updateCol_apply,Matrix.vandermonde_apply]
  split_ifs <;> simp only [hb,hy]


 

 


lemma functionMatrix_ring_map {R S P Q : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : P → Q) : (functionMatrix (K:=R) v).map f=functionMatrix v := by
  ext p q
  simp only [Matrix.map_apply,functionMatrix,optionMatrix]
  split_ifs <;> simp







def pairBound {n:ℕ} (i j k:Fin n) : ℕ := if j=i then 0 else if k=i ∨ k=j then 1 else 0

def selfBound {n:ℕ} (i:Fin n) (b:ℕ) (k:Fin n) : ℕ := if k=i then b else 0

lemma sum_pairBound {n:ℕ} (i k:Fin (n+1)) :
    (∑ j:Fin (n+1),pairBound i j k)=if k=i then n else 1 := by
  by_cases hki:k=i
  · subst k
    simp only [pairBound,ite_true]
    simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul,mul_one]
    have h:Finset.univ.filter (fun j:Fin (n+1) => ¬j=i)=Finset.univ.erase i := by ext j; simp [eq_comm]
    rw [h]
    simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  · have hh (j:Fin (n+1)) : pairBound i j k=if j=k then 1 else 0 := by
      by_cases hj:j=i <;> by_cases hk:j=k <;> simp_all [pairBound,eq_comm]
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hki,ite_false]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalExchange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma topPerm_swap {n : ℕ} (a b : Fin n) :
    topPerm (Equiv.swap a b)=Equiv.swap a.castSucc b.castSucc := by
  apply Equiv.ext
  intro j
  induction j using Fin.lastCases with
  | last => simp [Equiv.swap_apply_def,Ne.symm (Fin.castSucc_ne_last a),Ne.symm (Fin.castSucc_ne_last b)]
  | cast j =>
    simp only [topPerm_cast,Equiv.swap_apply_def,Fin.castSucc_inj]
    split_ifs <;> rfl

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Specialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section

variable {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F]

 
def RationalAt (φ : R →+* K) (x : F) (y : K) : Prop :=
  ∃ a b : R, φ b ≠ 0 ∧ x * algebraMap R F b = algebraMap R F a ∧ y * φ b = φ a

namespace RationalAt
variable {φ : R →+* K} {x x' : F} {y y' : K}

omit [IsDomain R] [IsFractionRing R F] in
theorem algebraMap (a : R) : RationalAt φ (algebraMap R F a) (φ a) := by
  exact ⟨a, 1, by simp, by simp, by simp⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem zero : RationalAt φ (0 : F) (0 : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (0 : R))

omit [IsDomain R] [IsFractionRing R F] in
theorem one : RationalAt φ (1 : F) (1 : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (1 : R))

omit [IsDomain R] in
theorem unique (h : RationalAt φ x y) (h' : RationalAt φ x y') : y = y' := by
  obtain ⟨a, b, hb, he, hv⟩ := h
  obtain ⟨a', b', hb', he', hv'⟩ := h'
  have hab : a * b' = a' * b := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, ← he, ← he']
    ring
  have hvv := congrArg φ hab
  simp only [map_mul, ← hv, ← hv'] at hvv
  apply mul_right_cancel₀ (mul_ne_zero hb hb')
  calc
    y * (φ b * φ b') = (y * φ b) * φ b' := by ring
    _ = (y' * φ b') * φ b := hvv
    _ = y' * (φ b * φ b') := by ring

omit [IsDomain R] [IsFractionRing R F] in
theorem add (h : RationalAt φ x y) (h' : RationalAt φ x' y') :
    RationalAt φ (x+x') (y+y') := by
  obtain ⟨a,b,hb,he,hv⟩ := h
  obtain ⟨a',b',hb',he',hv'⟩ := h'
  refine ⟨a*b'+a'*b, b*b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [_root_.map_mul, _root_.map_add, ← he, ← he']; ring
  · simp only [_root_.map_mul, _root_.map_add, ← hv, ← hv']; ring

omit [IsDomain R] [IsFractionRing R F] in
theorem mul (h : RationalAt φ x y) (h' : RationalAt φ x' y') :
    RationalAt φ (x*x') (y*y') := by
  obtain ⟨a,b,hb,he,hv⟩ := h
  obtain ⟨a',b',hb',he',hv'⟩ := h'
  refine ⟨a*a', b*b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [_root_.map_mul, ← he, ← he']; ring
  · simp only [_root_.map_mul, ← hv, ← hv']; ring

omit [IsDomain R] [IsFractionRing R F] in
theorem neg (h : RationalAt φ x y) : RationalAt φ (-x) (-y) := by
  obtain ⟨a,b,hb,he,hv⟩ := h
  exact ⟨-a,b,hb, by simp [← he], by simp [← hv]⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem sub (h : RationalAt φ x y) (h' : RationalAt φ x' y') :
    RationalAt φ (x-x') (y-y') := by simpa only [sub_eq_add_neg] using h.add h'.neg

omit [IsDomain R] in
theorem ne_zero (h : RationalAt φ x y) (hy : y ≠ 0) : x ≠ 0 := by
  intro hx
  rw [hx] at h
  exact hy (h.unique zero)

omit [IsDomain R] in
theorem inv (h : RationalAt φ x y) (hy : y ≠ 0) : RationalAt φ x⁻¹ y⁻¹ := by
  have hx := h.ne_zero hy
  obtain ⟨a,b,hb,he,hv⟩ := h
  refine ⟨b,a, by rw [← hv]; exact mul_ne_zero hy hb, ?_, ?_⟩
  · rw [← he, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · rw [← hv, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]

omit [IsDomain R] in
theorem div (h : RationalAt φ x y) (h' : RationalAt φ x' y') (hy' : y' ≠ 0) :
    RationalAt φ (x/x') (y/y') := by
  simpa only [div_eq_mul_inv] using h.mul (h'.inv hy')

omit [IsDomain R] [IsFractionRing R F] in
theorem pow (h : RationalAt φ x y) (n : ℕ) : RationalAt φ (x^n) (y^n) := by
  induction n with
  | zero => simpa using (one (φ := φ) (F := F))
  | succ n ih => simpa only [pow_succ] using ih.mul h

omit [IsDomain R] [IsFractionRing R F] in
theorem natCast (n : ℕ) : RationalAt φ (n : F) (n : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (n : R))

omit [IsDomain R] [IsFractionRing R F] in
theorem intCast (n : ℤ) : RationalAt φ (n : F) (n : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (n : R))

omit [IsDomain R] [IsFractionRing R F] in
theorem sum {ι : Type*} (s : Finset ι) (f : ι → F) (g : ι → K)
    (h : ∀ i ∈ s, RationalAt φ (f i) (g i)) :
    RationalAt φ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (φ := φ) (F := F))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [IsDomain R] [IsFractionRing R F] in
theorem prod {ι : Type*} (s : Finset ι) (f : ι → F) (g : ι → K)
    (h : ∀ i ∈ s, RationalAt φ (f i) (g i)) :
    RationalAt φ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (φ := φ) (F := F))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end RationalAt
end

 

 

noncomputable section
variable {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F] {φ : R →+* K}

namespace RationalAt

omit [IsDomain R] [IsFractionRing R F] in
theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (B : Matrix ι ι K)
    (h : ∀ i j, RationalAt φ (A i j) (B i j)) : RationalAt φ A.det B.det := by
  classical
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply sum
  intro σ _
  exact (intCast _).mul (prod _ _ _ (fun i _ => h (σ i) i))

omit [IsDomain R] [IsFractionRing R F] in
theorem matrixOne {ι : Type*} [DecidableEq ι] (i j : ι) :
    RationalAt φ ((1 : Matrix ι ι F) i j) ((1 : Matrix ι ι K) i j) := by
  classical
  by_cases h : i = j
  · subst j; simpa using (one (φ := φ) (F := F))
  · simpa [Matrix.one_apply, h] using (zero (φ := φ) (F := F))

omit [IsDomain R] [IsFractionRing R F] in
theorem adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (B : Matrix ι ι K)
    (h : ∀ i j, RationalAt φ (A i j) (B i j)) (i j : ι) :
    RationalAt φ (A.adjugate i j) (B.adjugate i j) := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  apply det
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst b; simpa using (one (φ := φ) (F := F))
    · simpa [Pi.single_apply, hb] using (zero (φ := φ) (F := F))
  · simp only [Matrix.updateRow_ne ha]
    exact h a b

omit [IsDomain R] in
theorem nonsingInv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (B : Matrix ι ι K)
    (h : ∀ i j, RationalAt φ (A i j) (B i j)) (hB : B.det ≠ 0) (i j : ι) :
    RationalAt φ (A⁻¹ i j) (B⁻¹ i j) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((det A B h).inv hB).mul (adjugate A B h i j)

omit [IsDomain R] [IsFractionRing R F] in
theorem mulVec {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ F) (B : Matrix ι κ K) (v : κ → F) (w : κ → K)
    (hA : ∀ i j, RationalAt φ (A i j) (B i j))
    (hv : ∀ j, RationalAt φ (v j) (w j)) (i : ι) :
    RationalAt φ (A.mulVec v i) (B.mulVec w i) := by
  apply sum
  intro j _
  exact (hA i j).mul (hv j)

end RationalAt



end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionSubstitutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped LaurentPolynomial Classical

lemma cosineCollisionPacket_eval_root {R : Type*} [CommRing R] [IsDomain R]
    (a u : Rˣ) (k : Fin 4) :
    LaurentPolynomial.eval₂ (RingHom.id R) (cosineCollisionRoots a u k) (cosineCollisionPacket a u)=0 := by
  let φ:=LaurentPolynomial.eval₂ (RingHom.id R) (cosineCollisionRoots a u k)
  have h:=congrArg φ (cosineCollision_factorization a u)
  rw [map_mul,map_prod] at h
  have hz : (∏ l : Fin 4,φ (LaurentPolynomial.T 1-LaurentPolynomial.C ((cosineCollisionRoots a u l):R)))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (by simp [φ,laurent_eval_linear])
  rw [hz] at h
  apply (mul_eq_zero.mp h.symm).resolve_left
  simp only [φ,map_mul,LaurentPolynomial.eval₂_C,LaurentPolynomial.eval₂_T,RingHom.id_apply,
    zpow_ofNat]
  exact mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _))

def collisionCopy {n : ℕ} (i : Fin (n+1)) (j : Fin n) : Fin (n+1) → Fin n := Fin.insertNth i j id

lemma collisionCopy_eq {n : ℕ} (i : Fin (n+1)) (j : Fin n) (r s : Fin (n+1)) (hrs:r≠s)
    (h:collisionCopy i j r=collisionCopy i j s) :
    (r=i ∧ s=i.succAbove j) ∨ (r=i.succAbove j ∧ s=i) := by
  unfold collisionCopy at h
  revert h hrs
  refine Fin.succAboveCases i ?_ (fun r => ?_) r
  · refine Fin.succAboveCases i ?_ (fun s => ?_) s
    · intro hrs _; exact (hrs rfl).elim
    · intro _ h
      simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,id_eq] at h
      exact Or.inl ⟨rfl,congrArg i.succAbove h.symm⟩
  · refine Fin.succAboveCases i ?_ (fun s => ?_) s
    · intro _ h
      simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,id_eq] at h
      exact Or.inr ⟨congrArg i.succAbove h,rfl⟩
    · intro hrs h
      simp only [Fin.insertNth_apply_succAbove,id_eq] at h
      exact (hrs (congrArg i.succAbove h)).elim

end

 

 

noncomputable section
open scoped Classical









lemma interpolate_lift_of_vandermonde_dvd {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) {n : ℕ} (b y : Fin n → R)
    (hb : Function.Injective (fun i => φ (b i)))
    (hd : ∀ k,(Matrix.vandermonde b).det ∣ interpolationNumerator b y k) :
    ∃ P : Polynomial R,P.map φ=Lagrange.interpolate Finset.univ (fun i => φ (b i)) (fun i => φ (y i)) := by
  choose q hq using hd
  let p:=Lagrange.interpolate Finset.univ (fun i => φ (b i)) (fun i => φ (y i))
  have hdet:φ (Matrix.vandermonde b).det=(Matrix.vandermonde (fun i => φ (b i))).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.map_apply,Matrix.vandermonde_apply]
  have hc (k:Fin n):φ (q k)=p.coeff k := by
    have h:=congrArg φ (hq k)
    rw [interpolationNumerator_map,map_mul,hdet,
      interpolationNumerator_eq_det_mul_coeff _ _ hb] at h
    exact mul_left_cancel₀ (Matrix.det_vandermonde_ne_zero_iff.mpr hb) h.symm
  refine ⟨Polynomial.ofFn n q,?_⟩
  ext k
  rw [Polynomial.coeff_map]
  by_cases hk:k<n
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    exact hc ⟨k,hk⟩
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),map_zero]
    symm
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have hp:=Lagrange.degree_interpolate_lt (s:=Finset.univ) (fun i => φ (y i)) hb.injOn
    simp only [Finset.card_univ,Fintype.card_fin] at hp
    exact hp.trans_le (by exact_mod_cast (show n≤k by omega))

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpecializationPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma RationalAt.eval₂ {R F K A:Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [CommRing A]
    (φ:R →+* K) (f:A →+* F) (g:A →+* K)
    (hfg:∀ a,RationalAt φ (f a) (g a)) {x:F} {y:K} (hxy:RationalAt φ x y)
    (P:Polynomial A) : RationalAt φ (P.eval₂ f x) (P.eval₂ g y) := by
  rw [Polynomial.eval₂_eq_sum,Polynomial.eval₂_eq_sum]
  exact RationalAt.sum _ _ _ (fun i _ => (hfg _).mul (hxy.pow i))

lemma RationalAt.eval_map {R F K:Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] (φ:R →+* K)
    {x:F} {y:K} (hxy:RationalAt φ x y) (P:Polynomial R) :
    RationalAt φ ((P.map (Algebra.algebraMap R F)).eval x) ((P.map φ).eval y) := by
  simpa only [Polynomial.eval_map] using
    RationalAt.eval₂ φ (Algebra.algebraMap R F) φ RationalAt.algebraMap hxy P

end





noncomputable section
open scoped Classical

lemma selfBound_one_add {n:ℕ} (i:Fin n) : selfBound i 1+selfBound i 1=selfBound i 2 := by
  funext j; by_cases h:j=i <;> simp [selfBound,h]

lemma sum_selfBound (n a:ℕ) : (∑i:Fin n,selfBound i a)=fun _ =>a := by
  funext j
  simp [selfBound]

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InterpolantCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma topPerm_symm {n:ℕ} (σ:Equiv.Perm (Fin n)) : (topPerm σ).symm=topPerm σ.symm := by
  apply Equiv.ext
  intro i
  apply (topPerm σ).injective
  induction i using Fin.lastCases <;> simp

end

 

 

noncomputable section
open Finset



def replaceFirst {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (v : Fin (n+1) → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K := fun i j =>
  if i = 0 then v j else if j = 0 then -v i else M i j

@[simp] theorem replaceFirst_row {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (v : Fin (n+1) → K) (j : Fin (n+1)) :
    replaceFirst M v 0 j = v j := by simp [replaceFirst]

@[simp] theorem replaceFirst_rest {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (v : Fin (n+1) → K) (i j : Fin n) :
    replaceFirst M v i.succ j.succ = M i.succ j.succ := by
  simp [replaceFirst, Fin.succ_ne_zero]

theorem replaceFirst_skew {K : Type*} [CommRing K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (hM : ∀ i j, M j i = -M i j)
    (v : Fin (n+1) → K) (hv : v 0 = 0) (i j : Fin (n+1)) :
    replaceFirst M v j i = -replaceFirst M v i j := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp only [replaceFirst, hi, hj, ite_true, ite_false]
  all_goals first | exact hM i j | simp only [hv, neg_zero, neg_neg]

theorem skew_diagonal_zero {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, M j i = -M i j) (i : Fin n) :
    M i i = 0 := by
  have h := hM i i
  have hz : (2:K)*M i i = 0 := by linear_combination h
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)








def frontBorder {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i j => Fin.cases (Fin.cases 0 (fun _ => v) j)
    (fun i => Fin.cases (-v) (M i) j) i

def backBorder {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n+1)) (Fin (n+1)) R :=
  fun i j => Fin.lastCases (Fin.lastCases 0 (fun _ => -1) j)
    (fun i => Fin.lastCases 1 (M i) j) i

@[simp] theorem frontBorder_zero_zero {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) : frontBorder M v 0 0 = 0 := rfl
@[simp] theorem frontBorder_zero_succ {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (j : Fin n) : frontBorder M v 0 j.succ = v := rfl
@[simp] theorem frontBorder_succ_zero {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (i : Fin n) : frontBorder M v i.succ 0 = -v := rfl
@[simp] theorem frontBorder_succ_succ {R : Type*} [Neg R] [Zero R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (i j : Fin n) :
    frontBorder M v i.succ j.succ = M i j := rfl
@[simp] theorem backBorder_last_last {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : backBorder M (Fin.last n) (Fin.last n) = 0 := by
  simp [backBorder]
@[simp] theorem backBorder_cast_last {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i : Fin n) : backBorder M i.castSucc (Fin.last n) = 1 := by
  simp [backBorder]
@[simp] theorem backBorder_last_cast {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (j : Fin n) : backBorder M (Fin.last n) j.castSucc = -1 := by
  simp [backBorder]
@[simp] theorem backBorder_cast_cast {R : Type*} [Neg R] [Zero R] [One R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) : backBorder M i.castSucc j.castSucc = M i j := by
  simp [backBorder]

theorem frontBorder_skew {R : Type*} [AddGroup R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (v : R) (hM : ∀ i j, M j i = -M i j) :
    ∀ i j, frontBorder M v j i = -frontBorder M v i j := by
  intro i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [frontBorder_zero_zero,frontBorder_zero_succ,frontBorder_succ_zero,
      frontBorder_succ_succ,neg_zero,neg_neg]
  exact hM _ _

theorem backBorder_skew {R : Type*} [AddGroupWithOne R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, M j i = -M i j) :
    ∀ i j, backBorder M j i = -backBorder M i j := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [backBorder_last_last,backBorder_last_cast,backBorder_cast_last,
      backBorder_cast_cast,neg_zero,neg_neg]
  exact hM _ _

@[simp] theorem rotateInv_zero (n : ℕ) : (finRotate (n+1)).symm 0 = Fin.last n := by
  apply (finRotate (n+1)).injective
  rw [Equiv.apply_symm_apply, finRotate_last]

@[simp] theorem rotateInv_succ {n : ℕ} (i : Fin n) :
    (finRotate (n+1)).symm i.succ = i.castSucc := by
  apply (finRotate (n+1)).injective
  rw [Equiv.apply_symm_apply]
  exact (finRotate_of_lt i.isLt).symm

theorem backBorder_rotate {R : Type*} [AddGroupWithOne R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    (fun i j => backBorder M ((finRotate (n+1)).symm i) ((finRotate (n+1)).symm j)) =
      frontBorder M (-1) := by
  funext i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [rotateInv_zero,rotateInv_succ,backBorder_last_last,backBorder_cast_last,
      backBorder_last_cast,backBorder_cast_cast,frontBorder_zero_zero,frontBorder_zero_succ,
      frontBorder_succ_zero,frontBorder_succ_succ,neg_neg]



def tailRotateInv (n : ℕ) : Equiv.Perm (Fin (n+2)) :=
  Equiv.Perm.decomposeFin.symm (0,(finRotate (n+1)).symm)

@[simp] theorem tailRotateInv_zero (n : ℕ) : tailRotateInv n 0 = 0 := by
  simp [tailRotateInv]
@[simp] theorem tailRotateInv_one (n : ℕ) : tailRotateInv n 1 = (Fin.last n).succ := by
  simp only [tailRotateInv,Equiv.Perm.decomposeFin_symm_apply_one,Equiv.swap_self,
    Equiv.refl_apply,rotateInv_zero]
@[simp] theorem tailRotateInv_succ_succ {n : ℕ} (i : Fin n) :
    tailRotateInv n i.succ.succ = i.castSucc.succ := by
  simp only [tailRotateInv,Equiv.Perm.decomposeFin_symm_apply_succ,Equiv.swap_self,
    Equiv.refl_apply,rotateInv_succ]







theorem back_front_row {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (t : K) (j : Fin (n+1)) :
    backBorder (frontBorder M t) 0 j.succ = Fin.lastCases 1 (fun _ => t) j := by
  change backBorder (frontBorder M t) (0 : Fin (n+1)).castSucc j.succ = _
  induction j using Fin.lastCases with
  | last => rw [Fin.succ_last,backBorder_cast_last]; simp only [Fin.lastCases_last]
  | cast j => rw [Fin.succ_castSucc,backBorder_cast_cast]; simp only [frontBorder_zero_succ,Fin.lastCases_castSucc]

theorem back_front_tail {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (t : K) (i j : Fin (n+1)) :
    backBorder (frontBorder M t) i.succ j.succ = backBorder M i j := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [Fin.succ_last,Fin.succ_castSucc,backBorder_last_last,backBorder_last_cast,
      backBorder_cast_last,backBorder_cast_cast,frontBorder_succ_succ]

theorem back_front_eq_rowAdd {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, M j i = -M i j) (t : K) :
    backBorder (frontBorder M t) =
      replaceFirst (frontBorder (backBorder M) 1)
        (fun j => if j = 0 then 0 else frontBorder (backBorder M) 1 0 j +
          (1-t)*frontBorder (backBorder M) 1 (Fin.last n).succ j) := by
  have hsk := backBorder_skew _ (frontBorder_skew M t hM)
  funext i j
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero =>
      change backBorder (frontBorder M t) (0 : Fin (n+1)).castSucc (0 : Fin (n+1)).castSucc = _
      rw [backBorder_cast_cast, frontBorder_zero_zero]
      simp only [replaceFirst, ite_true]
    | succ j =>
      rw [back_front_row]
      induction j using Fin.lastCases <;>
        simp only [replaceFirst,Fin.succ_ne_zero,ite_true,ite_false,
          frontBorder_zero_succ,frontBorder_succ_succ,backBorder_last_last,
          backBorder_last_cast,Fin.lastCases_last,Fin.lastCases_castSucc] <;> ring
  | succ i =>
    induction j using Fin.cases with
    | zero =>
      rw [hsk 0 i.succ,back_front_row]
      induction i using Fin.lastCases <;>
        simp only [replaceFirst,Fin.succ_ne_zero,ite_true,ite_false,
          frontBorder_zero_succ,frontBorder_succ_succ,backBorder_last_last,
          backBorder_last_cast,Fin.lastCases_last,Fin.lastCases_castSucc] <;> ring
    | succ j => rw [back_front_tail]; simp [replaceFirst]



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FirstFlatSpecialization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open Finset



def scalarEdgeDegree {n : ℕ} (k : Fin n) (i j : Fin (n+n%2)) : ℕ :=
  if i.val < n ∧ j.val < n ∧ (i.val = k.val ∨ j.val = k.val) then 2 else 0

theorem scalarEdgeDegree_symm {n : ℕ} (k : Fin n) (i j : Fin (n+n%2)) :
    scalarEdgeDegree k i j = scalarEdgeDegree k j i := by
  unfold scalarEdgeDegree
  congr 1
  apply propext
  tauto









theorem coeff_prod_budget {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (P : ι → Polynomial R) (w : ι → ℕ)
    (hP : ∀ i ∈ s, (P i).natDegree ≤ w i) :
    (∏ i ∈ s, P i).coeff (∑ i ∈ s, w i) = ∏ i ∈ s, (P i).coeff (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.prod_insert hi]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hP i (by simp))]
    · rw [ih (fun j hj => hP j (by simp [hj]))]
    · exact (Polynomial.natDegree_prod_le s P).trans
        (Finset.sum_le_sum (fun j hj => hP j (by simp [hj])))



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma matrix_residual_covariance {K:Type*} [CommRing K] {ι:Type*} [Fintype ι]
    (T R S:Matrix ι ι K) (v w:ι → K) (D:K)
    (hv:v=R.mulVec w) (hTR:T*R=R*S) :
    (fun p =>D*(T.mulVec v p-v p))=R.mulVec (fun p =>D*(S.mulVec w p-w p)) := by
  have h1:T.mulVec v=R.mulVec (S.mulVec w) := by
    rw [hv,Matrix.mulVec_mulVec,hTR,←Matrix.mulVec_mulVec]
  rw [h1,hv]
  change D • (R.mulVec (S.mulVec w)-R.mulVec w)=R.mulVec (D • (S.mulVec w-w))
  rw [Matrix.mulVec_smul,Matrix.mulVec_sub]


end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram





noncomputable section
open scoped Classical



lemma polynomial_top_numerator {K:Type*} [CommRing K] (rr a:K) :
    ((Polynomial.X-Polynomial.C a)*(Polynomial.X+Polynomial.C a+Polynomial.C rr)).coeff 2=1 := by
  have he:(Polynomial.X-Polynomial.C a)*(Polynomial.X+Polynomial.C a+Polynomial.C rr)=
      (Polynomial.X^2:Polynomial K)+Polynomial.C rr*Polynomial.X-Polynomial.C (a*(a+rr)) := by
    simp only [map_mul,map_add]; ring
  rw [he]; simp

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarDeleteContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

section Generic
variable {K:Type*} [Field K] {n:ℕ}
abbrev PolynomialField (K:Type*) [Field K] (n:ℕ) := FractionRing (MvPolynomial (Fin n) K)
def genericConst (n:ℕ) : K →+* PolynomialField K n :=
  (algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n)).comp MvPolynomial.C
def genericVar (i:Fin n) : PolynomialField K n :=
  algebraMap (MvPolynomial (Fin n) K) (PolynomialField K n) (MvPolynomial.X i)

lemma genericVar_ne_const (i:Fin n) (z:K) : genericVar i≠genericConst n z := by
  intro h
  have hh:=IsFractionRing.injective (MvPolynomial (Fin n) K) (PolynomialField K n) h
  have he:=congrArg (MvPolynomial.eval (fun _ => z+1)) hh
  simp at he

lemma genericVar_inj (n:ℕ) : Function.Injective (@genericVar K _ n) :=
  (IsFractionRing.injective _ _).comp MvPolynomial.X_injective

end Generic



end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ScalarMergeTrig
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section


lemma scalar_merge_delete_factor_algebra {K:Type*} [Field K] [CharZero K]
    (dd t x y g h:K) (hd:dd^2=1/2)
    (hs:x+y=2*dd*t) (hp:x*y=t^2-dd^2)
    (hg:g^2+h^2+2*dd*g*h-dd^2=0) :
    (x-(-2*dd*g-h))*(x-(-2*dd*h-g))*(y-(-2*dd*g-h))*(y-(-2*dd*h-g))=
      (t+g)*(t+h)*(t-(-2*dd*g-h))*(t-(-2*dd*h-g)) := by
  have he: (x-(-2*dd*g-h))*(x-(-2*dd*h-g))*(y-(-2*dd*g-h))*(y-(-2*dd*h-g))=
      (x*y-(-2*dd*g-h)*(x+y)+(-2*dd*g-h)^2)*
      (x*y-(-2*dd*h-g)*(x+y)+(-2*dd*h-g)^2) := by ring
  rw [he,hs,hp]
  grind






open scoped Classical

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairSelfNode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma matrixPrefix_zero_of_first {K ι:Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    {n:ℕ} (A:Fin (n+1) → Matrix ι ι K) (h:A 0=0) (k:ℕ) :
    matrixPrefix A (k+1)=0 := by
  induction k with
  | zero => simpa [matrixPrefix] using h
  | succ k ih => rw [matrixPrefix]; split_ifs <;> simp only [ih,Matrix.mul_zero]







def pairIndex (n:ℕ) : Fin (n+2) → Fin (n+1) := Fin.cons 0 (Fin.cons 0 Fin.succ)
def pairExponent (n s:ℕ) : Fin (n+2) → ℕ := fun i =>if i=1 then 3-s else 3

lemma pairExponent_le (n s:ℕ) (i:Fin (n+2)) : pairExponent n s i≤3 := by
  unfold pairExponent; split_ifs <;> omega







lemma Fin.snoc_twoCons {α:Type*} {n:ℕ} (a b y:α) (x:Fin n → α) :
    (Fin.snoc (Fin.cons a (Fin.cons b x)) y : Fin (n+3) → α)=(Fin.cons a (Fin.cons b (Fin.snoc x y)) : Fin (n+3) → α) := by
  rw [←Fin.cons_snoc_eq_snoc_cons,←Fin.cons_snoc_eq_snoc_cons]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalTorusValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

def mergeExponent (n:ℕ) : Fin (n+1) → ℕ := Fin.cons 2 (fun _ =>3)

lemma mergeExponent_le (n:ℕ) (i:Fin (n+1)) : mergeExponent n i≤3 := by
  induction i using Fin.cases <;> simp [mergeExponent]

lemma mergeExponent_mixed {n:ℕ} (i j:Fin (n+1))
    (hi:mergeExponent n i≠0 ∧ mergeExponent n i≠3)
    (hj:mergeExponent n j≠0 ∧ mergeExponent n j≠3) : i=j := by
  induction i using Fin.cases with
  | succ i => exact (hi.2 rfl).elim
  | zero => induction j using Fin.cases with
    | zero => rfl
    | succ j => exact (hj.2 rfl).elim

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ResidualParityCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical LaurentPolynomial



def residualRootPhase {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) : ℕ :=
  if j=i.castSucc then
    if k=0 then 0 else if k=1 then 8 else if k=2 then 3 else 11
  else if j=Fin.last n then
    if k=0 then 13 else if k=1 then 5 else if k=2 then 0 else 8
  else if j.val < i.val then
    if k=0 then 2 else if k=1 then 10 else if k=2 then 3 else 11
  else
    if k=0 then 14 else if k=1 then 6 else if k=2 then 13 else 5

lemma residualRootPhase_lt {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) : residualRootPhase i j k<16 := by
  unfold residualRootPhase
  split_ifs <;> norm_num

end





end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_NodalEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma functionMatrix_map_hom {K L:Type*} [CommRing K] [CommRing L] {α β:Type*}
    (f:K →+* L) (g:α → β) : (functionMatrix (K:=K) g).map f=functionMatrix (K:=L) g := by
  ext p q
  simp only [Matrix.map_apply,functionMatrix,optionMatrix]
  split_ifs <;> simp

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SplitGluing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators







def reflectExponentAt {n : ℕ} (i : Fin n) (e : Fin n → ℤ) : Fin n → ℤ :=
  Function.update e i (-e i)

@[simp] lemma reflectExponentAt_same {n : ℕ} (i : Fin n) (e : Fin n → ℤ) :
    reflectExponentAt i e i = -e i := by simp [reflectExponentAt]
@[simp] lemma reflectExponentAt_zero {n : ℕ} (i : Fin n) :
    reflectExponentAt i 0 = 0 := by ext j; simp [reflectExponentAt]
lemma reflectExponentAt_add {n : ℕ} (i : Fin n) (e f : Fin n → ℤ) :
    reflectExponentAt i (e+f) = reflectExponentAt i e + reflectExponentAt i f := by
  ext j
  by_cases h:j=i <;> simp [reflectExponentAt,h,add_comm]
@[simp] lemma reflectExponentAt_neg {n : ℕ} (i : Fin n) (e : Fin n → ℤ) :
    reflectExponentAt i (-e) = -reflectExponentAt i e := by
  ext j
  by_cases h:j=i <;> simp [reflectExponentAt,h]
@[simp] lemma reflectExponentAt_involutive {n : ℕ} (i : Fin n) (e : Fin n → ℤ) :
    reflectExponentAt i (reflectExponentAt i e) = e := by
  ext j
  by_cases h:j=i <;> simp [reflectExponentAt,h]

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ArchRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators LaurentPolynomial

abbrev ArchShiftIndex := Bool × Bool × Fin 2

def archRootShift : ArchShiftIndex → ℕ
  | (false,false,s) => s.val+2
  | (false,true,s) => s.val+10
  | (true,false,s) => 14-s.val
  | (true,true,s) => 6-s.val

abbrev ArchRootIndex (n : ℕ) := Option (Fin (n+1) × Bool × ArchShiftIndex)

end
 

 

noncomputable section
open scoped Classical BigOperators

 

def previousCoeff {K : Type*} [Semiring K] (n : ℕ) (P : Polynomial K) : K :=
  if n=0 then 0 else P.coeff (n-1)


def headPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.cases 0 (fun i => (σ i).succ)
  invFun := Fin.cases 0 (fun i => (σ.symm i).succ)
  left_inv i := by induction i using Fin.cases <;> simp
  right_inv i := by induction i using Fin.cases <;> simp

end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

def lastSwap (n : ℕ) : Equiv.Perm (Fin (n + 2)) :=
  Equiv.swap (Fin.last n).castSucc (Fin.last (n + 1))

@[simp] lemma lastSwap_old (n : ℕ) (i : Fin n) :
    lastSwap n i.castSucc.castSucc = i.castSucc.castSucc := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact Fin.castSucc_ne_last i (Fin.castSucc_injective _ h)
  · exact Fin.castSucc_ne_last _

@[simp] lemma lastSwap_middle (n : ℕ) : lastSwap n (Fin.last n).castSucc = Fin.last (n + 1) := by
  simp [lastSwap]
@[simp] lemma lastSwap_last (n : ℕ) : lastSwap n (Fin.last (n + 1)) = (Fin.last n).castSucc := by
  simp [lastSwap]
@[simp] lemma lastSwap_symm (n : ℕ) : (lastSwap n).symm = lastSwap n := rfl

@[simp] lemma kernel_self (a : ℂ) : kernel a a = 0 := by simp [kernel]

def kernelMatrix (N : ℕ) (a : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => kernel (a i) (a j)

def actualPf (N : ℕ) (a : Fin N → ℂ) : ℂ := pfaffian (pfSize N) (augmentedKernel N a)

def restrictMap (n : ℕ) : Vec (n + 1) →ₗ[ℂ] Vec n where
  toFun u i := u i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def flipLastMap (n : ℕ) : Vec (n + 1) →ₗ[ℂ] Vec (n + 1) where
  toFun u := Fin.snoc (fun i => u i.castSucc) (-u (Fin.last n))
  map_add' u v := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [add_comm]
  map_smul' t u := by ext i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [mul_neg]

@[simp] lemma restrictMap_snoc (n : ℕ) (u : Vec n) (t : ℂ) :
    restrictMap n (Fin.snoc u t) = u := by ext i; simp [restrictMap]
@[simp] lemma flipLastMap_snoc (n : ℕ) (u : Vec n) (t : ℂ) :
    flipLastMap n (Fin.snoc u t) = Fin.snoc u (-t) := by simp [flipLastMap]

def incrementLinear (N : ℕ) (a : Fin N → ℂ) : Vec (N + 1) →ₗ[ℂ] ℂ := by
  classical
  exact if Odd N then (borderLinear (kernelMatrix N a)).comp (restrictMap N)
    else -((borderLinear (border (kernelMatrix N a) (fun _ => 1))).comp (flipLastMap N))

def polyLift {n : ℕ} (L : Vec n →ₗ[ℂ] ℂ) (f : Fin n → Polynomial ℂ) : Polynomial ℂ :=
  ∑ i, C (L (standardBasis n i)) * f i

def Dpoly (a : ℂ) : Polynomial ℂ := X ^ 2 + C (2 * d * a) * X + C (a ^ 2 - d ^ 2)
def pairNumerator (a : ℂ) : Polynomial ℂ := (C a - X) * (C (a + rho) + X)
def denominatorPoly (N : ℕ) (a : Fin N → ℂ) : Polynomial ℂ := ∏ i, Dpoly (a i)
def deletedDenominator (N : ℕ) (a : Fin N → ℂ) (i : Fin N) : Polynomial ℂ :=
  ∏ j ∈ Finset.univ.erase i, Dpoly (a j)
def kernelNumerator (N : ℕ) (a : Fin N → ℂ) (i : Fin N) : Polynomial ℂ :=
  pairNumerator (a i) * deletedDenominator N a i

def clearedPf (N : ℕ) (a : Fin N → ℂ) : Polynomial ℂ :=
  polyLift (incrementLinear N a) (Fin.snoc (kernelNumerator N a) (denominatorPoly N a))

@[simp] lemma Dpoly_eval (a z : ℂ) : (Dpoly a).eval z = D a z := by simp [Dpoly, D]; ring
@[simp] lemma Dpoly_coeff (a : ℂ) : (Dpoly a).coeff 2 = 1 := by
  simp only [Dpoly, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C]
  norm_num
@[simp] lemma pairNumerator_coeff (a : ℂ) : (pairNumerator a).coeff 2 = -1 := by
  have h : (pairNumerator a).coeff (1 + 1) = (C a - X).coeff 1 * (C (a + rho) + X).coeff 1 := by
    apply coeff_mul_add_eq_of_natDegree_le <;> compute_degree!
  simpa using h

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open Polynomial

def nodalPoly (N : ℕ) (a : Fin N → ℂ) : Polynomial ℂ := ∏ i, (X - C (a i))

def prefactor (N : ℕ) (a : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, D (a i) (a j) / (a i - a j)

end
noncomputable section
open Polynomial
open scoped BigOperators

def flatC : ℂ := (Real.cos (Real.pi / 8) : ℝ)
def harmonicPoly : Polynomial ℂ := X ^ 2 * (1 - X ^ 2)
def Epoly (a : ℂ) : Polynomial ℂ := X ^ 2 - C (2 * d * a) * X + C (a ^ 2 - d ^ 2)
def perturbedRootC {N : ℕ} (a : Fin N → ℂ) : Polynomial ℂ :=
  (X - C flatC) * ∏ i, ((X - C (a i)) * Epoly (a i))
def HasProjectionC (N : ℕ) (Q : Polynomial ℂ) : Prop :=
  ∃ P J E : Polynomial ℂ,
    P.natDegree ≤ N ∧ J.natDegree ≤ N ∧ E.degree < (N : WithBot ℕ) ∧
    Q = P.comp harmonicPoly + X * J.comp harmonicPoly + X ^ 2 * E.comp harmonicPoly


def invariantFactor (a : ℂ) : Polynomial ℂ := C ((a ^ 2 - d ^ 2) ^ 2) - X

def kernelProjectP (a : ℂ) : Polynomial ℂ :=
  C (-flatC * (a ^ 2 + a * rho) * (a ^ 2 - d ^ 2)) - C (2 * d * a - rho + flatC) * X

def kernelProjectJ (a : ℂ) : Polynomial ℂ :=
  C ((a ^ 2 + a * rho) * (a ^ 2 - d ^ 2) +
    flatC * (2 * d * a * (a ^ 2 + a * rho) + rho * (a ^ 2 - d ^ 2))) + X

def kernelProjectE (a : ℂ) : Polynomial ℂ :=
  C (-2 * d * a * (a ^ 2 + a * rho) - rho * (a ^ 2 - d ^ 2) -
    flatC * (a * rho * (1 + 2 * d) + d ^ 2) + (2 * d * a - rho + flatC))

end
end StripPfaffian

namespace StripComplexification
noncomputable section
open Polynomial
open scoped BigOperators

def component (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) : Polynomial ℝ :=
  .ofFinsupp (.ofCoeff (Finsupp.mapRange l (map_zero l) p.toFinsupp.coeff))

@[simp] lemma component_coeff (l : ℂ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) (n : ℕ) :
    (component l p).coeff n = l (p.coeff n) := rfl

@[simp] lemma component_add (l : ℂ →ₗ[ℝ] ℝ) (p q : Polynomial ℂ) :
    component l (p + q) = component l p + component l q := by
  ext n
  simp

@[simp] lemma component_C (l : ℂ →ₗ[ℝ] ℝ) (c : ℂ) :
    component l (C c) = C (l c) := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [coeff_C, hn]

end
end StripComplexification

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DeficitBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators

section CauchyAlternants
open _root_.Matrix

 
def cauchyMatrix {n : ℕ} (x y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => 1 / (x i + y j)

def cauchyAlternant {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (Matrix.vandermonde x).det * (cauchyMatrix x y).det * (Matrix.vandermonde y).det

end CauchyAlternants

open Set MeasureTheory _root_.Matrix



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CauchyMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section



open Set MeasureTheory Filter
open scoped Topology

def quarticDen (r t : ℝ) : ℝ := t ^ 4 + 2 * t ^ 2 + r ^ 2
def quarticBase (r t : ℝ) : ℝ := (t ^ 2 + r) / quarticDen r t
def quarticWeighted (r t : ℝ) : ℝ := 2 * (t ^ 2 + r ^ 2) / quarticDen r t
def straightener (r t : ℝ) : ℝ := t - r / t

def uniformDen (t : ℝ) : ℝ := 2 * t ^ 4 + 4 * t ^ 2 + 1
def uniformizer (t : ℝ) : ℝ := 1 / uniformDen t

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_QuarticIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

def minusBranch (s : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt ((1 + s) / 2)) / 2)

def lBranch (x : ℝ) : ℝ := Real.sqrt (1 + Real.sqrt ((1 + 1 / x) / 2))

def squareWeight (x : ℝ) : ℝ := Real.sqrt ((1 - x) / (8 * x))

def squareUniformizer (t : ℝ) : ℝ := 1 / (1 + t ^ 2)


def realStieltjes (a : ℝ) (w : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ x in Ioo (0 : ℝ) 1, w x / (z - a * x)

def offCut (a z : ℝ) : Prop := ∀ x ∈ Icc (0 : ℝ) 1, z - a * x ≠ 0

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_StieltjesLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter
open scoped Topology




def fBranch (z : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt ((1 - 1 / z) / 2)) / 2)
def projectionF (P J E : Polynomial ℝ) (z : ℝ) : ℝ :=
  P.eval z + fBranch z * J.eval z + fBranch z ^ 2 * E.eval z
def projectionD (J E : Polynomial ℝ) (z : ℝ) : ℝ :=
  J.eval z + lBranch z * E.eval z

end

 

noncomputable section
open Polynomial Set Filter
open scoped Topology

 
def tildePoly (N : ℕ) (p : Polynomial ℝ) : Polynomial ℝ :=
  reflect N (p.comp (Polynomial.C (1 / 8) * (1 + X)))


def highBranch (u : ℝ) : ℝ := Real.sqrt ((1 + Real.sqrt ((1 - u) / 2)) / 2)
def lowBranch (u : ℝ) : ℝ := Real.sqrt ((1 - Real.sqrt ((1 - u) / 2)) / 2)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_Trigonometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open Polynomial Set MeasureTheory Filter
open scoped Topology BigOperators



def rootPolynomial (N : ℕ) : Polynomial ℝ :=
  (X - Polynomial.C C) ^ (2 * N + 1) * (X - Polynomial.C c) ^ N

theorem rootPolynomial_monic (N : ℕ) : (rootPolynomial N).Monic :=
  ((monic_X_sub_C C).pow _).mul ((monic_X_sub_C c).pow _)

theorem rootPolynomial_natDegree (N : ℕ) : (rootPolynomial N).natDegree = 3 * N + 1 := by
  rw [rootPolynomial, ((monic_X_sub_C C).pow _).natDegree_mul ((monic_X_sub_C c).pow _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  omega

theorem rootPolynomial_degree (N : ℕ) : (rootPolynomial N).degree = ((3 * N + 1 : ℕ) : WithBot ℕ) := by
  rw [degree_eq_natDegree (rootPolynomial_monic N).ne_zero, rootPolynomial_natDegree]

abbrev ProjectionSpace (N : ℕ) :=
  (degreeLT ℝ (N + 1)) × (degreeLT ℝ (N + 1)) × (degreeLT ℝ N)

def projectionMap (N : ℕ) : ProjectionSpace N →ₗ[ℝ] Polynomial ℝ where
  toFun t := t.1.val.comp harmonicCoordinate + X * t.2.1.val.comp harmonicCoordinate +
    X ^ 2 * t.2.2.val.comp harmonicCoordinate
  map_add' t u := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_comp]
    ring
  map_smul' a t := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_comp,
      smul_add, mul_smul_comm, RingHom.id_apply]

def projectionRemainder (N : ℕ) : ProjectionSpace N →ₗ[ℝ] degreeLT ℝ (3 * N + 1) where
  toFun t := ⟨(projectionMap N t) %ₘ rootPolynomial N, mem_degreeLT.2 (by
    have h := degree_modByMonic_lt (projectionMap N t) (rootPolynomial_monic N)
    rwa [rootPolynomial_degree] at h)⟩
  map_add' t u := by
    apply Subtype.ext
    simp only [map_add, add_modByMonic, Submodule.coe_add]
  map_smul' a t := by
    apply Subtype.ext
    simp only [map_smul, smul_modByMonic, Submodule.coe_smul, RingHom.id_apply]

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PolynomialDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/

namespace CriticalStrip
noncomputable section

open Polynomial Set MeasureTheory Filter _root_.Matrix
open scoped Topology BigOperators

 

def perturbedRoot {N : ℕ} (a : Fin N → ℝ) : Polynomial ℝ :=
  (X - Polynomial.C C) * ∏ i, ((X - Polynomial.C (a i)) *
    (X^2 - Polynomial.C (2*d*a i)*X + Polynomial.C ((a i)^2-d^2)))

end
end CriticalStrip


end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SpectralComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open Polynomial Set MeasureTheory Filter _root_.Matrix StripComplexification
open scoped Topology BigOperators

def rootPolynomialC (N : ℕ) : Polynomial ℂ :=
  (CriticalStrip.rootPolynomial N).map Complex.ofRealHom

def homogeneousQC (N : ℕ) (g : Polynomial ℂ) : Polynomial ℂ := rootPolynomialC N * g

def PerturbedMonicProblemC {N : ℕ} (a : Fin N → ℂ) (g : Polynomial ℂ) : Prop :=
  g.Monic ∧ g.natDegree = N ∧ HasProjectionC N (perturbedRootC a * g)

theorem harmonic_natDegree : harmonicPoly.natDegree = 4 := by
  unfold harmonicPoly
  compute_degree <;> norm_num

theorem degree_lt_natDegree_le_pred {N : ℕ} {p : Polynomial ℂ}
    (hN : 1 ≤ N) (hp : p.degree < (N : WithBot ℕ)) : p.natDegree ≤ N - 1 := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have h : p.natDegree < N := (natDegree_lt_iff_degree_lt hp0).2 hp
  omega

 
theorem projection_natDegree_le (N : ℕ) (hN : 1 ≤ N) (P J E : Polynomial ℂ)
    (hP : P.natDegree ≤ N) (hJ : J.natDegree ≤ N) (hE : E.degree < (N : WithBot ℕ)) :
    (P.comp harmonicPoly + X * J.comp harmonicPoly +
      X ^ 2 * E.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
  have he := degree_lt_natDegree_le_pred hN hE
  have hp' : (P.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
    rw [natDegree_comp, harmonic_natDegree]
    omega
  have hj' : (X * J.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X, natDegree_comp, harmonic_natDegree]
    omega
  have he' : (X ^ 2 * E.comp harmonicPoly).natDegree ≤ 4 * N + 1 := by
    apply le_trans natDegree_mul_le
    rw [natDegree_X_pow, natDegree_comp, harmonic_natDegree]
    omega
  exact le_trans (natDegree_add_le _ _) (max_le (le_trans (natDegree_add_le _ _) (max_le hp' hj')) he')

abbrev ProjectionSpace (N : ℕ) :=
  (degreeLT ℂ (N + 1)) × (degreeLT ℂ (N + 1)) × (degreeLT ℂ N)

def projectionMap (N : ℕ) : ProjectionSpace N →ₗ[ℂ] Polynomial ℂ where
  toFun t := t.1.val.comp harmonicPoly + X * t.2.1.val.comp harmonicPoly +
    X ^ 2 * t.2.2.val.comp harmonicPoly
  map_add' t u := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_comp]
    ring
  map_smul' a t := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_comp,
      smul_add, mul_smul_comm, RingHom.id_apply]

theorem natDegree_le_of_mem_degreeLT {N : ℕ} {p : Polynomial ℂ}
    (hp : p ∈ degreeLT ℂ (N + 1)) : p.natDegree ≤ N := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact Nat.lt_succ_iff.1 ((natDegree_lt_iff_degree_lt hp0).2 (mem_degreeLT.1 hp))

theorem Epoly_natDegree_le (a : ℂ) : (Epoly a).natDegree ≤ 2 := by
  unfold Epoly
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_mul_le).trans (by simp only [natDegree_C, natDegree_X]; omega)
  · simp only [natDegree_C]; omega

theorem perturbedRootC_natDegree_le {N : ℕ} (a : Fin N → ℂ) :
    (perturbedRootC a).natDegree ≤ 3*N+1 := by
  have hp (i : Fin N) : ((X - C (a i)) * Epoly (a i)).natDegree ≤ 3 := by
    exact (natDegree_mul_le).trans (by
      rw [natDegree_X_sub_C]
      have := Epoly_natDegree_le (a i)
      omega)
  have hh : (∏ i : Fin N, (X - C (a i)) * Epoly (a i)).natDegree ≤ N*3 := by
    apply (natDegree_prod_le (s := Finset.univ) (f := fun i : Fin N =>
      (X - C (a i)) * Epoly (a i))).trans
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_id] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  rw [perturbedRootC]
  exact (natDegree_mul_le).trans (by rw [natDegree_X_sub_C]; omega)

abbrev SystemSpace (N : ℕ) := ProjectionSpace N × degreeLT ℂ N
abbrev SystemIndex (N : ℕ) := (Fin (N+1) ⊕ (Fin (N+1) ⊕ Fin N)) ⊕ Fin N
def systemBasis (N : ℕ) : Module.Basis (SystemIndex N) ℂ (SystemSpace N) :=
  ((degreeLT.basis ℂ (N+1)).prod ((degreeLT.basis ℂ (N+1)).prod (degreeLT.basis ℂ N))).prod
    (degreeLT.basis ℂ N)
def systemIndexEquiv (N : ℕ) : SystemIndex N ≃ Fin (4*N+2) :=
  Fintype.equivFinOfCardEq (by simp [SystemIndex]; omega)
def targetBasis (N : ℕ) : Module.Basis (SystemIndex N) ℂ (degreeLT ℂ (4*N+2)) :=
  (degreeLT.basis ℂ (4*N+2)).reindex (systemIndexEquiv N).symm

def perturbedSystem {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) :
    SystemSpace N →ₗ[ℂ] degreeLT ℂ (4*N+2) where
  toFun t := ⟨projectionMap N t.1 - perturbedRootC a*t.2.val, mem_degreeLT.2 (by
    apply (degree_le_natDegree).trans_lt
    apply WithBot.coe_lt_coe.2
    simp only [Nat.cast_id]
    apply lt_of_le_of_lt (natDegree_sub_le _ _)
    apply max_lt
    · have hh := projection_natDegree_le N hN t.1.1.val t.1.2.1.val t.1.2.2.val
        (natDegree_le_of_mem_degreeLT t.1.1.property) (natDegree_le_of_mem_degreeLT t.1.2.1.property)
        (mem_degreeLT.1 t.1.2.2.property)
      exact lt_of_le_of_lt hh (by omega)
    · have hg : t.2.val.natDegree < N := by
        by_cases hz : t.2.val=0
        · simp [hz]; omega
        exact (natDegree_lt_iff_degree_lt hz).2 (mem_degreeLT.1 t.2.property)
      exact lt_of_le_of_lt natDegree_mul_le (by have := perturbedRootC_natDegree_le a; omega))⟩
  map_add' t u := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]
    ring
  map_smul' r t := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, Submodule.coe_smul, smul_sub,
      mul_smul_comm, RingHom.id_apply]

def CoeffContinuous {A : Type*} [TopologicalSpace A] (p : A → Polynomial ℂ) : Prop :=
  ∀ k, Continuous (fun a => (p a).coeff k)

def systemMatrix {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : Matrix (SystemIndex N) (SystemIndex N) ℂ :=
  LinearMap.toMatrix (systemBasis N) (targetBasis N) (perturbedSystem hN a)

def systemRHS {N : ℕ} (a : Fin N → ℂ) : degreeLT ℂ (4*N+2) :=
  ⟨perturbedRootC a * X^N, mem_degreeLT.2 (by
    apply (degree_le_natDegree).trans_lt
    apply WithBot.coe_lt_coe.2
    simp only [Nat.cast_id]
    have hh := natDegree_mul_le (p := perturbedRootC a) (q := (X : Polynomial ℂ)^N)
    have hd := perturbedRootC_natDegree_le a
    simp only [natDegree_X_pow] at hh
    omega)⟩
def rhsVector {N : ℕ} (a : Fin N → ℂ) : SystemIndex N → ℂ :=
  (targetBasis N).equivFun (systemRHS a)
def solutionVector {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : SystemIndex N → ℂ :=
  (systemMatrix hN a)⁻¹ *ᵥ rhsVector a
def solutionTuple {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : SystemSpace N :=
  (systemBasis N).equivFun.symm (solutionVector hN a)
def confluentPolynomial {N : ℕ} (hN : 1 ≤ N) (a : Fin N → ℂ) : Polynomial ℂ :=
  X^N + (solutionTuple hN a).2.val



end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianConfluentLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory

 
theorem rho_pos : 0 < rho := by
  unfold rho
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by positivity))

@[simp] theorem K_zero (N : ℕ) : K N 0 = 0 := by
  simp [K, archWeight]


end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_ColumnGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open scoped BigOperators
open Set MeasureTheory

 
def laguerreDomain (N : ℕ) : Set (Fin N → ℝ) :=
  {r | StrictMono r ∧ ∀ i, 0 < r i}

def laguerreWeight (a x : ℝ) : ℝ := x ^ (a - 1) * Real.exp (-x)

def laguerreDensity (N : ℕ) (a : ℝ) (r : Fin N → ℝ) : ℝ :=
  (∏ i, laguerreWeight a (r i)) *
    ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (r i) (r j)

def laguerreNormalizer (N : ℕ) (a : ℝ) : ℝ :=
  ∫ r in laguerreDomain N, laguerreDensity N a r

def laguerreExpectation (N : ℕ) (a : ℝ) (f : (Fin N → ℝ) → ℝ) : ℝ :=
  (∫ r in laguerreDomain N, f r * laguerreDensity N a r) / laguerreNormalizer N a



def laguerreLaw (N : ℕ) (a : ℝ) : Measure (Fin N → ℝ) :=
  (ENNReal.ofReal (laguerreNormalizer N a))⁻¹ •
    (volume.restrict (laguerreDomain N)).withDensity
      (fun r => ENNReal.ofReal (laguerreDensity N a r))

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TailIntegrals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory



def laguerreCut (n k : ℕ) (h : ℝ) : Set (Fin n → ℝ) :=
  laguerreDomain n ∩ {r | ∀ i, i.val < k → r i < h}

def laguerreCutIntegral (n : ℕ) (a : ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  ∫ r in laguerreCut n k h, laguerreDensity n a r


def laguerreDimension (a : ℝ) (k : ℕ) : ℝ := a * k + (k : ℝ) * (k - 1) / 2



def laguerreSmallCoefficient (N : ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  laguerreNormalizer (N - k) (a + k) /
    (laguerreNormalizer N a * ∏ j : Fin k, (a + j.val))

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter

 
def orderedPairKernel (x y : ℝ) : ℝ := (max (y - x) 0) ^ 2 / (y + x)

def coordinateBox (ι : Type*) (I : Set ℝ) : Set (ι → ℝ) := {x | ∀ i, x i ∈ I}

 

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PositiveAssociation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter



def orderedProductDensity (N : ℕ) (w : Fin N → ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  (∏ i, w i (x i)) * ∏ i, ∏ j ∈ Finset.Ioi i, orderedPairKernel (x i) (x j)




def orderedChamber (N : ℕ) (I : Set ℝ) : Set (Fin N → ℝ) :=
  {x | StrictMono x ∧ ∀ i, x i ∈ I}

def rawProductDensity (N : ℕ) (w : Fin N → ℝ → ℝ) (x : Fin N → ℝ) : ℝ :=
  (∏ i, w i (x i)) * ∏ i, ∏ j ∈ Finset.Ioi i, pairKernel (x i) (x j)



end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_DensityExhaustion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory Filter




def cutoffRamp (n : ℕ) (R x : ℝ) : ℝ := min 1 (max 0 ((n + 1 : ℝ) * (R - x)))



def cutoffEvent (N : ℕ) (R : ℝ) : Set (Fin N → ℝ) := coordinateBox (Fin N) (Iio R)

def cutoffProduct (N n : ℕ) (R : ℝ) (r : Fin N → ℝ) : ℝ :=
  ∏ i, cutoffRamp n R (r i)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CoordinateBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators
open Set MeasureTheory



def mobiusCoordinate (z : ℝ) : ℝ := 2 * z / (1 + z)


def mobiusPairFactor (x y : ℝ) : ℝ := (1 + 2 * x * y / (x + y))⁻¹

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_WeightComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip

noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter

 
def scaledLaguerreWeight (a β x : ℝ) : ℝ := x ^ (a - 1) * Real.exp (-(β * x))

def scaledLaguerreDensity (N : ℕ) (a β : ℝ) : (Fin N → ℝ) → ℝ :=
  rawProductDensity N (fun _ => scaledLaguerreWeight a β)

 

def laguerreDensityScale (N : ℕ) (a β : ℝ) : ℝ :=
  (∏ _ : Fin N, β ^ (a - 1)) * ∏ i : Fin N, ∏ _j ∈ Finset.Ioi i, β

abbrev inverseQuarterStatistic (N : ℕ) (y : Fin N → ℝ) : ℝ :=
  (∑ i, (y i)⁻¹) ^ (1 / 4 : ℝ)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter






def mobiusMap (N : ℕ) (z : Fin N → ℝ) : Fin N → ℝ := fun i => mobiusCoordinate (z i)


def mobiusDifferential (N : ℕ) (z : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.toSpanSingleton ℝ (2 / (1 + z i)^2)).comp (ContinuousLinearMap.proj i)

def mobiusJacobian (N : ℕ) (z : Fin N → ℝ) : ℝ := ∏ i, 2 / (1 + z i)^2


def mobiusDensityConstant (N : ℕ) : ℝ :=
  (∏ _ : Fin N, (2 : ℝ)) * ∏ i : Fin N, ∏ _j ∈ Finset.Ioi i, (2 : ℝ)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InverseIntegrability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators Pointwise
open Set MeasureTheory Filter

abbrev mobiusInverseQuarter {N : ℕ} (i : Fin N) (z : Fin N → ℝ) : ℝ :=
  (mobiusCoordinate (z i)) ^ (-(1/4:ℝ))

end
end CriticalStrip

 

namespace StripPfaffian
noncomputable section
open scoped BigOperators _root_.Matrix

def schurComplement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u v : Vec n) (t : ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => A i j - (u i * v j - v i * u j) / t

def eliminatingShear {n : ℕ} (u v : Vec n) (t : ℂ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ :=
  Fin.snoc
    (Fin.snoc
      (fun i : Fin n => Fin.snoc (Fin.snoc (fun j => if i = j then (1 : ℂ) else 0) (-v i / t)) (u i / t))
      (Fin.snoc (Fin.snoc (fun _ : Fin n => (0 : ℂ)) 1) 0))
    (Fin.snoc (Fin.snoc (fun _ : Fin n => (0 : ℂ)) 0) 1)

end

noncomputable section
open scoped BigOperators

def schurEntry (x y : ℂ) : ℂ := (y - x) / (x + y)
def schurMatrix {n : ℕ} (x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => schurEntry (x i) (x j)
def schurProduct {n : ℕ} (x : Fin n → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, schurEntry (x i) (x j)


end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SchurIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open MeasureTheory Set
open scoped BigOperators

def gammaLaplace (p q : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  laguerreWeight p z.1.1 * laguerreWeight q z.1.2 * z.1.1 *
    Real.exp (-(z.1.1 + z.1.2) * z.2)



def gammaSkewIntegrand (p q : ℝ) (rs : ℝ × ℝ) : ℝ :=
  laguerreWeight p rs.1 * laguerreWeight q rs.2 * ((rs.2-rs.1)/(rs.2+rs.1))

end
end CriticalStrip

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

def laguerreMomentMatrix (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((∫ rs, gammaSkewIntegrand (a+i.val) (a+j.val) rs ∂μ₊.prod μ₊) : ℝ)

def laguerreMomentColumn (n : ℕ) (a : ℝ) : Fin n → ℂ :=
  fun i => ((∫ x in Ioi 0, laguerreWeight (a+i.val) x) : ℝ)

 

def laguerreNormalizerProduct (n : ℕ) (a : ℝ) : ℝ :=
  (∏ i : Fin n, Real.Gamma (a+i.val)) *
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((j.val:ℝ)-i.val)/(2*a+i.val+j.val)

end
end CriticalStrip



end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PairCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
def pairArrayEquiv (α : Type*) (m : ℕ) : (Fin (m*2) → α) ≃ (Fin m → α × α) :=
  ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl α)).trans
    (Equiv.curry (Fin m) (Fin 2) α)).trans
    (Equiv.piCongrRight (fun _ => finTwoArrowEquiv α))

def pairLeft {m : ℕ} (i : Fin m) : Fin (m*2) := finProdFinEquiv (i, 0)
def pairRight {m : ℕ} (i : Fin m) : Fin (m*2) := finProdFinEquiv (i, 1)

@[simp] lemma pairArrayEquiv_apply {α : Type*} {m : ℕ} (v : Fin (m*2) → α) (i : Fin m) :
    pairArrayEquiv α m v i = (v (pairLeft i), v (pairRight i)) := rfl

def permInjectiveEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃
    {v : Fin n → Fin n // Function.Injective v} where
  toFun σ := ⟨σ, σ.injective⟩
  invFun v := Equiv.ofBijective v.val (Finite.injective_iff_bijective.mp v.property)
  left_inv σ := by ext i; rfl
  right_inv v := by ext i; rfl

def pairEntries {m : ℕ} (A : Matrix (Fin (m*2)) (Fin (m*2)) ℂ) : ℂ :=
  ∏ i : Fin m, A (pairLeft i) (pairRight i)



end

 

noncomputable section
open scoped BigOperators
open MeasureTheory Set

@[simp] lemma pairArrayEquiv_symm_left {α : Type*} {m : ℕ} (p : Fin m → α × α) (i : Fin m) :
    (pairArrayEquiv α m).symm p (pairLeft i) = (p i).1 := by
  exact congrArg (fun v => (v i).1) ((pairArrayEquiv α m).apply_symm_apply p)

@[simp] lemma pairArrayEquiv_symm_right {α : Type*} {m : ℕ} (p : Fin m → α × α) (i : Fin m) :
    (pairArrayEquiv α m).symm p (pairRight i) = (p i).2 := by
  exact congrArg (fun v => (v i).2) ((pairArrayEquiv α m).apply_symm_apply p)

def pairArrayMeasurableEquiv (α : Type*) [MeasurableSpace α] (m : ℕ) :
    (Fin (m*2) → α) ≃ᵐ (Fin m → α × α) where
  toEquiv := pairArrayEquiv α m
  measurable_toFun := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun v : Fin (m*2) → α => (v (pairLeft i), v (pairRight i)))
    fun_prop
  measurable_invFun := by
    apply Measurable.of_eval
    intro j
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective j
    fin_cases j
    · change Measurable (fun p => (pairArrayEquiv α m).symm p (pairLeft i))
      simp only [pairArrayEquiv_symm_left]
      fun_prop
    · change Measurable (fun p => (pairArrayEquiv α m).symm p (pairRight i))
      simp only [pairArrayEquiv_symm_right]
      fun_prop

def evaluationMatrix {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ) (x : Fin n → α) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => φ i (x j)

def doubleIntegrand {α : Type*} {n : ℕ} (φ : Fin n → α → ℂ) (k : α → α → ℂ)
    (i j : Fin n) (rs : α × α) : ℂ := φ i rs.1 * k rs.1 rs.2 * φ j rs.2

def doubleMomentMatrix {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    (φ : Fin n → α → ℂ) (k : α → α → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ∫ rs, doubleIntegrand φ k i j rs ∂μ.prod μ

def oddPairEntries {m : ℕ} (A : Matrix (Fin (m*2+1)) (Fin (m*2+1)) ℂ)
    (u : Fin (m*2+1) → ℂ) : ℂ :=
  (∏ k : Fin m, A (pairLeft k).castSucc (pairRight k).castSucc) * u (Fin.last (m*2))

end
end StripPfaffian

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_BoundaryTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.FiniteBranchTree
noncomputable section
open scoped BigOperators Classical

variable {V S : Type*} [DecidableEq V]

 

def leaves (vertex : S → V) (next : S → Bool → S) (free : Finset V) (s : S) :
    Finset (List Bool) :=
  if _h : vertex s ∈ free then
    (leaves vertex next (free.erase (vertex s)) (next s false)).image (List.cons false) ∪
      (leaves vertex next (free.erase (vertex s)) (next s true)).image (List.cons true)
  else {[]}
termination_by free.card
decreasing_by all_goals exact Finset.card_erase_lt_of_mem _h

 
def wordWeight (w : Bool → ℂ) : List Bool → ℂ
  | [] => 1
  | b::l => w b * wordWeight w l

@[simp] lemma wordWeight_nil (w : Bool → ℂ) : wordWeight w [] = 1 := rfl
@[simp] lemma wordWeight_cons (w : Bool → ℂ) (b : Bool) (l : List Bool) :
    wordWeight w (b::l) = w b * wordWeight w l := rfl


def visited (vertex : S → V) (next : S → Bool → S) (s : S) : List Bool → List V
  | [] => []
  | b::l => vertex s :: visited vertex next (next s b) l

 
def terminal (next : S → Bool → S) (s : S) : List Bool → S
  | [] => s
  | b::l => terminal next (next s b) l

omit [DecidableEq V] in
@[simp] lemma visited_length (vertex : S → V) (next : S → Bool → S)
    (s : S) (l : List Bool) : (visited vertex next s l).length = l.length := by
  induction l generalizing s with
  | nil => rfl
  | cons b l ih => simp only [visited,List.length_cons,ih]

omit [DecidableEq V] in
lemma visited_head (vertex : S → V) (next : S → Bool → S) (s : S) (l : List Bool)
    (hl : l ≠ []) : (visited vertex next s l).head? = some (vertex s) := by
  cases l with
  | nil => exact (hl rfl).elim
  | cons b l => rfl



def exitMass (vertex : S → V) (next : S → Bool → S) (w : Bool → ℂ)
    (D : Finset V) (s : S) : ℂ :=
  ∑ l ∈ (leaves vertex next D s).filter (fun l => vertex (terminal next s l) ∉ D), wordWeight w l

def collisionMass (vertex : S → V) (next : S → Bool → S) (w : Bool → ℂ)
    (D : Finset V) (s : S) : ℂ :=
  ∑ l ∈ (leaves vertex next D s).filter (fun l => vertex (terminal next s l) ∈ D), wordWeight w l



end
end CriticalStrip.FiniteBranchTree

 

 

 

namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped BigOperators Classical
open FiniteBranchTree

abbrev Vertex := ℤ × ℤ × Bool
abbrev State := Vertex × Fin 3

def neighbor (v : Vertex) (p : Fin 3) : Vertex :=
  if v.2.2 then
    if p = 0 then (v.1,v.2.1-1,false)
    else if p = 1 then (v.1-1,v.2.1,false) else (v.1,v.2.1,false)
  else
    if p = 0 then (v.1,v.2.1+1,true)
    else if p = 1 then (v.1+1,v.2.1,true) else (v.1,v.2.1,true)

lemma neighbor_reverse (v : Vertex) (p : Fin 3) : neighbor (neighbor v p) p = v := by
  rcases v with ⟨i,j,b⟩
  cases b <;> fin_cases p <;> simp [neighbor]

lemma neighbor_injective (v : Vertex) : Function.Injective (neighbor v) := by
  rcases v with ⟨i,j,b⟩
  intro p q h
  cases b <;> fin_cases p <;> fin_cases q <;> simp_all [neighbor,Prod.mk.injEq] <;> omega

 

def outgoing (p : Fin 3) (b : Bool) : Fin 3 := if b then p+1 else p+2

def next (s : State) (b : Bool) : State :=
  let q := outgoing s.2 b
  (neighbor s.1 q,q)

lemma outgoing_ne (p : Fin 3) (b : Bool) : outgoing p b ≠ p := by
  cases b <;> fin_cases p <;> decide

lemma outgoing_injective (p : Fin 3) : Function.Injective (outgoing p) := by
  intro b c h
  cases b <;> cases c <;> fin_cases p <;> simp_all [outgoing]

lemma outgoing_exhaust (p q : Fin 3) (h : q ≠ p) : ∃! b : Bool, outgoing p b = q := by
  fin_cases p <;> fin_cases q <;> simp_all [outgoing,ExistsUnique]

lemma next_injective (s : State) : Function.Injective (fun b => (next s b).1) := by
  intro b c h
  exact outgoing_injective s.2 (neighbor_injective s.1 h)

 
def sign (b : Bool) : ℤ := if b then 1 else -1

def turn : List Bool → ℤ
  | [] => 0
  | b::l => sign b + turn l


def words (D : Finset Vertex) (s : State) : Finset (List Bool) := leaves Prod.fst next D s


lemma visited_chain (s : State) (l : List Bool) :
    (visited Prod.fst next s l).IsChain (fun v w => ∃ p, neighbor v p=w) := by
  induction l generalizing s with
  | nil => simp [visited]
  | cons b l ih =>
    cases l with
    | nil => simp [visited]
    | cons c l =>
      apply List.isChain_cons_cons.mpr
      exact ⟨⟨outgoing s.2 b,rfl⟩,ih _⟩










def back (s : State) : State := (neighbor s.1 s.2,s.2)

@[simp] lemma back_back (s : State) : back (back s) = s := by
  simp only [back,neighbor_reverse]

@[simp] lemma back_next (s : State) (b : Bool) :
    back (next s b) = (s.1,outgoing s.2 b) := by
  simp only [back,next,neighbor_reverse]


def reverseTurns (l : List Bool) : List Bool := l.reverse.map Bool.not



def reverseCycle : List Bool → List Bool
  | [] => []
  | b::l => (!b)::reverseTurns l

end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_CollisionLeaf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

lemma lastVisited_mem (s : State) (l : List Bool) (hl : l ≠ []) :
    (back (terminal next s l)).1 ∈ visited Prod.fst next s l := by
  induction l generalizing s with
  | nil => exact (hl rfl).elim
  | cons b l ih =>
    cases l with
    | nil => simp only [terminal,back_next,visited,List.mem_cons,true_or]
    | cons c l => exact List.mem_cons_of_mem _ (ih _ (by simp))


def collisionIndex (s : State) (l : List Bool) : ℕ :=
  (visited Prod.fst next s l).idxOf (terminal next s l).1

def collisionReverse (s : State) (l : List Bool) : List Bool :=
  l.take (collisionIndex s l) ++ reverseCycle (l.drop (collisionIndex s l))

end
end CriticalStrip.HoneycombBranch

 

 

 

namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Pairing

def turnOrder {n : ℕ} (i j : Fin n) : ℤ :=
  if i < j then 1 else if j < i then -1 else 0

def arcTurn {n : ℕ} (g : Fin n → ℤ) (i j : Fin n) : ℤ :=
  g j - g i - 3 * turnOrder i j

end Pairing

 

 

 


namespace Graph

variable {V : Type*}
  {n : ℕ}
  {r : V → V → Prop}
  [Std.Symm r]
  {b : Fin n → V}

def boundaryConstant (b : Fin n → V) (r : V → V → Prop) (f : Fin n → ℤ) (v : V) : ℤ :=
  if h : ∃ i, Relation.ReflTransGen r v (b i) then f (Classical.choose h) else 0

end Graph
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RealEvaluation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped BigOperators Classical
open Finset

def anglePhase (u : ℝ) : ℂ := Complex.exp ((u:ℂ)*Complex.I)

@[simp] lemma anglePhase_ne_zero (u : ℝ) : anglePhase u≠0 := Complex.exp_ne_zero _
@[simp] lemma anglePhase_zero : anglePhase 0=1 := by simp [anglePhase]

def angleCharacter {n : ℕ} (u : Fin n → ℝ) : Multiplicative (Fin n → ℤ) →* ℂ where
  toFun e := ∏ i,anglePhase (u i)^e.toAdd i
  map_one' := by simp
  map_mul' e f := by
    change (∏i,anglePhase (u i)^(e.toAdd i+f.toAdd i))=_
    simp only [zpow_add₀ (anglePhase_ne_zero _),prod_mul_distrib]

end
end CriticalStrip.Diagram

 

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open Filter _root_.Matrix
open scoped BigOperators Topology Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Nonnegative (Q : Matrix ι ι ℝ) : Prop := ∀ i j, 0≤Q i j

def SummablePowers (Q : Matrix ι ι ℝ) : Prop := ∀ i j, Summable (fun k : ℕ => (Q^k) i j)

def Accessible (Q : Matrix ι ι ℝ) (v : ι → ℝ) : Prop :=
  ∀ i, ∃ k : ℕ, 0<(Q^k).mulVec v i

def HasSupervector (Q : Matrix ι ι ℝ) : Prop :=
  ∃ z : ι → ℝ, (∀i,0<z i) ∧ ∀i,Q.mulVec z i<z i

end
end CriticalStrip.PositiveMatrix

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombTiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/





namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

lemma atMostTwo_of_three {V : Type*} {r : V → V → Prop} {v a b c : V}
    {A B C : Prop} (h₃ : ¬(A ∧ B ∧ C))
    (h : ∀ w, r v w → (w=a ∧ A) ∨ (w=b ∧ B) ∨ (w=c ∧ C)) :
    ∀ {x y z}, r v x → r v y → r v z → x≠y → z=x ∨ z=y := by
  intro x y z hx hy hz hxy
  rcases h x hx with ⟨rfl,hx⟩ | ⟨rfl,hx⟩ | ⟨rfl,hx⟩ <;>
    rcases h y hy with ⟨rfl,hy⟩ | ⟨rfl,hy⟩ | ⟨rfl,hy⟩ <;>
    rcases h z hz with ⟨rfl,hz⟩ | ⟨rfl,hz⟩ | ⟨rfl,hz⟩ <;> tauto

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PfaffianIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
open MeasureTheory Set

def singleMoment {α : Type*} [MeasurableSpace α] {n : ℕ} (μ : Measure α)
    (φ : Fin n → α → ℂ) (g : α → ℂ) : Fin n → ℂ :=
  fun i => ∫ t, φ i t * g t ∂μ

end
end StripPfaffian



namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

def laguerrePhi (n : ℕ) (a : ℝ) (i : Fin n) (x : ℝ) : ℂ := laguerreWeight (a+i.val) x

def laguerreEvenIntegrand (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : ℂ :=
  (evaluationMatrix (laguerrePhi n a) x).det *
    pfaffian n (schurMatrix (fun i => (x i : ℂ)))

def laguerreOddIntegrand (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : ℂ :=
  (evaluationMatrix (laguerrePhi n a) x).det *
    pfaffian (n+1) (border (schurMatrix (fun i => (x i : ℂ))) (fun _ => 1))

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_LaguerreNormalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

def gammaPhi {n : ℕ} (q : Fin n → ℝ) (i : Fin n) (x : ℝ) : ℂ := laguerreWeight (q i) x

def gammaSchurProduct {n : ℕ} (q : Fin n → ℝ) : ℝ :=
  (∏ i, Real.Gamma (q i)) * (∏ i, ∏ j ∈ Finset.Ioi i, (q j - q i)/(q i + q j))

end

noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

 
def inverseExponents (n : ℕ) (a : ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (a-1) (fun i => a+(i.val+1))


end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_InverseMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian






def minTilt (s r : ℝ) : ℝ := (max (1-s/r) 0)^2 / (1+s/r)
def minTiltProduct (n : ℕ) (s : ℝ) (r : Fin n → ℝ) : ℝ := ∏ i, minTilt s (r i)
def inverseSum (n : ℕ) (r : Fin n → ℝ) : ℝ := ∑ i, (r i)⁻¹

end



end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_QuarterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip



noncomputable section
open scoped BigOperators
open Set MeasureTheory

def referenceUpperConstant : ℝ := 2*(2/Real.Gamma (1/2))^(1/2:ℝ)+2


end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_MomentGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped BigOperators
open Set MeasureTheory

abbrev unitCubeMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Ioo (0:ℝ) 1))

 def reflectionResidue (n : ℕ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  2 * ∏ j ∈ Finset.univ.erase i, (y j + y i) / (y j - y i)

end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_SewnAssignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace SewnRectangle
variable {n : ℕ}



lemma split_column (i : ℤ) : (∃ k : ℕ,i= -1-(k:ℤ)) ∨ ∃k : ℕ,i=(k:ℤ) := by
  by_cases hi : i<0
  · left; refine ⟨(-i-1).toNat,?_⟩
    rw [Int.toNat_of_nonneg (by omega)]; omega
  · right; exact ⟨i.toNat,(Int.toNat_of_nonneg (by omega)).symm⟩

end SewnRectangle
end
end CriticalStrip





end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FiniteEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram.PathGraph
noncomputable section
open scoped Classical

 

lemma reachable_of_odd_terminals {V : Type*} [Fintype V] (G : SimpleGraph V)
    {a b : V} (ha : Odd (G.degree a))
    (he : ∀ v, Odd (G.degree v) → v=a ∨ v=b) : G.Reachable a b := by
  let S : Set V := {v | G.Reachable a v}
  let H := G.induce S
  have hd (v : S) : H.degree v=G.degree v := by
    apply G.degree_induce_of_neighborSet_subset
    intro w hw
    exact v.property.trans hw.reachable
  let a' : S := ⟨a,SimpleGraph.Reachable.refl a⟩
  have ha' : Odd (H.degree a') := by simpa only [hd] using ha
  obtain ⟨w,hw,ho⟩ := H.exists_ne_odd_degree_of_exists_odd_degree a' ha'
  rw [hd] at ho
  rcases he w ho with hwa | hwb
  · exact (hw (Subtype.ext hwa)).elim
  · exact hwb ▸ w.property

end
end CriticalStrip.Diagram.PathGraph

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram Diagram.PathGraph

namespace Diagram.Graph

 

lemma reach_exit {V : Type*} {r : V → V → Prop} {S : Set V} {x z : V}
    (h : Relation.ReflTransGen r x z) (hx : x∈S) (hz : z∉S) :
    ∃ u v, u∈S ∧ v∉S ∧ r u v ∧
      Relation.ReflTransGen (fun a b=>a∈S ∧ b∈S ∧ r a b) x u := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact (hz hx).elim
  | @head y w hxy h ih =>
    by_cases hy : w∈S
    · obtain ⟨u,v,hu,hv,huv,hr⟩:=ih hy
      exact ⟨u,v,hu,hv,huv,hr.head ⟨hx,hy,hxy⟩⟩
    · exact ⟨y,w,hx,hy,hxy,.refl⟩

end Diagram.Graph

end





end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_HoneycombClip
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

 
def turnRow (N j : ℕ) : ℕ := if j<N then N-1-j else j

@[simp] lemma turnRow_involutive (N j : ℕ) : turnRow N (turnRow N j)=j := by
  by_cases hj : j<N
  · have hj' : N-1-j<N := by omega
    simp only [turnRow,hj,hj',ite_true]
    omega
  · simp only [turnRow,hj,ite_false]


end

 

 

noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Graph

lemma glued_reach_right_boundary {V W I : Type*} (r : V → V → Prop) (s : W → W → Prop)
    (a : I → V) (b : I → W) (active : I → Prop) (root : I)
    {x : V⊕W} (h : Relation.ReflTransGen (Patch.glued r s a b active) x (.inr (b root))) :
    match x with
    | .inl _ => True
    | .inr x => ∃ i,Relation.ReflTransGen s x (b i) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨root,.refl⟩
  | @head x y hxy h ih =>
    cases x with
    | inl x => trivial
    | inr x =>
      cases y with
      | inl y =>
        obtain ⟨i,hi,rfl,hy⟩:=hxy
        exact ⟨i,.refl⟩
      | inr y =>
        obtain ⟨i,hi⟩:=ih
        exact ⟨i,hi.head hxy⟩

end Diagram.Graph

end





end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Pairing

 

def gateTurn (ga gb ha hb : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![0, gb-ga+3, ha-ga, hb-ga],
    ![ga-gb-3, 0, ha-gb, hb-gb],
    ![ga-ha, gb-ha, 0, hb-ha-3],
    ![ga-hb, gb-hb, ha-hb+3, 0]]


def gateBoundary {n : ℕ} (a b : Fin n) (F : Fin n → ℤ) (x y : ℤ) : Fin n → ℤ :=
  fun i=>if i=a then x else if i=b then y else F i

@[simp] lemma gateBoundary_left {n : ℕ} (a b : Fin n) (F : Fin n → ℤ) (x y : ℤ) :
    gateBoundary a b F x y a=x := by simp [gateBoundary]
@[simp] lemma gateBoundary_right {n : ℕ} (a b : Fin n) (hab : a≠b)
    (F : Fin n → ℤ) (x y : ℤ) : gateBoundary a b F x y b=y := by
  simp [gateBoundary,hab.symm]

end Pairing






namespace BoundaryInsert
variable {n m : ℕ}

 
def old (k : ℕ) (_hk : k≤n) : Fin n ↪o Fin (n+m) where
  toFun i := ⟨if i.val<k then i.val else i.val+m,by split_ifs <;> omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; split_ifs at this <;> omega
  map_rel_iff' := by intro i j; change (if i.val<k then i.val else i.val+m) ≤
    (if j.val<k then j.val else j.val+m) ↔ i.val≤j.val; split_ifs <;> omega

def fresh (k : ℕ) (hk : k≤n) : Fin m ↪o Fin (n+m) where
  toFun j := ⟨k+j.val,by omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; omega
  map_rel_iff' := by intro i j; change k+i.val≤k+j.val ↔ i.val≤j.val; omega

lemma disjoint (k : ℕ) (hk : k≤n) (i : Fin n) (j : Fin m) : old k hk i≠fresh k hk j := by
  intro he
  have := congrArg Fin.val he
  change (if i.val<k then i.val else i.val+m)=k+j.val at this
  split_ifs at this <;> omega

end BoundaryInsert
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnDisk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace BoundaryInsert
variable {n m : ℕ}


def unionGraph {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) :
    (V ⊕ W) → (V ⊕ W) → Prop
  | .inl v,.inl w => r v w
  | .inr v,.inr w => s v w
  | _,_ => False

instance instSymmSumUnionGraph {V W : Type*} (r : V → V → Prop) (s : W → W → Prop) [Std.Symm r] [Std.Symm s] :
    Std.Symm (unionGraph r s) := ⟨by
    rintro (v|v) (w|w) h
    · exact (symm h : r w v)
    · exact h.elim
    · exact h.elim
    · exact (symm h : s w v)⟩

end BoundaryInsert






namespace BoundarySew






variable {V : Type*} {n : ℕ}

 
def graph (r : V → V → Prop) (a b : V) (active : Prop) (v w : V) : Prop :=
  r v w ∨ active ∧ ((v=a ∧ w=b) ∨ (v=b ∧ w=a))

instance instSymmGraph (r : V → V → Prop) [Std.Symm r] (a b : V) (active : Prop) :
    Std.Symm (graph r a b active) := ⟨by
  intro v w h
  rcases h with h|⟨h,h'⟩
  · exact Or.inl (symm h)
  · exact Or.inr ⟨h,h'.elim (fun h=>Or.inr ⟨h.2,h.1⟩) (fun h=>Or.inl ⟨h.2,h.1⟩)⟩⟩

def project (a b : V) : V ⊕ Fin 4 → V
  | .inl v => v
  | .inr i => if i=1 then b else a

end BoundarySew
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnWideGate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnDisk

namespace Gate4
def skip (k i : ℕ) : ℕ := if i<k then i else i+2

def input (i : Fin 4) : Fin 8 := ⟨3-i.val,by omega⟩
def output (i : Fin 4) : Fin 8 := ⟨4+i.val,by omega⟩

variable {n : ℕ}
  (k : ℕ)
  (hk : k+4≤n)

def slot (i : Fin 4) : Fin n := ⟨k+i.val,by omega⟩

end Gate4
end TurnDisk
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnRhombus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnDisk



namespace Rhombus

def upGauge (i : Fin 6) : ℤ := -5+2*(i.val/2 : ℕ)
def downGauge (i : Fin 6) : ℤ := -4+2*(i.val/2 : ℕ)

end Rhombus
end TurnDisk

 

 


namespace TurnNetwork
open TurnDisk
abbrev Local := Fin 6 ⊕ Fin 6
abbrev Node (n t : ℕ) := Fin n ⊕ (Fin t × Local)

def old {n t : ℕ} : Node n t → Node n (t+1)
  | .inl i => .inl i
  | .inr (i,v) => .inr (i.castSucc,v)
def fresh {n t : ℕ} (v : Local) : Node n (t+1) := .inr (Fin.last t,v)

lemma old_injective {n t : ℕ} : Function.Injective (old (n:=n) (t:=t)) := by
  rintro (i|⟨i,v⟩) (j|⟨j,w⟩) h <;> simp only [old,Sum.inl.injEq,Sum.inr.injEq,Prod.mk.injEq] at h
  · exact congrArg Sum.inl h
  · cases h
  · cases h
  · obtain ⟨h,rfl⟩:=h
    have h' : i=j := Fin.ext (congrArg (fun i : Fin (t+1)=>i.val) h)
    subst j
    rfl
lemma fresh_injective {n t : ℕ} : Function.Injective (fresh (n:=n) (t:=t)) := by
  intro v w h
  simpa only [fresh,Sum.inr.injEq,Prod.mk.injEq,true_and] using h
lemma old_ne_fresh {n t : ℕ} (v : Node n t) (w : Local) : old v≠fresh w := by
  cases v with
  | inl i => simp only [old,fresh,ne_eq,reduceCtorEq,not_false_eq_true]
  | inr x =>
    intro h
    have hz := congrArg (fun z : Node n (t+1)=> match z with
      | .inl _ => 0
      | .inr x => x.1.val) h
    change x.1.val=t at hz
    omega
lemma cover {n t : ℕ} (v : Node n (t+1)) :
    (∃ w : Node n t,v=old w) ∨ (∃ w : Local,v=fresh w) := by
  cases v with
  | inl i => exact Or.inl ⟨.inl i,rfl⟩
  | inr x =>
    obtain ⟨i,v⟩:=x
    by_cases h : i.val<t
    · exact Or.inl ⟨.inr (⟨i.val,h⟩,v),by rfl⟩
    · right
      refine ⟨v,?_⟩
      have he : i=Fin.last t := Fin.ext (by change i.val=t; omega)
      rw [he]
      rfl

end TurnNetwork
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnEvolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace TurnNetwork
open TurnDisk

 
def lift {n s t : ℕ} (h : s ≤ t) : Node n s → Node n t
  | .inl i => .inl i
  | .inr (i,v) => .inr (i.castLE h,v)

variable {n : ℕ}
  (g₀ : Fin n → ℤ)
  (k : ℕ → ℕ)
  (hk : ∀ t,k t+4 ≤ n)


def namedGauge (t : ℕ) : Node n t → ℤ
  | .inl i=>g₀ i
  | .inr (_, .inl i)=>Rhombus.upGauge i
  | .inr (_, .inr i)=>Rhombus.downGauge i

end TurnNetwork

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section BoundaryEvolution

def width (M N : ℕ) : ℕ := 2*(M+N)
def ports (M N : ℕ) : ℕ := 2*width M N
 

def position (M N t : ℕ) : ℕ := width M N+2*(M-1-t/N+t%N)

lemma position_bound {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) (t : ℕ) :
    position M N t+4 ≤ ports M N := by
  have hs : M-1-t/N ≤ M-1 := Nat.sub_le _ _
  have h:=Nat.mod_lt t (by omega : 0<N)
  dsimp [position,ports,width]
  omega
lemma time_lt {M N c r : ℕ} (hr : r<N) (hc : c<M) : c*N+r<M*N := by
  calc
    c*N+r < c*N+N := Nat.add_lt_add_left hr _
    _ = (c+1)*N := by ring
    _ ≤ M*N := Nat.mul_le_mul_right N (by omega)

variable {M N : ℕ}
  (hM : 1 ≤ M)
  (hN : 1 ≤ N)
  (g₀ : Fin (ports M N) → ℤ)

def southSlot {c r : ℕ} (_hc : c<M) (_hr : r<N) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) ⟨l.val,by omega⟩
def westSlot {c r : ℕ} (_hc : c<M) (_hr : r<N) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N (c*N+r)) (position_bound hM hN _) ⟨2+l.val,by omega⟩

end BoundaryEvolution

 

 


variable {M N : ℕ}
  (hM : 1 ≤ M)
  (hN : 1 ≤ N)
  (g₀ : Fin (ports M N) → ℤ)

def northSlot {c : ℕ} (_hc : c<M) (l : Fin 2) : Fin (ports M N) :=
  Gate4.slot (position M N (c*N+(N-1))) (position_bound hM hN _) ⟨2+l.val,by omega⟩

omit g₀

include g₀



def starterGauge (M N : ℕ) (i : Fin (ports M N)) : ℤ :=
  if i.val<2*N then -5 else if i.val<width M N then -3
    else if i.val<width M N+2*M then 0 else -2

end TurnRectangle
end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_TurnRectangleMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical





namespace TurnStarter

variable (w : ℕ)
def left (i : Fin w) : Fin (2*w) := ⟨w-1-i.val,by omega⟩
def right (i : Fin w) : Fin (2*w) := ⟨w+i.val,by omega⟩

lemma left_injective : Function.Injective (left w) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  dsimp [left] at hh
  omega
lemma right_injective : Function.Injective (right w) := by
  intro i j h
  apply Fin.ext
  have hh:=congrArg Fin.val h
  dsimp [right] at hh
  omega
lemma left_lt_right (i j : Fin w) : left w i < right w j := by
  change w-1-i.val<w+j.val
  omega

end TurnStarter

 

 

namespace TurnRectangle
open TurnDisk TurnNetwork
section PhysicalMatching

variable {M N : ℕ}
  (hM : 1 ≤ M)
  (hN : 1 ≤ N)

def cellNode (c : Fin M) (r : Fin N) (v : Local) : Node (ports M N) (M*N) :=
  .inr (⟨c.val*N+r.val,time_lt r.isLt c.isLt⟩,v)

end PhysicalMatching

 

 


variable {M N : ℕ}

def southRay (c : Fin M) (l : Fin 2) : Fin (width M N) :=
  ⟨2*(M-1-c.val)+l.val,by dsimp [width]; omega⟩
def westRay (r : Fin N) (l : Fin 2) : Fin (width M N) :=
  ⟨2*(M+r.val)+l.val,by dsimp [width]; omega⟩

end TurnRectangle






end
end CriticalStrip.Diagram

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical
open Diagram

 
def slot (b : Bool) (p : Fin 3) : Fin 3 :=
  if b then if p=0 then 1 else if p=1 then 0 else 2
  else if p=0 then 2 else if p=1 then 1 else 0

 
def lane (b : Bool) (p : Fin 3) (l : Fin 2) : Fin 6 :=
  ⟨2*(slot b p).val+l.val,by have := (slot b p).isLt; omega⟩

def localGauge (b : Bool) : Fin 6 → ℤ :=
  if b then TurnDisk.Rhombus.upGauge else TurnDisk.Rhombus.downGauge

end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree

 
def passes (s : State) : List Bool → List (State × Fin 3)
  | []=>[]
  | b::l=>(s,outgoing s.2 b)::passes (next s b) l

@[simp] lemma passes_nil (s : State) : passes s []=[] := rfl
@[simp] lemma passes_cons (s : State) (b : Bool) (l : List Bool) :
    passes s (b::l)=(s,outgoing s.2 b)::passes (next s b) l := rfl

lemma passes_vertices (s : State) (l : List Bool) :
    (passes s l).map (fun x=>x.1.1)=visited Prod.fst next s l := by
  induction l generalizing s with
  | nil=>rfl
  | cons b l ih=>simp only [passes,List.map_cons,visited,ih]


def routes (s : State) (l : List Bool) (v : Vertex) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter (fun pq=>((v,pq.1),pq.2)∈passes s l)

@[simp] lemma mem_routes (s : State) (l : List Bool) (v : Vertex) (pq : Fin 3 × Fin 3) :
    pq∈routes s l v ↔ ((v,pq.1),pq.2)∈passes s l := by simp [routes]

@[simp] lemma routes_nil (s : State) (v : Vertex) : routes s [] v=∅ := by
  ext x; simp

def swapPass (x : State × Fin 3) : State × Fin 3 := ((x.1.1,x.2),x.1.2)

end

 

 

noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk
namespace RibbonRectangle
section Geometry

variable (L : ℤ) (M N : ℕ)

def Inside (v : Vertex) : Prop :=
  L≤v.1 ∧ v.1<L+(M:ℤ) ∧ 0≤v.2.1 ∧ v.2.1<(N:ℤ)

def vertex (c : Fin M) (r : Fin N) (b : Bool) : Vertex := (L+(c.val:ℤ),(r.val:ℤ),b)

lemma vertex_inside (c : Fin M) (r : Fin N) (b : Bool) : Inside L M N (vertex L M N c r b) := by
  dsimp [Inside,vertex]
  have :=c.isLt; have :=r.isLt
  omega

variable {L M N}

def col {v : Vertex} (h : Inside L M N v) : Fin M := ⟨(v.1-L).toNat,by dsimp [Inside] at h; omega⟩
def row {v : Vertex} (h : Inside L M N v) : Fin N := ⟨v.2.1.toNat,by dsimp [Inside] at h; omega⟩

@[simp] lemma col_vertex (c : Fin M) (r : Fin N) (b : Bool) :
    col (vertex_inside L M N c r b)=c := by
  apply Fin.ext
  simp [col,vertex]
@[simp] lemma row_vertex (c : Fin M) (r : Fin N) (b : Bool) :
    row (vertex_inside L M N c r b)=r := by
  apply Fin.ext
  simp [row,vertex]

variable (L M N)

def node {v : Vertex} (h : Inside L M N v) (i : Fin 6) : Node (TurnRectangle.ports M N) (M*N) :=
  TurnRectangle.cellNode (col h) (row h) (if v.2.2 then .inl i else .inr i)

end Geometry






end RibbonRectangle
end





end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical
open Diagram FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ}
  {M N : ℕ}
  (hM : 1≤M)
  (hN : 1≤N)

lemma last_inside (s : State) (l : List Bool) (hl : l≠[])
    (hI : ∀x∈passes s l,Inside L M N x.1.1) :
    Inside L M N (back (terminal next s l)).1 := by
  have hh:=lastVisited_mem s l hl
  rw [←passes_vertices] at hh
  obtain ⟨x,hx,he⟩:=List.mem_map.mp hh
  exact he ▸ hI x hx

end RibbonRectangle
end

 

 

noncomputable section
open scoped Classical
open Diagram Diagram.TurnNetwork Diagram.TurnDisk FiniteBranchTree
namespace RibbonRectangle

variable {L : ℤ} {M N : ℕ}






def bottomIndex (c : Fin M) (l : Fin 2) : Fin (TurnRectangle.ports M N) :=
  TurnStarter.left (TurnRectangle.width M N) (TurnRectangle.southRay c (1-l))

end RibbonRectangle






end

 

 

noncomputable section
open scoped Classical
open Diagram FiniteBranchTree

def closeStem (stem tail : List Bool) : List Bool :=
  (stem++true::tail)++true::reverseTurns stem

end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_RibbonGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
namespace HoneycombBranch
open scoped Classical
section TreeMass
open Diagram FiniteBranchTree

 
def bottom (i : ℤ) : State := ((i,0,true),0)
def top (H : ℕ) (i : ℤ) : State := ((i,(H:ℤ)-1,false),0)

end TreeMass

open FiniteBranchTree

 

lemma word_unique (s : State) (l m : List Bool)
    (hv : visited Prod.fst next s l=visited Prod.fst next s m)
    (ht : terminal next s l=terminal next s m) : l=m := by
  induction l generalizing s m with
  | nil=>
    have hh:=congrArg List.length hv
    have hm : m.length=0 := by simpa only [visited_length,List.length_nil] using hh.symm
    exact (List.eq_nil_of_length_eq_zero hm).symm
  | cons b l ih=>
    cases m with
    | nil=>have hh:=congrArg List.length hv; simp only [visited_length,List.length_cons,List.length_nil] at hh; omega
    | cons c m=>
      have htail : visited Prod.fst next (next s b) l=visited Prod.fst next (next s c) m := (List.cons.inj hv).2
      have hlen : l.length=m.length := by simpa only [visited_length] using congrArg List.length htail
      have hbc : b=c := by
        apply next_injective s
        by_cases hl : l=[]
        · have hm : m=[] := by apply List.eq_nil_of_length_eq_zero; simpa only [hl,List.length_nil] using hlen.symm
          simpa only [hl,hm,terminal] using congrArg Prod.fst ht
        · have hm : m≠[] := by intro hh; apply hl; apply List.eq_nil_of_length_eq_zero; simpa only [hh,List.length_nil] using hlen
          have hh:=congrArg List.head? htail
          rw [visited_head _ _ _ _ hl,visited_head _ _ _ _ hm] at hh
          exact Option.some.inj hh
      subst c
      exact congrArg (List.cons b) (ih (next s b) m htail ht)

 

lemma exists_word (s t : State) (p : List Vertex)
    (hh : p.head?=some s.1) (hl : p.getLast?=some (back t).1)
    (hn : p.Nodup) (hc : p.IsChain (fun v w=>∃q : Fin 3,neighbor v q=w))
    (hi : (back s).1∉p) (ho : t.1∉p) (hne : s≠back t) :
    ∃l : List Bool, visited Prod.fst next s l=p ∧ terminal next s l=t := by
  induction p generalizing s with
  | nil=>simp only [List.head?_nil,reduceCtorEq] at hh
  | cons v p ih=>
    have he : v=s.1 := Option.some.inj hh
    subst v
    cases p with
    | nil=>
      have hs : s.1=(back t).1 := by simpa only [List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.some.injEq] using hl
      have hport : t.2≠s.2 := by
        intro ht
        exact hne (Prod.ext hs ht.symm)
      obtain ⟨b,hb,_⟩:=outgoing_exhaust s.2 t.2 hport
      refine ⟨[b],rfl,?_⟩
      change next s b=t
      dsimp [next]
      rw [hb,hs]
      exact back_back t
    | cons w p=>
      have had : ∃q : Fin 3,neighbor s.1 q=w := (List.isChain_cons_cons.mp hc).1
      obtain ⟨q,hq⟩:=had
      have hqne : q≠s.2 := by
        intro he
        have hew : w=(back s).1 := by rw [←hq,he]; rfl
        exact hi (hew ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨b,hb,_⟩:=outgoing_exhaust s.2 q hqne
      have hnext : (next s b).1=w := by dsimp [next]; rw [hb,hq]
      have hsnew : next s b≠back t := by
        intro he
        have hh : t.1=s.1 := by
          have he':=congrArg back he
          rw [back_back,back_next] at he'
          exact (congrArg Prod.fst he').symm
        exact ho (hh ▸ List.mem_cons_self)
      obtain ⟨l,hv,ht⟩:=ih (next s b) (by simp only [List.head?_cons,hnext])
        (by simpa only [List.getLast?_cons_cons] using hl) hn.tail
        (List.isChain_cons_cons.mp hc).2
        (by rw [back_next]; exact (List.nodup_cons.mp hn).1)
        (fun h=>ho (List.mem_cons_of_mem _ h)) hsnew
      exact ⟨b::l,by simp only [visited,hv],ht⟩

lemma word_nonempty_of_head (s : State) (l : List Bool) (p : List Vertex)
    (hh : p.head?=some s.1) (hv : visited Prod.fst next s l=p) : l≠[] := by
  intro hl
  subst l
  change []=p at hv
  rw [←hv,List.head?_nil] at hh
  contradiction

lemma word_terminal_ne_source {s : State} {l : List Bool} (hl : l≠[])
    (hn : (visited Prod.fst next s l).Nodup) : terminal next s l≠back s := by
  cases l with
  | nil=>exact (hl rfl).elim
  | cons b l=>
    intro ht
    cases l with
    | nil=>
      have hh:=congrArg Prod.snd ht
      exact outgoing_ne s.2 b hh
    | cons c l=>
      have hm:=lastVisited_mem (next s b) (c::l) (by simp)
      change (back (terminal next s (b::c::l))).1∈_ at hm
      rw [ht,back_back] at hm
      exact (List.nodup_cons.mp hn).1 hm



lemma visited_head_last (s : State) (l : List Bool) (hl : l≠[]) :
    (visited Prod.fst next s l).head?=some s.1 ∧
    (visited Prod.fst next s l).getLast?=some (back (terminal next s l)).1 := by
  refine ⟨visited_head _ _ _ _ hl,?_⟩
  induction l generalizing s with
  | nil=>exact (hl rfl).elim
  | cons b l ih=>
    cases l with
    | nil=>simp only [visited,terminal,back_next,List.getLast?_singleton]
    | cons c l=>
      simpa only [visited,List.getLast?_cons_cons,terminal] using ih (next s b) (by simp)

end HoneycombBranch
open scoped Classical BigOperators



namespace HoneycombBranch
open FiniteBranchTree



def SideWord (H : ℕ) (i k : ℤ) := {l : List Bool //
  l≠[] ∧ (visited Prod.fst next (bottom i) l).Nodup ∧
  (∀v∈visited Prod.fst next (bottom i) l,0≤v.2.1 ∧ v.2.1<(H:ℤ) ∧ v.1≠k) ∧
  (terminal next (bottom i) l).2=1 ∧ (terminal next (bottom i) l).1.1=k}

namespace SideWord
variable {H : ℕ} {i k : ℤ}

def state (x : SideWord H i k) : State:=terminal next (bottom i) x.val

lemma band (x : SideWord H i k) : 0≤x.state.1.2.1 ∧ x.state.1.2.1<(H:ℤ) := by
  have hm:=lastVisited_mem (bottom i) x.val x.property.1
  have hb:=x.property.2.2.1 _ hm
  have he : (back x.state).1.2.1=x.state.1.2.1 := by
    dsimp [back,state]
    rw [x.property.2.2.2.1]
    dsimp [neighbor]
    split <;> rfl
  exact he ▸ ⟨hb.1,hb.2.1⟩

end SideWord
end HoneycombBranch
end
end CriticalStrip

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_FluxWindow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree Filter Topology

 
def IsExit (D : Vertex→Prop) (i : ℤ) (l : List Bool) : Prop :=
  l≠[] ∧ (visited Prod.fst next (bottom i) l).Nodup ∧
  (∀v∈visited Prod.fst next (bottom i) l,D v) ∧
  ¬D (terminal next (bottom i) l).1

def window (H : ℕ) (i : ℤ) (m : ℕ) : Finset Vertex :=
  (Finset.Ico (i-(m:ℤ)) (i+(m:ℤ)+1)).product ((Finset.Ico 0 (H:ℤ)).product Finset.univ)

@[simp] lemma mem_window (H : ℕ) (i : ℤ) (m : ℕ) (v : Vertex) :
    v∈window H i m ↔ i-(m:ℤ)≤v.1 ∧ v.1 < i+(m:ℤ)+1 ∧ 0≤v.2.1 ∧ v.2.1<(H:ℤ) := by
  rcases v with ⟨k,r,b⟩
  simp [window, and_assoc]

def clip (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset Vertex :=
  (window H i m).filter D

def finiteExits (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset (List Bool) :=
  (words (clip D H i m) (bottom i)).filter (fun l=>(terminal next (bottom i) l).1∉clip D H i m)

def physicalExits (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset (List Bool) :=
  (finiteExits D H i m).filter (fun l=>¬D (terminal next (bottom i) l).1)

def sideExits (D : Vertex→Prop) (H : ℕ) (i : ℤ) (m : ℕ) : Finset (List Bool) :=
  (finiteExits D H i m).filter (fun l=>D (terminal next (bottom i) l).1)

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

 
structure BoundaryPorts (D : Vertex→Prop) (B : Type*) where
  port : B→State
  injective : Function.Injective port
  inside : ∀b,D (port b).1
  outside : ∀b,¬D (back (port b)).1
  complete : ∀s : State,D s.1→¬D (back s).1→∃b,port b=s

abbrev ExitWord (D : Vertex→Prop) (i : ℤ) := {l : List Bool // IsExit D i l}

variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

lemma source_outside (hD : ∀v,D v→0≤v.2.1 ∧ v.2.1<(H:ℤ)) : ¬D (back (bottom i)).1 := by
  intro hx
  have hh:=(hD _ hx).1
  norm_num [back,bottom,neighbor] at hh

lemma exists_exit_port (x : ExitWord D i) : ∃b,P.port b=back (terminal next (bottom i) x.val) := by
  apply P.complete
  · exact x.property.2.2.1 _ (lastVisited_mem _ _ x.property.1)
  · simpa only [back_back] using x.property.2.2.2

def exitPort (x : ExitWord D i) : B := Classical.choose (exists_exit_port P x)

lemma exitPort_spec (x : ExitWord D i) :
    P.port (exitPort P x)=back (terminal next (bottom i) x.val) := Classical.choose_spec (exists_exit_port P x)

lemma exitPort_terminal (x : ExitWord D i) :
    terminal next (bottom i) x.val=back (P.port (exitPort P x)) := by
  rw [exitPort_spec,back_back]

end

 

 

noncomputable section
open scoped Classical
open FiniteBranchTree

 
def steppedVertices (N : ℕ) (s : ℤ) (v : Vertex) : Prop :=
  0≤v.2.1 ∧ (v.2.1<(N:ℤ) ∨ v.2.1=(N:ℤ) ∧ s≤v.1)

def sidePort (N : ℕ) (s : ℤ) : State := ((s,(N:ℤ),true),1)

def stepTop (N : ℕ) (s j : ℤ) : State := if j < s then top N j else top (N+1) j

end
end CriticalStrip.HoneycombBranch

end OAI
end

section
-- module Solutions.OAIQ042_SS.StripMass_PhysicalPorts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.HoneycombBranch
noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree

def bandVertices (H : ℕ) (v : Vertex) : Prop := 0≤v.2.1 ∧ v.2.1<(H:ℤ)

def stripPort (H : ℕ) : ℤ⊕ℤ→State
  | .inl j=>bottom j
  | .inr j=>top H j

lemma stripPort_injective (H : ℕ) : Function.Injective (stripPort H) := by
  rintro (j|j) (k|k) he <;> simp [stripPort,bottom,top] at he ⊢ <;> tauto

lemma stripPort_inside (H : ℕ) (hH : 1≤H) (b : ℤ⊕ℤ) : bandVertices H (stripPort H b).1 := by
  cases b <;> dsimp [stripPort,bandVertices,bottom,top] <;> omega

lemma stripPort_outside (H : ℕ) (_hH : 1≤H) (b : ℤ⊕ℤ) : ¬bandVertices H (back (stripPort H b)).1 := by
  cases b <;> simp [stripPort,bandVertices,bottom,top,back,neighbor]

lemma stripPort_complete (H : ℕ) (s : State) (hi : bandVertices H s.1)
    (ho : ¬bandVertices H (back s).1) : ∃b,stripPort H b=s := by
  rcases s with ⟨⟨k,r,b⟩,p⟩
  fin_cases p
  · cases b
    · refine ⟨.inr k,?_⟩
      dsimp [bandVertices,back,neighbor] at hi ho
      have hr : r=(H:ℤ)-1 := by omega
      simp [stripPort,top,hr]
    · refine ⟨.inl k,?_⟩
      dsimp [bandVertices,back,neighbor] at hi ho
      have hr : r=0 := by omega
      simp [stripPort,bottom,hr]
  · cases b <;> simp [bandVertices,back,neighbor] at hi ho <;> omega
  · cases b <;> simp [bandVertices,back,neighbor] at hi ho <;> omega

def stripBoundaryPorts (H : ℕ) (hH : 1≤H) : BoundaryPorts (bandVertices H) (ℤ⊕ℤ) where
  port:=stripPort H
  injective:=stripPort_injective H
  inside:=stripPort_inside H hH
  outside:=stripPort_outside H hH
  complete:=stripPort_complete H

abbrev StepEndpoint := ℤ⊕(ℤ⊕Unit)

def stepPort (N : ℕ) (s : ℤ) : StepEndpoint→State
  | .inl j=>bottom j
  | .inr (.inl j)=>stepTop N s j
  | .inr (.inr _)=>sidePort N s

lemma stepPort_injective (N : ℕ) (s : ℤ) : Function.Injective (stepPort N s) := by
  rintro (j|(j|u)) (k|(k|v)) he
  all_goals simp only [stepPort,stepTop] at he
  all_goals try split_ifs at he
  all_goals simp_all [bottom,top,sidePort]

lemma stepPort_inside (N : ℕ) (hN : 1≤N) (s : ℤ) (b : StepEndpoint) :
    steppedVertices N s (stepPort N s b).1 := by
  rcases b with j|(j|u)
  · dsimp [stepPort,steppedVertices,bottom]; omega
  · simp only [stepPort,stepTop]
    split_ifs <;> dsimp [steppedVertices,top] <;> omega
  · dsimp [stepPort,steppedVertices,sidePort]; omega

lemma stepPort_outside (N : ℕ) (_hN : 1≤N) (s : ℤ) (b : StepEndpoint) :
    ¬steppedVertices N s (back (stepPort N s b)).1 := by
  rcases b with j|(j|u)
  · simp [stepPort,back,bottom,neighbor,steppedVertices]
  · simp only [stepPort,stepTop]
    split_ifs <;> dsimp [steppedVertices,top,back,neighbor] <;> omega
  · dsimp [stepPort,steppedVertices,sidePort,back,neighbor]; omega

lemma stepPort_complete (N : ℕ) (s : ℤ) (x : State) (hi : steppedVertices N s x.1)
    (ho : ¬steppedVertices N s (back x).1) : ∃b,stepPort N s b=x := by
  rcases x with ⟨⟨k,r,b⟩,p⟩
  fin_cases p
  · cases b
    · refine ⟨.inr (.inl k),?_⟩
      dsimp [steppedVertices,back,neighbor] at hi ho
      by_cases hk : k < s
      · have hr : r=(N:ℤ)-1 := by omega
        simp [stepPort,stepTop,hk,top,hr]
      · have hr : r=(N:ℤ) := by omega
        simp [stepPort,stepTop,hk,top,hr]
    · refine ⟨.inl k,?_⟩
      dsimp [steppedVertices,back,neighbor] at hi ho
      have hr : r=0 := by omega
      simp [stepPort,bottom,hr]
  · cases b
    · dsimp [steppedVertices,back,neighbor] at hi ho; omega
    · refine ⟨.inr (.inr ()),?_⟩
      dsimp [steppedVertices,back,neighbor] at hi ho
      have hr : r=(N:ℤ) := by omega
      have hk : k=s := by omega
      simp [stepPort,sidePort,hr,hk]
  · cases b <;> dsimp [steppedVertices,back,neighbor] at hi ho <;> omega

def stepBoundaryPorts (N : ℕ) (hN : 1≤N) (s : ℤ) : BoundaryPorts (steppedVertices N s) StepEndpoint where
  port:=stepPort N s
  injective:=stepPort_injective N s
  inside:=stepPort_inside N hN s
  outside:=stepPort_outside N hN s
  complete:=stepPort_complete N s

variable {D : Vertex→Prop} {B : Type*} (P : BoundaryPorts D B) {H : ℕ} {i : ℤ}

def stripTurn (i : ℤ) : ℤ⊕ℤ→ℤ
  | .inl j=>if i≤j then -3 else 3
  | .inr _=>0

end

 

 

noncomputable section
open scoped Classical BigOperators
open FiniteBranchTree



def stepTurn (i : ℤ) : StepEndpoint→ℤ
  | .inl j=>if i≤j then -3 else 3
  | .inr (.inl _)=>0
  | .inr (.inr _)=>1

end
end CriticalStrip.HoneycombBranch





end OAI
end


