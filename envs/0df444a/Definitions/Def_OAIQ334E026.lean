-- Prove2me | Definitions.Def_OAIQ334E026
-- name    : OAIQ334E026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-12T11:36:36.457249+00:00
-- url     : https://prove2.me/theorems/0ffc3663-532f-4526-8733-a60997e038ec
-- title:
--   Definitions bundle OAIQ334E026 of the split of OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.AtomicTriangular.universal_energy_minimum`, carved from OpenAI's openai/math development (OpenAI, *An atomic certificate for triangular-lattice universal optimality (result family 090)*, OpenAI Math Release, September 26, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 134 declarations of OpenAI's Lean: 39 definitions, 1 inductive type or structure, 16 instances and 78 theorems. The definitions and types are `OAI.AtomicTriangular.complexSchwartz`, `OAI.AtomicTriangular.gaussPot`, `OAI.AtomicTriangular.schwartzLP`, `OAI.TriangularUniversal.LPFunction`, `OAI.TriangularUniversal.NonzeroSite`, `OAI.TriangularUniversal.PositiveMixture.CM`, `OAI.TriangularUniversal.PositiveMixture.I`, `OAI.TriangularUniversal.PositiveMixture.Positive`, `OAI.TriangularUniversal.PositiveMixture.bernsteinBasis`, `OAI.TriangularUniversal.PositiveMixture.coordinate`, `OAI.TriangularUniversal.PositiveMixture.difference`, `OAI.TriangularUniversal.PositiveMixture.falling`, `OAI.TriangularUniversal.PositiveMixture.gridFiniteMeasure`, `OAI.TriangularUniversal.PositiveMixture.gridMeasure`, `OAI.TriangularUniversal.PositiveMixture.gridTime`, `OAI.TriangularUniversal.PositiveMixture.momentFunctional`, `OAI.TriangularUniversal.PositiveMixture.powerTest`, `OAI.TriangularUniversal.PositiveMixture.unitPower`, `OAI.TriangularUniversal.PositiveMixture.weight`, `OAI.TriangularUniversal.Theta.theta`, `OAI.TriangularUniversal.b`, `OAI.TriangularUniversal.cutoffConvolution`, `OAI.TriangularUniversal.cutoffMeasure`, `OAI.TriangularUniversal.firstMoment`, `OAI.TriangularUniversal.gaussPot`, `OAI.TriangularUniversal.kernelForm`, `OAI.TriangularUniversal.latticeEnergy`, `OAI.TriangularUniversal.nonzeroLatticeEquiv`, `OAI.TriangularUniversal.pattern`, `OAI.TriangularUniversal.phase`, `OAI.TriangularUniversal.pointsMeasure`, `OAI.TriangularUniversal.powerPotential`, `OAI.TriangularUniversal.radialCutoff`, `OAI.TriangularUniversal.triangularBasis`, `OAI.TriangularUniversal.triangularEquiv`, `OAI.TriangularUniversal.triangularLattice`, `OAI.TriangularUniversal.triangularModule`, `OAI.TriangularUniversal.triangularPoint`, `OAI.circleMeasurableSpace`, `OAI.starSubalgebraCommCStarAlgebra`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`Triangular_Energy_Basic`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Basic.lean), [`Triangular_Energy_Cutoff`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Cutoff.lean), [`Triangular_Energy_Density`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Density.lean), [`Triangular_Energy_Gaussian`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Gaussian.lean), [`Triangular_Energy_Lattice`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Lattice.lean), [`Triangular_Energy_Mixtures`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Mixtures.lean), [`Triangular_Energy_Potentials`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Potentials.lean), [`Triangular_Energy_Schwartz`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Schwartz.lean), [`Triangular_Energy_Spectral`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Spectral.lean), [`Triangular_Energy_Theta`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/Triangular/Energy/Theta.lean).
--
--   **Imports.** It imports the published bundle `Def_TriangularEnergy`.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.AtomicTriangular.gaussianPair_poisson_eu` and `OAI.AtomicTriangular.universal_energy_minimum`.
-- source:
--   OpenAI, An atomic certificate for triangular-lattice universal optimality (result family 090), OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-atomic-certificate-for-triangular-lattice-universal-optimality-September-26-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_TriangularEnergy

section
-- module Solutions.OAIQ334_EU.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
/-- A closed commutative ⋆-subalgebra of a C⋆-algebra is a commutative C⋆-algebra, found by instance search
in d13f23b (Kadison similarity, oaiq-075). A def, made a local instance by the port only in modules naming
`CommCStarAlgebra` or `IsMulCommutative` (`oaiport.comm_cstar_line`): as a global instance it made `whnf` time out in
FactorGeneration modules with their own `CStarAlgebra` instances on a subalgebra (oaiq-122). -/
@[reducible]
noncomputable def starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
    [IsClosed (A : Set B)] [IsMulCommutative A] : CommCStarAlgebra A :=
  { StarSubalgebra.cstarAlgebra A with
    mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
section OAIVecLookup
variable {α : Type _}
@[simp] theorem vecCons3_one (a b c : α) : (![a, b, c] : Fin 3 → α) 1 = b := rfl
@[simp] theorem vecCons3_two (a b c : α) : (![a, b, c] : Fin 3 → α) 2 = c := rfl
@[simp] theorem vecCons4_one (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 1 = b := rfl
@[simp] theorem vecCons4_two (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 2 = c := rfl
@[simp] theorem vecCons4_three (a b c d : α) : (![a, b, c, d] : Fin 4 → α) 3 = d := rfl
end OAIVecLookup
section OAIVecTail
variable {α : Type _}
@[simp] theorem vecConsTail1_1 (x : α) (f : Fin 1 → α) : (Matrix.vecCons x f : Fin 2 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_1 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail2_2 (x : α) (f : Fin 2 → α) : (Matrix.vecCons x f : Fin 3 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_1 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail3_2 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail3_3 (x : α) (f : Fin 3 → α) : (Matrix.vecCons x f : Fin 4 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_1 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 1 = f 0 := rfl
@[simp] theorem vecConsTail4_2 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 2 = f 1 := rfl
@[simp] theorem vecConsTail4_3 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 3 = f 2 := rfl
@[simp] theorem vecConsTail4_4 (x : α) (f : Fin 4 → α) : (Matrix.vecCons x f : Fin 5 → α) 4 = f 3 := rfl
end OAIVecTail
@[simp] theorem fin3_mk_0 (h : 0 < 3) : (⟨0, h⟩ : Fin 3) = 0 := rfl
@[simp] theorem fin3_mk_1 (h : 1 < 3) : (⟨1, h⟩ : Fin 3) = 1 := rfl
@[simp] theorem fin3_mk_2 (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl
@[simp] theorem fin4_mk_0 (h : 0 < 4) : (⟨0, h⟩ : Fin 4) = 0 := rfl
@[simp] theorem fin4_mk_1 (h : 1 < 4) : (⟨1, h⟩ : Fin 4) = 1 := rfl
@[simp] theorem fin4_mk_2 (h : 2 < 4) : (⟨2, h⟩ : Fin 4) = 2 := rfl
@[simp] theorem fin4_mk_3 (h : 3 < 4) : (⟨3, h⟩ : Fin 4) = 3 := rfl
@[simp] theorem fin5_mk_0 (h : 0 < 5) : (⟨0, h⟩ : Fin 5) = 0 := rfl
@[simp] theorem fin5_mk_1 (h : 1 < 5) : (⟨1, h⟩ : Fin 5) = 1 := rfl
@[simp] theorem fin5_mk_2 (h : 2 < 5) : (⟨2, h⟩ : Fin 5) = 2 := rfl
@[simp] theorem fin5_mk_3 (h : 3 < 5) : (⟨3, h⟩ : Fin 5) = 3 := rfl
@[simp] theorem fin5_mk_4 (h : 4 < 5) : (⟨4, h⟩ : Fin 5) = 4 := rfl
/-- `norm_num` cannot decide equalities of `Fin` literals here (oaiq-091). -/
@[simp] theorem fin3_lit_0_1 : ((0 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin3_lit_0_2 : ((0 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_1_0 : ((1 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_1_2 : ((1 : Fin 3) = 2) ↔ False := by decide
@[simp] theorem fin3_lit_2_0 : ((2 : Fin 3) = 0) ↔ False := by decide
@[simp] theorem fin3_lit_2_1 : ((2 : Fin 3) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_1 : ((0 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_0_2 : ((0 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_0_3 : ((0 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_1_0 : ((1 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_1_2 : ((1 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin4_lit_1_3 : ((1 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_2_0 : ((2 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_2_1 : ((2 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_2_3 : ((2 : Fin 4) = 3) ↔ False := by decide
@[simp] theorem fin4_lit_3_0 : ((3 : Fin 4) = 0) ↔ False := by decide
@[simp] theorem fin4_lit_3_1 : ((3 : Fin 4) = 1) ↔ False := by decide
@[simp] theorem fin4_lit_3_2 : ((3 : Fin 4) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_1 : ((0 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_0_2 : ((0 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_0_3 : ((0 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_0_4 : ((0 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_1_0 : ((1 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_1_2 : ((1 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_1_3 : ((1 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_1_4 : ((1 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_2_0 : ((2 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_2_1 : ((2 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_2_3 : ((2 : Fin 5) = 3) ↔ False := by decide
@[simp] theorem fin5_lit_2_4 : ((2 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_3_0 : ((3 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_3_1 : ((3 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_3_2 : ((3 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_3_4 : ((3 : Fin 5) = 4) ↔ False := by decide
@[simp] theorem fin5_lit_4_0 : ((4 : Fin 5) = 0) ↔ False := by decide
@[simp] theorem fin5_lit_4_1 : ((4 : Fin 5) = 1) ↔ False := by decide
@[simp] theorem fin5_lit_4_2 : ((4 : Fin 5) = 2) ↔ False := by decide
@[simp] theorem fin5_lit_4_3 : ((4 : Fin 5) = 3) ↔ False := by decide
/-- Mathlib d13f23b's `MeasurableSpace Circle` (Mathlib.MeasureTheory.Group.Circle): the subtype structure. A def,
turned on as a local instance in the modules that use the characters `𝐞`/`fourierChar`/`probChar` (q141). -/
@[reducible] def circleMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype (· ∈ Submonoid.unitSphere ℂ)
/-- Mathlib d13f23b's `MeasurableSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean): the product structure
(InvariantIsing, q251). Explicitly named: the platform's `Def_InvariantIsing` declares an anonymous copy of the same
instance. -/
instance _root_.Matrix.compatMeasurableSpace {m n α : Type*} [MeasurableSpace α] :
    MeasurableSpace (Matrix m n α) :=
  inferInstanceAs <| MeasurableSpace (m → n → α)
/-- Mathlib d13f23b's `BorelSpace (Matrix m n α)` (Mathlib/Analysis/Matrix/MeasurableSpace.lean; InvariantIsing, q258). -/
instance _root_.Matrix.compatBorelSpace {m n α : Type*} [Countable m] [Countable n] [MeasurableSpace α]
    [TopologicalSpace α] [SecondCountableTopology α] [BorelSpace α] : BorelSpace (Matrix m n α) :=
  inferInstanceAs <| BorelSpace (m → n → α)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology ENNReal NNReal
open Classical
open Filter

noncomputable section
namespace TriangularUniversal

def triangularPoint (jk : ℤ × ℤ) : Plane :=
  Real.sqrt (2 / Real.sqrt 3) •
    (EuclideanSpace.single 0 ((jk.1 : ℝ) + (jk.2 : ℝ) / 2) +
     EuclideanSpace.single 1 ((jk.2 : ℝ) * Real.sqrt 3 / 2))

def triangularLattice : Set Plane := Set.range triangularPoint

def latticeEnergy (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∑' a : {x : Plane // x ∈ triangularLattice ∧ x ≠ 0},
    ENNReal.ofReal (g (‖a.val‖ ^ 2))

end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/- Necessary analytic transfer from §2. We use finite positive measures for the
   comparison form; the eventual quadratic inequality also handles real signed
   linear combinations, without imposing spacing on the configuration. -/
def phase (w x : Plane) : ℂ := Complex.exp ((2 * Real.pi * ⟪w, x⟫ : ℝ) * I)
def pattern (μ : Measure Plane) (w : Plane) : ℂ :=
  charFun μ ((2 * Real.pi) • w)

def kernelForm (f : Plane → ℂ) (μ ν : Measure Plane) : ℂ :=
  ∫ xy : Plane × Plane, f (xy.1 - xy.2) ∂(μ.prod ν)

end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Cutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/-- A comparison density, equal to one on the competitor disk. It adds no
spacing or local-count hypothesis to the density-only LP argument. -/
def radialCutoff (R T : ℝ) (x : Plane) : ℝ :=
  max 0 (min 1 ((R + T - ‖x‖) / T))

def cutoffConvolution (f : Plane → ℂ) (R T : ℝ) (x : Plane) : ℂ :=
  ∫ z, radialCutoff R T (x-z) • f z

def firstMoment (f : Plane → ℂ) : ℝ := ∫ z, ‖z‖ * ‖f z‖



def cutoffMeasure (R T : ℝ) : Measure Plane :=
  volume.withDensity (fun x => ENNReal.ofReal (radialCutoff R T x))

end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace FourierTransform
open Classical Filter MeasureTheory Complex ComplexConjugate FourierTransform
namespace TriangularUniversal
/-- Regularity actually used by the density LP proof. Gaussian-bounded Fourier
pairs are put into this class below; no separation of a competitor is assumed. -/
structure LPFunction where
  toFun : Plane → ℂ
  continuous : Continuous toFun
  integrable : Integrable toFun
  fourierIntegrable : Integrable (𝓕 toFun)
  momentIntegrable : Integrable (fun z => ‖z‖ * ‖toFun z‖)
  bound : ℝ
  norm_bound : ∀ x, ‖toFun x‖ ≤ bound

instance instCoeFunLPFunctionForallPlaneComplex : CoeFun LPFunction (fun _ => Plane → ℂ) := ⟨LPFunction.toFun⟩


def pointsMeasure (S : Finset Plane) : Measure Plane := ∑ x ∈ S, Measure.dirac x

instance pointsMeasure_finite (S : Finset Plane) : IsFiniteMeasure (pointsMeasure S) := by
  unfold pointsMeasure
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Theta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace TriangularUniversal.Theta

def theta (c : ℂ) : ℂ := ∑' p : ℤ × ℤ,
  Complex.exp (-Real.pi*c*((p.1:ℂ)^2+(p.1:ℂ)*p.2+(p.2:ℂ)^2))


end TriangularUniversal.Theta

end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Mixtures
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Classical Filter
namespace TriangularUniversal
def b : ℝ := Real.sqrt 3 / 2

lemma sqrt_three_pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
lemma scale_pos : 0 < Real.sqrt (2 / Real.sqrt (3 : ℝ)) := by positivity

lemma triangularPoint_coord_zero (j k : ℤ) :
    triangularPoint (j, k) 0 = Real.sqrt (2 / Real.sqrt 3) * ((j : ℝ) + (k : ℝ) / 2) := by
  simp [triangularPoint]

lemma triangularPoint_coord_one (j k : ℤ) :
    triangularPoint (j, k) 1 = Real.sqrt (2 / Real.sqrt 3) * ((k : ℝ) * Real.sqrt 3 / 2) := by
  simp [triangularPoint]

lemma triangularPoint_injective : Function.Injective triangularPoint := by
  intro jk lm he
  rcases jk with ⟨j, k⟩
  rcases lm with ⟨l, m⟩
  have hzero := congrArg (fun v : Plane => v 0) he
  have hone := congrArg (fun v : Plane => v 1) he
  simp only [triangularPoint_coord_zero, triangularPoint_coord_one] at hzero hone
  have hk : k = m := by
    have hr : (k : ℝ) = (m : ℝ) := by
      have H := (mul_left_cancel₀ (ne_of_gt scale_pos)) hone
      have H' : (k : ℝ) * Real.sqrt 3 = (m : ℝ) * Real.sqrt 3 := by linarith
      exact mul_right_cancel₀ (ne_of_gt sqrt_three_pos) H' 
    exact_mod_cast hr
  subst m
  have hj : j = l := by
    have hr : (j : ℝ) = (l : ℝ) := by
      have H := (mul_left_cancel₀ (ne_of_gt scale_pos)) hzero
      linarith
    exact_mod_cast hr
  subst l
  rfl

lemma triangularPoint_zero : triangularPoint (0, 0) = 0 := by
  ext i
  fin_cases i <;> simp [triangularPoint]

def triangularEquiv : (Fin 2 → ℝ) ≃ₗ[ℝ] Plane where
  toFun v := Real.sqrt (2 / Real.sqrt 3) •
    (EuclideanSpace.single 0 (v 0 + v 1 / 2) +
      EuclideanSpace.single 1 (v 1 * Real.sqrt 3 / 2))
  invFun v := ![v 0 / Real.sqrt (2 / Real.sqrt 3) -
    v 1 / (Real.sqrt (2 / Real.sqrt 3) * Real.sqrt 3),
    2 * v 1 / (Real.sqrt (2 / Real.sqrt 3) * Real.sqrt 3)]
  left_inv v := by
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt scale_pos, ne_of_gt sqrt_three_pos] <;> ring
  right_inv v := by
    ext i
    fin_cases i <;> simp
    all_goals field_simp [ne_of_gt scale_pos, ne_of_gt sqrt_three_pos] <;> ring
  map_add' u v := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    ext i
    fin_cases i <;> simp <;> ring

def triangularBasis : Module.Basis (Fin 2) ℝ Plane :=
  Module.Basis.ofEquivFun triangularEquiv.symm

def triangularModule : Submodule ℤ Plane :=
  Submodule.span ℤ (Set.range triangularBasis)

instance instDiscreteTopologySubtypePlaneMemSubmoduleIntTriangularModule : DiscreteTopology triangularModule :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range triangularBasis)))

instance instIsZLatticeRealPlaneTriangularModule : IsZLattice ℝ triangularModule :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range triangularBasis)))

abbrev NonzeroSite := {x : Plane // x ∈ triangularLattice ∧ x ≠ 0}

end TriangularUniversal

open scoped BigOperators Topology NNReal ENNReal Polynomial
open Filter Finset MeasureTheory
noncomputable section
namespace TriangularUniversal.PositiveMixture

def difference (m : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => m j
  | r+1, j => difference m r j - difference m r (j+1)

def momentFunctional (m : ℕ → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j => LinearMap.mulRight ℝ (m j)

@[simp] lemma moment_monomial (m : ℕ → ℝ) (j : ℕ) (a : ℝ) :
    momentFunctional m (Polynomial.monomial j a) = a*m j := by
  simp [momentFunctional, Polynomial.lsum, Polynomial.sum_monomial_index]

@[simp] lemma moment_pow (m : ℕ → ℝ) (j : ℕ) :
    momentFunctional m (Polynomial.X^j) = m j := by
  rw [← Polynomial.monomial_one_right_eq_X_pow, moment_monomial, one_mul]

def weight (m : ℕ → ℝ) (n p : ℕ) : ℝ :=
  (n.choose p : ℝ)*difference m (n-p) p

def bernsteinBasis (n d : ℕ) (x : ℝ) : ℝ :=
  (n.choose d : ℝ) * x^d * (1-x)^(n-d)

abbrev I := Set.Icc (0 : ℝ) 1

def coordinate : C(I, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

def falling (n j : ℕ) : C(I, ℝ) :=
  ∏ r ∈ range j, ((1-(r : ℝ)/n)⁻¹) • (coordinate - ((r : ℝ)/n) • 1)

def gridMeasure (m : ℕ → ℝ) (n : ℕ) : Measure I :=
  ∑ p : Fin (n+1), ENNReal.ofReal (weight m n p) • Measure.dirac (bernstein.z p)

instance gridMeasure_finite (m : ℕ → ℝ) (n : ℕ) : IsFiniteMeasure (gridMeasure m n) := by
  constructor
  simp only [gridMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun _ _ => ENNReal.ofReal_lt_top)

def gridFiniteMeasure (m : ℕ → ℝ) (n : ℕ) : FiniteMeasure I :=
  ⟨gridMeasure m n, inferInstance⟩

def CM (g : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (⊤ : ℕ∞) g (Set.Ioi 0) ∧
  ∀ r : ℕ, ∀ t : ℝ, 0 < t → 0 ≤ (-1 : ℝ)^r * iteratedDeriv r g t

abbrev Positive := {t : ℝ // 0 < t}

def powerTest (t : Positive) : C(I, ℝ) :=
  ⟨fun v => (v : ℝ) ^ (t : ℝ), (Real.continuous_rpow_const t.property.le).comp continuous_subtype_val⟩

def unitPower (n : ℕ) : C(I, I) :=
  ⟨fun v => ⟨(v : ℝ)^n, ⟨pow_nonneg v.property.1 _, pow_le_one₀ v.property.1 v.property.2⟩⟩,
    (continuous_subtype_val.pow n).subtype_mk _⟩

def gridTime (t : ℝ) (n : ℕ) : ℝ := (⌊t*((n : ℝ)+1)⌋₊ + 1 : ℕ) / ((n : ℝ)+1)

end TriangularUniversal.PositiveMixture

open MeasureTheory
namespace TriangularUniversal
open PositiveMixture

def powerPotential (v : I) (t : ℝ) : ℝ := (v : ℝ)^t

instance nonzeroSite_countable : Countable NonzeroSite :=
  ((Set.countable_range triangularPoint).mono (fun _ h => h.1)).to_subtype

end TriangularUniversal

end
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Lattice
attribute [-instance] _root_.OAI.TriangularUniversal.instCoeFunLPFunctionForallPlaneComplex _root_.OAI.TriangularUniversal.pointsMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace TriangularUniversal
lemma triangularPoint_eq_zero_iff (v : ℤ × ℤ) : triangularPoint v=0 ↔ v=0 := by
  rw [← triangularPoint_zero]
  exact triangularPoint_injective.eq_iff

def nonzeroLatticeEquiv : {v : ℤ × ℤ // v≠0} ≃ NonzeroSite := Equiv.ofBijective
  (fun v => ⟨triangularPoint v.val,⟨⟨v.val,rfl⟩,fun h => v.property ((triangularPoint_eq_zero_iff _).mp h)⟩⟩)
  (by
    constructor
    · intro v w he
      apply Subtype.ext
      exact triangularPoint_injective (congrArg Subtype.val he)
    · intro x
      obtain ⟨v,hv⟩ := x.property.1
      refine ⟨⟨v,?_⟩,?_⟩
      · intro h
        exact x.property.2 (hv.symm.trans ((triangularPoint_eq_zero_iff _).mpr h))
      · exact Subtype.ext hv)
end TriangularUniversal
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Schwartz
attribute [-instance] _root_.OAI.TriangularUniversal.instDiscreteTopologySubtypePlaneMemSubmoduleIntTriangularModule _root_.OAI.TriangularUniversal.instIsZLatticeRealPlaneTriangularModule _root_.OAI.TriangularUniversal.nonzeroSite_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped FourierTransform SchwartzMap
open Complex MeasureTheory FourierTransform
namespace AtomicTriangular

def complexSchwartz (f : 𝓢(Plane,ℝ)) : 𝓢(Plane,ℂ) := f.postcompCLM Complex.ofRealCLM
def schwartzLP (f : 𝓢(Plane,ℝ)) : TriangularUniversal.LPFunction where
  toFun := complexSchwartz f
  continuous := (complexSchwartz f).continuous
  integrable := (complexSchwartz f).integrable
  fourierIntegrable := (𝓕 (complexSchwartz f)).integrable
  momentIntegrable := by simpa only [pow_one] using (complexSchwartz f).integrable_pow_mul volume 1
  bound := SchwartzMap.seminorm ℝ 0 0 (complexSchwartz f)
  norm_bound := SchwartzMap.norm_le_seminorm ℝ (complexSchwartz f)
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Gaussian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal
open Complex MeasureTheory
namespace AtomicTriangular

def gaussPot (α : ℝ) (s : ℝ) : ℝ := Real.exp (-Real.pi*α*s)
end AtomicTriangular
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Energy_Potentials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter MeasureTheory
namespace TriangularUniversal
def gaussPot (α s : ℝ) : ℝ := Real.exp (-Real.pi*α*s)
open PositiveMixture
end TriangularUniversal
end

end OAI
end


