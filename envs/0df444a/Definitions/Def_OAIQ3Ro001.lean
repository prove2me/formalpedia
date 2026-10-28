-- Prove2me | Definitions.Def_OAIQ3Ro001
-- name    : OAIQ3Ro001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T06:36:46.508046+00:00
-- url     : https://prove2.me/theorems/6fb25ec6-819f-489a-938f-cb7e816b98ff
-- title:
--   Definitions bundle OAIQ3Ro001 of the split of OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 130 declarations of OpenAI's Lean: 86 definitions, 1 inductive type or structure, 5 instances and 38 theorems. The definitions and types are `OAI.Rokhlin.ComplementSplit.restIndex`, `OAI.Rokhlin.DifferencePolynomial`, `OAI.Rokhlin.Dissociated`, `OAI.Rokhlin.HasEssentialTotalRange`, `OAI.Rokhlin.HasFixedInjectiveSquares`, `OAI.Rokhlin.JoiningOperator.IsRectangle`, `OAI.Rokhlin.JoiningOperator.instMeasurableSpaceCircle_solutions`, `OAI.Rokhlin.JoiningOperator.instMeasurableSpaceCircle_solutions_1`, `OAI.Rokhlin.JoiningOperator.instMeasurableSpaceSubtypeAEEqFunComplexMemAddSubgroupLpOfNatENNReal_solutions`, `OAI.Rokhlin.JoiningOperator.instMeasurableSpaceSubtypeAEEqFunComplexMemAddSubgroupLpOfNatENNReal_solutions_1`, `OAI.Rokhlin.JoiningOperator.pullEquiv`, `OAI.Rokhlin.JoiningOperator.weightedTest`, `OAI.Rokhlin.LagCesaroBound`, `OAI.Rokhlin.ProjectiveCharacters`, `OAI.Rokhlin.RationalSpanKey`, `OAI.Rokhlin.SequentialMixing`, `OAI.Rokhlin.Spaced`, `OAI.Rokhlin.StrongUnitary.instMeasurableSpaceCircle_solutions`, `OAI.Rokhlin.StrongUnitary.instMeasurableSpaceCircle_solutions_1`, `OAI.Rokhlin.StrongUnitary.instMeasurableSpaceCircle_solutions_2`, `OAI.Rokhlin.StrongUnitary.normalizeA`, `OAI.Rokhlin.StrongUnitary.normalizeB`, `OAI.Rokhlin.StrongUnitary.normalizeC`, `OAI.Rokhlin.StrongUnitary.normalizeD`, `OAI.Rokhlin.StrongUnitary.spectralCoords`, `OAI.Rokhlin.StrongUnitary.subgroupVersion`, `OAI.Rokhlin.VectorMeasurable`, `OAI.Rokhlin.aeLpTime`, `OAI.Rokhlin.cesaro`, `OAI.Rokhlin.characterAlgebra`, `OAI.Rokhlin.circleComplete`, `OAI.Rokhlin.circleMapComplex`, `OAI.Rokhlin.clippedConditional`, `OAI.Rokhlin.commutingRangeUnitary`, `OAI.Rokhlin.compactSeed`, `OAI.Rokhlin.compactSeedWeight`, `OAI.Rokhlin.completedFactor`, `OAI.Rokhlin.conditionalShannon`, `OAI.Rokhlin.conjugateOperator`, `OAI.Rokhlin.cyclicGenerator` and 47 more.
--
--   **Sources.** They come from these modules of lean/OAI/Dynamics/MultipleMixing, in whole or in part: [`MultipleMixing_Entropy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Entropy.lean), [`MultipleMixing_ExactLines`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/ExactLines.lean), [`MultipleMixing_FibreMeasures`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/FibreMeasures.lean), [`MultipleMixing_Foundations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Foundations.lean), [`MultipleMixing_HilbertCodes`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/HilbertCodes.lean), [`MultipleMixing_Joinings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Joinings.lean), [`MultipleMixing_Main`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Main.lean), [`MultipleMixing_OrbitCancellation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/OrbitCancellation.lean), [`MultipleMixing_Tail`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean), [`MultipleMixing_Tensors`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tensors.lean).
--
--   **Imports.** It imports the published bundle `Def_Rokhlin`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Ro002`; the statements `OAI.Rokhlin.ArrayObjects.Object.Rolled.grouped_restricted_fixed_squares`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.raw_correlation_zero`, `OAI.Rokhlin.ArrayObjects.Object.Rolled.saturated_correlation_zero`, `OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness`, `OAI.Rokhlin.finite_tail_entropy_zero`, `OAI.Rokhlin.polynomial_cancellation`, `OAI.Rokhlin.sequential_mixing_all`, `OAI.Rokhlin.tail_correlation_zero` and `OAI.Rokhlin.tail_finite_correlation_zero`; the proofs of `OAI.Rokhlin.finite_tail_entropy_zero`, `OAI.Rokhlin.last_centered_correlation_zero`, `OAI.Rokhlin.mixing_all_finite_orders`, `OAI.Rokhlin.polynomial_cancellation`, `OAI.Rokhlin.sequential_mixing_all`, `OAI.Rokhlin.tail_correlation_zero` and `OAI.Rokhlin.tail_finite_correlation_zero`.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Dynamics/MultipleMixing at commit adc7f12

import Mathlib
import Definitions.Def_Rokhlin

section
-- module Solutions.OAIQ3_Rok.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Foundations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Rokhlin

open MeasureTheory Filter
open scoped BigOperators ComplexConjugate

section

structure ProjectiveCharacters {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
    (η : Measure Y) (χ : L → Y → ℂ) : Prop where
  measurable : ∀ l, AEStronglyMeasurable (χ l) η
  modulus : ∀ l, ∀ᵐ y ∂η, ‖χ l y‖ = 1
  zero : χ 0 =ᵐ[η] fun _ => 1
  mul : ∀ l l', ∃ c : ℂ, ‖c‖ = 1 ∧
    (fun y => χ l y * χ l' y) =ᵐ[η] (fun y => c * χ (l + l') y)
  mean : ∀ l, l ≠ 0 → ∫ y, χ l y ∂η = 0

def Dissociated {L : Type*} [AddCommGroup L] (l : ℕ → L) : Prop :=
  ∀ s : Finset ℕ, s.Nonempty → ∀ ε : ℕ → Bool,
    (∑ i ∈ s, if ε i then l i else -l i) ≠ 0

end

open MeasureTheory Filter
open scoped BigOperators Topology

section

noncomputable def shannonEntropy {A : Type*} [Fintype A] (p : A → ℝ) : ℝ :=
  ∑ a, -p a * Real.log (p a)

end

section
open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

variable {Y L : Type*} [MeasurableSpace Y] [AddCommGroup L]
    {η : Measure Y} [IsProbabilityMeasure η] {χ : L → Y → ℂ}

def entropyWord {A : Type*} (F : ℕ → Y → A) (n : ℕ) : Y → (Fin n → A) :=
  fun y i => F i.val y

noncomputable def wordEntropy {A : Type*} [Fintype A] (F : ℕ → Y → A) (n : ℕ) : ℝ :=
  shannonEntropy (fun w => η.real (entropyWord F n ⁻¹' {w}))

end

open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexConjugate


section

variable {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (t : ι → Ω → Ω) (ht : ∀ i, MeasurePreserving (t i) μ μ) (l : Filter ι)

noncomputable def probabilityOne : Lp ℂ 2 μ :=
  indicatorConstLp 2 MeasurableSet.univ (measure_ne_top _ _) (1 : ℂ)

end

open Filter
open scoped BigOperators Topology InnerProductSpace

section

noncomputable def cesaro {E : Type*} [AddCommGroup E] [Module ℝ E]
    (v : ℕ → E) (N : ℕ) : E := (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, v n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def LagCesaroBound (v : ℕ → E) (c : ℕ → ℝ) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
    cesaro (fun n => |inner ℝ (v n) (v (n + h))|) N ≤ c h + ε

end

section

open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace ComplexConjugate

def DifferencePolynomial {L : Type*} [AddCommGroup L] : ℕ → (ℕ → L) → Prop
  | 0, P => ∃ l, ∀ m, P m = l
  | d + 1, P => ∀ h : ℕ, 0 < h → DifferencePolynomial d (fun m => P (m + h) - P m)

end

open scoped BigOperators
open Polynomial
section

section Torsion
variable {M : Type*} [AddCommGroup M] (G : M ≃ₗ[ℤ] M)

lemma map_mem_torsion {x : M} (hx : x ∈ Submodule.torsion ℤ M) :
    G x ∈ Submodule.torsion ℤ M := by
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
  apply (Submodule.mem_torsion_iff (G x)).mpr
  refine ⟨a, ?_⟩
  change (a : ℤ) • x = 0 at ha
  change (a : ℤ) • G x = 0
  simpa only [map_smul, map_zero] using congrArg G ha

lemma torsion_map_equiv : (Submodule.torsion ℤ M).map G.toLinearMap =
    Submodule.torsion ℤ M := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact map_mem_torsion G hy
  · intro hx
    exact ⟨G.symm x, map_mem_torsion G.symm hx, G.apply_symm_apply x⟩

noncomputable def torsionQuotEquiv : (M ⧸ Submodule.torsion ℤ M) ≃ₗ[ℤ]
    (M ⧸ Submodule.torsion ℤ M) :=
  Submodule.Quotient.equiv _ _ G (torsion_map_equiv G)

@[simp] lemma torsionQuotEquiv_mk (x : M) :
    torsionQuotEquiv G ((Submodule.torsion ℤ M).mkQ x) =
      (Submodule.torsion ℤ M).mkQ (G x) := rfl

noncomputable def torsionRestrictEquiv : (Submodule.torsion ℤ M) ≃ₗ[ℤ]
    (Submodule.torsion ℤ M) where
  toFun x := ⟨G x, map_mem_torsion G x.property⟩
  invFun x := ⟨G.symm x, map_mem_torsion G.symm x.property⟩
  left_inv x := by ext; exact G.symm_apply_apply x
  right_inv x := by ext; exact G.apply_symm_apply x
  map_add' x y := by ext; exact map_add G _ _
  map_smul' a x := by ext; exact map_smul G a (x : M)

end Torsion

end

open scoped BigOperators
section
variable {L : Type*} [AddCommGroup L] (G : L ≃ₗ[ℤ] L) (l : L)

noncomputable def cyclicOrbit : Submodule ℤ L :=
  Submodule.span ℤ (Set.range fun n : ℤ => (G ^ n) l)

noncomputable def initialOrbit (q : ℕ) : Submodule ℤ L :=
  Submodule.span ℤ ((fun n : ℕ => (G ^ n) l) '' {n | n < q})

end

section
variable {L : Type*} [AddCommGroup L] (G : L ≃ₗ[ℤ] L) (l : L)

lemma cyclicOrbit_zpow_mem (m : ℤ) {x : L} (hx : x ∈ cyclicOrbit G l) :
    (G ^ m) x ∈ cyclicOrbit G l := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨n, rfl⟩ := hy
    apply Submodule.subset_span
    exact ⟨m + n, by dsimp; rw [zpow_add, LinearEquiv.mul_apply]⟩
  | zero => simpa only [map_zero] using (zero_mem (cyclicOrbit G l))
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

lemma cyclicOrbit_apply_mem {x : L} (hx : x ∈ cyclicOrbit G l) :
    G x ∈ cyclicOrbit G l := by simpa using cyclicOrbit_zpow_mem G l 1 hx

lemma cyclicOrbit_symm_apply_mem {x : L} (hx : x ∈ cyclicOrbit G l) :
    G.symm x ∈ cyclicOrbit G l := by simpa using cyclicOrbit_zpow_mem G l (-1) hx

noncomputable def cyclicOrbitEquiv : cyclicOrbit G l ≃ₗ[ℤ] cyclicOrbit G l where
  toFun x := ⟨G x, cyclicOrbit_apply_mem G l x.property⟩
  invFun x := ⟨G.symm x, cyclicOrbit_symm_apply_mem G l x.property⟩
  left_inv x := by ext; exact G.symm_apply_apply x
  right_inv x := by ext; exact G.apply_symm_apply x
  map_add' x y := by ext; exact map_add G _ _
  map_smul' a x := by ext; exact map_smul G a (x : L)

noncomputable def cyclicGenerator : cyclicOrbit G l :=
  ⟨l, Submodule.subset_span ⟨0, by simp⟩⟩

end

open MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate


end Rokhlin

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

def rowEntropy (p : A → ℝ) : ℝ :=
  shannonEntropy p - Real.negMulLog (∑ a, p a)

def conditionalShannon (p : B → A → ℝ) : ℝ := ∑ b, rowEntropy (p b)

end

section
open MeasureTheory Filter
open scoped BigOperators Topology
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

def randomEntropy (F : Ω → A) : ℝ := shannonEntropy (fun a => μ.real (F ⁻¹' {a}))

def randomConditionalEntropy (F : Ω → A) (G : Ω → B) : ℝ :=
  conditionalShannon (fun b a => μ.real {x | G x = b ∧ F x = a})

end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B C : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Fintype C]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    [MeasurableSpace C] [MeasurableSingletonClass C]

def integerWord (F : ℤ → Ω → A) (t : ℤ) (n : ℕ) : Ω → Fin n → A :=
  fun x i => F (t+i.val) x

end

section
open MeasureTheory Filter Set
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)

@[instance_reducible]
def completedFactor (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[m₀] s ∧ ∃ t : Set Ω, MeasurableSet[m] t ∧
    ∀ᵐ x ∂μ, x ∈ s ↔ x ∈ t
  measurableSet_empty := ⟨@MeasurableSet.empty Ω m₀,∅,@MeasurableSet.empty Ω m,Eventually.of_forall fun _ => Iff.rfl⟩
  measurableSet_compl := by
    rintro s ⟨hs,t,ht,he⟩
    exact ⟨hs.compl,tᶜ,ht.compl,he.mono fun x hx => not_congr hx⟩
  measurableSet_iUnion := by
    intro s hs
    choose t ht he using fun n => (hs n).2
    refine ⟨MeasurableSet.iUnion fun n => (hs n).1,⋃ n, t n,MeasurableSet.iUnion ht,?_⟩
    filter_upwards [ae_all_iff.mpr he] with x hx
    simp only [mem_iUnion]
    exact exists_congr fun n => hx n

lemma completedFactor_le (m : MeasurableSpace Ω) : completedFactor (m₀ := m₀) μ m ≤ m₀ :=
  fun _ hs => hs.1

end

section
open MeasureTheory Filter Set
open scoped Topology BigOperators symmDiff
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

variable {B : Type*} [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

def pickFiniteBit (v : B → Bool) : B :=
  if h : ∃ b, v b = true then Classical.choose h else Classical.choice ‹Nonempty B›

end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A B : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    [MeasurableSpace B] [MeasurableSingletonClass B]

abbrev processPast (F : ℤ → Ω → A) (t : ℤ) : MeasurableSpace Ω :=
  ⨆ n : ℕ, MeasurableSpace.comap (integerWord F (t-n) n) inferInstance

abbrev processFull (F : ℤ → Ω → A) : MeasurableSpace Ω :=
  ⨆ n : ℕ, MeasurableSpace.comap (integerWord F (-(n:ℤ)) (2*n+1)) inferInstance

end

section
open Filter
open scoped Topology
variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
local instance complete_iInf (K : ℕ → Submodule 𝕜 H) [∀ n, CompleteSpace (K n)] :
    CompleteSpace ↥(⨅ n, K n) := by
  have h : IsClosed (↑(⨅ n, K n) : Set H) := by
    simp only [Submodule.coe_iInf]
    exact isClosed_iInter fun n => (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (K n))).isClosed
  exact h.completeSpace_coe

end

section
open MeasureTheory Filter
variable {Ω A : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω)
    [MeasurableSpace A]

abbrev processTail (F : ℤ → Ω → A) : MeasurableSpace Ω :=
  ⨅ n : ℕ, completedFactor (m₀ := m₀) μ (processPast F (-(n:ℤ)))

end

open MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

def clippedConditional (m : MeasurableSpace Ω) (f : Ω → ℝ) : Ω → ℝ :=
  fun x => max 0 (min 1 (μ[f | m] x))

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_HilbertCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section

open scoped InnerProductSpace CStarAlgebra
open ContinuousLinearMap

open MeasureTheory Filter
open scoped BigOperators Topology


variable {Ω : Type*} [MeasurableSpace Ω]

section EssentialRanges

variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup J] [NormedSpace ℂ J]

def HasEssentialTotalRange (μ : Measure X) (F : X → E →L[ℂ] H) : Prop :=
  ∀ p : Submodule ℂ H, IsClosed (p : Set H) →
    (∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ p) → p = ⊤

end EssentialRanges

section
variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def intertwinerAlgebra (N : E →L[ℂ] H) :
    StarSubalgebra ℝ ((H →L[ℂ] H) × (E →L[ℂ] E)) where
  carrier := {p | p.1 ∘L N = N ∘L p.2 ∧ star p.1 ∘L N = N ∘L star p.2}
  add_mem' := by
    rintro ⟨A,B⟩ ⟨C,D⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
    change (A+C) ∘L N = N ∘L (B+D) ∧ star (A+C) ∘L N = N ∘L star (B+D)
    simp only [add_comp, comp_add, star_add, h₁, h₂, h₃, h₄, and_self]
  mul_mem' := by
    rintro ⟨A,B⟩ ⟨C,D⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
    change (A ∘L C) ∘L N = N ∘L (B ∘L D) ∧
      star (A*C) ∘L N = N ∘L star (B*D)
    constructor
    · rw [comp_assoc, h₃, ← comp_assoc, h₁, comp_assoc]
    · simp only [star_mul]
      change (star C ∘L star A) ∘L N = N ∘L (star D ∘L star B)
      rw [comp_assoc, h₂, ← comp_assoc, h₄, comp_assoc]
  algebraMap_mem' := by
    intro r
    constructor <;> ext x <;> simp [← algebraMap_star_comm]
  star_mem' := by
    rintro ⟨A,B⟩ ⟨h₁,h₂⟩
    exact ⟨h₂, by simpa using h₁⟩

instance intertwinerAlgebra_isClosed (N : E →L[ℂ] H) :
    IsClosed (intertwinerAlgebra N : Set ((H →L[ℂ] H) × (E →L[ℂ] E))) := by
  change IsClosed {p : (H →L[ℂ] H) × (E →L[ℂ] E) |
    p.1 ∘L N = N ∘L p.2 ∧ star p.1 ∘L N = N ∘L star p.2}
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_eq (by fun_prop) (by fun_prop)

end

variable {X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]

def HasFixedInjectiveSquares (μ : Measure X) (F : X → H₂ →L[ℂ] H₁) : Prop :=
  ∃ P : H₂ →L[ℂ] H₂, ∃ Q : H₁ →L[ℂ] H₁,
    Function.Injective P ∧ Function.Injective Q ∧
    (∀ᵐ x ∂μ, (F x).adjoint ∘L F x = P) ∧
    (∀ᵐ x ∂μ, F x ∘L (F x).adjoint = Q)

end

section
open MeasureTheory ProbabilityTheory Set Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
abbrev RationalSpanKey := List ((ℚ × ℚ) × ℕ)
def rationalSpanTest (v : ℕ → H) (t : RationalSpanKey) : H :=
  (t.map (fun p => ((p.1.1 : ℂ) + p.1.2 * Complex.I) • v p.2)).sum

end

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Joinings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
namespace JoiningOperator
variable {A B C D : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
def IsRectangle (F : C →L[ℂ] A) (G : D →L[ℂ] B) (K : B →L[ℂ] A) (N : D →L[ℂ] C) : Prop :=
  F ∘L N = K ∘L G ∧ F.adjoint ∘L K = N ∘L G.adjoint
end JoiningOperator
end

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal

section ConditionalMarginals

variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  {m : Measure (U × Y)} {ρ : Measure Y}

def weightedTest (hy : MeasurePreserving Prod.snd m ρ)
    (A : Set U) (hA : MeasurableSet A) (h : Lp ℂ 2 ρ) : Lp ℂ 2 m :=
  (((Lp.memLp h).comp_measurePreserving hy).indicator (measurable_fst hA)).toLp _


end ConditionalMarginals


variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y} {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
  {ν : Measure X} {ρ : Measure Y}

omit [IsProbabilityMeasure μ] in
lemma snd_observation (hu : Measurable u) (hy : MeasurePreserving y μ ρ) :
    MeasurePreserving Prod.snd (μ.map (fun ω => (u ω, y ω))) ρ := by
  refine ⟨measurable_snd, ?_⟩
  rw [Measure.map_map measurable_snd (hu.prodMk hy.measurable)]
  exact hy.map_eq

end JoiningOperator

section
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace
variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J] [CompleteSpace J]

def VectorMeasurable (F : X → E →L[ℂ] H) : Prop :=
  ∀ v : E, StronglyMeasurable (fun x => F x v)

end

section

open MeasureTheory Filter
open scoped Topology ProbabilityTheory


variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

noncomputable def translateProbability (ρ : ProbabilityMeasure G) (u v : G) :
    ProbabilityMeasure G :=
  ρ.map (f := fun a => u * a * v⁻¹)
    ((continuous_const.mul continuous_id).mul continuous_const).measurable.aemeasurable

@[simp] theorem translateProbability_toMeasure (ρ : ProbabilityMeasure G) (u v : G) :
    (translateProbability ρ u v : Measure G) =
      (ρ : Measure G).map (fun a => u * a * v⁻¹) := rfl

@[simp] theorem translateProbability_one_right_toMeasure
    (ρ : ProbabilityMeasure G) (u : G) :
    (translateProbability ρ u 1 : Measure G) = (ρ : Measure G).map (u * ·) := by
  simp [translateProbability_toMeasure]

end

namespace StrongUnitary
open MeasureTheory ProbabilityTheory
open scoped Topology
variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [NormedSpace ℂ H₁] [SecondCountableTopology H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℂ H₂] [SecondCountableTopology H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℂ H₃] [SecondCountableTopology H₃]
  [NormedAddCommGroup H₄] [NormedSpace ℂ H₄] [SecondCountableTopology H₄]

def normalizeA (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (a : H₂ ≃ₗᵢ[ℂ] H₁) : H₄ ≃ₗᵢ[ℂ] H₄ := d₀.trans (a.trans (d₀.trans a₀).symm)
def normalizeB (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (b : H₄ ≃ₗᵢ[ℂ] H₃) : H₄ ≃ₗᵢ[ℂ] H₄ := b.trans b₀.symm
def normalizeC (a₀ : H₂ ≃ₗᵢ[ℂ] H₁) (b₀ : H₄ ≃ₗᵢ[ℂ] H₃) (d₀ : H₄ ≃ₗᵢ[ℂ] H₂)
    (c : H₃ ≃ₗᵢ[ℂ] H₁) : H₄ ≃ₗᵢ[ℂ] H₄ := b₀.trans (c.trans (d₀.trans a₀).symm)
def normalizeD (d₀ : H₄ ≃ₗᵢ[ℂ] H₂) (d : H₄ ≃ₗᵢ[ℂ] H₂) : H₄ ≃ₗᵢ[ℂ] H₄ := d.trans d₀.symm

end StrongUnitary

section

open MeasureTheory ContinuousLinearMap InnerProductSpace Filter
open scoped InnerProductSpace ComplexOrder Topology BigOperators


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Conjugation

noncomputable def conjugateOperator (U : H ≃ₗᵢ[ℂ] H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  U.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.toContinuousLinearMap

omit [CompleteSpace H] in
@[simp] theorem conjugateOperator_apply (U : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) (v : H) :
    conjugateOperator U Q v = U (Q (U.symm v)) := rfl

omit [CompleteSpace H] in
@[simp] theorem conjugateOperator_mul (U V : H ≃ₗᵢ[ℂ] H) (Q : H →L[ℂ] H) :
    conjugateOperator (U * V) Q = conjugateOperator U (conjugateOperator V Q) := rfl

end Conjugation
section CompactSeed

noncomputable def quadraticFormCLM (v : H) : (H →L[ℂ] H) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ H v)).restrictScalars ℝ)

omit [CompleteSpace H] in
@[simp] theorem quadraticFormCLM_apply (v : H) (Q : H →L[ℂ] H) :
    quadraticFormCLM v Q = (inner ℂ v (Q v)).re := rfl

noncomputable def compactSeedWeight (w : ℕ → H) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ n / (1 + ‖w n‖ ^ 2)

end CompactSeed

noncomputable def compactSeed (w : ℕ → H) : H →L[ℂ] H :=
  ∑' n, (compactSeedWeight w n : ℂ) • rankOne ℂ (w n) (w n)

end

section
open Module.End ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def unitaryPart (A : H →L[ℂ] H) : Bool → selfAdjoint (H →L[ℂ] H)
  | false => realPart A
  | true => imaginaryPart A

end

section
variable {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [Group G]

lemma eigenvalue_norm_one (U : H ≃ₗᵢ[ℂ] H) {v : H} (hv : v ≠ 0)
    {χ : ℂ} (he : U v = χ • v) : ‖χ‖ = 1 := by
  have h := congrArg norm he
  rw [U.norm_map, norm_smul] at h
  exact (mul_right_cancel₀ (norm_ne_zero_iff.mpr hv) (h.symm.trans (one_mul _).symm))

lemma eigenvalue_mul (U : G →* (H ≃ₗᵢ[ℂ] H)) {v : H} (hv : v ≠ 0)
    (χ : G → ℂ) (he : ∀ g, U g v = χ g • v) (g h : G) :
    χ (g*h) = χ g * χ h := by
  apply (smul_left_injective ℂ hv)
  change χ (g*h) • v = (χ g * χ h) • v
  rw [←he, map_mul]
  change U g (U h v) = _
  rw [he, map_smul, he, smul_smul, mul_comm]

def eigenCharacter (U : G →* (H ≃ₗᵢ[ℂ] H)) {v : H} (hv : v ≠ 0)
    (χ : G → ℂ) (he : ∀ g, U g v = χ g • v) : G →* Circle where
  toFun g := ⟨χ g, by
    change χ g ∈ Metric.sphere 0 1
    simpa only [Metric.mem_sphere, dist_zero_right] using eigenvalue_norm_one (U g) hv (he g)⟩
  map_one' := by
    apply Subtype.ext
    change χ 1 = 1
    apply (smul_left_injective ℂ hv)
    change χ 1 • v = (1 : ℂ) • v
    rw [←he, map_one, one_smul]
    rfl
  map_mul' g h := Subtype.ext (eigenvalue_mul U hv χ he g h)

end

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tensors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory
open scoped InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
lemma memLp_tensor (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    MemLp (fun p : X × Y => g p.1 * h p.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    ((g.1.stronglyMeasurable.comp_measurable measurable_fst).mul
      (h.1.stronglyMeasurable.comp_measurable measurable_snd)).aestronglyMeasurable).mpr
  change Integrable (fun p : X × Y => ‖g p.1 * h p.2‖ ^ 2) (μ.prod ν)
  simp only [norm_mul, mul_pow]
  exact ((Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mul_prod
    ((Lp.memLp h).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))

def tensorLp (g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (memLp_tensor g h).toLp _

end

section
open MeasureTheory ProbabilityTheory
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

def ratioKernel (ρ : Measure G) : Kernel G (G × G) :=
  (Kernel.id.prod (Kernel.const G ρ)).map (fun p : G × G => (p.1*p.2,p.2))

instance ratioKernel_markov (ρ : Measure G) [IsProbabilityMeasure ρ] :
    IsMarkovKernel (ratioKernel ρ) := by
  unfold ratioKernel
  exact Kernel.IsMarkovKernel.map _ (measurable_fst.mul measurable_snd |>.prodMk measurable_snd)

end

namespace JoiningOperator

open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped InnerProductSpace ENNReal


variable {Ω U X Y C : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {η : Measure U} {ν : Measure X} {ρ : Measure Y}
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]
local instance instMeasurableSpaceSubtypeAEEqFunComplexMemAddSubgroupLpOfNatENNReal_solutions : MeasurableSpace (Lp ℂ 2 ν) := borel _
end JoiningOperator

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
open scoped ENNReal
namespace JoiningOperator
local instance instFactNeENNRealOfNatTop_solutions : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
variable {Ω U X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y] [Nonempty X] [Nonempty Y]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {η : Measure U} [IsProbabilityMeasure η]
  {ν : Measure X} {ρ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure ρ]
  {u : Ω → U} {x : Ω → X} {y : Ω → Y}
  {κ : Kernel U (X × Y)} [IsMarkovKernel κ]

local instance instMeasurableSpaceSubtypeAEEqFunComplexMemAddSubgroupLpOfNatENNReal_solutions_1 : MeasurableSpace (Lp ℂ 2 ν) := borel _
end JoiningOperator

end

namespace StrongUnitary

open MeasureTheory


section
variable {H I X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]
local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
end

variable {H J X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [SecondCountableTopology H]
local instance instMeasurableSpaceCircle_solutions_1 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))

def subgroupVersion (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (g : H ≃ₗᵢ[ℂ] H) : S := by
  classical
  exact if h : g ∈ S then ⟨g,h⟩ else 1

def spectralCoords (S : Subgroup (H ≃ₗᵢ[ℂ] H)) (γ : J → S →* Circle)
    (g : H ≃ₗᵢ[ℂ] H) : J → Circle := fun j => γ j (subgroupVersion S g)


end StrongUnitary

section
open MeasureTheory ProbabilityTheory

namespace StrongUnitary
local instance instMeasurableSpaceCircle_solutions_2 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
universe u
end StrongUnitary
end

section
open MeasureTheory ProbabilityTheory ContinuousLinearMap
local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
universe u
end

section
open MeasureTheory
variable {X G : Type*} [TopologicalSpace X] [CompactSpace X] [Group G]

def characterAlgebra (χ : G →* C(X,ℂ)) (hs : ∀ g, star (χ g) = χ g⁻¹) :
    StarSubalgebra ℂ C(X,ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (Set.range χ)
  star_mem' := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem f hf =>
      obtain ⟨g,rfl⟩ := hf
      rw [hs]
      exact Algebra.subset_adjoin ⟨g⁻¹,rfl⟩
    | algebraMap c =>
      exact (Algebra.adjoin ℂ (Set.range χ)).algebraMap_mem (star c)
    | add f g hf hg hfs hgs =>
      rw [star_add]
      exact (Algebra.adjoin ℂ (Set.range χ)).add_mem hfs hgs
    | mul f g hf hg hfs hgs =>
      rw [star_mul]
      exact (Algebra.adjoin ℂ (Set.range χ)).mul_mem hgs hfs

end

section
open MeasureTheory
open scoped ENNReal
variable {I : Type*}

def torusWordCircle : FreeGroup I →* C((I → Circle), Circle) :=
  FreeGroup.lift (fun i => ⟨fun x => x i, continuous_apply i⟩)

def circleMapComplex {X : Type*} [TopologicalSpace X] : C(X,Circle) →* C(X,ℂ) where
  toFun f := ⟨fun x => (f x : ℂ), continuous_subtype_val.comp f.continuous⟩
  map_one' := by ext x; rfl
  map_mul' f g := by ext x; rfl

def torusWord : FreeGroup I →* C((I → Circle),ℂ) :=
  circleMapComplex.comp torusWordCircle

@[simp] lemma torusWord_of (i : I) (x : I → Circle) :
    torusWord (FreeGroup.of i) x = (x i : ℂ) := by
  change (torusWordCircle (FreeGroup.of i) x : ℂ) = _
  simp only [torusWordCircle, FreeGroup.lift_apply_of]
  rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

local instance instMeasurableSpaceCircle_solutions_1 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance instBorelSpaceCircle_solutions_1 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

end

variable {I : Type*}

lemma torusWordCircle_of (i : I) (x : I → Circle) :
    torusWordCircle (FreeGroup.of i) x = x i := by
  simp only [torusWordCircle, FreeGroup.lift_apply_of]
  rfl

lemma torusWordCircle_mul (w : FreeGroup I) (x y : I → Circle) :
    torusWordCircle w (x*y) = torusWordCircle w x * torusWordCircle w y := by
  induction w using OAI.freeGroupInductionOn with
  | one => simp only [map_one, ContinuousMap.one_apply, one_mul]
  | of i => simp only [torusWordCircle_of, Pi.mul_apply]
  | inv_of i hi =>
    simp only [map_inv, ContinuousMap.inv_apply, hi, mul_inv_rev]
    exact mul_comm _ _
  | mul a b ha hb =>
    simp only [map_mul, ContinuousMap.mul_apply, ha, hb]
    ac_rfl

lemma torusWordCircle_one (w : FreeGroup I) : torusWordCircle w (1 : I → Circle) = 1 := by
  have h := torusWordCircle_mul w (1 : I → Circle) 1
  simp only [one_mul] at h
  exact mul_left_cancel (by simpa only [mul_one] using h.symm :
    torusWordCircle w 1 * torusWordCircle w 1 = torusWordCircle w 1 * 1)

def torusCharacter (w : FreeGroup I) : (I → Circle) →* Circle where
  toFun := torusWordCircle w
  map_one' := torusWordCircle_one w
  map_mul' := torusWordCircle_mul w


end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_ExactLines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory
open scoped ENNReal
variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

variable {Ω X : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {ν : Measure X} {x : Ω → X}

local instance instMeasurableSpaceCircle_solutions_2 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance instBorelSpaceCircle_solutions_2 : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

end

namespace JoiningOperator
open MeasureTheory ProbabilityTheory
open scoped ENNReal

section
local instance instMeasurableSpaceCircle_solutions : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance instBorelSpaceCircle_solutions : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))

end

local instance instMeasurableSpaceCircle_solutions_1 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))

end JoiningOperator

section
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
local instance instMeasurableSpaceCircle_solutions_3 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
end

namespace ComplementSplit
variable {I : Type*} [Fintype I] [DecidableEq I] {R : Finset I}

def restIndex (i : ↥(Rᶜ)) (j : ↥((R ∪ {(i : I)})ᶜ)) : {j : ↥(Rᶜ) // j ≠ i} :=
  ⟨⟨j,Finset.mem_compl.mpr (fun hj => Finset.mem_compl.mp j.property (Finset.mem_union_left _ hj))⟩,
    by
      intro h
      have he : (j : I) = i := congrArg Subtype.val h
      exact Finset.mem_compl.mp j.property (Finset.mem_union_right _ (Finset.mem_singleton.mpr he))⟩

end ComplementSplit

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I A B : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace A]
  (μ : I → Measure A) [∀ i, IsProbabilityMeasure (μ i)]

def hybrid (s : Finset I) (x : I → A × A) : I → A :=
  fun i => if i ∈ s then (x i).1 else (x i).2

end

namespace JoiningOperator
open MeasureTheory ContinuousLinearMap
variable {Ω X Y Z : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace Y] [MeasurableSpace Z]
  {μ : Measure Ω} {ν : Measure X} {ρ : Measure Y} {τ : Measure Z}
  {x : Ω → X} {y : Ω → Y}

omit [MeasurableSpace Ω] [MeasurableSpace Y] in
noncomputable def pullEquiv (e : X ≃ᵐ Z) (he : MeasurePreserving e ν τ) :
    Lp ℂ 2 τ ≃ₗᵢ[ℂ] Lp ℂ 2 ν where
  __ := Lp.compMeasurePreservingₗᵢ ℂ e he
  invFun := Lp.compMeasurePreserving e.symm (he.symm e)
  left_inv f := by
    change Lp.compMeasurePreserving e.symm (he.symm e) (Lp.compMeasurePreserving e he f) = f
    rw [←Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.self_comp_symm] using Lp.compMeasurePreserving_id_apply f
  right_inv f := by
    change Lp.compMeasurePreserving e he (Lp.compMeasurePreserving e.symm (he.symm e) f) = f
    rw [←Lp.compMeasurePreserving_comp_apply]
    simpa only [MeasurableEquiv.symm_comp_self] using Lp.compMeasurePreserving_id_apply f

end JoiningOperator

section
variable {I : Type*} [Fintype I] [DecidableEq I]
lemma pair_complement_nonempty (hk : 3 ≤ Fintype.card I) (i j : I) :
    (({i,j} : Finset I)ᶜ).Nonempty := by
  apply Finset.card_pos.mp
  have hc := Finset.card_compl ({i,j} : Finset I)
  have hp : ({i,j} : Finset I).card ≤ 2 := by
    by_cases h : i = j
    · simp [h]
    · simp [Finset.card_pair h]
  omega
end

section
open MeasureTheory
open scoped BigOperators
variable {I Y : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Y]
local instance instMeasurableSpaceCircle_solutions_4 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))

def circleComplete (i : I) (f : Y → Circle) (a : ↥(({i} : Finset I)ᶜ) → Y → Circle)
    (j : I) (y : Y) : Circle := if h : j = i then f y else (a ⟨j,by simpa using h⟩ y)⁻¹

end

section
open MeasureTheory ProbabilityTheory Set
variable {P Z U : Type*} [MeasurableSpace P] [MeasurableSpace Z] [MeasurableSpace U]

def essentialMembership (κ : Kernel U P) (S : Set (P × Z)) : Set (U × Z) :=
  {uz | κ uz.1 {p | (p,uz.2) ∈ S} = 1}

end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance instMeasurableSpaceCircle_solutions_5 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
end

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance instMeasurableSpaceCircle_solutions_6 : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
end

open MeasureTheory Set

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_FibreMeasures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory ContinuousLinearMap
variable {Z : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  (τ σ : Z → Z) (hτ : MeasurePreserving τ ξ ξ) (hσ : MeasurePreserving σ ξ ξ)

lemma lp_time_inverse (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) (v : Lp ℂ 2 ξ) :
    Lp.compMeasurePreservingₗᵢ ℂ τ hτ (Lp.compMeasurePreservingₗᵢ ℂ σ hσ v) = v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreservingₗᵢ ℂ σ hσ v) hτ,
    hτ.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving v hσ),hστ] with z h1 h2 h3
  exact h1.trans (h2.trans (congrArg (fun x => v x) h3))

def aeLpTime (hστ : ∀ᵐ z ∂ξ, σ (τ z) = z) : Lp ℂ 2 ξ ≃ₗᵢ[ℂ] Lp ℂ 2 ξ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ τ hτ)
    (fun v => ⟨Lp.compMeasurePreservingₗᵢ ℂ σ hσ v,lp_time_inverse ξ τ σ hτ hσ hστ v⟩)

end

section

open ContinuousLinearMap
open scoped InnerProductSpace

section

theorem partial_unitary_algebra {A : Type*} [Monoid A] [StarMul A]
    (a : A) (h₁ : a = star a * a * a) (h₂ : a = a * a * star a) :
    star a * a = a * star a ∧ IsStarProjection (star a * a) := by
  have hn : star a * a = a * star a := calc
    star a * a = star a * (a * a * star a) := congrArg (star a * ·) h₂
    _ = (star a * a * a) * star a := by simp only [mul_assoc]
    _ = a * star a := congrArg (· * star a) h₁.symm
  refine ⟨hn, ?_⟩
  apply IsStarProjection.mk
  · change (star a * a) * (star a * a) = star a * a
    calc
      (star a * a) * (star a * a) = (star a * a) * (a * star a) := by rw [hn]
      _ = ((star a * a) * a) * star a := by simp only [mul_assoc]
      _ = a * star a := by rw [← h₁]
      _ = star a * a := hn.symm
  · simp only [IsSelfAdjoint, star_mul, star_star]

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

theorem partial_unitary_range (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    (M.adjoint * M).range = M.range := by
  have hn := (partial_unitary_algebra M h₁ h₂).1
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    refine ⟨M.adjoint w, ?_⟩
    have hh := congrArg (fun A : H →L[ℂ] H => A w) hn
    exact hh.symm
  · rintro v ⟨w, rfl⟩
    refine ⟨M w, ?_⟩
    exact (congrArg (fun A : H →L[ℂ] H => A w) h₁).symm

theorem partial_unitary_range_adjoint (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    M.range = M.adjoint.range := by
  have ha₁ : M.adjoint = M * M.adjoint * M.adjoint := by
    change star M = M * star M * star M
    have hh := congrArg star h₂
    simpa only [← star_eq_adjoint, star_mul, star_star, mul_assoc] using hh
  have ha₂ : M.adjoint = M.adjoint * M.adjoint * M := by
    change star M = star M * star M * M
    have hh := congrArg star h₁
    simpa only [← star_eq_adjoint, star_mul, star_star, mul_assoc] using hh
  rw [← partial_unitary_range M h₁ h₂,
    ← partial_unitary_range M.adjoint (by simpa using ha₁) (by simpa using ha₂),
    adjoint_adjoint]
  exact congrArg (fun A : H →L[ℂ] H => A.range) (partial_unitary_algebra M h₁ h₂).1

theorem partial_unitary_norm_on_range (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (v : H) (hv : v ∈ M.range) :
    ‖M v‖ = ‖v‖ := by
  have hfix : (M.adjoint * M) v = v := by
    rcases hv with ⟨w, rfl⟩
    exact (congrArg (fun A : H →L[ℂ] H => A w) h₁).symm
  apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
  rw [← adjoint_inner_right]
  exact congrArg (fun w => (inner ℂ v w).re) hfix
end

open MeasureTheory Filter

end

section
open ContinuousLinearMap
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partial_unitary_fixed (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) {v : H} (hv : v ∈ M.range) :
    M.adjoint (M v) = v := by
  obtain ⟨w,rfl⟩ := hv
  exact (congrArg (fun A : H →L[ℂ] H => A w) h₁).symm

lemma partial_unitary_fixed' (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint)
    {v : H} (hv : v ∈ M.range) : M (M.adjoint v) = v := by
  have hn := (partial_unitary_algebra M h₁ h₂).1
  have hh := congrArg (fun A : H →L[ℂ] H => A v) hn
  exact hh.symm.trans (partial_unitary_fixed M h₁ hv)

def partialUnitary (M : H →L[ℂ] H)
    (h₁ : M = M.adjoint * M * M) (h₂ : M = M * M * M.adjoint) :
    M.range ≃ₗᵢ[ℂ] M.range where
  toFun v := ⟨M v,⟨v,rfl⟩⟩
  invFun v := ⟨M.adjoint v,by exact (partial_unitary_range_adjoint M h₁ h₂).ge ⟨v,rfl⟩⟩
  map_add' v w := Subtype.ext (M.map_add _ _)
  map_smul' c v := Subtype.ext (M.map_smul _ _)
  left_inv v := Subtype.ext (partial_unitary_fixed M h₁ v.property)
  right_inv v := Subtype.ext (partial_unitary_fixed' M h₁ h₂ v.property)
  norm_map' v := partial_unitary_norm_on_range M h₁ v.val v.property

def commutingRangeUnitary (M : H →L[ℂ] H) (V : H ≃ₗᵢ[ℂ] H)
    (hV : ∀ v, V (M v) = M (V v)) : M.range ≃ₗᵢ[ℂ] M.range where
  toFun v := ⟨V v,by obtain ⟨w,hw⟩ := v.property; exact ⟨V w,by change M (V w) = V v; exact (hV w).symm.trans (congrArg V hw)⟩⟩
  invFun v := ⟨V.symm v,by
    obtain ⟨w,hw⟩ := v.property
    refine ⟨V.symm w,?_⟩
    apply V.injective
    change V (M (V.symm w)) = V (V.symm v)
    rw [hV,V.apply_symm_apply,V.apply_symm_apply]
    exact hw⟩
  map_add' v w := Subtype.ext (V.map_add _ _)
  map_smul' c v := Subtype.ext (V.map_smul _ _)
  left_inv v := Subtype.ext (V.symm_apply_apply v)
  right_inv v := Subtype.ext (V.apply_symm_apply v)
  norm_map' v := V.norm_map v

end

section
open MeasureTheory

variable {Z H : Type*} [MeasurableSpace Z] (ξ : Measure Z)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : H →ₗᵢ[ℂ] Lp ℂ 2 ξ) (D S : H ≃ₗᵢ[ℂ] H) (v : H)

def labelOrbitLP (p : ℤ × ℤ) : Lp ℂ 2 ξ := U ((D ^ p.1) ((S ^ p.2) v))
end

section
open MeasureTheory Set
open scoped ENNReal
variable {Z C W : Type*} [MeasurableSpace Z] [MeasurableSpace C]
  [MeasurableSingletonClass C] [MeasurableSpace W]
  (ξ : Measure Z) (ψ : Z → C)

def positiveLevels : Set C := {b | ξ {z | ψ z = b} ≠ 0}

end

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_OrbitCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Set
variable {U Z C : Type*}
  [MeasurableSpace U]
  [MeasurableSpace Z]
  [MeasurableSpace C]
  [MeasurableSingletonClass C]
  {S : Set (U × Z)}
  (ψ : U × Z → C)
  (hψ : Measurable ψ)

def fibreLevelEquiv (a b : U) (e : {z // (a,z) ∈ S} ≃ {z // (b,z) ∈ S})
    (D : C ≃ C) (he : ∀ z, ψ (b,(e z).val) = D (ψ (a,z.val))) (c : C) :
    {z // (a,z) ∈ S ∧ ψ (a,z) = D.symm c} ≃ {z // (b,z) ∈ S ∧ ψ (b,z) = c} :=
  Equiv.ofBijective (fun z => ⟨(e ⟨z.val,z.property.1⟩).val,⟨(e _).property,by
    rw [he,z.property.2,D.apply_symm_apply]⟩⟩) (by
    constructor
    · intro z w h
      have hv : (e ⟨z.val,z.property.1⟩).val = (e ⟨w.val,w.property.1⟩).val := congrArg (fun w : {z // (b,z) ∈ S ∧ ψ (b,z) = c} => w.val) h
      have hh : e ⟨z.val,z.property.1⟩ = e ⟨w.val,w.property.1⟩ := Subtype.ext hv
      have h' := e.injective hh
      exact Subtype.ext (Subtype.mk.inj h')
    · intro w
      let z := e.symm ⟨w.val,w.property.1⟩
      have hz : ψ (a,z.val) = D.symm c := by
        apply D.injective
        rw [D.apply_symm_apply,←he,e.apply_symm_apply]
        exact w.property.2
      refine ⟨⟨z.val,⟨z.property,hz⟩⟩,?_⟩
      apply Subtype.ext
      have hv : (e z).val = w.val := congrArg Subtype.val (e.apply_symm_apply ⟨w.val,w.property.1⟩)
      exact hv)

end

section
open MeasureTheory Set
variable {U Z C H : Type*}
  [MeasurableSpace U]
  [MeasurableSpace Z]
  [MeasurableSpace C]
  [MeasurableSingletonClass C]
  {S : Set (U × Z)}
  (ψ : U × Z → C)
  (hψ : Measurable ψ)
  (D : C ≃ C)
  (τ : H → C)
  (G : H ≃ H)
  (hG : ∀ h, τ (G h) = D.symm (τ h))
include hG in
omit [MeasurableSpace C] [MeasurableSingletonClass C] in
lemma block_iterate (n : ℕ) (l : H) :
    τ ((G^[n]) l) = (D.symm^[n]) (τ l) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',hG,ih,Function.iterate_succ_apply']

def movingBlockCodeEquiv (a : U) (e : H ≃ {z // (a,z) ∈ S})
    (he : ∀ l, ψ (a,(e l).val) = τ l) (b : C) (n : ℕ) :
    {l // τ l = b} ≃ {z // (a,z) ∈ S ∧ ψ (a,z) = (D.symm^[n]) b} :=
  (Equiv.subtypeEquiv (p := fun l => τ l = b)
    (q := fun z : {z // (a,z) ∈ S} => ψ (a,z.val) = (D.symm^[n]) b) ((G^n).trans e) (by
    intro l
    change τ l = b ↔ ψ (a,(e ((G^n) l)).val) = (D.symm^[n]) b
    rw [he,Equiv.Perm.coe_pow,block_iterate D τ G hG]
    exact (Function.Injective.iterate D.symm.injective n).eq_iff.symm)).trans
      { toFun := fun z => ⟨z.val.val,z.val.property,z.property⟩
        invFun := fun z => ⟨⟨z.val,z.property.1⟩,z.property.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }

end

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [TopologicalSpace A] [BorelSpace A]

def fullShift : (ℤ → A) ≃ₜ (ℤ → A) where
  toFun x q := x (q+1)
  invFun x q := x (q-1)
  left_inv x := by funext q; simp
  right_inv x := by funext q; simp
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

def symbolicCode (T : Ω ≃ᵐ Ω) (a : Ω → A) : Ω → (ℤ → A) :=
  fun x q => a (timeMap T q x)

end

section
open MeasureTheory Filter
open scoped Topology
variable {Ω A B : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [Fintype B] [Nonempty B] [MeasurableSpace B] [MeasurableSingletonClass B]

abbrev observableProcess (T : Ω ≃ᵐ Ω) (a : Ω → A) : ℤ → Ω → A :=
  fun q x => a (timeMap T q x)

abbrev observableTail (T : Ω ≃ᵐ Ω) (a : Ω → A) : MeasurableSpace Ω :=
  processTail μ (observableProcess T a)

end

open MeasureTheory Filter
open scoped Topology BigOperators

end Rokhlin

end

end OAI
end

section
-- module Solutions.OAIQ3_Rok.MultipleMixing_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

def Spaced {k : ℕ} (d : ℕ → Fin k → ℕ) : Prop :=
  ∀ r i j, i < j → d r i+r < d r j

def SequentialMixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (k : ℕ) : Prop :=
  ∀ d : ℕ → Fin k → ℕ, Spaced d → ∀ A : Fin k → Set Ω,
    (∀ i, MeasurableSet (A i)) → Tendsto
      (fun r => μ (⋂ i, (T^[d r i]) ⁻¹' A i)) atTop (𝓝 (∏ i, μ (A i)))

end

section
open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω I : Type*} [retained25 : MeasurableSpace Ω] [Fintype I]

def setIndicator (s : Set Ω) (x : Ω) : ℝ := by classical exact if x ∈ s then 1 else 0
end

open MeasureTheory Filter

end Rokhlin

end

end OAI
end


