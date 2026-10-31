-- Prove2me | Definitions.Def_OAIQ026G001
-- name    : OAIQ026G001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T00:28:23.326431+00:00
-- url     : https://prove2.me/theorems/35f8cb45-7168-4b57-843b-015614098875
-- title:
--   Definitions bundle OAIQ026G001 of the split of OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.GeneralMahler.general_mahler`, carved from OpenAI's openai/math development (OpenAI, *The Mahler Conjecture for General Convex Bodies (result family 087)*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 336 declarations of OpenAI's Lean: 239 definitions, 7 inductive types or structures, 10 instances and 80 theorems. The definitions and types are `OAI.GeneralMahler.ProjField.shiftD`, `OAI.GeneralMahler.Roots.U`, `OAI.GeneralMahler.Roots.Ux`, `OAI.GeneralMahler.Roots.Uy`, `OAI.GeneralMahler.Roots.fx`, `OAI.GeneralMahler.Roots.fy`, `OAI.GeneralMahler.Roots.gx`, `OAI.GeneralMahler.Roots.p`, `OAI.GeneralMahler.Roots.slab`, `OAI.GeneralMahler.Roots.u`, `OAI.GeneralMahler.Roots.xk`, `OAI.GeneralMahler.Roots.yk`, `OAI.GeneralMahler.SCal.Grid.By`, `OAI.GeneralMahler.SCal.Grid.Line`, `OAI.GeneralMahler.SCal.Grid.Nodes.A`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_11`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_180`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_22`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_360`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_45`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_721`, `OAI.GeneralMahler.SCal.Grid.Nodes.a0_90`, `OAI.GeneralMahler.SCal.Grid.Nodes.a101_112`, `OAI.GeneralMahler.SCal.Grid.Nodes.a112_123`, `OAI.GeneralMahler.SCal.Grid.Nodes.a112_135`, `OAI.GeneralMahler.SCal.Grid.Nodes.a11_22`, `OAI.GeneralMahler.SCal.Grid.Nodes.a123_135`, `OAI.GeneralMahler.SCal.Grid.Nodes.a135_146`, `OAI.GeneralMahler.SCal.Grid.Nodes.a135_157`, `OAI.GeneralMahler.SCal.Grid.Nodes.a135_180`, `OAI.GeneralMahler.SCal.Grid.Nodes.a146_157`, `OAI.GeneralMahler.SCal.Grid.Nodes.a157_168`, `OAI.GeneralMahler.SCal.Grid.Nodes.a157_180`, `OAI.GeneralMahler.SCal.Grid.Nodes.a168_180`, `OAI.GeneralMahler.SCal.Grid.Nodes.a180_191`, `OAI.GeneralMahler.SCal.Grid.Nodes.a180_202`, `OAI.GeneralMahler.SCal.Grid.Nodes.a180_225`, `OAI.GeneralMahler.SCal.Grid.Nodes.a180_270`, `OAI.GeneralMahler.SCal.Grid.Nodes.a180_360`, `OAI.GeneralMahler.SCal.Grid.Nodes.a191_202` and 206 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `Convex_GeneralMahler_AngleIntegral`, `Convex_GeneralMahler_Brouwer_Ghost`, `Convex_GeneralMahler_Brouwer_Grid`, `Convex_GeneralMahler_Brouwer_Scarf`, `Convex_GeneralMahler_Brouwer_Simplex`, `Convex_GeneralMahler_Budget_Major`, `Convex_GeneralMahler_Budget_Roots`, `Convex_GeneralMahler_Budget_Segment`, `Convex_GeneralMahler_DefectIBP`, `Convex_GeneralMahler_EntropyMap`, `Convex_GeneralMahler_Middle_Bound2`, `Convex_GeneralMahler_Middle_Cells`, `Convex_GeneralMahler_Middle_Features`, `Convex_GeneralMahler_Middle_Poly`, `Convex_GeneralMahler_Middle_Prefix`, `Convex_GeneralMahler_Middle_Tiles`, `Convex_GeneralMahler_Middle_Trap`, `Convex_GeneralMahler_Middle_Traversal`, `Convex_GeneralMahler_Orthant`, `Convex_GeneralMahler_Scalar_Data`, `Convex_GeneralMahler_Scalar_Grid`, `Convex_GeneralMahler_Scalar_HBox`, `Convex_GeneralMahler_Scalar_HSeries`, `Convex_GeneralMahler_Scalar_Integr`, `Convex_GeneralMahler_Scalar_NodesTbl`, `Convex_GeneralMahler_Scalar_Pass`, `Convex_GeneralMahler_Scalar_Regular`, `Convex_GeneralMahler_Scalar_Tail_Base`, `Convex_GeneralMahler_Scalar_Tail_Limit`, `Convex_GeneralMahler_Segment_Chord`, `Convex_GeneralMahler_Segment_Mean`, `Convex_GeneralMahler_Segment_Omega`, `Convex_GeneralMahler_Segment_Phase`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ026G002`.
-- source:
--   OpenAI, The Mahler Conjecture for General Convex Bodies (result family 087), OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mahler-Conjecture-for-General-Convex-Bodies-September-22-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ026_GM.Compat
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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_AngleIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Diagonal balance, with separate estimates at the two ends of the coordinate box. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric Matrix
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace GeneralMahler
variable {m : ℕ} [NeZero m]

-- Polynomial coefficient D as in angle_est.
def ek (j : ℝ) := Real.exp (-(j^2)/4)

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Scarf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Scarf incidence argument used to prove the fixed point principle needed
for the simultaneous normalization. In spirit cf. Ivanov "Beyond Sperner's
lemma". Here we use labels as extra ghost vertices so facets can use
ordinary Finset inclusion.
-/

noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

structure Orders (I T : Type*) where
  rank : I → T → ℕ
  inj : ∀ i, Function.Injective (rank i)
variable (r : Orders I T)

-- dominance formulated without choosing minima
def dom (s : Finset T) : Prop :=
  ∀ x : T, ∃ i:I, ∀ y∈s, r.rank i x ≤ r.rank i y

variable {A B : Type*} [DecidableEq A] [DecidableEq B]

section Door
variable (d : Finset T)
def room (s : Finset T) := s.card = Fintype.card I ∧ dom r s
def door := Fintype.card I = d.card+1 ∧ dom r d
variable {d}
-- candidate replacements for each repeated index
def cand (u : I → T) (i : I) := Finset.univ.filter fun x =>
    ∀ j:I, j ≠ i → r.rank j (u j) < r.rank j x

end Door
end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Ghost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Add labeled slack/ghost vertices. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable {I T : Type*} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T] [Nonempty T]
structure GOrders (I T : Type*) extends Orders I (I⊕T) where
  low : ∀ i x, rank i (.inl i) < rank i (.inr x)
  high : ∀ i j, i≠j → ∀ x, rank i (.inr x) < rank i (.inl j)

variable (q : GOrders I T)
def inside (s:Finset (I⊕T)) := ∃ x, Sum.inr x ∈ s

def outer (i:I) : Finset (I⊕T) := (univ.erase i).image Sum.inl

omit [Fintype T] [Nonempty T] in
@[simp] lemma mem_outer (i j:I) :
    Sum.inl j ∈ outer (T := T) i ↔ j≠i := by simp [outer]
omit [Fintype T] [Nonempty T] in
@[simp] lemma not_mem_outer (i:I) (x:T) :
    Sum.inr x ∉ outer i := by simp [outer]

end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! A colorful primitive room in grids on the standard simplex. -/
noncomputable section
open Finset
namespace GeneralMahler.Scarf
variable (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I]
  (N:ℕ)

abbrev Grid :=
  { f : I → Fin (N+1) // ∑ i,(f i).val = N }

def place {X : Type*} [Fintype X] (x:X) : ℕ := (Fintype.equivFin X x).val
lemma small {X : Type*} [Fintype X] (x:X) : place x < Fintype.card X :=
  (Fintype.equivFin X x).isLt
lemma place_inj {X : Type*} [Fintype X] {x y:X} (h:place x=place y) : x=y :=
  (Fintype.equivFin X).injective (Fin.ext h)

def key (i : I) (x : Grid I N) : ℕ :=
    1+(x.val i).val*Fintype.card (Grid I N)+place x
omit [Nonempty I] in
lemma key_pos i x : 0<key I N i x := by unfold key; omega
omit [Nonempty I] in
lemma key_lt i x :
    key I N i x < (N+1)*Fintype.card (Grid I N)+1 := by
  have h := small x
  have he := Nat.mul_le_mul_right (Fintype.card (Grid I N)) (show (x.val i).val ≤ N from by
    have h := (x.val i).isLt; omega)
  unfold key; rw [add_mul]; omega
omit [Nonempty I] in
lemma key_order (i:I) (x y:Grid I N) (h:(x.val i).val < (y.val i).val) :
    key I N i x < key I N i y := by
  have he := Nat.mul_le_mul_right (Fintype.card (Grid I N)) h
  have hv := small x
  unfold key
  change ((x.val i).val+1)*_ ≤ _ at he
  rw [add_mul] at he; omega
omit [Nonempty I] in
lemma key_inj (i:I) : Function.Injective (key I N i) := by
  intro x y h
  rcases lt_trichotomy (x.val i).val (y.val i).val with h₁|h₁|h₁
  · exact False.elim (ne_of_lt (key_order I N i x y h₁) h)
  · apply place_inj
    unfold key at h
    rw [h₁] at h
    omega
  exact False.elim (ne_of_lt (key_order I N i y x h₁) h.symm)

def grank (i:I) : I⊕Grid I N → ℕ := Sum.elim
  (fun j => if i=j then 0 else (N+1)*Fintype.card (Grid I N)+1+place j)
  (key I N i)

omit [Nonempty I] in
lemma lkey i x : grank I N i (.inl i)<grank I N i (.inr x) := by
  simpa [grank] using key_pos I N i x
omit [Nonempty I] in
lemma hkey i j (h:i≠j) x : grank I N i (.inr x)<grank I N i (.inl j) := by
  simp only [grank,h,Sum.elim_inl,Sum.elim_inr,ite_false, if_false]
  exact lt_of_lt_of_le (key_lt I N _ _) (Nat.le_add_right ..)
omit [Nonempty I] in
lemma inex i j x : grank I N i (.inl j) ≠ grank I N i (.inr x) := by
  by_cases h:i=j
  · rw [← h]; exact ne_of_lt (lkey ..)
  exact Ne.symm (ne_of_lt (hkey _ _ i j h x))

def gridOrder : GOrders I (Grid I N) where
  rank := grank I N
  inj := by
    intro i a b
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        simp only [grank,Sum.elim_inl,Sum.inl.injEq]
        split_ifs with h ho <;> grind [place_inj]
      | inr b => exact fun h => False.elim (inex I N _ _ _ h)
    | inr a =>
      cases b with
      | inl b => exact fun h => False.elim (inex I N _ _ _ h.symm)
      | inr b => exact fun h => congrArg _ (key_inj I N _ h)
  low := lkey I N
  high := hkey I N

end GeneralMahler.Scarf

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Brouwer_Simplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Brouwer fixed point for the standard simplex. -/
noncomputable section
open Set Filter Real Metric
open scoped Topology
namespace GeneralMahler
/-- Nonnegative weights of total mass one in the ambient function space. -/
abbrev simplexSet (I : Type*) [Fintype I] : Set (I → ℝ) :=
  {f | (∀ i, 0 ≤ f i) ∧ ∑ i, f i = 1}

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Exterior square-root kernel integrals in §05. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots

def u (t:ℝ):= √(1+t)-√t
def p (t:ℝ):=u t^2
def xk (t:ℝ):=2*u t^4/(1+2*t)
def yk (t:ℝ):=(1/2:ℝ)*u t^2*(1/(1+t)+(1/2:ℝ)*(1-√t / √(1+t))^2)

def fx (t:ℝ) := -(Real.log (1+p t^2)-p t^2/2)
def fy (t:ℝ) := -(Real.log (1+p t)/2-p t^2/8)
end GeneralMahler.Roots

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Major
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Piecewise kernel square estimates will use these scaled integrable
majorants. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.Roots
open Classical
def slab (f g:ℝ→ℝ) (t:ℝ) :=
  if t<0 then f (-t) else if t≤1 then g t else f (t-1)
def U (f g:ℝ→ℝ) (x y z:ℝ) :=
  |y-x| *slab f g ((z-min x y)/ |y-x|)

def gx (t:ℝ) := 2*(1-2*t)^2

def Ux := U xk gx
def Uy := U yk (fun _=>1/2)
end GeneralMahler.Roots

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_DefectIBP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar layer δ integration identities (including Eq 12). -/
noncomputable section
open MeasureTheory Filter Set Real Metric
open scoped Topology ENNReal NNReal
namespace GeneralMahler
variable {m:ℕ}
namespace ProjField

variable [NeZero m]

def shiftD (f:ℝ→ℝ) := fun x=>2*x*f x-deriv f x
end ProjField
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_EntropyMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Change of variables/Jensen for the projection scatter map. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Metric Matrix Real
open scoped NNReal ENNReal Topology RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
namespace GeneralMahler
variable {m:ℕ} [NeZero m]

def logN0 := Real.log ((√(2*π))⁻¹)
end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Budget_Segment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Scalar exterior and middle estimates via Cauchy--Schwarz. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Matrix Real Metric
open scoped Topology NNReal ENNReal RealInnerProductSpace Interval
namespace GeneralMahler.Seg
open Roots

def signE (x z:ℝ) := if z<x then (1:ℝ) else -1
def rcoef (x y z:ℝ) := if signE x z=signE y z then signE x z * √(|x-z|)*√(|y-z|) else 0
end GeneralMahler.Seg

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_HSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 log-series h in stable formulas. Remainders and smooth positive coefficients. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Finset
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal
-- scaled derivatives
def hden (u v:ℝ):= 1-u*v
def Qhv (n:Nat) (u v:ℝ):= (v/hden u v)^(n+1)
def Qh (n:Nat) (u:ℝ) := ∫ t in (0:ℝ)..1,Qhv n u t

-- rational/geometric remainder
def hCoef (i n:Nat) : ℝ := Nat.choose (i+n) n
def Rpow (i:Nat) (t:ℝ) := (1/(1-t))^(i+1)
def Rpoly (i n:Nat) (t:ℝ) := ∑ j∈range n,hCoef i j*t^j

end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_HBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
open Finset
-- coefficient taylor
noncomputable def Qpol (i n:ℕ) (u:ℝ):=
  ∑ j∈Finset.range n,hCoef i j*u^j / ((i+j+2:Nat):ℝ)
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite interval cells of appendix §07. Actual tagged values. -/
open Set Filter Real
namespace GeneralMahler.SCal
inductive Tag
  | R | K | C | Q | dK | dC | dQ | ddK | ddC | ddQ | NK | NC | NQ | RV | V | S
deriving DecidableEq, Repr
namespace Tag

instance instFintype : Fintype Tag :=
  Fintype.ofList [R, K, C, Q, dK, dC, dQ, ddK, ddC, ddQ, NK, NC, NQ, RV, V, S]
    (by intro t; cases t <;> simp)

end Tag

namespace Grid
open Tag
-- finite mesh: t_j=j/200
noncomputable def nd (n:ℕ):ℝ:= n/200
def sharp : Tag→Bool
  | R|K|C|Q=>true
  | _=>false
end Grid
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Pass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Range assertions and combined first derivative assertion for §07.
Integers in tables denote exact multiples 1/10000. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Tag

namespace Grid
def stage (n:Nat):Nat:=
  if n<20 then 0 else if n<40 then 1 else if n<60 then 2 else if n<80 then 3
  else if n<100 then 4 else if n<140 then 5 else if n<200 then 6 else if n<340 then 7 else 8

def allT := [R,K,C,Q,dK,dC,dQ,ddK,ddC,ddQ,NK,NC,NQ,RV,V,S]
end Grid
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Regular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Smooth growth and reflection for all profiles. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal
open Tag
variable {f:ℝ→ℝ}
namespace Tag
def odd : Tag→Bool
  | dK|dC|dQ|RV =>true
  | _=>false
end Tag
end GeneralMahler.SCal

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Compact certificate for §07 and table for later quadrature. -/
open Set Filter Real
namespace GeneralMahler.SCal.Grid
open Tag

structure Line where
  x:Int
  k:Int
  c:Int
  q:Int
  u:Int
  v:Int
  mx:Int
deriving Repr, Inhabited

noncomputable def gv (a:Int):ℝ:=a/100000000

-- The check recurses on the number of grid cells.
def runB (p:ℕ→Bool) (n:ℕ):ℕ→Bool
  | 0=>true
  | r+1=> p (n+r)&&runB p n r
def By (f:ℕ→Bool) (l u:Nat): Prop:=∀ i,l ≤ i → i < u → f i=true
end GeneralMahler.SCal.Grid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_NodesTbl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace GeneralMahler.SCal.Grid.Nodes
def a0_11 (n:ℕ):Line:= if n < 5 then (if n < 2 then (if n < 1 then (⟨-1,-691588,-34134118,7779633,22000000,0,-691212⟩) else (⟨1800007,-691294,-34135092,7780267,21994181,505955,-690329⟩)) else (if n < 3 then (⟨3600060,-690411,-34138016,7782168,21976728,1011643,-688859⟩) else (if n < 4 then (⟨5400202,-688940,-34142888,7785336,21947650,1516796,-686800⟩) else (⟨7200480,-686881,-34149708,7789770,21906962,2021146,-684155⟩)))) else (if n < 8 then (if n < 6 then (⟨9000937,-684235,-34158475,7795471,21854685,2524427,-680922⟩) else (if n < 7 then (⟨10801620,-681003,-34169187,7802437,21790848,3026373,-677104⟩) else (⟨12602572,-677184,-34181843,7810668,21715484,3526718,-672701⟩))) else (if n < 9 then (⟨14403840,-672781,-34196440,7820164,21628634,4025197,-667715⟩) else (if n < 10 then (⟨16205468,-667794,-34212977,7830922,21530342,4521547,-662146⟩) else (⟨18007500,-662225,-34231450,7842943,21420661,5015506,-655997⟩))))
def a11_22 (n:ℕ):Line:= if n < 16 then (if n < 13 then (if n < 12 then (⟨19809984,-656075,-34251857,7856224,21299649,5506811,-649268⟩) else (⟨21612962,-649346,-34274195,7870765,21167370,5995203,-641962⟩)) else (if n < 14 then (⟨23416480,-642040,-34298459,7886564,21023894,6480424,-634080⟩) else (if n < 15 then (⟨25220585,-634158,-34324646,7903620,20869297,6962217,-625625⟩) else (⟨27025319,-625703,-34352752,7921930,20703660,7440327,-616599⟩)))) else (if n < 19 then (if n < 17 then (⟨28830729,-616676,-34382771,7941492,20527072,7914501,-607005⟩) else (if n < 18 then (⟨30636860,-607081,-34414699,7962305,20339625,8384489,-596844⟩) else (⟨32443757,-596920,-34448530,7984367,20141419,8850041,-586120⟩))) else (if n < 20 then (⟨34251465,-586196,-34484259,8007674,19932559,9310913,-574836⟩) else (if n < 21 then (⟨36060030,-574911,-34521879,8032225,19713155,9766858,-562995⟩) else (⟨37869495,-563069,-34561384,8058016,19483323,10217638,-550599⟩))))
def a0_22 (n:ℕ):Line:= if n < 11 then (a0_11 n) else (a11_22 n)
def a22_33 (n:ℕ):Line:= if n < 27 then (if n < 24 then (if n < 23 then (⟨39679908,-550673,-34602767,8085046,19243185,10663012,-537653⟩) else (⟨41491312,-537726,-34646020,8113310,18992868,11102746,-524160⟩)) else (if n < 25 then (⟨43303754,-524233,-34691137,8142806,18732504,11536607,-510124⟩) else (if n < 26 then (⟨45117279,-510196,-34738108,8173531,18462231,11964365,-495548⟩) else (⟨46931931,-495620,-34786925,8205480,18182191,12385795,-480437⟩)))) else (if n < 30 then (if n < 28 then (⟨48747757,-480509,-34837579,8238650,17892534,12800672,-464796⟩) else (if n < 29 then (⟨50564801,-464867,-34890060,8273037,17593412,13208779,-448628⟩) else (⟨52383109,-448698,-34944359,8308637,17284984,13609898,-431939⟩))) else (if n < 31 then (⟨54202727,-432008,-35000465,8345447,16967412,14003818,-414733⟩) else (if n < 32 then (⟨56023701,-414801,-35058368,8383460,16640865,14390330,-397014⟩) else (⟨57846074,-397083,-35118055,8422673,16305515,14769230,-378790⟩))))
def a33_45 (n:ℕ):Line:= if n < 39 then (if n < 36 then (if n < 34 then (⟨59669894,-378857,-35179515,8463080,15961541,15140318,-360064⟩) else (if n < 35 then (⟨61495206,-360131,-35242735,8504678,15609122,15503396,-340843⟩) else (⟨63322055,-340909,-35307703,8547459,15248447,15858274,-321132⟩))) else (if n < 37 then (⟨65150487,-321197,-35374404,8591419,14879706,16204763,-300937⟩) else (if n < 38 then (⟨66980548,-301001,-35442826,8636552,14503094,16542680,-280264⟩) else (⟨68812283,-280327,-35512953,8682851,14118810,16871847,-259120⟩)))) else (if n < 42 then (if n < 40 then (⟨70645739,-259183,-35584770,8730311,13727057,17192088,-237511⟩) else (if n < 41 then (⟨72480960,-237573,-35658262,8778926,13328043,17503236,-215444⟩) else (⟨74317994,-215505,-35733411,8828687,12921979,17805124,-192926⟩))) else (if n < 43 then (⟨76156886,-192986,-35810202,8879589,12509080,18097594,-169964⟩) else (if n < 44 then (⟨77997682,-170024,-35888616,8931624,12089563,18380491,-146566⟩) else (⟨79840427,-146624,-35968636,8984784,11663652,18653665,-122738⟩))))
def a22_45 (n:ℕ):Line:= if n < 33 then (a22_33 n) else (a33_45 n)
def a0_45 (n:ℕ):Line:= if n < 22 then (a0_22 n) else (a22_45 n)
def a45_56 (n:ℕ):Line:= if n < 50 then (if n < 47 then (if n < 46 then (⟨81685169,-122795,-36050242,9039062,11231571,18916972,-98489⟩) else (⟨83531953,-98545,-36133416,9094449,10793548,19170272,-73826⟩)) else (if n < 48 then (⟨85380825,-73882,-36218137,9150938,10349816,19413431,-48759⟩) else (if n < 49 then (⟨87231832,-48813,-36304384,9208519,9900609,19646321,-23294⟩) else (⟨89085019,-23347,-36392136,9267184,9446165,19868819,2560⟩)))) else (if n < 53 then (if n < 51 then (⟨90940434,2507,-36481371,9326923,8986724,20080807,28793⟩) else (if n < 52 then (⟨92798122,28742,-36572067,9387727,8522529,20282172,55397⟩) else (⟨94658130,55347,-36664199,9449586,8053826,20472808,82363⟩))) else (if n < 54 then (⟨96520504,82314,-36757744,9512490,7580863,20652615,109681⟩) else (if n < 55 then (⟨98385292,109633,-36852677,9576429,7103889,20821497,137342⟩) else (⟨100252539,137296,-36948972,9641391,6623158,20979365,165336⟩))))
def a56_67 (n:ℕ):Line:= if n < 61 then (if n < 58 then (if n < 57 then (⟨102122292,165291,-37046603,9707365,6138924,21126136,193654⟩) else (⟨103994599,193610,-37145544,9774341,5651442,21261731,222285⟩)) else (if n < 59 then (⟨105869505,222242,-37245766,9842306,5160970,21386079,251219⟩) else (if n < 60 then (⟨107747058,251178,-37347242,9911249,4667769,21499115,280446⟩) else (⟨109627305,280406,-37449942,9981156,4172098,21600778,309954⟩)))) else (if n < 64 then (if n < 62 then (⟨111510293,309915,-37553836,10052016,3674221,21691014,339734⟩) else (if n < 63 then (⟨113396068,339696,-37658895,10123814,3174400,21769777,369774⟩) else (⟨115284678,369738,-37765087,10196539,2672899,21837024,400062⟩))) else (if n < 65 then (⟨117176170,400028,-37872380,10270175,2169985,21892719,430589⟩) else (if n < 66 then (⟨119070592,430555,-37980742,10344709,1665923,21936834,461341⟩) else (⟨120967991,461309,-38090140,10420126,1160980,21969345,492308⟩))))
def a45_67 (n:ℕ):Line:= if n < 56 then (a45_56 n) else (a56_67 n)
def a67_78 (n:ℕ):Line:= if n < 72 then (if n < 69 then (if n < 68 then (⟨122868413,492278,-38200539,10496412,655422,21990235,523478⟩) else (⟨124771908,523449,-38311906,10573551,149518,21999492,554838⟩)) else (if n < 70 then (⟨126678521,554811,-38424204,10651528,-356465,21997112,586377⟩) else (if n < 71 then (⟨128588302,586351,-38537398,10730327,-862260,21983096,618082⟩) else (⟨130501297,618058,-38651453,10809931,-1367598,21957451,649941⟩)))) else (if n < 75 then (if n < 73 then (⟨132417555,649919,-38766329,10890325,-1872214,21920192,681942⟩) else (if n < 74 then (⟨134337124,681921,-38881991,10971492,-2375838,21871337,714072⟩) else (⟨136260051,714052,-38998400,11053414,-2878206,21810913,746317⟩))) else (if n < 76 then (⟨138186384,746299,-39115516,11136073,-3379052,21738951,778666⟩) else (if n < 77 then (⟨140116172,778650,-39233301,11219452,-3878110,21655490,811105⟩) else (⟨142049463,811091,-39351714,11303533,-4375117,21560574,843621⟩))))
def a78_90 (n:ℕ):Line:= if n < 84 then (if n < 81 then (if n < 79 then (⟨143986305,843609,-39470716,11388296,-4869809,21454253,876202⟩) else (if n < 80 then (⟨145926747,876191,-39590265,11473724,-5361925,21336583,908833⟩) else (⟨147870837,908824,-39710320,11559797,-5851205,21207626,941503⟩))) else (if n < 82 then (⟨149818624,941495,-39830839,11646496,-6337390,21067451,974196⟩) else (if n < 83 then (⟨151770156,974190,-39951780,11733800,-6820223,20916132,1006901⟩) else (⟨153725482,1006896,-40073101,11821690,-7299447,20753748,1039605⟩)))) else (if n < 87 then (if n < 85 then (⟨155684652,1039600,-40194758,11910145,-7774811,20580387,1072295⟩) else (if n < 86 then (⟨157647714,1072288,-40316710,11999146,-8246062,20396139,1104955⟩) else (⟨159614717,1104946,-40438911,12088670,-8712950,20201101,1137572⟩))) else (if n < 88 then (⟨161585710,1137562,-40561319,12178697,-9175230,19995378,1170134⟩) else (if n < 89 then (⟨163560743,1170122,-40683889,12269205,-9632657,19779078,1202626⟩) else (⟨165539865,1202612,-40806578,12360173,-10084988,19552315,1235034⟩))))
def a67_90 (n:ℕ):Line:= if n < 78 then (a67_78 n) else (a78_90 n)
def a45_90 (n:ℕ):Line:= if n < 67 then (a45_67 n) else (a67_90 n)
def a0_90 (n:ℕ):Line:= if n < 45 then (a0_45 n) else (a45_90 n)
def a90_101 (n:ℕ):Line:= if n < 95 then (if n < 92 then (if n < 91 then (⟨167523126,1235019,-40929341,12451580,-10531984,19315209,1267347⟩) else (⟨169510574,1267330,-41052135,12543402,-10973409,19067886,1299550⟩)) else (if n < 93 then (⟨171502261,1299531,-41174914,12635617,-11409029,18810477,1331629⟩) else (if n < 94 then (⟨173498235,1331609,-41297635,12728204,-11838615,18543117,1363573⟩) else (⟨175498546,1363551,-41420254,12821140,-12261938,18265949,1395367⟩)))) else (if n < 98 then (if n < 96 then (⟨177503245,1395344,-41542725,12914401,-12678774,17979118,1426999⟩) else (if n < 97 then (⟨179512381,1426974,-41665006,13007966,-13088904,17682777,1458456⟩) else (⟨181526006,1458429,-41787052,13101810,-13492110,17377081,1489725⟩))) else (if n < 99 then (⟨183544168,1489697,-41908820,13195912,-13888179,17062194,1520793⟩) else (if n < 100 then (⟨185566919,1520763,-42030266,13290247,-14276902,16738282,1551648⟩) else (⟨187594309,1551617,-42151347,13384792,-14658072,16405515,1582278⟩))))
def a101_112 (n:ℕ):Line:= if n < 106 then (if n < 103 then (if n < 102 then (⟨189626390,1582245,-42272020,13479525,-15031489,16064070,1612670⟩) else (⟨191663210,1612636,-42392243,13574421,-15396955,15714127,1642813⟩)) else (if n < 104 then (⟨193704823,1642777,-42511974,13669457,-15754275,15355872,1672694⟩) else (if n < 105 then (⟨195751278,1672657,-42631171,13764610,-16103262,14989494,1702302⟩) else (⟨197802627,1702264,-42749795,13859857,-16443731,14615187,1731626⟩)))) else (if n < 109 then (if n < 107 then (⟨199858921,1731586,-42867803,13955174,-16775502,14233149,1760654⟩) else (if n < 108 then (⟨201920211,1760613,-42985157,14050537,-17098398,13843582,1789376⟩) else (⟨203986549,1789333,-43101817,14145924,-17412250,13446692,1817780⟩))) else (if n < 110 then (⟨206057987,1817736,-43217745,14241312,-17716892,13042689,1845857⟩) else (if n < 111 then (⟨208134577,1845812,-43332904,14336677,-18012161,12631787,1873596⟩) else (⟨210216370,1873550,-43447257,14431997,-18297903,12214203,1900988⟩))))
def a90_112 (n:ℕ):Line:= if n < 101 then (a90_101 n) else (a101_112 n)
def a112_123 (n:ℕ):Line:= if n < 117 then (if n < 114 then (if n < 113 then (⟨212303418,1900940,-43560766,14527249,-18573965,11790158,1928022⟩) else (⟨214395774,1927973,-43673399,14622410,-18840202,11359876,1954690⟩)) else (if n < 115 then (⟨216493490,1954639,-43785119,14717458,-19096473,10923585,1980982⟩) else (if n < 116 then (⟨218596618,1980931,-43895895,14812370,-19342643,10481516,2006890⟩) else (⟨220705211,2006837,-44005692,14907126,-19578580,10033902,2032405⟩)))) else (if n < 120 then (if n < 118 then (⟨222819322,2032352,-44114482,15001703,-19804162,9580980,2057520⟩) else (if n < 119 then (⟨224939003,2057466,-44222232,15096081,-20019267,9122991,2082226⟩) else (⟨227064308,2082171,-44328914,15190237,-20223782,8660175,2106517⟩))) else (if n < 121 then (⟨229195289,2106461,-44434499,15284151,-20417600,8192779,2130386⟩) else (if n < 122 then (⟨231332000,2130329,-44538961,15377803,-20600617,7721049,2153825⟩) else (⟨233474495,2153767,-44642275,15471172,-20772737,7245234,2176828⟩))))
def a123_135 (n:ℕ):Line:= if n < 129 then (if n < 126 then (if n < 124 then (⟨235622826,2176770,-44744414,15564239,-20933868,6765587,2199390⟩) else (if n < 125 then (⟨237777048,2199331,-44845357,15656985,-21083926,6282361,2221504⟩) else (⟨239937215,2221445,-44945080,15749390,-21222831,5795812,2243167⟩))) else (if n < 127 then (⟨242103380,2243107,-45043563,15841436,-21350510,5306197,2264372⟩) else (if n < 128 then (⟨244275597,2264311,-45140786,15933106,-21466895,4813775,2285116⟩) else (⟨246453921,2285055,-45236730,16024380,-21571924,4318807,2305394⟩)))) else (if n < 132 then (if n < 130 then (⟨248638407,2305332,-45331379,16115242,-21665542,3821554,2325202⟩) else (if n < 131 then (⟨250829109,2325140,-45424716,16205676,-21747700,3322280,2344538⟩) else (⟨253026081,2344476,-45516727,16295665,-21818354,2821248,2363398⟩))) else (if n < 133 then (⟨255229379,2363335,-45607398,16385192,-21877466,2318724,2381780⟩) else (if n < 134 then (⟨257439058,2381717,-45696717,16474244,-21925006,1814973,2399681⟩) else (⟨259655173,2399618,-45784675,16562805,-21960947,1310263,2417100⟩))))
def a112_135 (n:ℕ):Line:= if n < 123 then (a112_123 n) else (a123_135 n)
def a90_135 (n:ℕ):Line:= if n < 112 then (a90_112 n) else (a112_135 n)
def a135_146 (n:ℕ):Line:= if n < 140 then (if n < 137 then (if n < 136 then (⟨261877779,2417036,-45871260,16650860,-21985272,804859,2434034⟩) else (⟨264106933,2433971,-45956465,16738397,-21997968,299029,2450484⟩)) else (if n < 138 then (⟨266342689,2450420,-46040283,16825402,-21999027,-206959,2466448⟩) else (if n < 139 then (⟨268585103,2466384,-46122708,16911861,-21988448,-712837,2481926⟩) else (⟨270834232,2481862,-46203736,16997764,-21966239,-1218338,2496917⟩)))) else (if n < 143 then (if n < 141 then (⟨273090132,2496853,-46283363,17083099,-21932410,-1723195,2511423⟩) else (if n < 142 then (⟨275352859,2511359,-46361588,17167854,-21886979,-2227140,2525442⟩) else (⟨277622471,2525379,-46438409,17252019,-21829970,-2729907,2538978⟩))) else (if n < 144 then (⟨279899022,2538914,-46513827,17335585,-21761414,-3231230,2552030⟩) else (if n < 145 then (⟨282182571,2551966,-46587844,17418541,-21681347,-3730844,2564600⟩) else (⟨284473175,2564537,-46660461,17500879,-21589811,-4228484,2576691⟩))))
def a146_157 (n:ℕ):Line:= if n < 151 then (if n < 148 then (if n < 147 then (⟨286770891,2576628,-46731683,17582590,-21486854,-4723888,2588304⟩) else (⟨289075776,2588241,-46801514,17663668,-21372531,-5216792,2599442⟩)) else (if n < 149 then (⟨291387887,2599379,-46869960,17744104,-21246903,-5706937,2610107⟩) else (if n < 150 then (⟨293707284,2610045,-46937028,17823893,-21110035,-6194064,2620303⟩) else (⟨296034023,2620241,-47002726,17903027,-20962001,-6677913,2630033⟩)))) else (if n < 154 then (if n < 152 then (⟨298368163,2629971,-47067062,17981502,-20802878,-7158231,2639300⟩) else (if n < 153 then (⟨300709762,2639239,-47130046,18059313,-20632751,-7634761,2648109⟩) else (⟨303058879,2648048,-47191688,18136454,-20451710,-8107253,2656462⟩))) else (if n < 155 then (⟨305415573,2656402,-47252000,18212922,-20259850,-8575457,2664365⟩) else (if n < 156 then (⟨307779902,2664306,-47310993,18288713,-20057274,-9039124,2671823⟩) else (⟨310151925,2671764,-47368681,18363824,-19844087,-9498010,2678838⟩))))
def a135_157 (n:ℕ):Line:= if n < 146 then (a135_146 n) else (a146_157 n)
def a157_168 (n:ℕ):Line:= if n < 162 then (if n < 159 then (if n < 158 then (⟨312531703,2678780,-47425077,18438253,-19620404,-9951872,2685418⟩) else (⟨314919293,2685360,-47480195,18511997,-19386342,-10400469,2691565⟩)) else (if n < 160 then (⟨317314757,2691508,-47534051,18585055,-19142024,-10843565,2697287⟩) else (if n < 161 then (⟨319718153,2697230,-47586659,18657426,-18887582,-11280925,2702587⟩) else (⟨322129543,2702531,-47638037,18729108,-18623148,-11712317,2707472⟩)))) else (if n < 165 then (if n < 163 then (⟨324548985,2707417,-47688199,18800102,-18348862,-12137514,2711947⟩) else (if n < 164 then (⟨326976542,2711893,-47737164,18870407,-18064871,-12556290,2716018⟩) else (⟨329412272,2715965,-47784949,18940024,-17771324,-12968425,2719691⟩))) else (if n < 166 then (⟨331856239,2719638,-47831572,19008953,-17468376,-13373699,2722972⟩) else (if n < 167 then (⟨334308501,2722920,-47877051,19077196,-17156188,-13771899,2725867⟩) else (⟨336769122,2725816,-47921405,19144755,-16834925,-14162814,2728382⟩))))
def a168_180 (n:ℕ):Line:= if n < 174 then (if n < 171 then (if n < 169 then (⟨339238161,2728332,-47964652,19211630,-16504756,-14546238,2730524⟩) else (if n < 170 then (⟨341715682,2730474,-48006813,19277825,-16165857,-14921966,2732299⟩) else (⟨344201745,2732250,-48047906,19343341,-15818406,-15289801,2733712⟩))) else (if n < 172 then (⟨346696414,2733664,-48087952,19408182,-15462588,-15649549,2734772⟩) else (if n < 173 then (⟨349199750,2734724,-48126969,19472350,-15098590,-16001018,2735483⟩) else (⟨351711816,2735437,-48164978,19535849,-14726606,-16344023,2735854⟩)))) else (if n < 177 then (if n < 175 then (⟨354232674,2735808,-48201999,19598682,-14346832,-16678382,2735889⟩) else (if n < 176 then (⟨356762389,2735844,-48238052,19660853,-13959468,-17003919,2735888⟩) else (⟨359301023,2735552,-48273157,19722366,-13564720,-17320461,2735596⟩))) else (if n < 178 then (⟨361848639,2734939,-48307334,19783226,-13162797,-17627841,2734982⟩) else (if n < 179 then (⟨364405301,2734011,-48340604,19843436,-12753911,-17925896,2734052⟩) else (⟨366971074,2732774,-48372986,19903001,-12338279,-18214469,2732815⟩))))
def a157_180 (n:ℕ):Line:= if n < 168 then (a157_168 n) else (a168_180 n)
def a135_180 (n:ℕ):Line:= if n < 157 then (a135_157 n) else (a157_180 n)
def a90_180 (n:ℕ):Line:= if n < 135 then (a90_135 n) else (a135_180 n)
def a0_180 (n:ℕ):Line:= if n < 90 then (a0_90 n) else (a90_180 n)
def a180_191 (n:ℕ):Line:= if n < 185 then (if n < 182 then (if n < 181 then (⟨369546021,2731235,-48404500,19961927,-11916119,-18493407,2731275⟩) else (⟨372130206,2729401,-48435167,20020217,-11487657,-18762562,2729440⟩)) else (if n < 183 then (⟨374723695,2727278,-48465006,20077878,-11053118,-19021793,2727317⟩) else (if n < 184 then (⟨377326552,2724873,-48494037,20134913,-10612732,-19270961,2724911⟩) else (⟨379938842,2722192,-48522279,20191329,-10166732,-19509935,2722229⟩)))) else (if n < 188 then (if n < 186 then (⟨382560631,2719242,-48549752,20247131,-9715354,-19738589,2719278⟩) else (if n < 187 then (⟨385191984,2716028,-48576474,20302324,-9258837,-19956802,2716063⟩) else (⟨387832966,2712558,-48602466,20356914,-8797422,-20164458,2712592⟩))) else (if n < 189 then (⟨390483644,2708837,-48627744,20410907,-8331353,-20361448,2708870⟩) else (if n < 190 then (⟨393144085,2704871,-48652329,20464308,-7860878,-20547667,2704904⟩) else (⟨395814354,2700668,-48676238,20517124,-7386244,-20723016,2700700⟩))))
def a191_202 (n:ℕ):Line:= if n < 196 then (if n < 193 then (if n < 192 then (⟨398494518,2696232,-48699489,20569359,-6907703,-20887404,2696263⟩) else (⟨401184645,2691570,-48722099,20621021,-6425508,-21040743,2691600⟩)) else (if n < 194 then (⟨403884802,2686687,-48744087,20672114,-5939914,-21182951,2686717⟩) else (if n < 195 then (⟨406595055,2681591,-48765469,20722645,-5451178,-21313954,2681620⟩) else (⟨409315474,2676285,-48786262,20772620,-4959559,-21433683,2676313⟩)))) else (if n < 199 then (if n < 197 then (⟨412046125,2670776,-48806482,20822045,-4465316,-21542074,2670804⟩) else (if n < 198 then (⟨414787078,2665070,-48826146,20870926,-3968711,-21639070,2665097⟩) else (⟨417538400,2659172,-48845269,20919268,-3470006,-21724619,2659198⟩))) else (if n < 200 then (⟨420300161,2653087,-48863868,20967079,-2969466,-21798676,2653113⟩) else (if n < 201 then (⟨423072429,2646822,-48881957,21014362,-2467356,-21861202,2646847⟩) else (⟨425855274,2640380,-48899551,21061126,-1963940,-21912164,2640404⟩))))
def a180_202 (n:ℕ):Line:= if n < 191 then (a180_191 n) else (a191_202 n)
def a202_213 (n:ℕ):Line:= if n < 207 then (if n < 204 then (if n < 203 then (⟨428648766,2633767,-48916665,21107375,-1459485,-21951535,2633791⟩) else (⟨431452974,2626989,-48933312,21153116,-954258,-21979295,2627012⟩)) else (if n < 205 then (⟨434267968,2620049,-48949508,21198354,-448526,-21995427,2620072⟩) else (if n < 206 then (⟨437093819,2612954,-48965265,21243095,57442,-21999925,2612976⟩) else (⟨439930597,2605708,-48980596,21287345,563381,-21992785,2605729⟩)))) else (if n < 210 then (if n < 208 then (⟨442778373,2598315,-48995515,21331110,1069021,-21974012,2598336⟩) else (if n < 209 then (⟨445637219,2590780,-49010035,21374396,1574096,-21943615,2590800⟩) else (⟨448507206,2583108,-49024166,21417207,2078339,-21901610,2583128⟩))) else (if n < 211 then (⟨451388406,2575303,-49037922,21459550,2581481,-21848019,2575322⟩) else (if n < 212 then (⟨454280890,2567370,-49051314,21501431,3083259,-21782872,2567388⟩) else (⟨457184732,2559312,-49064354,21542854,3583405,-21706202,2559330⟩))))
def a213_225 (n:ℕ):Line:= if n < 219 then (if n < 216 then (if n < 214 then (⟨460100003,2551134,-49077051,21583825,4081656,-21618050,2551151⟩) else (if n < 215 then (⟨463026776,2542840,-49089418,21624350,4577748,-21518462,2542857⟩) else (⟨465965126,2534433,-49101464,21664434,5071418,-21407492,2534450⟩))) else (if n < 217 then (⟨468915124,2525919,-49113200,21704082,5562406,-21285198,2525935⟩) else (if n < 218 then (⟨471876845,2517300,-49124635,21743300,6050451,-21151644,2517315⟩) else (⟨474850364,2508580,-49135779,21782092,6535296,-21006902,2508595⟩)))) else (if n < 222 then (if n < 220 then (⟨477835753,2499763,-49146641,21820464,7016683,-20851047,2499778⟩) else (if n < 221 then (⟨480833089,2490853,-49157230,21858420,7494359,-20684163,2490867⟩) else (⟨483842445,2481853,-49167555,21895967,7968071,-20506337,2481867⟩))) else (if n < 223 then (⟨486863898,2472766,-49177625,21933108,8437567,-20317664,2472779⟩) else (if n < 224 then (⟨489897522,2463595,-49187447,21969848,8902601,-20118243,2463608⟩) else (⟨492943393,2454345,-49197030,22006193,9362925,-19908180,2454358⟩))))
def a202_225 (n:ℕ):Line:= if n < 213 then (a202_213 n) else (a213_225 n)
def a180_225 (n:ℕ):Line:= if n < 202 then (a180_202 n) else (a202_225 n)
def a225_236 (n:ℕ):Line:= if n < 230 then (if n < 227 then (if n < 226 then (⟨496001588,2445018,-49206381,22042147,9818296,-19687586,2445030⟩) else (⟨499072183,2435617,-49215507,22077714,10268474,-19456578,2435629⟩)) else (if n < 228 then (⟨502155255,2426145,-49224417,22112900,10713220,-19215278,2426156⟩) else (if n < 229 then (⟨505250881,2416605,-49233117,22147708,11152299,-18963814,2416616⟩) else (⟨508359139,2407001,-49241613,22182144,11585479,-18702318,2407012⟩)))) else (if n < 233 then (if n < 231 then (⟨511480105,2397334,-49249913,22216212,12012530,-18430929,2397345⟩) else (if n < 232 then (⟨514613858,2387608,-49258022,22249916,12433227,-18149790,2387618⟩) else (⟨517760477,2377826,-49265948,22283260,12847347,-17859051,2377835⟩))) else (if n < 234 then (⟨520920039,2367989,-49273695,22316248,13254671,-17558864,2367998⟩) else (if n < 235 then (⟨524092625,2358101,-49281270,22348886,13654983,-17249389,2358110⟩) else (⟨527278313,2348164,-49288679,22381177,14048072,-16930790,2348173⟩))))
def a236_247 (n:ℕ):Line:= if n < 241 then (if n < 238 then (if n < 237 then (⟨530477183,2338180,-49295926,22413124,14433731,-16603235,2338189⟩) else (⟨533689315,2328152,-49303017,22444733,14811754,-16266897,2328161⟩)) else (if n < 239 then (⟨536914789,2318083,-49309957,22476007,15181942,-15921955,2318091⟩) else (if n < 240 then (⟨540153686,2307973,-49316750,22506950,15544099,-15568589,2307981⟩) else (⟨543406087,2297827,-49323403,22537565,15898034,-15206989,2297834⟩)))) else (if n < 244 then (if n < 242 then (⟨546672074,2287645,-49329919,22567858,16243559,-14837344,2287652⟩) else (if n < 243 then (⟨549951727,2277430,-49336302,22597831,16580492,-14459851,2277437⟩) else (⟨553245129,2267184,-49342557,22627487,16908654,-14074709,2267191⟩))) else (if n < 245 then (⟨556552362,2256909,-49348689,22656832,17227871,-13682122,2256915⟩) else (if n < 246 then (⟨559873508,2246607,-49354700,22685868,17537976,-13282297,2246613⟩) else (⟨563208652,2236279,-49360596,22714599,17838803,-12875446,2236285⟩))))
def a225_247 (n:ℕ):Line:= if n < 236 then (a225_236 n) else (a236_247 n)
def a247_258 (n:ℕ):Line:= if n < 252 then (if n < 249 then (if n < 248 then (⟨566557876,2225929,-49366379,22743028,18130194,-12461784,2225935⟩) else (⟨569921264,2215557,-49372053,22771160,18411995,-12041530,2215562⟩)) else (if n < 250 then (⟨573298900,2205165,-49377622,22798996,18684056,-11614907,2205170⟩) else (if n < 251 then (⟨576690868,2194755,-49383090,22826542,18946233,-11182140,2194760⟩) else (⟨580097254,2184328,-49388459,22853799,19198389,-10743457,2184333⟩)))) else (if n < 255 then (if n < 253 then (⟨583518142,2173887,-49393733,22880772,19440389,-10299092,2173892⟩) else (if n < 254 then (⟨586953619,2163433,-49398914,22907463,19672105,-9849278,2163438⟩) else (⟨590403769,2152967,-49404006,22933876,19893415,-9394255,2152972⟩))) else (if n < 256 then (⟨593868679,2142492,-49409011,22960014,20104203,-8934262,2142496⟩) else (if n < 257 then (⟨597348436,2132007,-49413933,22985879,20304355,-8469543,2132011⟩) else (⟨600843127,2121516,-49418773,23011476,20493767,-8000344,2121520⟩))))
def a258_270 (n:ℕ):Line:= if n < 264 then (if n < 261 then (if n < 259 then (⟨604352839,2111019,-49423535,23036807,20672339,-7526913,2111022⟩) else (if n < 260 then (⟨607877659,2100517,-49428221,23061875,20839975,-7049500,2100521⟩) else (⟨611417677,2090013,-49432833,23086683,20996587,-6568358,2090016⟩))) else (if n < 262 then (⟨614972980,2079507,-49437374,23111234,21142093,-6083742,2079510⟩) else (if n < 263 then (⟨618543658,2069000,-49441845,23135531,21276415,-5595908,2069003⟩) else (⟨622129799,2058494,-49446250,23159576,21399482,-5105113,2058498⟩)))) else (if n < 267 then (if n < 265 then (⟨625731493,2047991,-49450590,23183373,21511229,-4611618,2047994⟩) else (if n < 266 then (⟨629348831,2037490,-49454866,23206924,21611597,-4115684,2037494⟩) else (⟨632981902,2026994,-49459082,23230232,21700534,-3617573,2026998⟩))) else (if n < 268 then (⟨636630798,2016503,-49463239,23253300,21777991,-3117548,2016507⟩) else (if n < 269 then (⟨640295610,2006019,-49467338,23276130,21843928,-2615873,2006023⟩) else (⟨643976429,1995542,-49471382,23298724,21898311,-2112815,1995547⟩))))
def a247_270 (n:ℕ):Line:= if n < 258 then (a247_258 n) else (a258_270 n)
def a225_270 (n:ℕ):Line:= if n < 247 then (a225_247 n) else (a247_270 n)
def a180_270 (n:ℕ):Line:= if n < 225 then (a180_225 n) else (a225_270 n)
def a270_281 (n:ℕ):Line:= if n < 275 then (if n < 272 then (if n < 271 then (⟨647673348,1985075,-49475372,23321087,21941109,-1608640,1985079⟩) else (⟨651386459,1974616,-49479310,23343219,21972302,-1103613,1974621⟩)) else (if n < 273 then (⟨655115854,1964169,-49483197,23365124,21991871,-598003,1964173⟩) else (if n < 274 then (⟨658861627,1953733,-49487035,23386804,21999807,-92076,1953737⟩) else (⟨662623872,1943309,-49490825,23408262,21996106,413899,1943314⟩)))) else (if n < 278 then (if n < 276 then (⟨666402682,1932899,-49494569,23429499,21980770,919655,1932904⟩) else (if n < 277 then (⟨670198153,1922503,-49498268,23450519,21953806,1424925,1922508⟩) else (⟨674010378,1912123,-49501924,23471324,21915229,1929441,1912128⟩))) else (if n < 279 then (⟨677839454,1901758,-49505537,23491915,21865059,2432937,1901763⟩) else (if n < 280 then (⟨681685476,1891410,-49509109,23512297,21803324,2935145,1891416⟩) else (⟨685548540,1881080,-49512641,23532469,21730055,3435801,1881086⟩))))
def a281_292 (n:ℕ):Line:= if n < 286 then (if n < 283 then (if n < 282 then (⟨689428743,1870768,-49516134,23552436,21645291,3934640,1870774⟩) else (⟨693326181,1860475,-49519589,23572199,21549077,4431397,1860481⟩)) else (if n < 284 then (⟨697240953,1850203,-49523008,23591760,21441464,4925810,1850208⟩) else (if n < 285 then (⟨701173156,1839950,-49526391,23611122,21322510,5417617,1839956⟩) else (⟨705122888,1829719,-49529739,23630287,21192276,5906559,1829725⟩)))) else (if n < 289 then (if n < 287 then (⟨709090248,1819510,-49533054,23649256,21050832,6392376,1819516⟩) else (if n < 288 then (⟨713075336,1809323,-49536336,23668032,20898253,6874812,1809329⟩) else (⟨717078250,1799159,-49539585,23686618,20734619,7353611,1799165⟩))) else (if n < 290 then (⟨721099091,1789020,-49542804,23705014,20560016,7828520,1789026⟩) else (if n < 291 then (⟨725137960,1778904,-49545992,23723224,20374538,8299288,1778910⟩) else (⟨729194958,1768814,-49549151,23741248,20178283,8765666,1768820⟩))))
def a270_292 (n:ℕ):Line:= if n < 281 then (a270_281 n) else (a281_292 n)
def a292_303 (n:ℕ):Line:= if n < 297 then (if n < 294 then (if n < 293 then (⟨733270185,1758749,-49552281,23759089,19971353,9227407,1758755⟩) else (⟨737363744,1748710,-49555383,23776750,19753859,9684267,1748716⟩)) else (if n < 295 then (⟨741475738,1738698,-49558458,23794231,19525916,10136005,1738704⟩) else (if n < 296 then (⟨745606268,1728713,-49561506,23811535,19287644,10582380,1728719⟩) else (⟨749755438,1718755,-49564528,23828664,19039170,11023158,1718762⟩)))) else (if n < 300 then (if n < 298 then (⟨753923352,1708826,-49567525,23845620,18780624,11458105,1708832⟩) else (if n < 299 then (⟨758110115,1698925,-49570496,23862404,18512143,11886991,1698931⟩) else (⟨762315830,1689053,-49573444,23879018,18233870,12309589,1689060⟩))) else (if n < 301 then (⟨766540603,1679210,-49576368,23895464,17945952,12725675,1679217⟩) else (if n < 302 then (⟨770784540,1669398,-49579269,23911743,17648541,13135030,1669405⟩) else (⟨775047746,1659616,-49582147,23927859,17341794,13537436,1659623⟩))))
def a303_315 (n:ℕ):Line:= if n < 309 then (if n < 306 then (if n < 304 then (⟨779330329,1649864,-49585004,23943811,17025874,13932682,1649871⟩) else (if n < 305 then (⟨783632395,1640144,-49587838,23959603,16700947,14320557,1640151⟩) else (⟨787954052,1630455,-49590652,23975235,16367186,14700858,1630462⟩))) else (if n < 307 then (⟨792295407,1620798,-49593444,23990710,16024767,15073381,1620805⟩) else (if n < 308 then (⟨796656570,1611173,-49596217,24006028,15673872,15437932,1611180⟩) else (⟨801037650,1601580,-49598970,24021193,15314685,15794316,1601587⟩)))) else (if n < 312 then (if n < 310 then (⟨805438756,1592021,-49601703,24036204,14947397,16142345,1592028⟩) else (if n < 311 then (⟨809859997,1582494,-49604417,24051064,14572203,16481836,1582501⟩) else (⟨814301485,1573001,-49607112,24065775,14189300,16812608,1573009⟩))) else (if n < 313 then (⟨818763331,1563542,-49609789,24080338,13798891,17134486,1563549⟩) else (if n < 314 then (⟨823245646,1554117,-49612448,24094754,13401183,17447301,1554124⟩) else (⟨827748542,1544726,-49615089,24109025,12996386,17750886,1544733⟩))))
def a292_315 (n:ℕ):Line:= if n < 303 then (a292_303 n) else (a303_315 n)
def a270_315 (n:ℕ):Line:= if n < 292 then (a270_292 n) else (a292_315 n)
def a315_326 (n:ℕ):Line:= if n < 320 then (if n < 317 then (if n < 316 then (⟨832272131,1535370,-49617713,24123153,12584714,18045082,1535377⟩) else (⟨836816528,1526048,-49620319,24137139,12166385,18329732,1526056⟩)) else (if n < 318 then (⟨841381845,1516762,-49622909,24150985,11741621,18604686,1516769⟩) else (if n < 319 then (⟨845968196,1507511,-49625482,24164691,11310645,18869799,1507518⟩) else (⟨850575697,1498295,-49628039,24178260,10873687,19124930,1498303⟩)))) else (if n < 323 then (if n < 321 then (⟨855204463,1489116,-49630580,24191693,10430976,19369944,1489123⟩) else (if n < 322 then (⟨859854608,1479972,-49633105,24204991,9982748,19604712,1479979⟩) else (⟨864526250,1470864,-49635615,24218156,9529239,19829110,1470872⟩))) else (if n < 324 then (⟨869219505,1461793,-49638109,24231188,9070689,20043019,1461800⟩) else (if n < 325 then (⟨873934491,1452758,-49640588,24244090,8607341,20246325,1452766⟩) else (⟨878671325,1443760,-49643053,24256863,8139440,20438922,1443768⟩))))
def a326_337 (n:ℕ):Line:= if n < 331 then (if n < 328 then (if n < 327 then (⟨883430125,1434799,-49645502,24269508,7667234,20620706,1434807⟩) else (⟨888211012,1425875,-49647937,24282027,7190971,20791583,1425883⟩)) else (if n < 329 then (⟨893014104,1416988,-49650358,24294420,6710905,20951462,1416996⟩) else (if n < 330 then (⟨897839521,1408138,-49652764,24306689,6227289,21100258,1408146⟩) else (⟨902687385,1399326,-49655157,24318835,5740379,21237892,1399334⟩)))) else (if n < 334 then (if n < 332 then (⟨907557815,1390552,-49657536,24330860,5250432,21364292,1390560⟩) else (if n < 333 then (⟨912450935,1381815,-49659901,24342765,4757708,21479390,1381823⟩) else (⟨917366866,1373116,-49662252,24354550,4262467,21583127,1373124⟩))) else (if n < 335 then (⟨922305731,1364455,-49664590,24366218,3764972,21675447,1364463⟩) else (if n < 336 then (⟨927267654,1355832,-49666915,24377769,3265485,21756300,1355840⟩) else (⟨932252759,1347247,-49669227,24389205,2764270,21825646,1347255⟩))))
def a315_337 (n:ℕ):Line:= if n < 326 then (a315_326 n) else (a326_337 n)
def a337_348 (n:ℕ):Line:= if n < 342 then (if n < 339 then (if n < 338 then (⟨937261170,1338701,-49671526,24400527,2261594,21883446,1338709⟩) else (⟨942293012,1330192,-49673812,24411736,1757721,21929670,1330200⟩)) else (if n < 340 then (⟨947348412,1321723,-49676085,24422833,1252918,21964294,1321730⟩) else (if n < 341 then (⟨952427496,1313291,-49678346,24433819,747452,21987299,1313299⟩) else (⟨957530390,1304898,-49680594,24444695,241591,21998673,1304906⟩)))) else (if n < 345 then (if n < 343 then (⟨962657223,1296544,-49682830,24455463,-264398,21998411,1296552⟩) else (if n < 344 then (⟨967808122,1288229,-49685053,24466124,-770247,21986512,1288237⟩) else (⟨972983216,1279952,-49687265,24476678,-1275688,21962983,1279960⟩))) else (if n < 346 then (⟨978182636,1271714,-49689464,24487127,-1780455,21927836,1271722⟩) else (if n < 347 then (⟨983406509,1263514,-49691651,24497472,-2284280,21881089,1263522⟩) else (⟨988654968,1255354,-49693826,24507714,-2786896,21822768,1255362⟩))))
def a348_360 (n:ℕ):Line:= if n < 354 then (if n < 351 then (if n < 349 then (⟨993928143,1247232,-49695989,24517854,-3288038,21752903,1247240⟩) else (if n < 350 then (⟨999226167,1239149,-49698140,24527893,-3787441,21671532,1239157⟩) else (⟨1004549171,1231106,-49700280,24537832,-4284841,21578696,1231114⟩))) else (if n < 352 then (⟨1009897289,1223101,-49702408,24547672,-4779974,21474446,1223109⟩) else (if n < 353 then (⟨1015270655,1215135,-49704525,24557414,-5272578,21358837,1215143⟩) else (⟨1020669402,1207208,-49706629,24567060,-5762394,21231929,1207216⟩)))) else (if n < 357 then (if n < 355 then (⟨1026093667,1199320,-49708723,24576609,-6249161,21093790,1199327⟩) else (if n < 356 then (⟨1031543583,1191470,-49710805,24586063,-6732623,20944493,1191478⟩) else (⟨1037019288,1183660,-49712876,24595423,-7212523,20784117,1183668⟩))) else (if n < 358 then (⟨1042520919,1175889,-49714935,24604690,-7688608,20612746,1175897⟩) else (if n < 359 then (⟨1048048613,1168157,-49716984,24613865,-8160626,20430472,1168165⟩) else (⟨1053602508,1160463,-49719021,24622949,-8628327,20237391,1160471⟩))))
def a337_360 (n:ℕ):Line:= if n < 348 then (a337_348 n) else (a348_360 n)
def a315_360 (n:ℕ):Line:= if n < 337 then (a315_337 n) else (a337_360 n)
def a270_360 (n:ℕ):Line:= if n < 315 then (a270_315 n) else (a315_360 n)
def a180_360 (n:ℕ):Line:= if n < 270 then (a180_270 n) else (a270_360 n)
def a0_360 (n:ℕ):Line:= if n < 180 then (a0_180 n) else (a180_360 n)
def a360_371 (n:ℕ):Line:= if n < 365 then (if n < 362 then (if n < 361 then (⟨1059182743,1152809,-49721047,24631942,-9091463,20033604,1152817⟩) else (⟨1064789458,1145193,-49723062,24640846,-9549791,19819220,1145201⟩)) else (if n < 363 then (⟨1070422793,1137616,-49725066,24649662,-10003067,19594352,1137624⟩) else (if n < 364 then (⟨1076082888,1130078,-49727059,24658389,-10451052,19359120,1130086⟩) else (⟨1081769885,1122579,-49729041,24667031,-10893508,19113646,1122587⟩)))) else (if n < 368 then (if n < 366 then (⟨1087483927,1115118,-49731012,24675586,-11330202,18858062,1115126⟩) else (if n < 367 then (⟨1093225156,1107696,-49732973,24684056,-11760903,18592503,1107704⟩) else (⟨1098993715,1100313,-49734922,24692443,-12185382,18317109,1100321⟩))) else (if n < 369 then (⟨1104789750,1092969,-49736861,24700746,-12603415,18032025,1092976⟩) else (if n < 370 then (⟨1110613404,1085663,-49738789,24708966,-13014782,17737403,1085670⟩) else (⟨1116464824,1078395,-49740707,24717105,-13419264,17433398,1078403⟩))))
def a371_382 (n:ℕ):Line:= if n < 376 then (if n < 373 then (if n < 372 then (⟨1122344155,1071166,-49742613,24725164,-13816647,17120171,1071174⟩) else (⟨1128251545,1063975,-49744510,24733142,-14206722,16797888,1063983⟩)) else (if n < 374 then (⟨1134187141,1056823,-49746395,24741041,-14589282,16466719,1056831⟩) else (if n < 375 then (⟨1140151092,1049709,-49748270,24748862,-14964125,16126840,1049717⟩) else (⟨1146143547,1042633,-49750135,24756605,-15331051,15778430,1042641⟩)))) else (if n < 379 then (if n < 377 then (⟨1152164656,1035595,-49751989,24764271,-15689868,15421674,1035603⟩) else (if n < 378 then (⟨1158214568,1028595,-49753833,24771861,-16040386,15056760,1028603⟩) else (⟨1164293436,1021634,-49755666,24779376,-16382418,14683881,1021641⟩))) else (if n < 380 then (⟨1170401412,1014710,-49757489,24786817,-16715785,14303235,1014718⟩) else (if n < 381 then (⟨1176538648,1007824,-49759302,24794183,-17040309,13915023,1007832⟩) else (⟨1182705297,1000976,-49761104,24801477,-17355819,13519450,1000983⟩))))
def a360_382 (n:ℕ):Line:= if n < 371 then (a360_371 n) else (a371_382 n)
def a382_393 (n:ℕ):Line:= if n < 387 then (if n < 384 then (if n < 383 then (⟨1188901514,994165,-49762896,24808698,-17662149,13116726,994173⟩) else (⟨1195127453,987392,-49764678,24815848,-17959136,12707063,987400⟩)) else (if n < 385 then (⟨1201383271,980657,-49766449,24822927,-18246622,12290678,980665⟩) else (if n < 386 then (⟨1207669123,973959,-49768210,24829936,-18524457,11867792,973967⟩) else (⟨1213985167,967298,-49769962,24836875,-18792493,11438628,967306⟩)))) else (if n < 390 then (if n < 388 then (⟨1220331561,960675,-49771703,24843745,-19050588,11003414,960682⟩) else (if n < 389 then (⟨1226708463,954089,-49773434,24850548,-19298605,10562379,954096⟩) else (⟨1233116033,947539,-49775154,24857283,-19536414,10115756,947547⟩))) else (if n < 391 then (⟨1239554431,941027,-49776865,24863951,-19763889,9663783,941035⟩) else (if n < 392 then (⟨1246023818,934552,-49778566,24870553,-19980909,9206697,934559⟩) else (⟨1252524355,928113,-49780257,24877090,-20187360,8744742,928121⟩))))
def a393_405 (n:ℕ):Line:= if n < 399 then (if n < 396 then (if n < 394 then (⟨1259056206,921711,-49781937,24883562,-20383132,8278161,921718⟩) else (if n < 395 then (⟨1265619533,915345,-49783608,24889970,-20568121,7807201,915353⟩) else (⟨1272214501,909016,-49785269,24896315,-20742231,7332111,909024⟩))) else (if n < 397 then (⟨1278841274,902724,-49786920,24902597,-20905369,6853142,902731⟩) else (if n < 398 then (⟨1285500018,896467,-49788561,24908816,-21057448,6370548,896475⟩) else (⟨1292190900,890247,-49790193,24914974,-21198388,5884585,890254⟩)))) else (if n < 402 then (if n < 400 then (⟨1298914087,884063,-49791814,24921071,-21328115,5395509,884070⟩) else (if n < 401 then (⟨1305669746,877914,-49793426,24927108,-21446560,4903578,877922⟩) else (⟨1312458048,871801,-49795028,24933085,-21553660,4409054,871809⟩))) else (if n < 403 then (⟨1319279161,865724,-49796620,24939002,-21649358,3912197,865732⟩) else (if n < 404 then (⟨1326133256,859683,-49798202,24944861,-21733605,3413271,859690⟩) else (⟨1333020504,853677,-49799775,24950662,-21806355,2912539,853684⟩))))
def a382_405 (n:ℕ):Line:= if n < 393 then (a382_393 n) else (a393_405 n)
def a360_405 (n:ℕ):Line:= if n < 382 then (a360_382 n) else (a382_405 n)
def a405_416 (n:ℕ):Line:= if n < 410 then (if n < 407 then (if n < 406 then (⟨1339941078,847706,-49801338,24956406,-21867570,2410267,847714⟩) else (⟨1346895150,841771,-49802892,24962093,-21917217,1906720,841778⟩)) else (if n < 408 then (⟨1353882895,835870,-49804436,24967724,-21955271,1402164,835878⟩) else (if n < 409 then (⟨1360904487,830005,-49805970,24973299,-21981711,896867,830012⟩) else (⟨1367960102,824174,-49807495,24978818,-21996523,391095,824181⟩)))) else (if n < 413 then (if n < 411 then (⟨1375049916,818378,-49809010,24984283,-21999700,-114884,818386⟩) else (if n < 412 then (⟨1382174106,812617,-49810516,24989694,-21991239,-620802,812624⟩) else (⟨1389332851,806890,-49812013,24995052,-21971146,-1126392,806897⟩))) else (if n < 414 then (⟨1396526329,801197,-49813499,25000356,-21939430,-1631386,801205⟩) else (if n < 415 then (⟨1403754720,795539,-49814977,25005608,-21896108,-2135517,795546⟩) else (⟨1411018205,789915,-49816445,25010808,-21841205,-2638518,789922⟩))))
def a416_427 (n:ℕ):Line:= if n < 421 then (if n < 418 then (if n < 417 then (⟨1418316966,784325,-49817904,25015957,-21774747,-3140124,784332⟩) else (⟨1425651185,778768,-49819354,25021055,-21696772,-3640068,778775⟩)) else (if n < 419 then (⟨1433021045,773245,-49820794,25026102,-21607319,-4138087,773253⟩) else (if n < 420 then (⟨1440426730,767756,-49822225,25031099,-21506436,-4633917,767763⟩) else (⟨1447868427,762300,-49823647,25036047,-21394178,-5127296,762308⟩)))) else (if n < 424 then (if n < 422 then (⟨1455346320,756878,-49825059,25040946,-21270602,-5617963,756885⟩) else (if n < 423 then (⟨1462860597,751489,-49826463,25045797,-21135774,-6105658,751496⟩) else (⟨1470411445,746132,-49827857,25050599,-20989766,-6590123,746139⟩))) else (if n < 425 then (⟨1477999054,740809,-49829242,25055354,-20832655,-7071102,740816⟩) else (if n < 426 then (⟨1485623613,735518,-49830618,25060062,-20664524,-7548340,735525⟩) else (⟨1493285313,730260,-49831985,25064724,-20485462,-8021586,730268⟩))))
def a405_427 (n:ℕ):Line:= if n < 416 then (a405_416 n) else (a416_427 n)
def a427_438 (n:ℕ):Line:= if n < 432 then (if n < 429 then (if n < 428 then (⟨1500984344,725035,-49833343,25069339,-20295564,-8490588,725042⟩) else (⟨1508720901,719842,-49834692,25073909,-20094929,-8955100,719849⟩)) else (if n < 430 then (⟨1516495176,714681,-49836032,25078433,-19883665,-9414874,714688⟩) else (if n < 431 then (⟨1524307363,709552,-49837364,25082913,-19661883,-9869668,709559⟩) else (⟨1532157657,704456,-49838686,25087348,-19429701,-10319241,704463⟩)))) else (if n < 435 then (if n < 433 then (⟨1540046256,699391,-49839999,25091740,-19187240,-10763355,699398⟩) else (if n < 434 then (⟨1547973356,694357,-49841304,25096088,-18934630,-11201776,694364⟩) else (⟨1555939156,689356,-49842600,25100393,-18672004,-11634271,689362⟩))) else (if n < 436 then (⟨1563943854,684385,-49843887,25104656,-18399501,-12060612,684392⟩) else (if n < 437 then (⟨1571987651,679446,-49845166,25108876,-18117265,-12480574,679453⟩) else (⟨1580070747,674538,-49846435,25113055,-17825445,-12893933,674545⟩))))
def a438_450 (n:ℕ):Line:= if n < 444 then (if n < 441 then (if n < 439 then (⟨1588193345,669661,-49847696,25117193,-17524196,-13300472,669668⟩) else (if n < 440 then (⟨1596355649,664815,-49848949,25121289,-17213677,-13699975,664822⟩) else (⟨1604557861,660000,-49850193,25125345,-16894053,-14092231,660007⟩))) else (if n < 442 then (⟨1612800187,655215,-49851428,25129361,-16565492,-14477033,655222⟩) else (if n < 443 then (⟨1621082834,650461,-49852655,25133337,-16228168,-14854177,650467⟩) else (⟨1629406007,645737,-49853873,25137274,-15882260,-15223463,645743⟩)))) else (if n < 447 then (if n < 445 then (⟨1637769916,641043,-49855083,25141172,-15527950,-15584696,641049⟩) else (if n < 446 then (⟨1646174769,636379,-49856285,25145032,-15165427,-15937686,636386⟩) else (⟨1654620776,631745,-49857478,25148853,-14794882,-16282244,631752⟩))) else (if n < 448 then (⟨1663108150,627141,-49858662,25152636,-14416510,-16618190,627147⟩) else (if n < 449 then (⟨1671637100,622566,-49859839,25156382,-14030512,-16945345,622573⟩) else (⟨1680207842,618021,-49861007,25160092,-13637093,-17263537,618027⟩))))
def a427_450 (n:ℕ):Line:= if n < 438 then (a427_438 n) else (a438_450 n)
def a405_450 (n:ℕ):Line:= if n < 427 then (a405_427 n) else (a427_450 n)
def a360_450 (n:ℕ):Line:= if n < 405 then (a360_405 n) else (a405_450 n)
def a450_461 (n:ℕ):Line:= if n < 455 then (if n < 452 then (if n < 451 then (⟨1688820590,613505,-49862167,25163764,-13236460,-17572596,613511⟩) else (⟨1697475557,609018,-49863319,25167400,-12828825,-17872360,609025⟩)) else (if n < 453 then (⟨1706172962,604560,-49864462,25171000,-12414403,-18162670,604567⟩) else (if n < 454 then (⟨1714913021,600132,-49865598,25174565,-11993415,-18443372,600138⟩) else (⟨1723695954,595732,-49866725,25178094,-11566083,-18714319,595738⟩)))) else (if n < 458 then (if n < 456 then (⟨1732521978,591360,-49867844,25181588,-11132633,-18975365,591367⟩) else (if n < 457 then (⟨1741391316,587017,-49868956,25185048,-10693293,-19226375,587024⟩) else (⟨1750304189,582703,-49870059,25188474,-10248297,-19467213,582709⟩))) else (if n < 459 then (⟨1759260819,578416,-49871154,25191866,-9797880,-19697755,578423⟩) else (if n < 460 then (⟨1768261431,574158,-49872242,25195224,-9342281,-19917876,574164⟩) else (⟨1777306249,569927,-49873321,25198549,-8881739,-20127462,569934⟩))))
def a461_472 (n:ℕ):Line:= if n < 466 then (if n < 463 then (if n < 462 then (⟨1786395501,565725,-49874393,25201841,-8416499,-20326400,565731⟩) else (⟨1795529412,561550,-49875457,25205101,-7946807,-20514587,561556⟩)) else (if n < 464 then (⟨1804708212,557402,-49876513,25208328,-7472911,-20691921,557408⟩) else (if n < 465 then (⟨1813932129,553282,-49877562,25211524,-6995062,-20858310,553288⟩) else (⟨1823201395,549189,-49878603,25214688,-6513514,-21013666,549195⟩)))) else (if n < 469 then (if n < 467 then (⟨1832516241,545123,-49879636,25217820,-6028519,-21157905,545129⟩) else (if n < 468 then (⟨1841876900,541084,-49880661,25220922,-5540336,-21290953,541090⟩) else (⟨1851283606,537072,-49881679,25223993,-5049222,-21412738,537078⟩))) else (if n < 470 then (⟨1860736594,533086,-49882690,25227033,-4555437,-21523197,533093⟩) else (if n < 471 then (⟨1870236101,529127,-49883693,25230044,-4059242,-21622270,529133⟩) else (⟨1879782363,525195,-49884688,25233025,-3560900,-21709905,525201⟩))))
def a450_472 (n:ℕ):Line:= if n < 461 then (a450_461 n) else (a461_472 n)
def a472_483 (n:ℕ):Line:= if n < 477 then (if n < 474 then (if n < 473 then (⟨1889375621,521288,-49885676,25235976,-3060674,-21786057,521294⟩) else (⟨1899016113,517408,-49886657,25238898,-2558830,-21850684,517414⟩)) else (if n < 475 then (⟨1908704080,513554,-49887630,25241791,-2055631,-21903753,513560⟩) else (if n < 476 then (⟨1918439765,509725,-49888597,25244656,-1551346,-21945235,509731⟩) else (⟨1928223411,505922,-49889555,25247492,-1046240,-21975108,505928⟩)))) else (if n < 480 then (if n < 478 then (⟨1938055263,502145,-49890507,25250301,-540580,-21993357,502151⟩) else (if n < 479 then (⟨1947935566,498393,-49891451,25253081,-34634,-21999973,498399⟩) else (⟨1957864568,494666,-49892389,25255834,471330,-21994951,494673⟩))) else (if n < 481 then (⟨1967842516,490965,-49893319,25258560,977044,-21978293,490971⟩) else (if n < 482 then (⟨1977869661,487289,-49894242,25261259,1482242,-21950010,487295⟩) else (⟨1987946253,483637,-49895158,25263931,1986656,-21910116,483643⟩))))
def a483_495 (n:ℕ):Line:= if n < 489 then (if n < 486 then (if n < 484 then (⟨1998072543,480010,-49896067,25266577,2490018,-21858632,480016⟩) else (if n < 485 then (⟨2008248785,476408,-49896969,25269196,2992064,-21795586,476414⟩) else (⟨2018475234,472830,-49897864,25271790,3492527,-21721010,472836⟩))) else (if n < 487 then (⟨2028752144,469277,-49898752,25274358,3991142,-21634944,469283⟩) else (if n < 488 then (⟨2039079773,465748,-49899634,25276900,4487647,-21537433,465754⟩) else (⟨2049458380,462242,-49900509,25279418,4981777,-21428530,462248⟩)))) else (if n < 492 then (if n < 490 then (⟨2059888223,458761,-49901376,25281910,5473272,-21308292,458767⟩) else (if n < 491 then (⟨2070369563,455304,-49902238,25284378,5961872,-21176782,455310⟩) else (⟨2080902663,451870,-49903092,25286822,6447318,-21034070,451876⟩))) else (if n < 493 then (⟨2091487786,448460,-49903940,25289241,6929354,-20880231,448466⟩) else (if n < 494 then (⟨2102125195,445073,-49904781,25291637,7407724,-20715348,445079⟩) else (⟨2112815158,441709,-49905616,25294008,7882176,-20539506,441715⟩))))
def a472_495 (n:ℕ):Line:= if n < 483 then (a472_483 n) else (a483_495 n)
def a450_495 (n:ℕ):Line:= if n < 472 then (a450_472 n) else (a472_495 n)
def a495_506 (n:ℕ):Line:= if n < 500 then (if n < 497 then (if n < 496 then (⟨2123557942,438369,-49906444,25296357,8352458,-20352799,438375⟩) else (⟨2134353814,435051,-49907266,25298682,8818322,-20155327,435057⟩)) else (if n < 498 then (⟨2145203046,431757,-49908081,25300984,9279521,-19947192,431762⟩) else (if n < 499 then (⟨2156105907,428485,-49908890,25303263,9735812,-19728506,428491⟩) else (⟨2167062672,425235,-49909692,25305520,10186953,-19499384,425241⟩)))) else (if n < 503 then (if n < 501 then (⟨2178073613,422009,-49910488,25307754,10632705,-19259948,422014⟩) else (if n < 502 then (⟨2189139006,418804,-49911278,25309966,11072832,-19010323,418810⟩) else (⟨2200259127,415622,-49912062,25312157,11507102,-18750642,415628⟩))) else (if n < 504 then (⟨2211434256,412462,-49912839,25314326,11935286,-18481043,412468⟩) else (if n < 505 then (⟨2222664670,409324,-49913610,25316473,12357155,-18201668,409329⟩) else (⟨2233950651,406207,-49914375,25318599,12772489,-17912664,406213⟩))))
def a506_517 (n:ℕ):Line:= if n < 511 then (if n < 508 then (if n < 507 then (⟨2245292480,403113,-49915134,25320704,13181065,-17614185,403119⟩) else (⟨2256690443,400040,-49915887,25322788,13582670,-17306389,400045⟩)) else (if n < 509 then (⟨2268144822,396988,-49916633,25324852,13977089,-16989437,396994⟩) else (if n < 510 then (⟨2279655906,393958,-49917374,25326895,14364115,-16663499,393964⟩) else (⟨2291223980,390949,-49918109,25328918,14743542,-16328746,390955⟩)))) else (if n < 514 then (if n < 512 then (⟨2302849336,387961,-49918838,25330921,15115171,-15985356,387967⟩) else (if n < 513 then (⟨2314532263,384994,-49919561,25332904,15478804,-15633510,385000⟩) else (⟨2326273053,382048,-49920278,25334867,15834249,-15273394,382053⟩))) else (if n < 515 then (⟨2338072001,379122,-49920990,25336811,16181318,-14905198,379128⟩) else (if n < 516 then (⟨2349929400,376217,-49921695,25338736,16519828,-14529119,376223⟩) else (⟨2361845548,373333,-49922395,25340642,16849599,-14145353,373339⟩))))
def a495_517 (n:ℕ):Line:= if n < 506 then (a495_506 n) else (a506_517 n)
def a517_528 (n:ℕ):Line:= if n < 522 then (if n < 519 then (if n < 518 then (⟨2373820741,370469,-49923089,25342529,17170457,-13754106,370475⟩) else (⟨2385855281,367625,-49923778,25344397,17482232,-13355582,367631⟩)) else (if n < 520 then (⟨2397949467,364801,-49924461,25346247,17784759,-12949994,364807⟩) else (if n < 521 then (⟨2410103602,361998,-49925138,25348078,18077879,-12537555,362003⟩) else (⟨2422317989,359214,-49925810,25349892,18361436,-12118485,359219⟩)))) else (if n < 525 then (if n < 523 then (⟨2434592935,356449,-49926476,25351687,18635280,-11693004,356455⟩) else (if n < 524 then (⟨2446928746,353705,-49927137,25353465,18899267,-11261337,353710⟩) else (⟨2459325730,350980,-49927792,25355225,19153256,-10823714,350985⟩))) else (if n < 526 then (⟨2471784197,348274,-49928442,25356968,19397114,-10380365,348279⟩) else (if n < 527 then (⟨2484304459,345587,-49929087,25358693,19630711,-9931525,345593⟩) else (⟨2496886828,342920,-49929726,25360401,19853924,-9477432,342925⟩))))
def a528_540 (n:ℕ):Line:= if n < 534 then (if n < 531 then (if n < 529 then (⟨2509531620,340272,-49930360,25362093,20066634,-9018326,340277⟩) else (if n < 530 then (⟨2522239151,337642,-49930989,25363767,20268730,-8554448,337648⟩) else (⟨2535009737,335032,-49931613,25365425,20460104,-8086046,335037⟩))) else (if n < 532 then (⟨2547843699,332440,-49932231,25367067,20640655,-7613367,332445⟩) else (if n < 533 then (⟨2560741357,329866,-49932844,25368692,20810288,-7136660,329872⟩) else (⟨2573703034,327311,-49933452,25370302,20968913,-6656178,327317⟩)))) else (if n < 537 then (if n < 535 then (⟨2586729054,324775,-49934056,25371895,21116445,-6172175,324780⟩) else (if n < 536 then (⟨2599819742,322256,-49934654,25373473,21252808,-5684907,322262⟩) else (⟨2612975425,319756,-49935247,25375035,21377928,-5194632,319761⟩))) else (if n < 538 then (⟨2626196433,317274,-49935835,25376581,21491740,-4701609,317279⟩) else (if n < 539 then (⟨2639483096,314809,-49936418,25378113,21594183,-4206099,314815⟩) else (⟨2652835746,312363,-49936996,25379629,21685203,-3708364,312368⟩))))
def a517_540 (n:ℕ):Line:= if n < 528 then (a517_528 n) else (a528_540 n)
def a495_540 (n:ℕ):Line:= if n < 517 then (a495_517 n) else (a517_540 n)
def a450_540 (n:ℕ):Line:= if n < 495 then (a450_495 n) else (a495_540 n)
def a360_540 (n:ℕ):Line:= if n < 450 then (a360_450 n) else (a450_540 n)
def a540_551 (n:ℕ):Line:= if n < 545 then (if n < 542 then (if n < 541 then (⟨2666254718,309934,-49937569,25381130,21764753,-3208668,309939⟩) else (⟨2679740346,307522,-49938138,25382616,21832789,-2707274,307527⟩)) else (if n < 543 then (⟨2693292967,305128,-49938701,25384087,21889276,-2204448,305133⟩) else (if n < 544 then (⟨2706912921,302751,-49939260,25385544,21934185,-1700456,302756⟩) else (⟨2720600548,300392,-49939815,25386987,21967490,-1195564,300397⟩)))) else (if n < 548 then (if n < 546 then (⟨2734356190,298049,-49940364,25388415,21989176,-690040,298054⟩) else (if n < 547 then (⟨2748180191,295724,-49940909,25389829,21999229,-184151,295729⟩) else (⟨2762072897,293415,-49941449,25391229,21997646,321835,293420⟩))) else (if n < 549 then (⟨2776034654,291123,-49941985,25392615,21984426,827651,291128⟩) else (if n < 550 then (⟨2790065813,288848,-49942516,25393988,21959577,1333029,288853⟩) else (⟨2804166724,286590,-49943043,25395347,21923112,1837703,286595⟩))))
def a551_562 (n:ℕ):Line:= if n < 556 then (if n < 553 then (if n < 552 then (⟨2818337738,284348,-49943565,25396692,21875050,2341404,284353⟩) else (⟨2832579212,282122,-49944082,25398024,21815417,2843866,282127⟩)) else (if n < 554 then (⟨2846891500,279912,-49944595,25399343,21744244,3344824,279917⟩) else (if n < 555 then (⟨2861274960,277719,-49945104,25400649,21661569,3844013,277724⟩) else (⟨2875729953,275542,-49945609,25401942,21567435,4341169,275547⟩)))) else (if n < 559 then (if n < 557 then (⟨2890256839,273380,-49946109,25403222,21461893,4836028,273385⟩) else (if n < 558 then (⟨2904855981,271235,-49946605,25404490,21344997,5328329,271240⟩) else (⟨2919527745,269105,-49947096,25405745,21216811,5817811,269110⟩))) else (if n < 560 then (⟨2934272498,266991,-49947583,25406987,21077402,6304216,266995⟩) else (if n < 561 then (⟨2949090607,264892,-49948067,25408217,20926843,6787286,264897⟩) else (⟨2963982444,262809,-49948545,25409435,20765214,7266766,262813⟩))))
def a540_562 (n:ℕ):Line:= if n < 551 then (a540_551 n) else (a551_562 n)
def a562_573 (n:ℕ):Line:= if n < 567 then (if n < 564 then (if n < 563 then (⟨2978948380,260741,-49949020,25410641,20592601,7742402,260746⟩) else (⟨2993988791,258688,-49949491,25411835,20409095,8213942,258693⟩)) else (if n < 565 then (⟨3009104051,256650,-49949958,25413017,20214793,8681137,256655⟩) else (if n < 566 then (⟨3024294539,254628,-49950420,25414188,20009798,9143741,254633⟩) else (⟨3039560634,252620,-49950879,25415346,19794218,9601507,252625⟩)))) else (if n < 570 then (if n < 568 then (⟨3054902719,250627,-49951333,25416494,19568167,10054194,250632⟩) else (if n < 569 then (⟨3070321176,248649,-49951784,25417630,19331766,10501563,248654⟩) else (⟨3085816392,246686,-49952231,25418755,19085138,10943377,246690⟩))) else (if n < 571 then (⟨3101388753,244737,-49952673,25419868,18828415,11379402,244741⟩) else (if n < 572 then (⟨3117038649,242802,-49953112,25420971,18561732,11809408,242807⟩) else (⟨3132766471,240882,-49953547,25422062,18285230,12233167,240887⟩))))
def a573_585 (n:ℕ):Line:= if n < 579 then (if n < 576 then (if n < 574 then (⟨3148572613,238976,-49953979,25423143,17999056,12650454,238981⟩) else (if n < 575 then (⟨3164457469,237084,-49954406,25424213,17703360,13061050,237089⟩) else (⟨3180421436,235207,-49954830,25425273,17398300,13464737,235211⟩))) else (if n < 577 then (⟨3196464915,233343,-49955250,25426322,17084037,13861301,233348⟩) else (if n < 578 then (⟨3212588305,231493,-49955666,25427360,16760737,14250533,231498⟩) else (⟨3228792010,229657,-49956079,25428389,16428570,14632227,229662⟩)))) else (if n < 582 then (if n < 580 then (⟨3245076434,227835,-49956488,25429407,16087714,15006181,227839⟩) else (if n < 581 then (⟨3261441986,226026,-49956893,25430415,15738347,15372197,226030⟩) else (⟨3277889075,224230,-49957295,25431413,15380655,15730081,224235⟩))) else (if n < 583 then (⟨3294418110,222449,-49957694,25432401,15014827,16079645,222453⟩) else (if n < 584 then (⟨3311029506,220680,-49958089,25433379,14641056,16420702,220685⟩) else (⟨3327723679,218925,-49958480,25434348,14259541,16753074,218929⟩))))
def a562_585 (n:ℕ):Line:= if n < 573 then (a562_573 n) else (a573_585 n)
def a540_585 (n:ℕ):Line:= if n < 562 then (a540_562 n) else (a562_585 n)
def a585_596 (n:ℕ):Line:= if n < 590 then (if n < 587 then (if n < 586 then (⟨3344501044,217183,-49958868,25435307,13870483,17076583,217187⟩) else (⟨3361362022,215453,-49959252,25436257,13474088,17391060,215458⟩)) else (if n < 588 then (⟨3378307034,213737,-49959633,25437197,13070565,17696337,213742⟩) else (if n < 589 then (⟨3395336505,212034,-49960011,25438128,12660128,17992253,212039⟩) else (⟨3412450858,210343,-49960385,25439049,12242994,18278651,210348⟩)))) else (if n < 593 then (if n < 591 then (⟨3429650524,208666,-49960756,25439962,11819384,18555381,208670⟩) else (if n < 592 then (⟨3446935930,207001,-49961124,25440865,11389522,18822295,207005⟩) else (⟨3464307510,205348,-49961488,25441760,10953635,19079253,205352⟩))) else (if n < 594 then (⟨3481765699,203708,-49961849,25442645,10511954,19326118,203712⟩) else (if n < 595 then (⟨3499310931,202080,-49962207,25443522,10064712,19562760,202084⟩) else (⟨3516943646,200464,-49962562,25444390,9612146,19789054,200469⟩))))
def a596_607 (n:ℕ):Line:= if n < 601 then (if n < 598 then (if n < 597 then (⟨3534664285,198861,-49962913,25445250,9154496,20004880,198866⟩) else (⟨3552473291,197270,-49963262,25446101,8692003,20210123,197274⟩)) else (if n < 599 then (⟨3570371109,195691,-49963607,25446944,8224912,20404677,195695⟩) else (if n < 600 then (⟨3588358187,194123,-49963949,25447778,7753470,20588436,194128⟩) else (⟨3606434973,192568,-49964288,25448604,7277927,20761305,192572⟩)))) else (if n < 604 then (if n < 602 then (⟨3624601921,191024,-49964625,25449422,6798534,20923191,191029⟩) else (if n < 603 then (⟨3642859484,189492,-49964958,25450231,6315545,21074010,189497⟩) else (⟨3661208118,187972,-49965288,25451033,5829215,21213681,187977⟩))) else (if n < 605 then (⟨3679648283,186463,-49965615,25451827,5339802,21342130,186468⟩) else (if n < 606 then (⟨3698180440,184966,-49965939,25452612,4847564,21459290,184970⟩) else (⟨3716805051,183480,-49966260,25453390,4352762,21565098,183485⟩))))
def a585_607 (n:ℕ):Line:= if n < 596 then (a585_596 n) else (a596_607 n)
def a607_618 (n:ℕ):Line:= if n < 612 then (if n < 609 then (if n < 608 then (⟨3735522582,182005,-49966578,25454161,3855657,21659499,182010⟩) else (⟨3754333502,180542,-49966894,25454923,3356513,21742443,180546⟩)) else (if n < 610 then (⟨3773238280,179090,-49967207,25455679,2855593,21813885,179094⟩) else (if n < 611 then (⟨3792237389,177649,-49967516,25456426,2353162,21873789,177653⟩) else (⟨3811331305,176218,-49967823,25457166,1849487,21922121,176223⟩)))) else (if n < 615 then (if n < 613 then (⟨3830520504,174799,-49968128,25457899,1344834,21958857,174803⟩) else (if n < 614 then (⟨3849805466,173391,-49968429,25458625,839469,21983978,173395⟩) else (⟨3869186673,171993,-49968728,25459343,333660,21997470,171997⟩))) else (if n < 616 then (⟨3888664610,170606,-49969024,25460055,-172326,21999325,170610⟩) else (if n < 617 then (⟨3908239765,169230,-49969317,25460759,-678220,21989543,169234⟩) else (⟨3927912625,167864,-49969608,25461456,-1183755,21968130,167868⟩))))
def a618_630 (n:ℕ):Line:= if n < 624 then (if n < 621 then (if n < 619 then (⟨3947683683,166508,-49969896,25462146,-1688665,21935095,166513⟩) else (if n < 620 then (⟨3967553434,165163,-49970181,25462830,-2192681,21890458,165168⟩) else (⟨3987522374,163829,-49970464,25463507,-2695537,21834241,163833⟩))) else (if n < 622 then (⟨4007591002,162504,-49970744,25464177,-3196967,21766474,162508⟩) else (if n < 623 then (⟨4027759820,161190,-49971022,25464840,-3696707,21687193,161194⟩) else (⟨4048029332,159886,-49971297,25465497,-4194490,21596441,159890⟩)))) else (if n < 627 then (if n < 625 then (⟨4068400045,158591,-49971569,25466147,-4690055,21494264,158596⟩) else (if n < 626 then (⟨4088872468,157307,-49971840,25466791,-5183139,21380717,157312⟩) else (⟨4109447114,156033,-49972107,25467428,-5673481,21255861,156037⟩))) else (if n < 628 then (⟨4130124495,154768,-49972372,25468059,-6160823,21119760,154773⟩) else (if n < 629 then (⟨4150905130,153514,-49972635,25468684,-6644905,20972488,153518⟩) else (⟨4171789538,152269,-49972896,25469303,-7125472,20814121,152273⟩))))
def a607_630 (n:ℕ):Line:= if n < 618 then (a607_618 n) else (a618_630 n)
def a585_630 (n:ℕ):Line:= if n < 607 then (a585_607 n) else (a607_630 n)
def a540_630 (n:ℕ):Line:= if n < 585 then (a540_585 n) else (a585_630 n)
def a630_641 (n:ℕ):Line:= if n < 635 then (if n < 632 then (if n < 631 then (⟨4192778241,151033,-49973154,25469915,-7602270,20644745,151037⟩) else (⟨4213871764,149807,-49973409,25470522,-8075047,20464448,149811⟩)) else (if n < 633 then (⟨4235070633,148591,-49973662,25471122,-8543552,20273325,148595⟩) else (if n < 634 then (⟨4256375380,147384,-49973913,25471717,-9007537,20071479,147388⟩) else (⟨4277786536,146186,-49974162,25472305,-9466758,19859015,146190⟩)))) else (if n < 638 then (if n < 636 then (⟨4299304637,144998,-49974408,25472888,-9920971,19636047,145002⟩) else (if n < 637 then (⟨4320930221,143818,-49974653,25473465,-10369937,19402691,143822⟩) else (⟨4342663828,142648,-49974894,25474036,-10813417,19159072,142652⟩))) else (if n < 639 then (⟨4364506002,141487,-49975134,25474602,-11251176,18905318,141491⟩) else (if n < 640 then (⟨4386457290,140335,-49975371,25475162,-11682984,18641563,140339⟩) else (⟨4408518238,139192,-49975607,25475716,-12108613,18367948,139196⟩))))
def a641_652 (n:ℕ):Line:= if n < 646 then (if n < 643 then (if n < 642 then (⟨4430689400,138058,-49975840,25476265,-12527836,18084616,138062⟩) else (⟨4452971330,136932,-49976071,25476808,-12940432,17791718,136936⟩)) else (if n < 644 then (⟨4475364583,135816,-49976299,25477346,-13346182,17489409,135820⟩) else (if n < 645 then (⟨4497869722,134708,-49976526,25477879,-13744873,17177848,134712⟩) else (⟨4520487307,133608,-49976750,25478406,-14136294,16857200,133613⟩)))) else (if n < 649 then (if n < 647 then (⟨4543217904,132518,-49976973,25478929,-14520236,16527636,132522⟩) else (if n < 648 then (⟨4566062083,131435,-49977193,25479446,-14896498,16189328,131439⟩) else (⟨4589020413,130362,-49977412,25479958,-15264880,15842457,130366⟩))) else (if n < 650 then (⟨4612093469,129296,-49977628,25480464,-15625187,15487206,129300⟩) else (if n < 651 then (⟨4635281827,128239,-49977842,25480966,-15977228,15123762,128243⟩) else (⟨4658586068,127190,-49978055,25481463,-16320818,14752318,127194⟩))))
def a630_652 (n:ℕ):Line:= if n < 641 then (a630_641 n) else (a641_652 n)
def a652_663 (n:ℕ):Line:= if n < 657 then (if n < 654 then (if n < 653 then (⟨4682006774,126149,-49978265,25481955,-16655775,14373070,126153⟩) else (⟨4705544530,125117,-49978473,25482442,-16981921,13986220,125121⟩)) else (if n < 655 then (⟨4729199924,124092,-49978680,25482924,-17299085,13591971,124096⟩) else (if n < 656 then (⟨4752973550,123076,-49978884,25483401,-17607097,13190532,123080⟩) else (⟨4776865999,122067,-49979087,25483874,-17905796,12782116,122071⟩)))) else (if n < 660 then (if n < 658 then (⟨4800877871,121067,-49979288,25484342,-18195022,12366938,121071⟩) else (if n < 659 then (⟨4825009765,120074,-49979487,25484805,-18474625,11945219,120078⟩) else (⟨4849262284,119089,-49979684,25485264,-18744454,11517180,119093⟩))) else (if n < 661 then (⟨4873636035,118112,-49979879,25485718,-19004368,11083050,118116⟩) else (if n < 662 then (⟨4898131627,117142,-49980072,25486168,-19254229,10643056,117146⟩) else (⟨4922749673,116180,-49980264,25486613,-19493906,10197433,116184⟩))))
def a663_675 (n:ℕ):Line:= if n < 669 then (if n < 666 then (if n < 664 then (⟨4947490788,115226,-49980454,25487053,-19723270,9746416,115230⟩) else (if n < 665 then (⟨4972355590,114279,-49980642,25487490,-19942201,9290243,114283⟩) else (⟨4997344702,113340,-49980828,25487922,-20150583,8829155,113344⟩))) else (if n < 667 then (⟨5022458747,112408,-49981012,25488350,-20348307,8363398,112412⟩) else (if n < 668 then (⟨5047698354,111483,-49981195,25488773,-20535266,7893216,111487⟩) else (⟨5073064154,110566,-49981376,25489192,-20711362,7418859,110570⟩)))) else (if n < 672 then (if n < 670 then (⟨5098556781,109655,-49981556,25489608,-20876503,6940577,109659⟩) else (if n < 671 then (⟨5124176872,108752,-49981733,25490019,-21030601,6458624,108756⟩) else (⟨5149925067,107857,-49981909,25490425,-21173574,5973255,107860⟩))) else (if n < 673 then (⟨5175802011,106968,-49982084,25490828,-21305346,5484726,106972⟩) else (if n < 674 then (⟨5201808350,106086,-49982256,25491227,-21425849,4993295,106090⟩) else (⟨5227944735,105211,-49982428,25491622,-21535018,4499224,105215⟩))))
def a652_675 (n:ℕ):Line:= if n < 663 then (a652_663 n) else (a663_675 n)
def a630_675 (n:ℕ):Line:= if n < 652 then (a630_652 n) else (a652_675 n)
def a675_686 (n:ℕ):Line:= if n < 680 then (if n < 677 then (if n < 676 then (⟨5254211819,104343,-49982597,25492013,-21632795,4002772,104347⟩) else (⟨5280610258,103482,-49982765,25492400,-21719129,3504203,103486⟩)) else (if n < 678 then (⟨5307140713,102628,-49982931,25492784,-21793974,3003780,102632⟩) else (if n < 679 then (⟨5333803846,101781,-49983096,25493163,-21857291,2501768,101785⟩) else (⟨5360600325,100940,-49983259,25493539,-21909045,1998433,100944⟩)))) else (if n < 683 then (if n < 681 then (⟨5387530819,100106,-49983421,25493911,-21949210,1494041,100110⟩) else (if n < 682 then (⟨5414596002,99279,-49983581,25494279,-21977765,988859,99282⟩) else (⟨5441796550,98458,-49983740,25494644,-21994694,483153,98462⟩))) else (if n < 684 then (⟨5469133143,97643,-49983897,25495005,-21999988,-22808,97647⟩) else (if n < 685 then (⟨5496606465,96836,-49984053,25495362,-21993645,-528757,96839⟩) else (⟨5524217202,96034,-49984207,25495716,-21975667,-1034427,96038⟩))))
def a686_698 (n:ℕ):Line:= if n < 692 then (if n < 689 then (if n < 687 then (⟨5551966045,95239,-49984359,25496067,-21946065,-1539549,95243⟩) else (if n < 688 then (⟨5579853687,94450,-49984511,25496413,-21904854,-2043857,94454⟩) else (⟨5607880826,93668,-49984661,25496757,-21852056,-2547083,93672⟩))) else (if n < 690 then (⟨5636048163,92892,-49984809,25497097,-21787699,-3048963,92895⟩) else (if n < 691 then (⟨5664356401,92122,-49984956,25497434,-21711816,-3549229,92125⟩) else (⟨5692806248,91358,-49985102,25497767,-21624449,-4047618,91361⟩)))) else (if n < 695 then (if n < 693 then (⟨5721398415,90600,-49985246,25498097,-21525642,-4543866,90604⟩) else (if n < 694 then (⟨5750133618,89848,-49985389,25498424,-21415449,-5037710,89852⟩) else (⟨5779012574,89102,-49985531,25498747,-21293928,-5528890,89106⟩))) else (if n < 696 then (⟨5808036006,88362,-49985671,25499067,-21161143,-6017145,88366⟩) else (if n < 697 then (⟨5837204639,87628,-49985810,25499384,-21017164,-6502217,87632⟩) else (⟨5866519203,86900,-49985947,25499698,-20862067,-6983849,86904⟩))))
def a675_698 (n:ℕ):Line:= if n < 686 then (a675_686 n) else (a686_698 n)
def a698_709 (n:ℕ):Line:= if n < 703 then (if n < 700 then (if n < 699 then (⟨5895980430,86178,-49986083,25500009,-20695935,-7461787,86182⟩) else (⟨5925589056,85462,-49986218,25500317,-20518855,-7935778,85465⟩)) else (if n < 701 then (⟨5955345823,84751,-49986352,25500622,-20330922,-8405571,84755⟩) else (if n < 702 then (⟨5985251474,84046,-49986485,25500923,-20132233,-8870918,84050⟩) else (⟨6015306756,83347,-49986616,25501222,-19922895,-9331572,83350⟩)))) else (if n < 706 then (if n < 704 then (⟨6045512421,82653,-49986746,25501518,-19703019,-9787290,82657⟩) else (if n < 705 then (⟨6075869225,81965,-49986874,25501810,-19472720,-10237831,81968⟩) else (⟨6106377925,81282,-49987002,25502100,-19232120,-10682956,81286⟩))) else (if n < 707 then (⟨6137039285,80605,-49987128,25502387,-18981347,-11122431,80608⟩) else (if n < 708 then (⟨6167854072,79933,-49987253,25502671,-18720533,-11556021,79937⟩) else (⟨6198823055,79267,-49987377,25502953,-18449817,-11983499,79270⟩))))
def a709_721 (n:ℕ):Line:= if n < 715 then (if n < 712 then (if n < 710 then (⟨6229947009,78606,-49987500,25503231,-18169341,-12404638,78609⟩) else (if n < 711 then (⟨6261226712,77950,-49987621,25503507,-17879254,-12819215,77954⟩) else (⟨6292662946,77299,-49987741,25503780,-17579709,-13227011,77303⟩))) else (if n < 713 then (⟨6324256497,76654,-49987861,25504050,-17270865,-13627811,76658⟩) else (if n < 714 then (⟨6356008155,76014,-49987979,25504318,-16952885,-14021401,76018⟩) else (⟨6387918713,75379,-49988096,25504583,-16625937,-14407575,75383⟩)))) else (if n < 718 then (if n < 716 then (⟨6419988970,74750,-49988211,25504845,-16290195,-14786127,74753⟩) else (if n < 717 then (⟨6452219726,74125,-49988326,25505105,-15945836,-15156858,74129⟩) else (⟨6484611789,73505,-49988440,25505362,-15593041,-15519571,73509⟩))) else (if n < 719 then (⟨6517165967,72891,-49988552,25505617,-15231998,-15874074,72894⟩) else (if n < 720 then (⟨6549883074,72281,-49988664,25505869,-14862898,-16220181,72285⟩) else (⟨6582763929,71676,-49988774,25506118,-14485936,-16557707,71676⟩))))
def a698_721 (n:ℕ):Line:= if n < 709 then (a698_709 n) else (a709_721 n)
def a675_721 (n:ℕ):Line:= if n < 698 then (a675_698 n) else (a698_721 n)
def a630_721 (n:ℕ):Line:= if n < 675 then (a630_675 n) else (a675_721 n)
def a540_721 (n:ℕ):Line:= if n < 630 then (a540_630 n) else (a630_721 n)
def a360_721 (n:ℕ):Line:= if n < 540 then (a360_540 n) else (a540_721 n)
def a0_721 (n:ℕ):Line:= if n < 360 then (a0_360 n) else (a360_721 n)
def A (n:ℕ):Line:=a0_721 n
end GeneralMahler.SCal.Grid.Nodes

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Base
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Tail jets use log coordinate t, denoted y here. This implements D=x∂_x. -/
open Set Filter Real
noncomputable section
namespace GeneralMahler.SCal.Tail
def XX:=Real.exp
def iv (y:ℝ):=(XX y)⁻¹
def ev (y:ℝ):=(iv y)^2 -- ξ
def Z0:=Real.log (√(2*π))-1/2
def Lv (y:ℝ):=y+Z0
def Wv (y:ℝ):=ev y*Lv y
end GeneralMahler.SCal.Tail

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Tail_Limit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §07 log domain elementary envelope values. -/
open Set Filter Real
namespace GeneralMahler.SCal.Tail
open Grid Tag
noncomputable section
def y0:= Real.log 64
end

end GeneralMahler.SCal.Tail

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §08 segment coordinates and physical averages. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal.SE
open Tag Grid
variable {m h:ℝ}
def left (m h :ℝ):=m-h
def right (m h:ℝ):=m+h
def loc (m h β:ℝ):=m+h*β
def mean0 (f:ℝ→ℝ):=(1/2:ℝ)*(∫ β in (-1:ℝ)..1,f β)
def de (m h:ℝ)(x:ℝ):= cosh (loc m h x)
def normM (m h:ℝ):= mean0 (de m h)
def normE (m h:ℝ)(f:ℝ→ℝ):=mean0 (fun x=> de m h x*f x)/normM m h
def Pbar (m h:ℝ)(f:ℝ→ℝ):=normE m h (fun x=> f (loc m h x))

end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Scalar_Integr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Finite-area bound and infinite tail for K. -/
open MeasureTheory Set Filter Real
open scoped Topology Interval
namespace GeneralMahler.SCal
open Grid Tag Nodes

noncomputable def wI (x:ℝ):= -(Real.log x+1)/x
noncomputable def wD (x:ℝ):=Real.log x/x^2
end GeneralMahler.SCal

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Bound2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Interval on t; second derivative majorants. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid SE

structure Cap where
  a:ℝ
  b:ℝ
  c:ℝ
namespace Cap
def plus (X Y:Cap):Cap:=⟨X.a+Y.a,X.b+Y.b,X.c+Y.c⟩
def times (X Y:Cap):Cap:=⟨X.a*Y.a,X.b*Y.a+X.a*Y.b,X.c*Y.a+X.a*Y.c+2*X.b*Y.b⟩
def av (X:Cap):Cap:=⟨X.a,X.b+2*X.a,X.c+4*X.b+6*X.a⟩
def fl (a:ℝ):Cap:=⟨a,0,0⟩
end Cap
end GeneralMahler.SCal.Mid

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Phase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Circular means on normalized interval and variance inequality. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid
variable (m h:ℝ)
def cott (h:ℝ):=Real.cosh h/Real.sinh h
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Features
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Center profiles for direct evaluation in compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Tag Grid SE
inductive Ft
  | K|C|Q|J|V|M
deriving DecidableEq

instance instFintypeFt : Fintype Ft :=
  Fintype.ofList [Ft.K, Ft.C, Ft.Q, Ft.J, Ft.V, Ft.M]
    (by intro p; cases p <;> simp)

noncomputable section
def k0:ℝ:=1/100
def c0:ℝ:=-(42/100)
def q0:ℝ:=16/100
namespace Ft
def cK:Cap:= ⟨18/1000,66/1000,26/100⟩
def cC:Cap:=⟨81/1000,247/1000,95/100⟩
def cP:Cap:=⟨96/1000,193/1000,56/100⟩
def cJ:Cap:=⟨22/100,1012/1000,466/100⟩
def cap:Ft→Cap
  | K=>cK
  | C=>cC
  | Q=>cP
  | M=> Cap.times cP cP
  | _=> cJ
end Ft
end
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Traversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Uniform second derivative bound of endpoint spectral averages for smooth profiles. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure Real Metric
open scoped Topology Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid SE
-- integral parametrization
variable {f g:ℝ→ℝ→ℝ}
def ment (f:ℝ→ℝ→ℝ) (x:ℝ):=mean0 (f x)
def contB (f:ℝ→ℝ→ℝ):=Continuous f.uncurry

def s (t:ℝ):=(1+t)/2
def T0 (a x t:ℝ):= a+s t*(x-a)
def W0 (a x t:ℝ):= cosh (T0 a x t)
def Wd (a x t:ℝ):= sinh (T0 a x t)
def denom (a:ℝ):= ment (W0 a)
variable (a:ℝ)(f₀:ℝ→ℝ)
def Rg (x t:ℝ):= W0 a x t*f₀ (T0 a x t)
def trav := fun x=>ment (Rg a f₀) x/denom a x

variable {f₀}

def G1 (x t:ℝ):=
  s t*(W0 a x t * deriv f₀ (T0 a x t)+Wd a x t*f₀ (T0 a x t))
end GeneralMahler.SCal.Mid

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Poly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Middle-width certificate uses second derivative envelope on the
actual endpoint functional. Syntax shares proof of interval and profile estimates. -/
open Set Filter MeasureTheory MeasureTheory.Measure Real
namespace GeneralMahler.SCal.Mid
open Grid SE Ft
inductive Op
  | src (k:Fin 3) (f:Ft)
  -- rational constant q/r
  | num (q r:Int)
  | add (u v:Op)
  | sub (u v:Op)
  | mul (u v:Op)
deriving Inhabited
namespace Op
noncomputable def eval (k:Fin 3→Ft→ℝ):Op→ℝ
  | src n feat=> k n feat
  | num a b=> (a:ℝ)/b
  | add a b=>eval k a+eval k b
  | sub a b=>eval k a-eval k b
  | mul a b=>eval k a*eval k b

noncomputable def capE (k:Fin 3→Ft→Cap):Op→Cap
  | src n feat=> k n feat
  | num a b=> Cap.fl |(a:ℝ)/(b:ℝ)|
  | add a b=>Cap.plus (capE k a) (capE k b)
  | sub a b=>Cap.plus (capE k a) (capE k b)
  | mul a b=>Cap.times (capE k a) (capE k b)

-- endpoints stored 0,1; averages 2
def q (v:Op):Op:=mul v v
def ekp:=sub (src 2 Ft.K) (mul (num 1 2) (add (src 0 Ft.K) (src 1 Ft.K)))
def gammaOp:Op:=
  let c:=sub (src 1 Ft.C) (src 0 Ft.C)
  let k:=sub (src 1 Ft.K) (src 0 Ft.K)
  mul (mul (num 8 10) (q (num 1000 352))) (add
    (mul (num 125 100) (q (add k (mul (num 21 1000) c))))
    (mul (mul (num 5 1) (q (num 43 1000))) (q c)))
def ru2 := q (num 22 100)
def sm (p:Fin 3) := add ru2 (src p Ft.M)
def dotOp (p:Fin 3) := add (add (mul (src 2 Ft.Q) (src p Ft.Q)) (mul (src 2 Ft.J) (src p Ft.J)))
  (mul (src 2 Ft.V) (src p Ft.V))
def mb (p:Fin 3) := sub (add (sm 2) (sm p)) (mul (num 2 1) (dotOp p))
def bolt (p q:Fin 3):= sub (sub (src 2 Ft.C) (src q Ft.C)) (mb p)
def E:Op := sub (add (add (add ekp gammaOp)
  (mul (num 10 52) (add (q (bolt 0 1)) (q (bolt 1 0)))))
  (mul (num 32 1000) (add (mb 0) (mb 1))))
  (mul (num 1064 1000) (sub (sm 2) (dotOp 2)))
end Op
noncomputable section
def caps (i:Fin 3) (f:Ft) := if i=0 then Cap.fl f.cap.a else if i=1 then f.cap else Cap.av f.cap
def budgetCap:= Op.capE caps Op.E
end
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Trap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! A posteriori approximation of functional via actual f bounded derivatives. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Interval
namespace GeneralMahler.SCal.Mid
open Tag Grid SE
def stepG:ℝ:=1/200

def perE:ℝ:=1/40000
end GeneralMahler.SCal.Mid

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Prefix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Vertex checking via prefix integrals. -/
open Set Filter MeasureTheory Real
namespace GeneralMahler.SCal.Mid
open Grid Nodes Tag SE
def signF {α} [Neg α](b:Bool)(x:α):α:= if b then -x else x
def fo (p:Ft):Bool:=match p with|.V=>true|_=>false
def sFt {α} [Neg α](b:Bool)(p:Ft)(x:α):α:= signF (b && fo p) x
def sP {α} [Neg α](b:Bool)(p:Ft)(x:α):α:= signF (b && !fo p) x

end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Cells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Adaptive grid interpolation verification. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid SE
variable (b:Bool)

def gtwt (b:Bool)(i j:Nat):Bool:=
  if b then decide (i+j>0) else decide (i<j)
def vac (b:Bool)(i j d:Nat):Bool:=
  if b then decide (j+d < i) || decide (j+d+i+d<64)
  else decide (j+d < i+64)
noncomputable def limk (d:ℕ):ℝ:= -(37/4)*((d:ℝ)/200)^2
noncomputable def InRegion (b:Bool)(i j d:Nat)(x y:ℝ):Prop:=
  nd i ≤ x∧ x≤nd (i+d) ∧ nd j ≤ y ∧ y≤ nd (j+d) ∧ x≤y ∧
    32/100 ≤ y-signF b x
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Middle_Tiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Arithmetic verification of compact region. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid SE
def everyF (p:Ft→Bool):Bool:= [Ft.K,Ft.C,Ft.Q,Ft.M,Ft.J,Ft.V].all p
end GeneralMahler.SCal.Mid

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Orthant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Full-dimensional simplicial cones, coordinates and Laplace integrals. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Set Real WithLp Module
open scoped RealInnerProductSpace ENNReal Topology
namespace GeneralMahler
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {m : ℕ}

section Orthant

variable (b : Basis (Fin m) ℝ E)

/-- Simplifying two bases via coefficient equivalence. -/
def rebase (a : Basis (Fin m) ℝ E) : E ≃ₗ[ℝ] E :=
  b.equivFun.trans a.equivFun.symm

end Orthant

end GeneralMahler

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Chord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! §08 chord kernel W for signed comparison. -/
noncomputable section
open Set Filter Real MeasureTheory MeasureTheory.Measure
open scoped Topology NNReal ENNReal Interval
namespace GeneralMahler.SCal.SE
open Tag
variable (m h:ℝ)
def shv:= sinh h /h
end GeneralMahler.SCal.SE

end

end OAI
end

section
-- module Solutions.OAIQ026_GM.Convex_GeneralMahler_Segment_Omega
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
/-! Chord kernel bounds sharp enough for all midpoints. -/
noncomputable section
open Set Filter Real MeasureTheory
open scoped Topology Interval
namespace GeneralMahler.SCal.SE
open Tag Grid
variable (m:ℝ){h:ℝ}

def pm (m h t:ℝ):=(sinh t-sinh (m-h))/(2*cosh m*sinh h)
end GeneralMahler.SCal.SE

end

end OAI
end


