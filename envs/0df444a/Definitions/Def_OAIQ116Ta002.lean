-- Prove2me | Definitions.Def_OAIQ116Ta002
-- name    : OAIQ116Ta002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T01:31:40.699083+00:00
-- url     : https://prove2.me/theorems/360df15b-95e8-41d8-8905-22b45ce83e4b
-- title:
--   Definitions bundle OAIQ116Ta002 of the split of OpenAI, A counterexample to Tachikawa's second conjecture
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Tachikawa.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *A counterexample to Tachikawa's second conjecture*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 264 declarations of OpenAI's Lean: 70 definitions, 2 inductive types or structures, 64 instances and 128 theorems. The definitions and types are `OAI.Tachikawa.Cutoff.differential`, `OAI.Tachikawa.Cutoff.term`, `OAI.Tachikawa.DownCone.iL`, `OAI.Tachikawa.DownCone.pL`, `OAI.Tachikawa.DownHom.Closed`, `OAI.Tachikawa.DownHom.Cochain`, `OAI.Tachikawa.DownHom.Index`, `OAI.Tachikawa.DownHom.mapComplex`, `OAI.Tachikawa.Enveloping.Coind`, `OAI.Tachikawa.Enveloping.LeftRestrictedRegular`, `OAI.Tachikawa.Enveloping.leftRegularObj`, `OAI.Tachikawa.Enveloping.leftRegularUnderlying`, `OAI.Tachikawa.Enveloping.rightRegularEndUnderlying`, `OAI.Tachikawa.Enveloping.rightRegularObj`, `OAI.Tachikawa.Enveloping.rightRegularOne`, `OAI.Tachikawa.Enveloping.rightRegularUnderlying`, `OAI.Tachikawa.HomColumnBoundaries`, `OAI.Tachikawa.HomRowBoundaries`, `OAI.Tachikawa.InAdd`, `OAI.Tachikawa.IndReplacement`, `OAI.Tachikawa.LeftCoinduced.C`, `OAI.Tachikawa.LeftCoinduced.J`, `OAI.Tachikawa.LeftCoinduced.iterate`, `OAI.Tachikawa.LeftCoinduced.restrictRegularEquiv`, `OAI.Tachikawa.LeftCoinduced.short`, `OAI.Tachikawa.LeftCoinduced.underlying`, `OAI.Tachikawa.LeftCoinduced.unit`, `OAI.Tachikawa.LeftCoinduced.π`, `OAI.Tachikawa.LeftDual`, `OAI.Tachikawa.LeftDual.map`, `OAI.Tachikawa.OuterTensor.precompose`, `OAI.Tachikawa.OuterTensor.restrictHom`, `OAI.Tachikawa.RightDual`, `OAI.Tachikawa.RightDual.map`, `OAI.Tachikawa.SourceField.Base`, `OAI.Tachikawa.SourceField.H₁`, `OAI.Tachikawa.SourceField.H₂`, `OAI.Tachikawa.SourceField.K`, `OAI.Tachikawa.SourceField.parameter`, `OAI.Tachikawa.SourceField.q` and 32 more.
--
--   **Sources.** They come from these modules of lean/OAI/RingTheory, in whole or in part: `Tachikawa_Coinduction`, `Tachikawa_Cone`, `Tachikawa_Coresolution`, `Tachikawa_Corner`, `Tachikawa_Delta`, `Tachikawa_DerivedDescent`, `Tachikawa_DerivedInduction`, `Tachikawa_DownHom`, `Tachikawa_FiniteCoinduction`, `Tachikawa_HomProfile`, `Tachikawa_Induction`, `Tachikawa_Nakayama`, `Tachikawa_OuterExt`, `Tachikawa_OuterTensor`, `Tachikawa_Perfect`, `Tachikawa_RightInduction`, `Tachikawa_StableLift`, `Tachikawa_StableShift`, `Tachikawa_Triangular`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ116Ta004` and `OAIQ116Ta005`.
-- source:
--   OpenAI, A counterexample to Tachikawa's second conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-counterexample-to-Tachikawas-second-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RingTheory at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ116_Tach.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
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
in d13f23b (Kadison similarity, oaiq-075). -/
noncomputable instance starSubalgebraCommCStarAlgebra {B : Type*} [CStarAlgebra B] (A : StarSubalgebra ℂ B)
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
-- module Solutions.OAIQ116_Tach.Tachikawa_StableShift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k R M N P Q : Type} [Field k] [Ring R] [Algebra k R]
 [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
 [Module R M] [Module R N] [Module R P] [Module R Q]
 [Module k N] [Module k Q]
 [IsScalarTower k R N] [IsScalarTower k R Q]

lemma linear_descent (ε : P →ₗ[R] M) (hε : Function.Surjective ε) (f : P →ₗ[R] Q)
    (h : LinearMap.ker ε ≤ LinearMap.ker f) : ∃ g : M →ₗ[R] Q, g.comp ε = f := by
  refine ⟨((LinearMap.ker ε).liftQ f h).comp (ε.quotKerEquivOfSurjective hε).symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x
  change (LinearMap.ker ε).liftQ f h ((ε.quotKerEquivOfSurjective hε).symm (ε x)) = f x
  have hx : ε x = (ε.quotKerEquivOfSurjective hε) ((LinearMap.ker ε).mkQ x) := rfl
  rw [hx,LinearEquiv.symm_apply_apply]
  rfl

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coresolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesInjectiveObjects] [F.PreservesHomology]
  {Y : C} (P : InjectiveResolution Y)

def mappedCoresolution : InjectiveResolution (F.obj Y) where
  cocomplex := (F.mapHomologicalComplex _).obj P.cocomplex
  injective n := Functor.PreservesInjectiveObjects.injective_obj (P.injective n)
  ι := (HomologicalComplex.singleMapHomologicalComplex _ _ _).inv.app _ ≫
    (F.mapHomologicalComplex _).map P.ι
  quasiIso := inferInstance

open CochainComplex CochainComplex.HomComplex
end Tachikawa



namespace Tachikawa.VectorSplit
open CategoryTheory HomologicalComplex
variable {k : Type*} [Field k] {I₁ I₂ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂}
  (K₁ : HomologicalComplex (ModuleCat k) c₁) (K₂ : HomologicalComplex (ModuleCat k) c₂)
  (c : ComplexShape J) [DecidableEq J] [TotalComplexShape c₁ c₂ c]

abbrev tensorFunctor := CategoryTheory.MonoidalCategory.curriedTensor (ModuleCat k)
variable [HasMapBifunctor K₁ K₂ (tensorFunctor (k := k)) c]

def zeroDifferentialHomologyIso {C : Type*} [Category* C] [Preadditive C]
    {I : Type*} {d : ComplexShape I} (L : HomologicalComplex C d)
    (hd : ∀ i j, L.d i j = 0) (i : I) [L.HasHomology i] :
    L.homology i ≅ L.X i :=
  (ShortComplex.HomologyData.ofZeros (L.sc i) (hd _ _) (hd _ _)).left.homologyIso

end Tachikawa.VectorSplit



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CochainComplex.HomComplex
open scoped ModuleCat.Algebra
variable (k R : Type) [Field k] [Ring R] [Algebra k R]
  (P : CochainComplex (ModuleCat R) ℕ) (N : ModuleCat R)

variable {k R} {M : ModuleCat R} (Q : InjectiveResolution M)
lemma injective_extMk_smul {n : ℕ} (f : N ⟶ Q.cocomplex.X n)
    (hf : f ≫ Q.cocomplex.d n (n+1) = 0) (r : k)
    (hrf : (r • f) ≫ Q.cocomplex.d n (n+1) = 0) :
    Q.extMk (r • f) (n+1) rfl hrf = r • Q.extMk f (n+1) rfl hf := by
  have h := Q.mk₀_comp_extMk f (n+1) rfl hf (r • 𝟙 N)
  simpa only [CategoryTheory.Linear.smul_comp, Category.id_comp, Ext.mk₀_smul,
    Ext.smul_comp, Ext.mk₀_id_comp] using h.symm

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section
set_option backward.isDefEq.respectTransparency true



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  {M U : ModuleCat A} {N V : ModuleCat B}

def restrictHom : (M ⟶ U) →ₗ[k] (M →ₗ[k] U) where
  toFun f := f.hom.restrictScalars k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma restrictHom_injective : Function.Injective (restrictHom (k := k) (M := M) (U := U)) := by
  intro f g h
  exact ModuleCat.hom_ext (LinearMap.restrictScalars_injective k h)

end Tachikawa.OuterTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def precompose {M M' U : ModuleCat A} (p : M' ⟶ M) : (M ⟶ U) →ₗ[k] (M' ⟶ U) where
  toFun f := p ≫ f
  map_add' _ _ := by simp only [Preadditive.comp_add]
  map_smul' _ _ := by simp only [CategoryTheory.Linear.comp_smul, RingHom.id_apply]

end Tachikawa.OuterTensor

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_OuterExt
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {I : Type} (F : I → ModuleCat R) (N : ModuleCat R)

def coproductHomEquiv : (∐ F ⟶ N) ≃ₗ[k] (∀ i, F i ⟶ N) where
  toFun f i := Sigma.ι F i ≫ f
  invFun f := Sigma.desc f
  left_inv f := Sigma.hom_ext _ _ (fun i => by simp)
  right_inv f := funext fun i => by simp
  map_add' f g := funext fun i => by simp only [Pi.add_apply, Preadditive.comp_add]
  map_smul' r f := funext fun i => by simp only [Pi.smul_apply, RingHom.id_apply, CategoryTheory.Linear.comp_smul]

variable {J : Type} [Finite J] (G : J → ModuleCat k)

def coproductPiEquiv : (∐ G : ModuleCat k) ≃ₗ[k] (∀ i, G i) :=
  ((biproduct.isoCoproduct G).symm ≪≫ ModuleCat.biproductIsoPi G).toLinearEquiv

lemma coproductPiEquiv_ι (i j : J) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j =
      (biproduct.ι G i ≫ biproduct.π G j) x := by
  have h : Sigma.ι G i ≫ (biproduct.isoCoproduct G).inv = biproduct.ι G i := by simp
  have h' : (ModuleCat.biproductIsoPi G).hom ≫
      ModuleCat.ofHom (LinearMap.proj j) = biproduct.π G j := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  change ((Sigma.ι G i ≫ (biproduct.isoCoproduct G).inv ≫
    (ModuleCat.biproductIsoPi G).hom ≫ ModuleCat.ofHom (LinearMap.proj j)) x) = _
  rw [h', ← Category.assoc, h]

lemma coproductPiEquiv_ι_self (i : J) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) i = x := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_self]
  rfl

lemma coproductPiEquiv_ι_ne {i j : J} (h : i ≠ j) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j = 0 := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_ne _ h]
  rfl

end Tachikawa



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

instance instTensorSignsNatUp_solutions : ComplexShape.TensorSigns (ComplexShape.up ℕ) where
  ε' := MonoidHom.mk' (fun (i : Multiplicative ℕ) => (-1 : ℤˣ)^i.toAdd)
    (fun i j => pow_add (-1 : ℤˣ) i.toAdd j.toAdd)
  rel_add p q r (h : p+1=q) := by change p+r+1=q+r; omega
  add_rel p q r (h : p+1=q) := by change r+p+1=r+q; omega
  ε'_succ := by
    intro p q h
    change p+1=q at h
    change (-1 : ℤˣ)^q = -(-1 : ℤˣ)^p
    subst q
    rw [pow_succ, mul_neg, mul_one]

abbrev Diag (n : ℕ) := {ij : ℕ × ℕ // ij.1 + ij.2 = n}
variable (K : HomologicalComplex₂ (ModuleCat R) (.down ℕ) (.down ℕ))
  (G : HomologicalComplex₂ (ModuleCat k) (.up ℕ) (.up ℕ)) (N : ModuleCat R)
  (p : ∀ i j, (G.X i).X j ≃ₗ[k] ((K.X i).X j ⟶ N))

abbrev chainFamily (n : ℕ) (t : Diag n) : ModuleCat R := (K.X t.val.1).X t.val.2
abbrev cochainFamily (n : ℕ) (t : Diag n) : ModuleCat k := (G.X t.val.1).X t.val.2

instance instFiniteDiag (n : ℕ) : Finite (Diag n) := by
  let f : Diag n → Fin (n+1) × Fin (n+1) := fun t =>
    (⟨t.val.1, by have := t.property; omega⟩, ⟨t.val.2, by have := t.property; omega⟩)
  apply Finite.of_injective f
  intro t u h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : Fin (n+1) × Fin (n+1) => z.1.val) h)
    (congrArg (fun z : Fin (n+1) × Fin (n+1) => z.2.val) h)

end Tachikawa.TotalDualPairing



namespace Tachikawa.TotalDualPairing
open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [hk : CharP k 2]

lemma units_smul_eq {M : Type*} [AddCommGroup M] [Module k M] (u : ℤˣ) (x : M) : u • x = x := by
  rcases Int.units_eq_one_or u with h | h
  · rw [h, one_smul]
  · rw [h]
    change (-1 : ℤ) • x = x
    rw [neg_one_zsmul, ← neg_one_smul k, CharTwo.neg_eq (1 : k), one_smul]

end Tachikawa.TotalDualPairing



namespace Tachikawa.OuterTensor
open CategoryTheory HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k A B : Type} [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
  (P : ChainComplex (ModuleCat A) ℕ) (Q : ChainComplex (ModuleCat B) ℕ)
  (U : ModuleCat A) (V : ModuleCat B)

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Finite B (Q.X n)]
  [∀ n, Module.Projective A (P.X n)] [∀ n, Module.Projective B (Q.X n)]
  [∀ n, FiniteDimensional k (P.X n)] [∀ n, FiniteDimensional k (Q.X n)]

lemma precompose_id {M U : ModuleCat A} :
    precompose (k := k) (U := U) (𝟙 M) = LinearMap.id := by
  apply LinearMap.ext
  intro f
  exact Category.id_comp f

end Tachikawa.OuterTensor



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Nakayama
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

namespace VectorSplit

instance tensorFunctor_linear : (tensorFunctor (k := k)).Linear k where
  map_smul := by
    intro X Y f r
    apply NatTrans.ext
    funext Z
    exact MonoidalLinear.smul_whiskerRight r f Z

end VectorSplit
end Tachikawa



namespace Tachikawa
open CategoryTheory

lemma boundaries_of_ext_subsingleton {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (P : ProjectiveResolution X) (n : ℕ)
    [Subsingleton (Abelian.Ext X Y (n+1))]
    (f : P.complex.X (n+1) ⟶ Y) (hf : P.complex.d (n+2) (n+1) ≫ f = 0) :
    ∃ g : P.complex.X n ⟶ Y, P.complex.d (n+1) n ≫ g = f := by
  exact (P.extMk_eq_zero_iff f (n+2) rfl hf n rfl).mp (Subsingleton.elim _ _)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Corner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section



namespace Tachikawa

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  [FiniteDimensional k R]

omit [FiniteDimensional k R] in
lemma end_expansion {ι : Type*} [Fintype ι] (e : Module.Basis ι k R)
    (F : R →ₗ[k] R) :
    F = ∑ i, (e.coord i).smulRight (F (e i)) := by
  classical
  ext x
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply]
  have h := congrArg F (e.sum_repr x)
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using h.symm

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_RightInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive] {M : C} [Projective M]

lemma map_resolution_quasiIso (P : ProjectiveResolution M) :
    QuasiIso ((F.mapHomologicalComplex _).map P.π) := by
  let e := ProjectiveResolution.homotopyEquiv P (ProjectiveResolution.self M)
  have h : e.hom = P.π := by
    simpa only [e, ProjectiveResolution.self, Category.comp_id] using
      ProjectiveResolution.homotopyEquiv_hom_π P (ProjectiveResolution.self M)
  rw [← h]
  exact (F.mapHomotopyEquiv e).quasiIso_hom

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] {ι : Type*} {c : ComplexShape ι}

lemma quasiIso_map_natIso (e : F ≅ G) {K L : HomologicalComplex C c} (f : K ⟶ L) :
    QuasiIso ((F.mapHomologicalComplex c).map f) ↔ QuasiIso ((G.mapHomologicalComplex c).map f) := by
  let i := NatIso.mapHomologicalComplex e c
  have h := i.hom.naturality f
  rw [← quasiIso_iff_comp_right ((F.mapHomologicalComplex c).map f) (i.hom.app L), h,
    quasiIso_iff_comp_left (i.hom.app K)]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Coinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.LeftCoinduced
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def J : ModuleCat R ⥤ ModuleCat R :=
  ModuleCat.restrictScalars (algebraMap k R) ⋙ ModuleCat.coextendScalars (algebraMap k R)

def unit : 𝟭 (ModuleCat R) ⟶ J (k := k) :=
  ModuleCat.RestrictionCoextensionAdj.unit' (algebraMap k R)

instance coextend_additive : (ModuleCat.coextendScalars (algebraMap k R)).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro x
    rfl

instance instAdditiveModuleCatJ : (J (k := k) (R := R)).Additive := inferInstanceAs
  (ModuleCat.restrictScalars (algebraMap k R) ⋙ ModuleCat.coextendScalars (algebraMap k R)).Additive

lemma unit_injective (M : ModuleCat R) : Function.Injective ((unit (k := k)).app M) := by
  intro x y h
  have h' := congrArg (fun f => ModuleCat.CoextendScalars.equiv (algebraMap k R) _ f (1:R)) h
  change (1:R) • x = (1:R) • y at h'
  simpa only [one_smul] using h'
instance instMonoModuleCatAppUnit (M : ModuleCat R) : Mono ((unit (k := k)).app M) :=
  (ModuleCat.mono_iff_injective _).2 (unit_injective M)
instance instMonoFunctorModuleCatUnit : Mono (unit (k := k) (R := R)) := NatTrans.mono_of_mono_app _

instance coextend_preservesInjective :
    (ModuleCat.coextendScalars (algebraMap k R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (ModuleCat.restrictCoextendScalarsAdj (algebraMap k R))

instance instInjectiveModuleCatObjJ (M : ModuleCat R) : Injective ((J (k := k)).obj M) := by
  let X := (ModuleCat.restrictScalars (algebraMap k R)).obj M
  let : Module.Injective k X := Module.injective_of_isSemisimpleRing k X
  let : Injective X := Module.injective_object_of_injective_module k X
  exact (ModuleCat.coextendScalars (algebraMap k R)).injective_obj X

def C : ModuleCat R ⥤ ModuleCat R := cokernel (unit (k := k) (R := R))

instance instAdditiveModuleCatC : (C (k := k) (R := R)).Additive := by
  constructor
  intro X Y f g
  dsimp only [C]
  let π := cokernel.π (unit (k := k) (R := R))
  let : Epi (π.app X) := inferInstance
  apply (cancel_epi (π.app X)).1
  erw [← π.naturality, Functor.map_add, Preadditive.add_comp,
    Preadditive.comp_add, ← π.naturality, ← π.naturality]

def π (M : ModuleCat R) : (J (k := k)).obj M ⟶ (C (k := k)).obj M :=
  (cokernel.π (unit (k := k))).app M
instance instEpiModuleCatπ (M : ModuleCat R) : Epi (π (k := k) M) :=
  inferInstanceAs (Epi ((cokernel.π (unit (k := k))).app M))

lemma unit_π (M : ModuleCat R) : (unit (k := k)).app M ≫ π M = 0 :=
  congrArg (fun f => f.app M) (cokernel.condition (unit (k := k)))

def short (M : ModuleCat R) : ShortComplex (ModuleCat R) := ShortComplex.mk _ _ (unit_π (k := k) M)

lemma short_exact (M : ModuleCat R) : (short (k := k) M).ShortExact := by
  let T : ShortComplex (ModuleCat R ⥤ ModuleCat R) := ShortComplex.mk (unit (k := k)) (cokernel.π _) (cokernel.condition _)
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  exact hT.map ((evaluation _ _).obj M)

def iterate : ℕ → ModuleCat R ⥤ ModuleCat R
  | 0 => 𝟭 _
  | n+1 => iterate n ⋙ C (k := k)

lemma c_dimension (M : ModuleCat R) (d : ℕ) [HasInjectiveDimensionLE M (d+1)] :
    HasInjectiveDimensionLE ((C (k := k)).obj M) d := by
  apply (short_exact (k := k) M).hasInjectiveDimensionLT_X₃ (d+1)
  · exact hasInjectiveDimensionLT_of_ge ((J (k := k)).obj M) 1 (d+1) (by omega)
  · exact inferInstanceAs (HasInjectiveDimensionLE M (d+1))

lemma iterate_dimension (M : ModuleCat R) (d n : ℕ) [HasInjectiveDimensionLE M (d+n)] :
    HasInjectiveDimensionLE ((iterate (k := k) n).obj M) d := by
  induction n generalizing d with
  | zero => exact inferInstanceAs (HasInjectiveDimensionLE M d)
  | succ n ih =>
    have h : HasInjectiveDimensionLE M ((d+1)+n) := by simpa only [Nat.add_assoc,Nat.add_comm 1 n] using (inferInstance : HasInjectiveDimensionLE M (d+(n+1)))
    let := ih (d+1)
    exact c_dimension ((iterate (k := k) n).obj M) d

end Tachikawa.LeftCoinduced



namespace Tachikawa
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (M : Type) [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]

def moduleCatObj : ModuleCat R := ModuleCat.of R M

def moduleCatUnderlyingEquiv : moduleCatObj (R := R) M ≃ₗ[k] M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change (algebraMap k R c) • (show M from x) = c • (show M from x)
    exact IsScalarTower.algebraMap_smul R c (show M from x)

lemma moduleCatFinite [FiniteDimensional k M] : FiniteDimensional k (moduleCatObj (R := R) M) :=
  Module.Finite.equiv (moduleCatUnderlyingEquiv (k := k) (R := R) M).symm

end Tachikawa



namespace Tachikawa.LeftCoinduced
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def restrictRegularEquiv :
    (ModuleCat.restrictScalars (algebraMap k R)).obj (ModuleCat.of R R) ≃ₗ[k] R where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    change algebraMap k R c * (show R from x) = c • (show R from x)
    rw [Algebra.smul_def]

def underlying (M : ModuleCat R) : (J (k := k)).obj M ≃ₗ[k] (R →ₗ[k] M) where
  toFun φ := (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ).comp
    (restrictRegularEquiv (k := k) (R := R)).symm.toLinearMap
  invFun φ := (ModuleCat.CoextendScalars.equiv (algebraMap k R) _).symm
    (φ.comp (restrictRegularEquiv (k := k) (R := R)).toLinearMap)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c φ := by
    apply LinearMap.ext
    intro x
    change (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ)
      (x * algebraMap k R c) = c • (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ) x
    have h : x * algebraMap k R c = algebraMap k R c * x := Algebra.commutes c x |>.symm
    rw [h]
    exact (ModuleCat.CoextendScalars.equiv (algebraMap k R) _ φ).map_smul c x

instance J_finite [FiniteDimensional k R] (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((J (k := k)).obj M) := Module.Finite.equiv (underlying M).symm

instance C_finite [FiniteDimensional k R] (M : ModuleCat R) [FiniteDimensional k M] :
    FiniteDimensional k ((C (k := k)).obj M) := by
  have h := (ModuleCat.epi_iff_surjective (π (k := k) M)).1 inferInstance
  exact Module.Finite.of_surjective ((π (k := k) M).hom.restrictScalars k) h

instance iterate_finite [FiniteDimensional k R] (M : ModuleCat R) [FiniteDimensional k M] (n : ℕ) :
    FiniteDimensional k ((iterate (k := k) n).obj M) := by
  induction n with
  | zero => exact inferInstanceAs (FiniteDimensional k M)
  | succ n ih => exact inferInstanceAs (FiniteDimensional k ((C (k := k)).obj ((iterate (k := k) n).obj M)))

end Tachikawa.LeftCoinduced



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def Coind (N : ModuleCat Sᵐᵒᵖ) := R →ₗ[k] N

namespace Coind
variable (N : ModuleCat Sᵐᵒᵖ)
instance instFunLikeCarrierMulOpposite : FunLike (Coind (k := k) (R := R) N) R N := inferInstanceAs (FunLike (R →ₗ[k] N) R N)
instance instLinearMapClassCarrierMulOpposite : LinearMapClass (Coind (k := k) (R := R) N) k R N := inferInstanceAs (LinearMapClass (R →ₗ[k] N) k R N)
instance instAddCommGroup : AddCommGroup (Coind (k := k) (R := R) N) := inferInstanceAs (AddCommGroup (R →ₗ[k] N))
instance instModule : Module k (Coind (k := k) (R := R) N) := inferInstanceAs (Module k (R →ₗ[k] N))
instance instModuleMulOpposite : Module Sᵐᵒᵖ (Coind (k := k) (R := R) N) := inferInstanceAs (Module Sᵐᵒᵖ (R →ₗ[k] N))
instance instIsScalarTowerMulOpposite : IsScalarTower k Sᵐᵒᵖ (Coind (k := k) (R := R) N) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ (R →ₗ[k] N))
instance instModule_1 : Module R (Coind (k := k) (R := R) N) where
  smul a f := (show R →ₗ[k] N from f).comp (LinearMap.mulRight k a)
  one_smul f := by apply LinearMap.ext; intro x; change f (x*1) = f x; rw [mul_one]
  mul_smul a b f := by
    apply LinearMap.ext; intro x; change f (x*(a*b)) = f ((x*a)*b); rw [mul_assoc]
  smul_zero a := by apply LinearMap.ext; intro x; rfl
  smul_add a f g := by apply LinearMap.ext; intro x; rfl
  add_smul a b f := by
    apply LinearMap.ext; intro x; change f (x*(a+b)) = f (x*a)+f (x*b)
    rw [mul_add,map_add]
  zero_smul f := by apply LinearMap.ext; intro x; change f (x*0) = 0; rw [mul_zero,map_zero]
instance instIsScalarTower : IsScalarTower k R (Coind (k := k) (R := R) N) where
  smul_assoc c a f := by
    apply LinearMap.ext; intro x
    change f (x*(c • a)) = c • f (x*a)
    rw [Algebra.mul_smul_comm,map_smul]
instance instSMulCommClassMulOpposite : SMulCommClass R Sᵐᵒᵖ (Coind (k := k) (R := R) N) where
  smul_comm _ _ _ := rfl

instance instFiniteDimensionalOfCarrierMulOpposite [FiniteDimensional k R] [FiniteDimensional k N] :
    FiniteDimensional k (Coind (k := k) (R := R) N) := inferInstanceAs (FiniteDimensional k (R →ₗ[k] N))

end Coind

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def rightRegularObj : ModuleCat Sᵐᵒᵖ := ModuleCat.of Sᵐᵒᵖ Sᵐᵒᵖ

def rightRegularOne : rightRegularObj (S := S) := (1 : Sᵐᵒᵖ)

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R]

instance rightRegularProjective : Module.Projective Sᵐᵒᵖ (rightRegularObj (S := S)) :=
  inferInstanceAs (Module.Projective Sᵐᵒᵖ Sᵐᵒᵖ)
instance rightRegularFinite : Module.Finite Sᵐᵒᵖ (rightRegularObj (S := S)) :=
  inferInstanceAs (Module.Finite Sᵐᵒᵖ Sᵐᵒᵖ)

end Tachikawa.Enveloping



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Induction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [FiniteDimensional k R]

def rightRegularEndUnderlying : rightRegularObj (S := R) ≃ₗ[k] R :=
  (moduleCatUnderlyingEquiv (k := k) (R := Rᵐᵒᵖ) Rᵐᵒᵖ).trans (MulOpposite.opLinearEquiv k).symm

end Tachikawa.Enveloping



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def LeftRestrictedRegular (_φ : R →ₐ[k] S) := S
instance instAddCommGroupLeftRestrictedRegular (φ : R →ₐ[k] S) : AddCommGroup (LeftRestrictedRegular φ) := inferInstanceAs (AddCommGroup S)
instance instModuleLeftRestrictedRegular (φ : R →ₐ[k] S) : Module k (LeftRestrictedRegular φ) := inferInstanceAs (Module k S)
instance instModuleLeftRestrictedRegular_1 (φ : R →ₐ[k] S) : Module R (LeftRestrictedRegular φ) := Module.compHom S φ.toRingHom
instance instModuleMulOppositeLeftRestrictedRegular (φ : R →ₐ[k] S) : Module Sᵐᵒᵖ (LeftRestrictedRegular φ) := inferInstanceAs (Module Sᵐᵒᵖ S)
instance instIsScalarTowerLeftRestrictedRegular (φ : R →ₐ[k] S) : IsScalarTower k R (LeftRestrictedRegular φ) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change φ (algebraMap k R c) * (show S from x) = c • (show S from x)
    rw [φ.commutes, Algebra.smul_def]
instance instIsScalarTowerMulOppositeLeftRestrictedRegular (φ : R →ₐ[k] S) : IsScalarTower k Sᵐᵒᵖ (LeftRestrictedRegular φ) :=
  inferInstanceAs (IsScalarTower k Sᵐᵒᵖ S)
instance instSMulCommClassMulOppositeLeftRestrictedRegular (φ : R →ₐ[k] S) : SMulCommClass R Sᵐᵒᵖ (LeftRestrictedRegular φ) where
  smul_comm r s x := (mul_assoc (φ r) (show S from x) s.unop).symm

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category* C] [Abelian C]

def transportResolution {M N : C} (P : ProjectiveResolution M) (e : M ≅ N) :
    ProjectiveResolution N where
  complex := P.complex
  projective n := P.projective n
  π := P.π ≫ (ChainComplex.single₀ C).map e.hom
  quasiIso := inferInstance

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
set_option backward.isDefEq.respectTransparency false


noncomputable section



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R] {M : ModuleCat.{0} R}

lemma finite_resolution_cochain (P : ProjectiveResolution M)
    (hfin : ∀ n, Module.Finite R (P.complex.X n)) (i : ℤ) :
    Module.Finite R (P.cochainComplex.X i) := by
  by_cases hi : i ≤ 0
  · obtain ⟨n,rfl⟩ := Int.exists_eq_neg_ofNat hi
    let := hfin n
    exact Module.Finite.equiv (P.cochainComplexXIso (-(n:ℤ)) n).toLinearEquiv.symm
  · let := ModuleCat.isZero_iff_subsingleton.mp
      (P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega))
    infer_instance

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex

def negUpDown : (ComplexShape.up ℤ).Embedding (.down ℤ) where
  f i := -i
  injective_f := neg_injective
  rel h := by change _+1=_ at h; change _+1=_; omega

instance instIsRelIffIntNegUpDown : negUpDown.IsRelIff where
  rel' := by intro i j h; change (-j)+1=(-i) at h; change i+1=j; omega

def negDownUp : (ComplexShape.down ℤ).Embedding (.up ℤ) where
  f i := -i
  injective_f := neg_injective
  rel h := by change _+1=_ at h; change _+1=_; omega

instance instIsRelIffIntNegDownUp : negDownUp.IsRelIff where
  rel' := by intro i j h; change (-i)+1=(-j) at h; change j+1=i; omega

variable {C : Type*} [Category C] [Preadditive C]

abbrev reflectChain (K : ChainComplex C ℤ) : CochainComplex C ℤ := K.restriction negUpDown
abbrev reflectCochain (K : CochainComplex C ℤ) : ChainComplex C ℤ := K.restriction negDownUp
abbrev reflectChainMap {K L : ChainComplex C ℤ} (f : K ⟶ L) : reflectChain K ⟶ reflectChain L :=
  restrictionMap f negUpDown
abbrev reflectCochainMap {K L : CochainComplex C ℤ} (f : K ⟶ L) : reflectCochain K ⟶ reflectCochain L :=
  restrictionMap f negDownUp

def reflectChainHomotopy {K L : ChainComplex C ℤ} {f g : K ⟶ L} (h : Homotopy f g) :
    Homotopy (reflectChainMap f) (reflectChainMap g) where
  hom i j := h.hom (-i) (-j)
  zero i j hij := h.zero _ _ (by change ¬ (-i)+1=(-j); change ¬ j+1=i at hij; omega)
  comm i := by
    have hh := h.comm (-i)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (-i) (-i-1) by change (-i-1)+1=(-i); omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (-i+1) (-i) by rfl)] at hh
    erw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i by change (i-1)+1=i; omega)]
    change f.f (-i) = K.d (-i) (-(i+1)) ≫ h.hom (-(i+1)) (-i) +
      h.hom (-i) (-(i-1)) ≫ L.d (-(i-1)) (-i) + g.f (-i)
    have hi : -(i+1) = -i-1 := by omega
    have hj : -(i-1) = -i+1 := by omega
    rw [hi,hj]
    exact hh

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits

lemma chainNat_exactAt_iff {R : Type} [Ring R] (P : ChainComplex (ModuleCat.{0} R) ℕ)
    (n : ℕ) (hn : 0 < n) : P.ExactAt n ↔ Function.Exact (P.d (n+1) n) (P.d n (n-1)) := by
  rw [P.exactAt_iff' (n+1) n (n-1) ((ComplexShape.down ℕ).prev_eq' (by rfl))
    ((ComplexShape.down ℕ).next_eq' (by change n-1+1=n; omega))]
  exact ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Perfect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R S : Type} [Ring R] [Ring S]

def cokerLinearEquiv {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] [Module R A] [Module R B] [Module R C] [Module R D]
    (f : A →ₗ[R] B) (g : C →ₗ[R] D) (e : A ≃ₗ[R] C) (v : B ≃ₗ[R] D)
    (h : v.toLinearMap.comp f = g.comp e.toLinearMap) :
    (B ⧸ LinearMap.range f) ≃ₗ[R] (D ⧸ LinearMap.range g) :=
  Submodule.Quotient.equiv _ _ v (by
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      exact ⟨e z,(LinearMap.congr_fun h z).symm⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨z,rfl⟩ := e.surjective y
      exact ⟨f z,⟨z,rfl⟩,LinearMap.congr_fun h z⟩)

end Tachikawa



namespace Tachikawa.Construction
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
variable {k : Type} [Field k] [CharP k 2] (q : k)
variable (hp : ∀ n : ℕ, 0 < n → 1+q^n ≠ 0)

lemma natIntSign (i : ℕ) : (i:ℤ).negOnePow = (-1:ℤˣ)^i := by
  apply Units.ext
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using Int.coe_negOnePow_natCast i

end Tachikawa.Construction



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
variable {R : Type} [Ring R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} (f : P ⟶ Q)

lemma exact_tail_at (n : ℤ)
    (hq : ∀ j, n ≤ j → Function.Exact (Q.d (j+1) j) (Q.d j (j-1)))
    (i j l : ℤ) (hij : i+1=j) (hjl : j+1=l) (hj : n ≤ j) :
    Function.Exact (Q.d l j) (Q.d j i) := by
  have hi : i=j-1 := by omega
  have hl : l=j+1 := by omega
  subst i
  subst l
  exact hq j hj

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {R : Type} [Ring R]

namespace Cutoff
variable (Q : ChainComplex (ModuleCat.{0} R) ℤ) (n : ℤ)

def term (j : ℤ) : Submodule R (Q.X j) := if j ≤ n then ⊤ else ⊥

lemma d_mem (i j : ℤ) (x : term Q n i) : Q.d i j x.val ∈ term Q n j := by
  classical
  by_cases hj : j ≤ n
  · simp only [term, ite_eq_left hj, Submodule.mem_top]
  · by_cases hi : i ≤ n
    · have hrel : ¬ (ComplexShape.down ℤ).Rel i j := by
        change ¬ j+1=i
        omega
      rw [Q.shape i j hrel]
      exact (term Q n j).zero_mem
    · have hx : x.val = 0 := by simpa only [term, ite_eq_right hi, Submodule.mem_bot] using x.property
      rw [hx, map_zero]
      exact (term Q n j).zero_mem

def differential (i j : ℤ) : term Q n i →ₗ[R] term Q n j :=
  ((Q.d i j).hom.comp (term Q n i).subtype).codRestrict _ (d_mem Q n i j)

end Cutoff
end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v w
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

lemma ext_subsingleton_retract_left {X X' Y : C} (r : Retract X X') (n : ℕ)
    [Subsingleton (Ext X' Y n)] : Subsingleton (Ext X Y n) := by
  have hz (x : Ext X Y n) : x = 0 := by
    have h : (Ext.mk₀ r.r).comp x (zero_add n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun z => (Ext.mk₀ r.i).comp z (zero_add n)) h
    simpa only [Ext.mk₀_comp_mk₀_assoc, r.retract, Ext.mk₀_id_comp, Ext.comp_zero] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

lemma ext_subsingleton_retract_right {X Y Y' : C} (r : Retract Y Y') (n : ℕ)
    [Subsingleton (Ext X Y' n)] : Subsingleton (Ext X Y n) := by
  have hz (x : Ext X Y n) : x = 0 := by
    have h : x.comp (Ext.mk₀ r.i) (add_zero n) = 0 := Subsingleton.elim _ _
    have h' := congrArg (fun z => z.comp (Ext.mk₀ r.r) (add_zero n)) h
    simpa only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      r.retract, Ext.comp_mk₀_id, Ext.zero_comp] using h'
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

def InAdd (W V : C) : Prop := ∃ n : ℕ, Nonempty (Retract V (⨁ fun _ : Fin n => W))

lemma ext_subsingleton_inAdd_left {W V Y : C} (h : InAdd W V) (n : ℕ)
    [Subsingleton (Ext W Y n)] : Subsingleton (Ext V Y n) := by
  obtain ⟨d,⟨r⟩⟩ := h
  let : Subsingleton (Ext (⨁ fun _ : Fin d => W) Y n) :=
    (Ext.biproductAddEquiv (biproduct.isBilimit _) Y n).injective.subsingleton
  exact ext_subsingleton_retract_left r n

lemma ext_subsingleton_inAdd_right {W V X : C} (h : InAdd W V) (n : ℕ)
    [Subsingleton (Ext X W n)] : Subsingleton (Ext X V n) := by
  obtain ⟨d,⟨r⟩⟩ := h
  let : Subsingleton (Ext X (⨁ fun _ : Fin d => W) n) :=
    (Ext.addEquivBiproduct X (biproduct.isBilimit _) n).injective.subsingleton
  exact ext_subsingleton_retract_right r n

end Tachikawa

end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DerivedDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt C]

lemma InAdd.projectiveDimension {W V : C} (h : InAdd W V) (n : ℕ)
    [HasProjectiveDimensionLT W n] : HasProjectiveDimensionLT V n := by
  apply HasProjectiveDimensionLT.mk
  intro i hi Y e
  let := HasProjectiveDimensionLT.subsingleton W n i hi Y
  let := ext_subsingleton_inAdd_left h i (Y := Y)
  exact Subsingleton.elim _ _

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v w t
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} {D : Type w} [Category.{v} C] [Category.{t} D] [Abelian C] [Abelian D]

lemma InAdd.map (F : C ⥤ D) [F.Additive] {W V : C} (h : InAdd W V) :
    InAdd (F.obj W) (F.obj V) := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨(r.map F).trans (F.mapBiproduct (fun _ : Fin n => W)).retract⟩⟩

lemma InAdd.iso {W V V' : C} (h : InAdd W V) (e : V' ≅ V) : InAdd W V' := by
  obtain ⟨n,⟨r⟩⟩ := h
  exact ⟨n,⟨e.retract.trans r⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
attribute [local instance] HasDerivedCategory.standard

lemma mappingCone_map_quasiIso {K L K' L' : CochainComplex C ℤ}
    (f : K ⟶ L) (g : K' ⟶ L') (a : K ⟶ K') (b : L ⟶ L')
    (h : f ≫ b = a ≫ g) [QuasiIso a] [QuasiIso b] :
    QuasiIso (mappingCone.map f g a b h) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  let t := DerivedCategory.Q.mapTriangle.map (mappingCone.triangleMap f g a b h)
  have h1 : IsIso t.hom₁ := by
    change IsIso (DerivedCategory.Q.map a)
    infer_instance
  have h2 : IsIso t.hom₂ := by
    change IsIso (DerivedCategory.Q.map b)
    infer_instance
  exact isIso₃_of_isIso₁₂ t (DerivedCategory.mappingCone_triangle_distinguished f)
    (DerivedCategory.mappingCone_triangle_distinguished g) h1 h2

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def shortExactReplacementMapDual (S : ShortComplex (CochainComplex C ℤ))
    {Q : CochainComplex C ℤ} (α : Q ⟶ S.X₁) : mappingCone (α ≫ S.f) ⟶ S.X₃ :=
  mappingCone.map (α ≫ S.f) S.f α (𝟙 S.X₂) (by simp) ≫ mappingCone.descShortComplex S

lemma shortExactReplacementMapDual_quasiIso (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) {Q : CochainComplex C ℤ} (α : Q ⟶ S.X₁) [QuasiIso α] :
    QuasiIso (shortExactReplacementMapDual S α) := by
  have := mappingCone_map_quasiIso (α ≫ S.f) S.f α (𝟙 S.X₂) (by simp)
  have := mappingCone.quasiIso_descShortComplex hS
  exact quasiIso_comp _ _

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

structure IndReplacement (P : CochainComplex (ModuleCat.{0} R) ℤ) where
  complex : CochainComplex (ModuleCat.{0} R) ℤ
  map : complex ⟶ P
  quasiIso : QuasiIso map
attribute [instance] IndReplacement.quasiIso

lemma mappingCone_projective {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L)
    (hK : ∀ i, Projective (K.X i)) (hL : ∀ i, Projective (L.X i)) (i : ℤ) :
    Projective ((mappingCone f).X i) := by
  let := hK (i+1)
  let := hL i
  exact Projective.of_iso (homotopyCofiber.XIsoBiprod f i (i+1) (by rfl)).symm inferInstance

lemma mappingCone_finite {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L)
    (hK : ∀ i, FiniteDimensional k (K.X i)) (hL : ∀ i, FiniteDimensional k (L.X i)) (i : ℤ) :
    FiniteDimensional k ((mappingCone f).X i) := by
  let := hK (i+1)
  let := hL i
  let e := homotopyCofiber.XIsoBiprod f i (i+1) (by rfl) ≪≫ ModuleCat.biprodIsoProd _ _
  exact Module.Finite.equiv (e.toLinearEquiv.restrictScalars k).symm

lemma mappingCone_isZero_X {K L : CochainComplex (ModuleCat.{0} R) ℤ} (f : K ⟶ L) (i : ℤ)
    (hK : IsZero (K.X (i+1))) (hL : IsZero (L.X i)) : IsZero ((mappingCone f).X i) :=
  IsZero.of_iso ((biprod_isZero_iff _ _).2 ⟨hK,hL⟩)
    (homotopyCofiber.XIsoBiprod f i (i+1) (by rfl))

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def exactDerivedHom {X Y : CochainComplex C ℤ}
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj X) ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj Y) :=
  F.mapDerivedCategoryFactors.inv.app X ≫ F.mapDerivedCategory.map f ≫
    F.mapDerivedCategoryFactors.hom.app Y

lemma exactDerivedHom_comp {X Y Z : CochainComplex C ℤ}
    (f : DerivedCategory.Q.obj X ⟶ DerivedCategory.Q.obj Y)
    (g : DerivedCategory.Q.obj Y ⟶ DerivedCategory.Q.obj Z) :
    exactDerivedHom F (f ≫ g) = exactDerivedHom F f ≫ exactDerivedHom F g := by
  simp only [exactDerivedHom,Functor.map_comp,Category.assoc,
    Iso.hom_inv_id_app_assoc]

lemma exactDerivedHom_map {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    exactDerivedHom F (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) := by
  dsimp only [exactDerivedHom]
  rw [F.mapDerivedCategoryFactors_hom_naturality,Iso.inv_hom_id_app_assoc]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℤ}

def HomColumnBoundaries (K L : CochainComplex C ℤ) : Prop :=
  ∀ (n : ℕ) (a : K.X (-(n+1 : ℤ)) ⟶ L.X (-(n+1 : ℤ))),
    K.d (-(n+2 : ℤ)) (-(n+1 : ℤ)) ≫ a = 0 →
    ∃ b : K.X (-(n : ℤ)) ⟶ L.X (-(n+1 : ℤ)),
      K.d (-(n+1 : ℤ)) (-(n : ℤ)) ≫ b = a

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {X : C} (P : ProjectiveResolution X) (L : CochainComplex C ℤ)

lemma resolution_HomColumnBoundaries
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext X (L.X (-(n+1 : ℤ))) (n+1))) :
    HomColumnBoundaries (P.complex.extend ComplexShape.embeddingDownNat) L := by
  intro n a ha
  let e (j : ℕ) := P.complex.extendXIso ComplexShape.embeddingDownNat
    (i := j) (i' := -(j : ℤ)) rfl
  have d (i j : ℕ) : (P.complex.extend ComplexShape.embeddingDownNat).d (-(i : ℤ)) (-(j : ℤ)) =
      (e i).hom ≫ P.complex.d i j ≫ (e j).inv :=
    P.complex.extend_d_eq ComplexShape.embeddingDownNat rfl rfl
  have he1 : -(↑(n+1) : ℤ) = -(n+1 : ℤ) := by push_cast; rfl
  have he2 : -(↑(n+2) : ℤ) = -(n+2 : ℤ) := by push_cast; rfl
  let e1 : (P.complex.extend ComplexShape.embeddingDownNat).X (-(n+1 : ℤ)) ≅ P.complex.X (n+1) :=
    eqToIso (congrArg _ he1.symm) ≪≫ e (n+1)
  let e2 : (P.complex.extend ComplexShape.embeddingDownNat).X (-(n+2 : ℤ)) ≅ P.complex.X (n+2) :=
    eqToIso (congrArg _ he2.symm) ≪≫ e (n+2)
  have hd1 : (P.complex.extend ComplexShape.embeddingDownNat).d (-(n+2 : ℤ)) (-(n+1 : ℤ)) =
      e2.hom ≫ P.complex.d (n+2) (n+1) ≫ e1.inv := by
    simpa [e1,e2,he1,he2] using d (n+2) (n+1)
  have hd0 : (P.complex.extend ComplexShape.embeddingDownNat).d (-(n+1 : ℤ)) (-(n : ℤ)) =
      e1.hom ≫ P.complex.d (n+1) n ≫ (e n).inv := by
    simpa [e1,he1] using d (n+1) n
  have ha' : P.complex.d (n+2) (n+1) ≫ e1.inv ≫ a = 0 := by
    have hs := congrArg (fun t => e2.inv ≫ t) ha
    simpa only [hd1, Category.assoc, Iso.inv_hom_id_assoc, comp_zero] using hs
  let := hExt n
  obtain ⟨b,hb⟩ := boundaries_of_ext_subsingleton P n (e1.inv ≫ a) ha'
  refine ⟨(e n).hom ≫ b, ?_⟩
  rw [hd0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hb, Iso.hom_inv_id_assoc]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C]
variable {K L : CochainComplex C ℤ}

def HomRowBoundaries (K L : CochainComplex C ℤ) : Prop :=
  ∀ (n : ℕ) (a : K.X (n+1 : ℤ) ⟶ L.X (n+1 : ℤ)),
    a ≫ L.d (n+1 : ℤ) (n+2 : ℤ) = 0 →
    ∃ b : K.X (n+1 : ℤ) ⟶ L.X (n : ℤ),
      b ≫ L.d (n : ℤ) (n+1 : ℤ) = a

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex CategoryTheory.Limits
variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable {Y : C} (R : InjectiveResolution Y) (K : CochainComplex C ℤ)

lemma coresolution_HomRowBoundaries
    (hExt : ∀ n : ℕ, Subsingleton (Abelian.Ext (K.X (n+1 : ℤ)) Y (n+1))) :
    HomRowBoundaries K R.cochainComplex := by
  intro n a ha
  let e (j : ℕ) := R.cochainComplexXIso (j : ℤ) j rfl
  have he1 : (↑(n+1) : ℤ) = (n+1 : ℤ) := by push_cast; rfl
  have he2 : (↑(n+2) : ℤ) = (n+2 : ℤ) := by push_cast; rfl
  let e1 : R.cochainComplex.X (n+1 : ℤ) ≅ R.cocomplex.X (n+1) :=
    eqToIso (congrArg _ he1.symm) ≪≫ e (n+1)
  let e2 : R.cochainComplex.X (n+2 : ℤ) ≅ R.cocomplex.X (n+2) :=
    eqToIso (congrArg _ he2.symm) ≪≫ e (n+2)
  have hd1 : R.cochainComplex.d (n+1 : ℤ) (n+2 : ℤ) =
      e1.hom ≫ R.cocomplex.d (n+1) (n+2) ≫ e2.inv := by
    simpa [e1,e2,e,he1,he2] using R.cochainComplex_d (n+1 : ℤ) (n+2 : ℤ) (n+1) (n+2) he1 he2
  have hd0 : R.cochainComplex.d (n : ℤ) (n+1 : ℤ) =
      (e n).hom ≫ R.cocomplex.d n (n+1) ≫ e1.inv := by
    simpa [e1,e,he1] using R.cochainComplex_d (n : ℤ) (n+1 : ℤ) n (n+1) rfl he1
  have ha' : (a ≫ e1.hom) ≫ R.cocomplex.d (n+1) (n+2) = 0 := by
    have hs := congrArg (fun t => t ≫ e2.hom) ha
    simpa only [hd1, Category.assoc, Iso.inv_hom_id, Category.comp_id, zero_comp] using hs
  let := hExt n
  obtain ⟨b,hb⟩ := (R.extMk_eq_zero_iff (a ≫ e1.hom) (n+2) rfl ha' n rfl).mp
    (Subsingleton.elim _ 0)
  refine ⟨b ≫ (e n).inv, ?_⟩
  rw [hd0]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Tachikawa



namespace Tachikawa
open CategoryTheory HomologicalComplex
variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

lemma kInjective_chain_representative (K L : CochainComplex C ℤ) [L.IsKInjective]
    (a : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    ∃ f : K ⟶ L, DerivedCategory.Q.map f = a := by
  let e := DerivedCategory.quotientCompQhIso C
  obtain ⟨b,hb⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (.up ℤ)).obj K) L).surjective
      ((e.app K).hom ≫ a ≫ (e.app L).inv)
  obtain ⟨f,rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective b
  refine ⟨f,?_⟩
  have ht := congrArg (fun t => (e.app K).inv ≫ t ≫ (e.app L).hom) hb
  change e.inv.app K ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) ≫ e.hom.app L =
    e.inv.app K ≫ (e.hom.app K ≫ a ≫ e.inv.app L) ≫ e.hom.app L at ht
  simpa [e] using ht

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_FiniteCoinduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [FiniteDimensional k R] [FiniteDimensional k S]

def dualRightTensorRestriction :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.opAlgEquiv k k R S).symm.toRingHom


instance dualRightTensorRestriction_additive :
    (dualRightTensorRestriction (k := k) (R := R) (S := S)).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars (Algebra.TensorProduct.opAlgEquiv k k R S).symm.toRingHom).Additive

instance dualRightTensorRestriction_isEquivalence :
    (dualRightTensorRestriction (k := k) (R := R) (S := S)).IsEquivalence :=
  inferInstanceAs (ModuleCat.restrictScalars
    (Algebra.TensorProduct.opAlgEquiv k k R S).symm.toRingEquiv.toRingHom).IsEquivalence
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def LeftDual (M : ModuleCat Rᵐᵒᵖ) := Module.Dual k M
namespace LeftDual
variable {M N : ModuleCat Rᵐᵒᵖ}
instance instAddCommGroup : AddCommGroup (LeftDual (k := k) M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance instModule : Module k (LeftDual (k := k) M) := inferInstanceAs (Module k (Module.Dual k M))
instance instFunLikeCarrierMulOpposite : FunLike (LeftDual (k := k) M) M k := inferInstanceAs (FunLike (Module.Dual k M) M k)
instance instLinearMapClassCarrierMulOpposite : LinearMapClass (LeftDual (k := k) M) k M k := inferInstanceAs (LinearMapClass (Module.Dual k M) k M k)
@[ext] lemma ext {φ ψ : LeftDual (k := k) M} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h
instance instModule_1 : Module R (LeftDual (k := k) M) where
  smul r φ := φ.comp (DistribSMul.toLinearMap k M (MulOpposite.op r))
  one_smul φ := by ext x; change φ ((1 : Rᵐᵒᵖ) • x) = φ x; simp
  mul_smul a b φ := by ext x; change φ (MulOpposite.op (a*b) • x) = φ (MulOpposite.op b • MulOpposite.op a • x); simp [mul_smul]
  smul_zero r := by ext x; rfl
  smul_add r φ ψ := by ext x; rfl
  add_smul r s φ := by ext x; change φ (MulOpposite.op (r+s) • x) = φ (MulOpposite.op r • x) + φ (MulOpposite.op s • x); simp [add_smul]
  zero_smul φ := by ext x; change φ ((0 : Rᵐᵒᵖ) • x) = 0; simp
@[simp] lemma smul_apply (r : R) (φ : LeftDual (k := k) M) (x : M) : (r • φ) x = φ (MulOpposite.op r • x) := rfl
instance instIsScalarTower : IsScalarTower k R (LeftDual (k := k) M) where
  smul_assoc c r φ := by ext x; change φ (MulOpposite.op (c • r) • x) = c • φ (MulOpposite.op r • x); simp [smul_assoc]
instance instSMulCommClass : SMulCommClass k R (LeftDual (k := k) M) where
  smul_comm c r φ := by ext x; rfl
instance instFiniteDimensionalOfCarrierMulOpposite [FiniteDimensional k M] : FiniteDimensional k (LeftDual (k := k) M) := inferInstanceAs (FiniteDimensional k (Module.Dual k M))

def map (f : M ⟶ N) : LeftDual (k := k) N →ₗ[R] LeftDual (k := k) M where
  toFun φ := φ.comp (f.hom.restrictScalars k)
  map_add' _ _ := rfl
  map_smul' r φ := by ext x; change φ (MulOpposite.op r • f x) = φ (f (MulOpposite.op r • x)); rw [f.hom.map_smul]
@[simp] lemma map_apply (f : M ⟶ N) (φ : LeftDual (k := k) N) (x : M) : map f φ x = φ (f x) := rfl
lemma map_injective (f : M ⟶ N) (h : Function.Surjective f) : Function.Injective (map (k := k) f) := by
  intro φ ψ he
  ext x
  obtain ⟨y,rfl⟩ := h x
  exact congrArg (fun a : LeftDual (k := k) M => a y) he
end LeftDual

def RightDual (M : ModuleCat R) := Module.Dual k M
namespace RightDual
variable {M N : ModuleCat R}
instance instAddCommGroup : AddCommGroup (RightDual (k := k) M) := inferInstanceAs (AddCommGroup (Module.Dual k M))
instance instModule : Module k (RightDual (k := k) M) := inferInstanceAs (Module k (Module.Dual k M))
instance instFunLikeCarrier : FunLike (RightDual (k := k) M) M k := inferInstanceAs (FunLike (Module.Dual k M) M k)
instance instLinearMapClassCarrier : LinearMapClass (RightDual (k := k) M) k M k := inferInstanceAs (LinearMapClass (Module.Dual k M) k M k)
@[ext] lemma ext {φ ψ : RightDual (k := k) M} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h
instance instModuleMulOpposite : Module Rᵐᵒᵖ (RightDual (k := k) M) where
  smul r φ := φ.comp (DistribSMul.toLinearMap k M r.unop)
  one_smul φ := by ext x; change φ ((1 : R) • x) = φ x; simp
  mul_smul a b φ := by ext x; change φ ((b.unop*a.unop) • x) = φ (b.unop • a.unop • x); rw [mul_smul]
  smul_zero r := by ext x; rfl
  smul_add r φ ψ := by ext x; rfl
  add_smul r s φ := by ext x; change φ ((r.unop+s.unop) • x) = φ (r.unop • x) + φ (s.unop • x); simp [add_smul]
  zero_smul φ := by ext x; change φ ((0 : R) • x) = 0; simp
@[simp] lemma smul_apply (r : Rᵐᵒᵖ) (φ : RightDual (k := k) M) (x : M) : (r • φ) x = φ (r.unop • x) := rfl
instance instIsScalarTowerMulOpposite : IsScalarTower k Rᵐᵒᵖ (RightDual (k := k) M) where
  smul_assoc c r φ := by ext x; change φ ((c • r.unop) • x) = c • φ (r.unop • x); simp [smul_assoc]
instance instSMulCommClassMulOpposite : SMulCommClass k Rᵐᵒᵖ (RightDual (k := k) M) where
  smul_comm c r φ := by ext x; rfl

def map (f : M ⟶ N) : RightDual (k := k) N →ₗ[Rᵐᵒᵖ] RightDual (k := k) M where
  toFun φ := φ.comp (f.hom.restrictScalars k)
  map_add' _ _ := rfl
  map_smul' r φ := by ext x; change φ (r.unop • f x) = φ (f (r.unop • x)); rw [f.hom.map_smul]
@[simp] lemma map_apply (f : M ⟶ N) (φ : RightDual (k := k) N) (x : M) : map f φ x = φ (f x) := rfl
lemma map_surjective (f : M ⟶ N) (h : Function.Injective f) : Function.Surjective (map (k := k) f) :=
  LinearMap.dualMap_surjective_of_injective h
end RightDual




def dualTranspose {M : ModuleCat R} {P : ModuleCat Rᵐᵒᵖ}
    (g : M →ₗ[R] LeftDual (k := k) P) : P →ₗ[Rᵐᵒᵖ] RightDual (k := k) M where
  toFun p :=
    { toFun := fun x => g x p
      map_add' x y := by change g (x+y) p = g x p + g y p; rw [g.map_add]; rfl
      map_smul' c x := by
        change g (c • x) p = c • g x p
        exact congrArg (fun φ : LeftDual (k := k) P => φ p)
          ((g.restrictScalars k).map_smul c x) }
  map_add' p q := by ext x; exact (g x).map_add p q
  map_smul' r p := by
    ext x
    change g x (r • p) = g (r.unop • x) p
    rw [g.map_smul]
    rfl

def dualUntranspose {M : ModuleCat R} {P : ModuleCat Rᵐᵒᵖ}
    (g : P →ₗ[Rᵐᵒᵖ] RightDual (k := k) M) : M →ₗ[R] LeftDual (k := k) P where
  toFun x :=
    { toFun := fun p => g p x
      map_add' p q := by change g (p+q) x = g p x + g q x; rw [g.map_add]; rfl
      map_smul' c p := by
        change g (c • p) x = c • g p x
        exact congrArg (fun φ : RightDual (k := k) M => φ x)
          ((g.restrictScalars k).map_smul c p) }
  map_add' x y := by ext p; exact (g p).map_add x y
  map_smul' r x := by
    ext p
    change g p (r • x) = g (MulOpposite.op r • p) x
    rw [g.map_smul]
    rfl

instance leftDual_injective (P : ModuleCat Rᵐᵒᵖ) [Module.Projective Rᵐᵒᵖ P] :
    Module.Injective R (LeftDual (k := k) P) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let X' : ModuleCat R := ModuleCat.of R X
    let Y' : ModuleCat R := ModuleCat.of R Y
    let f' : X' ⟶ Y' := ModuleCat.ofHom f
    let g' : X' →ₗ[R] LeftDual (k := k) P := g
    obtain ⟨h,hh⟩ := Module.projective_lifting_property (RightDual.map (k := k) f')
      (dualTranspose g') (RightDual.map_surjective f' hf)
    refine ⟨dualUntranspose (M := Y') h, ?_⟩
    intro x
    apply LeftDual.ext
    intro p
    exact congrArg (fun φ : RightDual (k := k) X' => φ x) (LinearMap.congr_fun hh p)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def leftDualObj (M : ModuleCat Rᵐᵒᵖ) : ModuleCat R := ModuleCat.of R (LeftDual (k := k) M)

lemma leftDualObj_isZero {M : ModuleCat Rᵐᵒᵖ} (hM : IsZero M) :
    IsZero (leftDualObj (k := k) M) := by
  have hm (x : M) : x = 0 := by
    have h := hM.eq_of_src (𝟙 M) 0
    exact congrArg (fun f : M ⟶ M => f x) h
  have : Subsingleton (LeftDual (k := k) M) := by
    constructor
    intro φ ψ
    apply LeftDual.ext
    intro x
    rw [hm x]
    exact map_zero φ |>.trans (map_zero ψ).symm
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R (LeftDual (k := k) M))

end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

def leftRegularObj : ModuleCat R := ModuleCat.of R R

def leftRegularUnderlying : leftRegularObj (R := R) ≃ₗ[k] R :=
  moduleCatUnderlyingEquiv (k := k) (R := R) R

def rightRegularUnderlying : rightRegularObj (S := S) ≃ₗ[k] Sᵐᵒᵖ :=
  moduleCatUnderlyingEquiv (k := k) (R := Sᵐᵒᵖ) Sᵐᵒᵖ

end Tachikawa.Enveloping



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma InAdd.trans {W V X : C} (h : InAdd W V) (h' : InAdd V X) : InAdd W X := by
  classical
  obtain ⟨n,⟨r⟩⟩ := h
  obtain ⟨m,⟨s⟩⟩ := h'
  let t : Retract (⨁ fun _ : Fin m => V) (⨁ fun _ : Fin m => ⨁ fun _ : Fin n => W) :=
    { i := biproduct.map (fun _ => r.i)
      r := biproduct.map (fun _ => r.r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,Category.id_comp,
          r.retract,Category.comp_id] }
  let e := biproductBiproductIso (fun _ : Fin m => Fin n) (fun _ _ => W)
  let d := biproduct.whiskerEquiv (f := fun _ : Σ _ : Fin m, Fin n => W)
    (g := fun _ : Fin (Fintype.card (Σ _ : Fin m, Fin n)) => W)
    (Fintype.equivFin _) (fun _ => Iso.refl _)
  exact ⟨_,⟨s.trans (t.trans (e.retract.trans d.retract))⟩⟩

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
open HomologicalComplex CochainComplex
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def shortExactReplacementMap (S : ShortComplex (CochainComplex C ℤ))
    {Q : CochainComplex C ℤ} (α : S.X₃ ⟶ Q) : S.X₁ ⟶ mappingCocone (S.g ≫ α) :=
  let h := mappingCone.descShortComplex S ≫ α
  let w : mappingCone.inr S.f ≫ h = (𝟙 S.X₂) ≫ (S.g ≫ α) := by
    simp [h,← Category.assoc,mappingCone.inr_descShortComplex]
  (shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1) (by omega)).inv.app S.X₁ ≫
    ((mappingCone.rotateHomotopyEquiv S.f).hom ≫
      mappingCone.map (mappingCone.inr S.f) (S.g ≫ α) (𝟙 _) h w)⟦(-1 : ℤ)⟧'

lemma shortExactReplacementMap_quasiIso (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) {Q : CochainComplex C ℤ} (α : S.X₃ ⟶ Q) [QuasiIso α] :
    QuasiIso (shortExactReplacementMap S α) := by
  have := mappingCone.quasiIso_descShortComplex hS
  have : QuasiIso (mappingCone.descShortComplex S ≫ α) := inferInstance
  dsimp only [shortExactReplacementMap]
  have := mappingCone_map_quasiIso (mappingCone.inr S.f) (S.g ≫ α) (𝟙 S.X₂)
    (mappingCone.descShortComplex S ≫ α) (by
      simp [← Category.assoc,mappingCone.inr_descShortComplex])
  have hr : QuasiIso (mappingCone.rotateHomotopyEquiv S.f).hom :=
    (mappingCone.rotateHomotopyEquiv S.f).quasiIso_hom
  have hc : QuasiIso ((mappingCone.rotateHomotopyEquiv S.f).hom ≫
      mappingCone.map (mappingCone.inr S.f) (S.g ≫ α) (𝟙 S.X₂)
        (mappingCone.descShortComplex S ≫ α) (by
          simp [← Category.assoc,mappingCone.inr_descShortComplex])) := inferInstance
  have hs := (CochainComplex.quasiIso_shift_iff _ (-1)).2 hc
  have he : QuasiIso
      ((shiftFunctorCompIsoId (CochainComplex C ℤ) (1 : ℤ) (-1) (by omega)).inv.app S.X₁) := by
    exact quasiIso_of_isIso _
  exact quasiIso_comp _ _ (hφ := he) (hφ' := hs)

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits
universe u v
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

lemma InAdd.biproduct {W : C} {ι : Type} [Fintype ι] (V : ι → C)
    (h : ∀ i, InAdd W (V i)) : InAdd W (⨁ V) := by
  classical
  choose n r using h
  let s (i : ι) := (r i).some
  let t : Retract (⨁ V) (⨁ fun i : ι => ⨁ fun _ : Fin (n i) => W) :=
    { i := biproduct.map (fun i => (s i).i)
      r := biproduct.map (fun i => (s i).r)
      retract := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc,biproduct.map_π,biproduct.map_π_assoc,Category.id_comp,
          (s j).retract,Category.comp_id] }
  let e := biproductBiproductIso (fun i : ι => Fin (n i)) (fun _ _ => W)
  let d := biproduct.whiskerEquiv (f := fun _ : Σ i : ι, Fin (n i) => W)
    (g := fun _ : Fin (Fintype.card (Σ i : ι, Fin (n i))) => W)
    (Fintype.equivFin _) (fun _ => Iso.refl _)
  exact ⟨_,⟨t.trans (e.retract.trans d.retract)⟩⟩

lemma InAdd.biprod {W X Y : C} (hX : InAdd W X) (hY : InAdd W Y) :
    InAdd W (X ⊞ Y) := by
  have h : ∀ i, InAdd W (pairFunction X Y i) := by
    intro i
    cases i
    · exact hX
    · exact hY
  let e := biprod.uniqueUpToIso X Y
    ((Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit (pairFunction X Y)))
  exact (InAdd.biproduct _ h).iso e.symm

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_StableLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
open CategoryTheory HomologicalComplex
open scoped ModuleCat.Algebra
attribute [local instance] HasDerivedCategory.standard

lemma lift_composite_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q T S U : C} (a : P ⟶ Q) (b : Q ⟶ T) (p : Q ⟶ S) (r : T ⟶ U)
    (v : P ⟶ S) (w : S ⟶ U)
    (ha : F.map a ≫ F.map p = F.map v)
    (hb : F.map b ≫ F.map r = F.map p ≫ F.map w) :
    F.map (a ≫ b) ≫ F.map r = F.map (v ≫ w) := by
  rw [Functor.map_comp,Category.assoc,hb,← Category.assoc,ha,← Functor.map_comp]

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_HomProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace Tachikawa.SourceField
abbrev Base := MvPolynomial (Fin 3) (ZMod 2)
abbrev K := FractionRing Base

def parameter (i : Fin 3) : K := algebraMap Base K (MvPolynomial.X i)
def q : K := parameter 0
def H₁ : K := parameter 1
def H₂ : K := parameter 2

lemma parameter_ne_zero (i : Fin 3) : parameter i ≠ 0 := by
  intro h
  apply MvPolynomial.X_ne_zero (R := ZMod 2) (s := i)
  apply IsFractionRing.injective Base K
  exact h.trans (map_zero _).symm

lemma one_add_q_pow_ne_zero (n : ℕ) (hn : 0 < n) : 1 + q^n ≠ 0 := by
  intro h
  have he : 1 + (MvPolynomial.X (0 : Fin 3) : Base)^n = 0 := by
    apply IsFractionRing.injective Base K
    simpa only [map_add, map_one, map_pow, map_zero, q, parameter] using h
  have hv := congrArg (MvPolynomial.eval (fun _ : Fin 3 => (0 : ZMod 2))) he
  have hv' : (1 : ZMod 2) = 0 := by
    simpa only [map_add, map_one, map_pow, map_zero, MvPolynomial.eval_X,
      zero_pow (Nat.ne_of_gt hn), add_zero] using hv
  exact one_ne_zero hv'

end Tachikawa.SourceField



namespace Tachikawa
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]
variable {M N P Q M' N' : ModuleCat.{0} R}
variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]

omit [Module.Injective R R] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] in
lemma exact_square_difference_inverse
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M')
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N')
    (f : M →ₗ[R] N) (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (f' : N →ₗ[R] M) (h' : Q →ₗ[R] P) (g' : N' →ₗ[R] M')
    (hu : h.comp i = j.comp f) (hl : delta.comp h = g.comp pi)
    (hu' : h'.comp j = i.comp f') (hl' : pi.comp h' = g'.comp delta) :
    (h'.comp h - LinearMap.id).comp i = i.comp (f'.comp f - LinearMap.id) ∧
    pi.comp (h'.comp h - LinearMap.id) = (g'.comp g - LinearMap.id).comp pi := by
  constructor
  · simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.comp_assoc]
    rw [hu, ← LinearMap.comp_assoc, hu', LinearMap.comp_assoc]
  · simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id]
    rw [← LinearMap.comp_assoc, hl', LinearMap.comp_assoc, hl, ← LinearMap.comp_assoc]

end Tachikawa



namespace Tachikawa
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
variable {k : Type} [Field k]

def piSupportedEquiv {ι : Type} (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (i₀ : ι) (hz : ∀ i, i ≠ i₀ → Subsingleton (V i)) :
    (∀ i, V i) ≃ₗ[k] V i₀ := by
  classical
  apply LinearEquiv.ofBijective (LinearMap.proj i₀)
  constructor
  · intro x y h
    funext i
    by_cases hi : i = i₀
    · subst i; exact h
    · exact (hz i hi).elim _ _
  · intro x
    refine ⟨Pi.single i₀ x, ?_⟩
    exact Pi.single_eq_same i₀ x

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Delta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def scalarPair (r s : k) : (V × V) →ₗ[k] (V × V) :=
  ((r • LinearMap.fst k V V) + LinearMap.snd k V V).prod
    ((s • LinearMap.fst k V V) + LinearMap.snd k V V)

end Tachikawa



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Triangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
abbrev zeroObj : ModuleCat R := ModuleCat.of R PUnit

end Tachikawa.Triangular



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (ι : Type)
  [Fintype ι]

def freeObj := ModuleCat.of R (ι → R)
def freeUnderlying : freeObj (R := R) ι ≃ₗ[R] (ι → R) := LinearEquiv.refl R _

end Tachikawa.Triangular



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_DownHom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
variable (P Q : ChainComplex (ModuleCat.{0} R) ℤ)

abbrev Cochain (a : ℤ) := ∀ (i j : ℤ), i = j+a → (P.X i ⟶ Q.X j)

variable {P Q}
def Closed {a : ℤ} (f : Cochain P Q a) : Prop :=
  ∀ i j l m (hij : i=j+a) (hlm : l=m+a),
    f i j hij ≫ Q.d j m = P.d i l ≫ f l m hlm

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory HomologicalComplex CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {P Q S : ChainComplex (ModuleCat.{0} R) ℤ}
structure Index (a : ℤ) where
  i : ℤ
  j : ℤ
  h : i=j+a

end Tachikawa.DownHom



namespace Tachikawa.DownHom
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R]  [Algebra k R]
variable {P Q : ChainComplex (ModuleCat.{0} R) ℤ} {N : ModuleCat.{0} R}
  (ε : Q.X 0 ⟶ N) (hε : Q.d 1 0 ≫ ε = 0)

variable (F : ModuleCat.{0} R ⥤ ModuleCat.{0} R) [F.Additive]
abbrev mapComplex (P : ChainComplex (ModuleCat.{0} R) ℤ) :=
  (F.mapHomologicalComplex (.down ℤ)).obj P

variable [F.Linear k] (X : ModuleCat.{0} R) (εP : P.X 0 ⟶ X)
  (hεP : P.d 1 0 ≫ εP = 0) (u : P ⟶ mapComplex F P) (u₀ : X ⟶ F.obj X)
  (hu : u.f 0 ≫ F.map εP = εP ≫ u₀)
include hεP in
lemma map_augmentation_zero : (mapComplex F P).d 1 0 ≫ F.map εP = 0 := by
  change F.map (P.d 1 0) ≫ F.map εP = 0
  rw [← F.map_comp,hεP,F.map_zero]

end Tachikawa.DownHom



end

end OAI
end

section
-- module Solutions.OAIQ116_Tach.Tachikawa_Cone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace Tachikawa.DownCone
open CategoryTheory CategoryTheory.Preadditive CategoryTheory.Limits HomologicalComplex
open scoped ModuleCat.Algebra
open DownHom
variable {k R : Type} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable {A B : ChainComplex (ModuleCat.{0} R) ℤ} (v : B ⟶ A)
abbrev iL (j : ℤ) := homotopyCofiber.inlX v j (j+1) (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)
abbrev pL (j : ℤ) := homotopyCofiber.fstX v (j+1) j (show (ComplexShape.down ℤ).Rel (j+1) j from rfl)

end Tachikawa.DownCone



namespace Tachikawa.Triangular
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
abbrev oneFree := freeObj (R := R) (PUnit : Type)
instance instFiniteCarrierOneFree : Module.Finite R (oneFree (R := R)) := inferInstanceAs (Module.Finite R (PUnit → R))
instance instProjectiveCarrierOneFree : Module.Projective R (oneFree (R := R)) := inferInstanceAs (Module.Projective R (PUnit → R))

end Tachikawa.Triangular



end

end OAI
end


