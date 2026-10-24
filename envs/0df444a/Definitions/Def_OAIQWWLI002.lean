-- Prove2me | Definitions.Def_OAIQWWLI002
-- name    : OAIQWWLI002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T21:23:04.733567+00:00
-- url     : https://prove2.me/theorems/64368880-d1ed-4dc3-9a63-6d9a0d30136c
-- title:
--   OpenAI Weisfeiler–Leman identification split: definitions bundle OAIQWWLI002
-- statement:
--   A definitions bundle of the split of OpenAI's proof that deciding whether Weisfeiler–Leman refinement of a given dimension identifies a graph is EXPTIME-complete (`OAI.WLIdentification.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/WLIdentification` (OpenAI, *The complexity of identifying a graph by Weisfeiler–Leman refinement*, OpenAI Math Release, September 25, 2026, result family 133, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   This bundle holds the ring and circuit gadgets of the hardness construction: ring values and ports (`ringValue`, `Point`, `PortTrue`), the comparison targets and shifted images used to reconstruct an arbitrary equivalent mate (`comparisonTarget`, `Shifts`, `Images`, `imagesOfEquivalent`), the accepting and rejecting truth assignments (`Accepted`, `rejectingImages`), the cellular rule letters and initial seeds (`Letter`, `localRule`, `InitialSeed`), and the compiled circuit of the simulated machine (`compiledCircuit`, `actionConfig`).
--
--   The definitions of the published statement (`Graph`, `WLdim`, `dimensionLanguage`, `InEXPTIME`, `PolytimeManyOne`, `EXPTIMEComplete` and the rest) are not repeated: the bundle imports them from the published bundle `Def_WLIdentification`. It also imports the bundles `OAIQWWLI000`, `OAIQWWLI001` of this split.
--
--   Modules: `AcceptingBroadcast`, `BufferedCircuits`, `CircuitCodes`, `CircuitForms`, `CircuitPresentation`, `CircuitReduction`, `DimensionDecider`, `ExponentialComputation`, `ExpressionBounds`, `ExpressionCompiler`, `FiniteEncoding`, `FinitePresentation`, `FiniteRefinement`, `GraphEnumeration`, `Hardness`, `LeafPresentation`, `MachineCells`, `MachinePresentation`, `MachineReduction`, `NumericKernel`, `PolynomialArithmetic`, `PresentationArithmetic`, `PrivateLeaves`, `RefinementCorrectness`, `RingCodes`, `RingLegality`, `RingMembership`, `RowOffsets`, `SchemaPresentation`, `SeedBits`, `SeedLetter`, `StackCommands`, `StackMachines`, `TapeCompiler`, `WordArithmetic`, `WordCommands`, `WordExpressions`.
--
--   The theorems of the development that the definitions do not need are proved in the single solution of this split, which imports the bundle `OAIQWWLI002` (and through it the other two) and proves `OAI.WLIdentification.main`. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, The complexity of identifying a graph by Weisfeiler–Leman refinement, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 133; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-complexity-of-identifying-a-graph-by-Weisfeiler-Leman-refinement-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/WLIdentification at commit adc7f12

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_OAIQWWLI000
import Definitions.Def_OAIQWWLI001

section
-- module Solutions.OAIQW_WLIdentification.PrivateLeaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/-- Color-preserving base isomorphisms extend to all private leaves. -/
def withLeavesIso {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (ell : V → ℕ) (ell' : W → ℕ) (hell : ∀ v, ell v = ell' (e v)) :
    withLeaves G ell ≃g withLeaves H ell' where
  toEquiv := Equiv.sumCongr e.toEquiv (Equiv.sigmaCongr e.toEquiv (fun v => finCongr (hell v)))
  map_rel_iff' := by
    intro x y
    cases x <;> cases y
    · exact e.map_adj_iff
    · change e _ = e _ ↔ _ = _
      exact e.toEquiv.injective.eq_iff
    · change e _ = e _ ↔ _ = _
      exact e.toEquiv.injective.eq_iff
    · rfl

noncomputable def baseDegreeEquiv {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (color : V → ℕ) (hcolor : ∀ v, 0 < color v) :
    V ≃ {x : LeafVertex (tagSize color) // 1 < (withLeaves G (tagSize color)).degree x} where
  toFun v := ⟨.inl v, tag_base_degree_gt_one G color hcolor v⟩
  invFun x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl v => exact v
    | inr w =>
      have hf := withLeaves_leaf_degree G (tagSize color) w.1 w.2
      exact False.elim (by rw [hf] at hx; omega)
  left_inv _ := rfl
  right_inv x := by
    obtain ⟨x, hx⟩ := x
    cases x with
    | inl v => rfl
    | inr w =>
      have hf := withLeaves_leaf_degree G (tagSize color) w.1 w.2
      exact False.elim (by rw [hf] at hx; omega)

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RowOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

def ringValue (x : R.Horizontal) (t : T) (a : R.Address t) : Fin (R.dimension t) → Bit :=
  ∑ i, x ⟨t, i, a i, a (finRotate r i)⟩

end RingLayout

namespace RingLayout
variable {r : ℕ} {T L : Type} [Fintype T] [Fintype L] (R : RingLayout r T L)

omit [Fintype T] [Fintype L] in
theorem hCoords_card (h : R.HName) : (R.hCoords h).card = R.dimension h.1 := by
  classical
  rw [hCoords, Finset.card_image_of_injective]
  · simp
  · intro i j hh
    exact (Sigma.mk.inj (Sum.inl.inj hh)).2 |> eq_of_heq

omit [Fintype T] [Fintype L] in
theorem coordinates_card (b : R.Block) : (R.coordinates b).card ≤ 5 := by
  classical
  cases b with
  | inl h =>
    change (R.hCoords h).card ≤ 5
    rw [R.hCoords_card]
    rcases R.dimension_bound h.1 with h | h <;> omega
  | inr b =>
    have h1 := R.dimension_bound (R.first b.1)
    have h2 := R.dimension_bound (R.second b.1)
    have h3 := R.internal_endpoint b.1
    have ha := Finset.card_union_le (R.hCoords (R.leftH b)) (R.hCoords (R.rightH b))
    have hb := Finset.card_union_le (R.hCoords (R.leftH b) ∪ R.hCoords (R.rightH b))
      {Sum.inr (R.topV b), Sum.inr (R.bottomV b)}
    have hc : ({Sum.inr (R.topV b), Sum.inr (R.bottomV b)} : Finset R.Coordinate).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    rw [R.hCoords_card, R.hCoords_card] at ha
    change (R.hCoords (R.leftH b) ∪ R.hCoords (R.rightH b) ∪
      {Sum.inr (R.topV b), Sum.inr (R.bottomV b)}).card ≤ 5
    change _ ≤ R.dimension (R.first b.1) + R.dimension (R.second b.1) at ha
    omega

/-- Every vertical name has a neighboring square, even for singleton factors. -/
noncomputable def owner : R.Coordinate → R.Block
  | .inl h => .inl h.1
  | .inr v => .inr ⟨v.1, v.2.1, v.2.2,
      ⟨(R.matchLabels_nonempty v.1 (finRotate r v.2.1)).choose,
        (R.matchLabels_nonempty v.1 (finRotate r v.2.1)).choose_spec⟩⟩

end RingLayout

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.BufferedCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ProductMap
variable {r : ℕ}
abbrev Point (D : ProductMap r) := (i : Fin r) → {b // b ∈ D.domain i}
def source (D : ProductMap r) (a : D.Point) : Fin r → Bool := fun i => (a i).val
def target (D : ProductMap r) (a : D.Point) : Fin r → Bool := fun i => D.mapping i (a i).val

def ofAddress (a : Fin r → Bool) : (identity r).Point :=
  fun i => ⟨a i, Finset.mem_univ _⟩

end ProductMap

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

inductive PortTrue : (p : P) → (Fin r → Bool) → Fin (C.dimension p) → Prop
  | seed (z : Z) (a : (C.seedMap z).Point) (j : Fin (C.dimension (C.seedType z))) :
      PortTrue (C.seedType z) ((C.seedMap z).source a) j
  | edge (e : E) (a : (C.edgeMap e).Point)
      (h : ∀ j, PortTrue (C.source e) ((C.edgeMap e).source a) j) :
      PortTrue (C.target e) ((C.edgeMap e).target a) (C.port e)

def True (p : P) (a : Fin r → Bool) : Prop := ∀ j, C.PortTrue p a j

def Accepted : Prop := ∃ (t : T) (a : (C.testMap t).Point),
  C.True (C.testType t) ((C.testMap t).source a)

abbrev connectionTarget : C.Connection → C.Primary
  | .original e => some (C.target e)
  | .test _ => none
  | .flip _ => none
  | .broadcast p _ => some p
  | .self p _ => p
  | .conflict => none

abbrev targetForm (l : C.Connection) : (Fin (C.primaryDimension (C.connectionTarget l)) → Bit) →ₗ[Bit] Bit :=
  match l with
  | .original e => LinearMap.proj (C.port e)
  | .test _ => LinearMap.proj (0 : Fin 1)
  | .flip _ => LinearMap.proj (0 : Fin 1)
  | .broadcast _ j => LinearMap.proj j
  | .self _ j => LinearMap.proj j
  | .conflict => LinearMap.proj (0 : Fin 1)

abbrev comparisonTarget : C.Comparison → C.RealType
  | .seed _ => .dummy
  | .first l => .buffer l
  | .second l => .buffer l
  | .third l => .primary (C.connectionTarget l)

abbrev comparisonRight (e : C.Comparison) :
    (Fin (C.realDimension (C.comparisonTarget e)) → Bit) →ₗ[Bit] Bit :=
  match e with
  | .seed _ => 0
  | .first _ => LinearMap.proj (0 : Fin 2)
  | .second _ => LinearMap.proj (1 : Fin 2)
  | .third l => C.targetForm l

def realIndexValue : C.RealType → ℕ
  | .primary p => Nat.pair 0 (NaturalCode.option C.pointIndex p)
  | .buffer l => Nat.pair 1 (C.connectionIndex l)
  | .dummy => Nat.pair 2 0

def realIndex : C.RealType ↪ ℕ where
  toFun := C.realIndexValue
  inj' := by
    intro a b h
    cases a <;> cases b <;>
      simp only [realIndexValue, Nat.pair_eq_pair, Nat.reduceEqDiff, false_and,
        true_and] at h
    · exact congrArg RealType.primary ((NaturalCode.option C.pointIndex).injective h)
    · exact congrArg RealType.buffer (C.connectionIndex.injective h)
    · rfl

def schemas : ComparisonSchemas r C.RealType C.Comparison where
  pointIndex := C.realIndex
  edgeIndex := C.comparisonIndex
  dimension := C.realDimension
  dimension_bound p := by
    cases p with
    | primary p => cases p with
      | none => exact Or.inl rfl
      | some p => exact C.dimension_bound p
    | buffer _ => exact Or.inr rfl
    | dummy => exact Or.inl rfl
  source := C.comparisonSource
  target := C.comparisonTarget
  domain e := (C.comparisonMap e).domain
  domain_nonempty e := (C.comparisonMap e).nonempty
  mapping e i a := (C.comparisonMap e).mapping i a.val
  mapping_injective e i := by
    intro a b h
    exact Subtype.ext ((C.comparisonMap e).injective i a.property b.property h)
  left := C.comparisonLeft
  right := C.comparisonRight

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.AcceptingBroadcast
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

abbrev Shifts := (e : C.Comparison) → (C.comparisonMap e).Point → Bit

/-- General, address-dependent image consistency, as extracted from arbitrary
WL mates. It is deliberately weaker than simultaneous pointwise solvability. -/
structure Images (delta : C.Shifts) where
  values : (p : C.RealType) → (Fin r → Bool) → Set (Fin (C.realDimension p) → Bit)
  nonempty : ∀ p a, (values p a).Nonempty
  equation : ∀ e (a : (C.comparisonMap e).Point),
    C.comparisonLeft e '' values (C.comparisonSource e) ((C.comparisonMap e).source a) =
      (fun v => delta e a + C.comparisonRight e v) ''
        values (C.comparisonTarget e) ((C.comparisonMap e).target a)

namespace Images
variable {C} {delta : C.Shifts} (I : C.Images delta)
open BufferAlgebra

noncomputable def primaryValue (p : C.Primary) (a : Fin r → Bool) :
    Fin (C.primaryDimension p) → Bit := (I.nonempty (.primary p) a).choose

end Images
end ProductCircuit

namespace ProductCircuit.Images
variable {r : ℕ} {P E Z T : Type} {C : ProductCircuit r P E Z T}
    {delta : C.Shifts} (I : C.Images delta)

noncomputable def bufferValue (l : C.Connection) (a : (C.connectionMap l).Point) :
    Fin 2 → Bit := (I.nonempty (.buffer l) ((C.connectionMap l).source a)).choose

end ProductCircuit.Images

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

abbrev wireDelta (n : ℕ) (beta : (C.schemas.layout n).Block → Bit) : C.Shifts :=
  fun e a => C.schemas.wireShift n beta e a

noncomputable def imagesOfEquivalent (hr : 32 ≤ r) (n : ℕ)
    (beta : (C.schemas.layout n).Block → Bit)
    (he : Equivalent r (((C.schemas.layout n).affine (by omega)).graph 0)
      (((C.schemas.layout n).affine (by omega)).graph beta)) : C.Images (C.wireDelta n beta) where
  values p a := C.schemas.responseImages (by omega) n beta p (ProductMap.ofAddress a)
  nonempty p a := (C.schemas.image_consistency hr n beta he).1 p (ProductMap.ofAddress a)
  equation e a := (C.schemas.image_consistency hr n beta he).2 e a

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

abbrev primaryTruth (p : C.Primary) (a : Fin r → Bool) : Fin (C.primaryDimension p) → Prop :=
  match p with
  | none => fun _ => False
  | some p => C.PortTrue p a

abbrev primarySet (p : C.Primary) (a : Fin r → Bool) :=
  BufferAlgebra.truthVectors (C.primaryTruth p a)

abbrev sourceTruth (l : C.Connection) (a : Fin r → Bool) : Prop := match l with
  | .original e => C.True (C.source e) a
  | .test t => C.True (C.testType t) a
  | .flip _ => False
  | .broadcast _ _ => False
  | .self p j => C.primaryTruth p a j
  | .conflict => False

abbrev targetTruth (l : C.Connection) (a : Fin r → Bool) : Prop := match l with
  | .original e => C.PortTrue (C.target e) a (C.port e)
  | .test _ => False
  | .flip _ => False
  | .broadcast p j => C.PortTrue p a j
  | .self p j => C.primaryTruth p a j
  | .conflict => False

def rejectConstant : C.Comparison → Bit
  | .third .conflict => 1
  | _ => 0

theorem source_truth_image (l : C.Connection) (a : Fin r → Bool) :
    C.sourceForm l '' C.primarySet (C.connectionSource l) a =
      @ite (Set Bit) (C.sourceTruth l a) (Classical.propDecidable _) {0} Set.univ := by
  classical
  have hs (p : P) : ⇑(sumForm (C.dimension p)) = fun v => ∑ j, v j :=
    funext (sumForm_apply _)
  cases l with
  | original e =>
    rw [hs]
    have hu := BufferAlgebra.sum_truth (C.PortTrue (C.source e) a)
    by_cases ht : ∀ j, C.PortTrue (C.source e) a j <;>
      simpa only [sourceTruth, True, connectionSource, primarySet, primaryTruth, ht, ite_true, ite_false] using hu
  | test t =>
    rw [hs]
    have hu := BufferAlgebra.sum_truth (C.PortTrue (C.testType t) a)
    by_cases ht : ∀ j, C.PortTrue (C.testType t) a j <;>
      simpa only [sourceTruth, True, connectionSource, primarySet, primaryTruth, ht, ite_true, ite_false] using hu
  | flip i => simpa only [sourceForm, connectionSource, primarySet, primaryTruth, sourceTruth, ite_false, ite_eq_right not_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | broadcast p j => simpa only [sourceForm, connectionSource, primarySet, primaryTruth, sourceTruth, ite_false, ite_eq_right not_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | self p j => exact BufferAlgebra.projection_truth (C.primaryTruth p a) j
  | conflict => simpa only [sourceForm, connectionSource, primarySet, primaryTruth, sourceTruth, ite_false, ite_eq_right not_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0

theorem target_truth_image (l : C.Connection) (a : Fin r → Bool) :
    C.targetForm l '' C.primarySet (C.connectionTarget l) a =
      @ite (Set Bit) (C.targetTruth l a) (Classical.propDecidable _) {0} Set.univ := by
  classical
  cases l with
  | original e => exact BufferAlgebra.projection_truth (C.PortTrue (C.target e) a) (C.port e)
  | test t => simpa only [targetForm, connectionTarget, primarySet, primaryTruth, targetTruth, ite_false, ite_eq_right not_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | flip i => simpa only [targetForm, connectionTarget, primarySet, primaryTruth, targetTruth, ite_false, ite_eq_right not_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0
  | broadcast p j => exact BufferAlgebra.projection_truth (C.PortTrue p a) j
  | self p j => exact BufferAlgebra.projection_truth (C.primaryTruth p a) j
  | conflict => simpa only [targetForm, connectionTarget, primarySet, primaryTruth, targetTruth, ite_false, ite_eq_right not_false, LinearMap.coe_proj, Function.eval] using BufferAlgebra.projection_truth (fun _ : Fin 1 => False) 0

theorem source_implies_target (h : ¬ C.Accepted) (l : C.Connection)
    (a : (C.connectionMap l).Point) (ht : C.sourceTruth l ((C.connectionMap l).source a)) :
    C.targetTruth l ((C.connectionMap l).target a) ∧ C.rejectConstant (.third l) = 0 := by
  cases l with
  | original e => exact ⟨PortTrue.edge e a ht, rfl⟩
  | test t => exact (h ⟨t, a, ht⟩).elim
  | flip i => exact ht.elim
  | broadcast p j => exact ht.elim
  | self p j => exact ⟨ht, rfl⟩
  | conflict => exact ht.elim

def rejectDestination (l : C.Connection) (a : Fin r → Bool) : Set Bit :=
  (fun v => C.rejectConstant (.third l) + C.targetForm l v) ''
    C.primarySet (C.connectionTarget l) (fun i => (C.connectionMap l).mapping i (a i))

theorem rejectDestination_nonempty (l : C.Connection) (a : Fin r → Bool) :
    (C.rejectDestination l a).Nonempty :=
  (BufferAlgebra.truthVectors_nonempty _).image _

theorem rejectDestination_true (h : ¬ C.Accepted) (l : C.Connection)
    (a : (C.connectionMap l).Point) (ht : C.sourceTruth l ((C.connectionMap l).source a)) :
    C.rejectDestination l ((C.connectionMap l).source a) = {0} := by
  obtain ⟨hd, hb⟩ := C.source_implies_target h l a ht
  dsimp only [rejectDestination]
  rw [hb]
  simp only [zero_add]
  change C.targetForm l '' C.primarySet (C.connectionTarget l) ((C.connectionMap l).target a) = _
  rw [C.target_truth_image l _, ite_eq_left hd]

noncomputable def rejectBuffer (l : C.Connection) (a : Fin r → Bool) : Set (Fin 2 → Bit) := by
  classical
  exact if C.sourceTruth l a then {0} else BufferAlgebra.correlated (C.rejectDestination l a)

theorem rejectBuffer_nonempty (l : C.Connection) (a : Fin r → Bool) :
    (C.rejectBuffer l a).Nonempty := by
  classical
  unfold rejectBuffer
  split
  · exact Set.singleton_nonempty _
  · exact BufferAlgebra.correlated_nonempty (C.rejectDestination_nonempty l a)

theorem rejectBuffer_projection (l : C.Connection) (a : Fin r → Bool) (j : Fin 2) :
    (fun v => v j) '' C.rejectBuffer l a = C.sourceForm l '' C.primarySet (C.connectionSource l) a := by
  classical
  rw [C.source_truth_image]
  unfold rejectBuffer
  split
  · simp
  · exact BufferAlgebra.correlated_projection (C.rejectDestination_nonempty l a) j

theorem rejectBuffer_sum (h : ¬ C.Accepted) (l : C.Connection) (a : (C.connectionMap l).Point) :
    (fun v => v 0 + v 1) '' C.rejectBuffer l ((C.connectionMap l).source a) =
      (fun v => C.rejectConstant (.third l) + C.targetForm l v) ''
        C.primarySet (C.connectionTarget l) ((C.connectionMap l).target a) := by
  classical
  change _ = C.rejectDestination l ((C.connectionMap l).source a)
  unfold rejectBuffer
  split
  · rw [C.rejectDestination_true h l a ‹_›]
    simp
  · exact BufferAlgebra.correlated_sum _

/-- Rejection produces actual nonempty scalar-image sets, including correlated
buffers. This does not assert an unavailable simultaneous global assignment. -/
noncomputable def rejectingImages (h : ¬ C.Accepted) : C.schemas.SpecialImages C.rejectConstant where
  values p a := match p with
    | .primary p => C.primarySet p a
    | .buffer l => C.rejectBuffer l a
    | .dummy => Set.univ
  nonempty p a := by
    cases p with
    | primary p => exact BufferAlgebra.truthVectors_nonempty _
    | buffer l => exact C.rejectBuffer_nonempty l a
    | dummy => exact ⟨0, Set.mem_univ _⟩
  equation e a := by
    classical
    cases e with
    | seed z =>
      change sumForm (C.dimension (C.seedType z)) '' C.primarySet (some (C.seedType z))
        ((C.seedMap z).source a) = (fun _ : Fin 1 → Bit => (0 : Bit)) '' Set.univ
      have ht : C.True (C.seedType z) ((C.seedMap z).source a) := fun j => PortTrue.seed z a j
      have hs := BufferAlgebra.sum_truth (C.PortTrue (C.seedType z) ((C.seedMap z).source a))
      rw [ite_eq_left (show ∀ j, C.PortTrue (C.seedType z) ((C.seedMap z).source a) j from ht)] at hs
      rw [show ⇑(sumForm (C.dimension (C.seedType z))) = (fun v => ∑ j, v j) from funext (sumForm_apply _)]
      simpa using hs
    | first l =>
      change C.sourceForm l '' C.primarySet (C.connectionSource l) ((C.connectionMap l).source a) =
        (fun v : Fin 2 → Bit => 0 + v 0) '' C.rejectBuffer l ((C.connectionMap l).source a)
      simpa only [zero_add] using (C.rejectBuffer_projection l ((C.connectionMap l).source a) 0).symm
    | second l =>
      change C.sourceForm l '' C.primarySet (C.connectionSource l) ((C.connectionMap l).source a) =
        (fun v : Fin 2 → Bit => 0 + v 1) '' C.rejectBuffer l ((C.connectionMap l).source a)
      simpa only [zero_add] using (C.rejectBuffer_projection l ((C.connectionMap l).source a) 1).symm
    | third l => exact C.rejectBuffer_sum h l a

end ProductCircuit

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine

abbrev Letter (M : Machine) := M.Symbol × Option M.State

/-- A completely fixed radius-one alphabet table. The arbitrary multihead cases
are settled by center, then left, then right priority. -/
def localRule (M : Machine) (a b c : M.Letter) : M.Letter :=
  let written := match b.2 with
    | none => b.1
    | some q => (M.action q b.1).2.1
  let head := match b.2 with
    | some q => if (M.action q b.1).2.2 = .stay then some (M.action q b.1).1 else none
    | none => match a.2 with
      | some q => if (M.action q a.1).2.2 = .right then some (M.action q a.1).1 else
          match c.2 with
          | none => none
          | some q => if (M.action q c.1).2.2 = .left then some (M.action q c.1).1 else none
      | none => match c.2 with
        | none => none
        | some q => if (M.action q c.1).2.2 = .left then some (M.action q c.1).1 else none
  (written, head)

namespace TapeConfig
variable {M : Machine} {X : Type} [DecidableEq X]

def letter (c : M.TapeConfig X) (x : X) : M.Letter :=
  (c.tape x, if x = c.head then some c.state else none)

end TapeConfig

end Machine

namespace Machine
open BinaryAddress

abbrev InitialSeed (d : ℕ) (w : Word) := Fin (inputSpan w) ⊕ ThresholdCase (ofNat d (inputSpan w))

def initialSeedLetter (M : Machine) (d : ℕ) (w : Word) : InitialSeed d w → M.Letter
  | .inl i => ((M.ringInitial w).letter (ofNat d i.val))
  | .inr _ => (0, none)

def initialSeedMap (d : ℕ) (w : Word) : InitialSeed d w → ProductMap d
  | .inl i => ProductMap.singleton (ofNat d i.val) (ofNat d i.val)
  | .inr h => thresholdMap (ofNat d (inputSpan w)) h

/-- The concrete compressed tableau, now with no semantic seed assumption. -/
noncomputable abbrev compiledCircuit (M : Machine) (d : ℕ) (w : Word) :=
  { CellularCircuit.circuit M.localRule (M.initialSeedLetter d w) (initialSeedMap d w)
    (fun a => a.2 = some 1) with
    seedIndex := NaturalCode.sum (NaturalCode.fin (inputSpan w))
      (NaturalCode.option (NaturalCode.subtype (NaturalCode.fin d) _)) }

end Machine

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachineReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace Machine
open BinaryAddress

def actionConfig (M : Machine) (c : Configuration M) : Configuration M :=
  let a := M.action c.state (c.tape c.head)
  { state := a.1
    head := c.head + a.2.2.displacement
    tape := Function.update c.tape c.head a.2.1 }

structure RingAgrees (M : Machine) (d T : ℕ) (c : Configuration M) (q : M.TapeConfig (Bits d)) : Prop where
  state : c.state = q.state
  head : residue d c.head = q.head
  tape : ∀ z : ℤ, -(T : ℤ) ≤ z ∧ z ≤ T → c.tape z = q.tape (residue d z)

end Machine

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

/-- The fixed-width output construction, with private-wire length absorbed. -/
noncomputable def outputGraph (hr : 32 ≤ r) : Graph :=
  (((C.schemas.layout (4 * (r + 1) - 1)).affine (by omega)).graph 0)

end ProductCircuit

namespace Machine

noncomputable def reductionGraph (M : Machine) (C e : ℕ) (w : Word) : Graph := by
  classical
  exact (M.compiledCircuit (addressWidth C e w.length) w).outputGraph
    (by change 32 ≤ reductionDimension C e w.length; have := reductionDimension_ge C e w.length; omega)

end Machine

/-- Canonical most-significant-first binary representation. -/
def binaryWord (n : ℕ) : Word := n.bits.reverse

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StackMachines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

/- A finite-alphabet parallel-stack interpreter, with local one-tape execution.
All stored registers below range over a fixed finite type; no unbounded value is
hidden in a transition table. The only unbounded data are the literal bit stk. -/
namespace StackModel

variable {K Λ R : Type} [DecidableEq K]

def initial (P : Program K Λ R) (input : K) (w : Word) : Config K Λ R :=
  ⟨.inr P.main, P.initialStore, Function.update (fun _ => []) input w⟩

def run (P : Program K Λ R) (input : K) (w : Word) (t : ℕ) : Config K Λ R :=
  (step P)^[t] (initial P input w)

variable [Fintype K] [Fintype Λ] [Fintype R]

noncomputable def config (P : Program K Λ R) (input : K) (p : Phase K Λ R) (z : ℤ)
    (S : K → Word) : Configuration (compile P input) := ⟨state p, z, tape input S⟩

end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.TapeCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel
variable {K Λ R : Type} [DecidableEq K] [Fintype K] [Fintype Λ] [Fintype R]
    (P : Program K Λ R) (input : K)

noncomputable def encodeConfig (c : Config K Λ R) : Configuration (compile P input) where
  state := match c.control with
    | .inl b => if b then 1 else 2
    | .inr l => state (.ready l c.store)
  head := 0
  tape := tape input c.stk

end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.StackCommands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel

namespace Instruction
variable {K R A B : Type}
def map (f : A → B) : Instruction K A R → Instruction K B R
  | .push k value next => .push k value (f next)
  | .pop k store next => .pop k store (f next)
  | .modify store next => .modify store (f next)
  | .branch test yes no => .branch test (f yes) (f no)
  | .halt b => .halt b

@[simp] theorem map_map {C : Type} (f : A → B) (g : B → C) (i : Instruction K A R) :
    map g (map f i) = map (g ∘ f) i := by cases i <;> rfl
@[simp] theorem map_id (i : Instruction K A R) : map id i = i := by cases i <;> rfl
end Instruction

namespace Command
variable {K R : Type}

def code : (c : Command K R) → Control c → Instruction K (Option (Control c)) R
  | .skip, _ => .modify id none
  | .push k f, _ => .push k f none
  | .pop k f, _ => .pop k f none
  | .modify f, _ => .modify f none
  | .seq c d, .inl x => (c.code x).map (fun a => a.elim (some (.inr d.entry)) (some ∘ Sum.inl))
  | .seq _ d, .inr x => (d.code x).map (Option.map Sum.inr)
  | .branch test c d, .inl _ => .branch test (some (.inr (.inl c.entry))) (some (.inr (.inr d.entry)))
  | .branch _ c _, .inr (.inl x) => (c.code x).map (Option.map (Sum.inr ∘ Sum.inl))
  | .branch _ _ d, .inr (.inr x) => (d.code x).map (Option.map (Sum.inr ∘ Sum.inr))
  | .while test c, .inl _ => .branch test (some (.inr c.entry)) none
  | .while _ c, .inr x => (c.code x).map (fun a => a.elim (some (.inl ())) (some ∘ Sum.inr))

def program (c : Command K R) (s : R) : Program K (Option (Control c)) R where
  main := some c.entry
  initialStore := s
  code
    | none => .halt true
    | some x => c.code x

/-- Execution costs count actual finite-control stack instructions. -/
inductive Exec [DecidableEq K] : Command K R → R → (K → Word) → R → (K → Word) → ℕ → Prop
  | skip (s S) : Exec .skip s S s S 1
  | push (k f s S) : Exec (.push k f) s S s (Function.update S k (S k ++ [f s])) 1
  | pop (k f s S) : Exec (.pop k f) s S (f s (S k).getLast?) (Function.update S k (S k).dropLast) 1
  | modify (f s S) : Exec (.modify f) s S (f s) S 1
  | seq {c d s S t T u U a b} : Exec c s S t T a → Exec d t T u U b →
      Exec (.seq c d) s S u U (b + a)
  | branch_true {test c d s S t T n} : test s = true → Exec c s S t T n →
      Exec (.branch test c d) s S t T (n + 1)
  | branch_false {test c d s S t T n} : test s = false → Exec d s S t T n →
      Exec (.branch test c d) s S t T (n + 1)
  | while_false (test c s S) : test s = false → Exec (.while test c) s S s S 1
  | while_true {test c s S t T u U a b} : test s = true → Exec c s S t T a →
      Exec (.while test c) t T u U b → Exec (.while test c) s S u U (b + a + 1)

variable [DecidableEq K] {Λ : Type}

/-- A compositional (not oracle) embedding of all source control locations. -/
def Embeds (P : Program K Λ R) (c : Command K R) (e : Control c → Λ) (next : Λ) : Prop :=
  ∀ x, P.code (e x) = (c.code x).map (fun a => a.elim next e)

end Command
end StackModel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FiniteRefinement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace FiniteWL

def neighbor (G H : Graph) (s : ℕ) : Fin G.order ⊕ Fin H.order → NeighborColor s :=
  Sum.elim (neighborColor G s) (neighborColor H s)

def neighbors (G H : Graph) : Fin G.order ⊕ Fin H.order → Multiset (Fin G.order ⊕ Fin H.order)
  | .inl x => (Finset.univ.filter (fun y => G.edge x y = true)).val.map Sum.inl
  | .inr x => (Finset.univ.filter (fun y => H.edge x y = true)).val.map Sum.inr

def tuple (G H : Graph) (k s : ℕ) :
    (Fin k → Fin G.order) ⊕ (Fin k → Fin H.order) → TupleColor k s :=
  Sum.elim (tupleColor G k s) (tupleColor H k s)

def vectors (G H : Graph) (k : ℕ) :
    (Fin k → Fin G.order) ⊕ (Fin k → Fin H.order) →
      Multiset (Fin k → ((Fin k → Fin G.order) ⊕ (Fin k → Fin H.order)))
  | .inl x => Finset.univ.val.map (fun z i => Sum.inl (Function.update x i z))
  | .inr x => Finset.univ.val.map (fun z i => Sum.inr (Function.update x i z))

end FiniteWL

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordCommands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel
namespace Command
variable {K : Type} [DecidableEq K]

def appendMany (ks : List K) (b : Bool) (S : K → Word) : K → Word :=
  fun k => if k ∈ ks then S k ++ [b] else S k

def fanEffect (a : K) (ks : List K) (S : K → Word) : K → Word :=
  fun k => if k = a then [] else if k ∈ ks then S k ++ (S a).reverse else S k

end Command
end StackModel
namespace StackModel.Command
variable {K L R : Type}

variable [DecidableEq K] [DecidableEq L]

/-- Renaming uses only the named stacks; arbitrary ambient data are framed. -/
theorem Exec.rename {c : Command K R} {s S t T n} (h : Exec c s S t T n)
    (e : K ↪ L) (W : L → Word) (hW : W ∘ e = S) :
    ∃ U, Exec (c.rename e) s W t U n ∧ U ∘ e = T ∧
      ∀ l, (∀ k, e k ≠ l) → U l = W l := by
  induction h generalizing W with
  | skip s S => exact ⟨W, .skip _ _, hW, by intros; rfl⟩
  | modify f s S => exact ⟨W, .modify _ _ _, hW, by intros; rfl⟩
  | push k f s S =>
    let U := Function.update W (e k) (W (e k) ++ [f s])
    refine ⟨U, .push _ _ _ _, ?_, ?_⟩
    · have hval : W (e k) = S k := congrFun hW k
      simp only [U, Function.update_comp_eq_of_injective W e.injective, hW, hval]
    · intro l hl
      exact Function.update_of_ne (hl k).symm _ _
  | pop k f s S =>
    let U := Function.update W (e k) (W (e k)).dropLast
    have hval : W (e k) = S k := congrFun hW k
    refine ⟨U, ?_, ?_, ?_⟩
    · simpa only [Command.rename, U, ← hval] using Exec.pop (e k) f s W
    · simp only [U, Function.update_comp_eq_of_injective W e.injective, hW, hval]
    · intro l hl
      exact Function.update_of_ne (hl k).symm _ _
  | seq hc hd ihc ihd =>
    obtain ⟨V, hV, heV, hfV⟩ := ihc W hW
    obtain ⟨U, hU, heU, hfU⟩ := ihd V heV
    exact ⟨U, .seq hV hU, heU, fun l hl => (hfU l hl).trans (hfV l hl)⟩
  | branch_true ht hc ih =>
    obtain ⟨U, hU, heU, hfU⟩ := ih W hW
    exact ⟨U, .branch_true ht hU, heU, hfU⟩
  | branch_false ht hc ih =>
    obtain ⟨U, hU, heU, hfU⟩ := ih W hW
    exact ⟨U, .branch_false ht hU, heU, hfU⟩
  | while_false test c s S ht => exact ⟨W, .while_false _ _ _ _ ht, hW, by intros; rfl⟩
  | while_true ht hc hd ihc ihd =>
    obtain ⟨V, hV, heV, hfV⟩ := ihc W hW
    obtain ⟨U, hU, heU, hfU⟩ := ihd V heV
    exact ⟨U, .while_true ht hV hU, heU, fun l hl => (hfU l hl).trans (hfV l hl)⟩

end StackModel.Command

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordExpressions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions

namespace Expr

open StackModel.Command

/-- The result register is separate from immutable inputs; all temporary
register numbers are at least `base` and are cleared before return. -/
def code : {n : ℕ} → Expr n → (Fin n → ℕ) → ℕ → ℕ → StackModel.Command ℕ (Option Bool)
  | _, .var i, env, out, base => copy (env i) out base
  | _, .nil, _, out, _ => clear out
  | _, .snoc e b, env, out, base => .seq (e.code env out base) (.push out (fun _ => b))
  | _, .drop e, env, out, base => .seq (e.code env out base) (.pop out (fun _ _ => none))
  | _, .cases e p q r, env, out, base =>
      .seq (e.code env base (base+1))
        (.seq (StackModel.Command.read base)
          (.seq (.branch Option.isSome
             (.branch (fun x => x.getD false) (r.code env out (base+1)) (q.code env out (base+1)))
             (p.code env out (base+1))) (clear base)))
  | _, .bind e f, env, out, base =>
      .seq (e.code env base (base+1))
        (.seq (f.code (Fin.snoc env base) out (base+1)) (clear base))
  | _, .loop c a f, env, out, base =>
      .seq (c.code env base (base+1))
        (.seq (a.code env out (base+1))
          (.seq (drain base
            (.seq (copy out (base+2) (base+3))
              (.seq (f.code (Fin.snoc (Fin.snoc env (base+1)) (base+2)) out (base+3))
                (.seq (clear (base+2)) (.push (base+1) (fun _ => false))))))
            (clear (base+1))))

def cost : {n : ℕ} → Expr n → ℕ → ℕ
  | _, .var _, B => 12*B+8
  | _, .nil, B => 3*B+2
  | _, .snoc e _, B | _, .drop e, B => e.cost B+1
  | _, .cases e p q r, B => e.cost B + max (p.cost B) (max (q.cost B) (r.cost B)) + 3*B+5
  | _, .bind e f, B => e.cost B+f.cost B+3*B+2
  | _, .loop c a f, B => c.cost B+a.cost B+(f.cost B+12*B+13)*B+3*B+4

end Expr
end WordExpressions
namespace WordExpressions.Expr
open StackModel.Command

def Clean (S : ℕ → Word) (b : ℕ) : Prop := ∀ i, b ≤ i → S i = []

theorem Clean.update {S b k w} (h : Clean S b) (hk : k < b) : Clean (Function.update S k w) b := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact h i hi

def Correct {n} (e : Expr n) : Prop :=
  ∀ (B : ℕ) (S : ℕ → Word) (env : Fin n → ℕ) (out base : ℕ),
    out < base → (∀ i, env i < base ∧ env i ≠ out) → Clean S base → (S out).length ≤ B →
    e.Bounded (S ∘ env) B → ∀ s : Option Bool,
      ∃ t ≤ e.cost B, Exec (e.code env out base) s S none
        (Function.update S out (e.eval (S ∘ env))) t

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionCompiler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace StackModel.Command
variable {R : Type}

/-- A three-instruction output test after a structured command, followed by a
literal accepting or rejecting stack-machine halt. -/
def testProgram {K : Type} (c : Command K (Option Bool)) (s : Option Bool) (out : K) :
    Program K (Option (Control c) ⊕ (Bool ⊕ Unit)) (Option Bool) where
  main := .inl (some c.entry)
  initialStore := s
  code
    | .inl (some x) => (c.code x).map Sum.inl
    | .inl none => .pop out (fun _ b => b) (.inr (.inr ()))
    | .inr (.inr _) => .branch (fun b => b.getD false) (.inr (.inl true)) (.inr (.inl false))
    | .inr (.inl b) => .halt b

end StackModel.Command

namespace WordExpressions.Expr
open ComputationBounds

def outputBound {n} (e : Expr n) (B : ℕ) : ℕ :=
  2+(e.cost B+15*B+13)*(2*(B+(e.cost B+15*B+13))+3)

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExpressionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.Expr
open StackModel.Command

def outputCode (e : Expr 1) : StackModel.Command ℕ (Option Bool) :=
  .seq (e.code (fun _ => 0) 1 2) (.seq (clear 0) (.seq (copy 1 0 2) (clear 1)))

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.WordArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions

namespace NatPoly
variable {n : ℕ}

theorem pow_const {f : (Fin n → Word) → ℕ} (hf : NatPoly f) (d : ℕ) : NatPoly (fun S => (f S)^d) := by
  induction d with
  | zero => simpa using const 1
  | succ d ih => simpa only [pow_succ] using mul ih hf

end NatPoly

end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PolynomialArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
namespace Poly
variable {n : ℕ}

theorem reverse {w : (Fin n → Word) → Word} (hw : Poly w) : Poly (fun S => (w S).reverse) := by
  have hp := nth (rename hw Fin.castSucc)
    (NatPoly.sub (NatPoly.length (rename hw Fin.castSucc)) (NatPoly.succ (NatPoly.var (Fin.last n))))
  apply (tabulate (NatPoly.length hw) hp).congr
  intro S
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_map, List.getElem_range, Fin.snoc_last, unary, List.length_replicate,
    snoc_prefix]
  have hi' : i < (w S).length := by simpa using hj
  rw [List.getElem?_eq_getElem (by omega)]
  simp only [Option.getD_some, List.getElem_reverse, Nat.sub_sub, Nat.add_comm]

end Poly
end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FiniteEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions.Expr
open StackModel.Command ComputationBounds

def decisionBound {n} (e : Expr n) (B : ℕ) : ℕ :=
  2+(e.cost B+15*B+15)*(2*(B+(e.cost B+15*B+15))+3)

end WordExpressions.Expr

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.ExponentialComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace WordExpressions
open ComputationBounds

/-- One-exponential realizability by a single finite word expression, with
an explicit bound on all its intermediate words. -/
def Exp {n : ℕ} (f : (Fin n → Word) → Word) : Prop :=
  ∃ (e : Expr n) (B : ℕ → ℕ), Exponential B ∧
    (∀ S, e.eval S = f S) ∧
    ∀ S N, (∀ i, (S i).length ≤ N) → e.Bounded S (B N)

end WordExpressions

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.NumericKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericKernel

variable {N width branch : ℕ} (D : Data N width branch)

def Encoded (active trans : Word) : Prop :=
  (∀ (a : Fin N) (z : Fin branch), lookup active a z = D.active a z) ∧
  (∀ (a : Fin N) (z : Fin branch) (i : Fin width) (y : Fin N),
    trans[Nat.pair a (Nat.pair z (Nat.pair i y))]?.getD false = decide (D.next a z i = y))

def Represents (W : Word) (R : Fin N → Fin N → Bool) : Prop :=
  ∀ a b : Fin N, lookup W a b = R a b

end NumericKernel

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.GraphEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericGraph

abbrev ofWord (n : ℕ) (W : Word) (h : simple n W = true) : Graph where
  order := n
  edge i j := edge n W i j
  symmetric := (simple_true n W).mp h |>.2
  loopless := (simple_true n W).mp h |>.1

def mateGraph (n mask : ℕ) : Graph where
  order := n
  edge i j := mateEdge n mask i j
  symmetric i j := by simp only [mateEdge, ne_comm, min_comm, max_comm]
  loopless i := by simp [mateEdge]

end NumericGraph

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RefinementCorrectness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericWL
open NumericKernel

@[simp] theorem left_inl (t : ℕ) (x : Fin t) : left t (sides t (.inl x)) = true := by
  simp [left, x.isLt]
@[simp] theorem left_inr (t : ℕ) (x : Fin t) : left t (sides t (.inr x)) = false := by
  simp [left]
@[simp] theorem code_inl (t : ℕ) (x : Fin t) : code t (sides t (.inl x)) = x.val := by
  simp [code, x.isLt]
@[simp] theorem code_inr (t : ℕ) (x : Fin t) : code t (sides t (.inr x)) = x.val := by
  simp [code]

def neighborData (n : ℕ) (W V : Word) : Data (n+n) 1 n where
  active a z := neighborActive n W V a z
  next a z _ := sides n (match (sides n).symm a with | .inl _ => .inl z | .inr _ => .inr z)

def nc (n : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : Fin (n+n)) : NeighborColor s :=
  FiniteWL.neighbor (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) s ((sides n).symm a)

end NumericWL

namespace NumericWL
open NumericKernel

def te (n k : ℕ) : tuples n k ≃ Fin (n^k+n^k) :=
  (Equiv.sumCongr finFunctionFinEquiv finFunctionFinEquiv).trans (sides (n^k))

@[simp] theorem te_inl (n k : ℕ) (v : Fin k → Fin n) :
    te n k (.inl v) = sides (n^k) (.inl (finFunctionFinEquiv v)) := rfl
@[simp] theorem te_inr (n k : ℕ) (v : Fin k → Fin n) :
    te n k (.inr v) = sides (n^k) (.inr (finFunctionFinEquiv v)) := rfl

@[simp] theorem te_symm_inl (n k : ℕ) (x : Fin (n^k)) :
    (te n k).symm (sides (n^k) (.inl x)) = .inl (finFunctionFinEquiv.symm x) := by
  change Sum.map finFunctionFinEquiv.symm finFunctionFinEquiv.symm
    ((sides (n^k)).symm ((sides (n^k)) _)) = _
  rw [Equiv.symm_apply_apply]
  rfl
@[simp] theorem te_symm_inr (n k : ℕ) (x : Fin (n^k)) :
    (te n k).symm (sides (n^k) (.inr x)) = .inr (finFunctionFinEquiv.symm x) := by
  change Sum.map finFunctionFinEquiv.symm finFunctionFinEquiv.symm
    ((sides (n^k)).symm ((sides (n^k)) _)) = _
  rw [Equiv.symm_apply_apply]
  rfl

def tupleData (n k : ℕ) : Data (n^k+n^k) k n where
  active _ _ := true
  next a z i := te n k (match (te n k).symm a with
    | .inl v => .inl (Function.update v i z)
    | .inr v => .inr (Function.update v i z))

end NumericWL

namespace NumericWL
open NumericKernel

def tc (n k : ℕ) (W V : Word) (hW : NumericGraph.simple n W = true) (hV : NumericGraph.simple n V = true)
    (s : ℕ) (a : Fin (n^k+n^k)) : TupleColor k s :=
  FiniteWL.tuple (NumericGraph.ofWord n W hW) (NumericGraph.ofWord n V hV) k s ((te n k).symm a)

end NumericWL

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.DimensionDecider
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace NumericGraph

@[simp] theorem ofWord_matrixWord (G : Graph) : ofWord G.order (matrixWord G) (simple_matrixWord G) = G := by
  apply Graph.ext (ofWord G.order (matrixWord G) (simple_matrixWord G)) G rfl
  intro i j
  exact edge_matrixWord G i j

@[simp] theorem mate_simple (n x : ℕ) : simple n (mate n x) = true := by
  apply (simple_true _ _).mpr
  constructor
  · intro i; rw [edge_mate]; exact (mateGraph n x).loopless i
  · intro i j; rw [edge_mate, edge_mate]; exact (mateGraph n x).symmetric i j

@[simp] theorem ofWord_mate (n x : ℕ) : ofWord n (mate n x) (mate_simple n x) = mateGraph n x := by
  apply Graph.ext (ofWord n (mate n x) (mate_simple n x)) (mateGraph n x) rfl
  exact edge_mate n x

end NumericGraph

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.FinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
/- Polynomially presented finite types. Membership refers to actual natural
codes and all iteration bounds have literal unary word realizers. -/

namespace FinitePresentation
open WordExpressions
variable {A : Word → Type}

namespace PresentedGraph
variable {P : Presented A} {G : ∀ w, SimpleGraph (A w)} (Q : PresentedGraph P G)

noncomputable def graph (w : Word) : Graph where
  order := P.card w
  edge i j := Q.adjacent w (P.select w i) (P.select w j)
  symmetric i j := by
    rw [← P.code_decode w i, ← P.code_decode w j]
    apply Bool.eq_iff_iff.mpr
    rw [Q.adjacent_iff, Q.adjacent_iff, (G w).adj_comm]
  loopless i := by
    rw [← P.code_decode w i]
    apply Bool.eq_false_iff.mpr
    intro h
    exact (G w).loopless.irrefl _ ((Q.adjacent_iff w _ _).mp h)

end PresentedGraph
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.PresentationArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification

namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}

namespace Test
variable {P : Presented A} {f g : ∀ w, A w → Bool}

def numLt {f g : ∀ w, A w → ℕ} (F : Number P f) (G : Number P g) : Test P (fun w x => decide (f w x<g w x)) :=
  ⟨fun w i => decide (F.eval w i<G.eval w i), fun w x => by rw [F.correct,G.correct], NatPoly.lt F.poly G.poly⟩

end Test
end FinitePresentation

namespace FinitePresentation
open WordExpressions
variable {A B C : Word → Type}

namespace Map
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def inl (P : Presented A) (Q : Presented B) : Map P (P.sum Q) (fun _ x => Sum.inl x) :=
  (Number.const P 2).mul (Number.code P)

def inr (P : Presented A) (Q : Presented B) : Map Q (P.sum Q) (fun _ x => Sum.inr x) :=
  ((Number.const Q 2).mul (Number.code Q)).add (Number.const Q 1)

def some (P : Presented A) : Map P P.option (fun _ x => some x) := (Number.code P).add (Number.const P 1)

def untype (P : Presented A) (e : ∀ w, B w ≃ A w) : Map P (P.retype e) (fun w x => (e w).symm x) :=
  (Number.code P).congr (by intro w x; change P.code w x=P.code w (e w ((e w).symm x)); rw [Equiv.apply_symm_apply])

def coe (P : Presented A) (p : ∀ w, A w → Prop) [∀ w x, Decidable (p w x)]
    (H : Test P (fun w x => decide (p w x))) : Map (P.restrict p H) P (fun _ x => x.val) :=
  Number.code (P.restrict p H)

end Map
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.LeafPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions

namespace PresentedGraph
variable {A : Word → Type} {P : Presented A} {G : ∀ w, SimpleGraph (A w)} (Q : PresentedGraph P G)

def matrix (w : Word) : Word := (List.range (P.card w * P.card w)).map
  (fun i => Q.adjacent w (P.select w (i/P.card w)) (P.select w (i%P.card w)))

def output (k : Word → ℕ) (w : Word) : Word :=
  List.replicate (P.card w) true ++ [false] ++ Q.matrix w ++ binaryWord (k w)

end PresentedGraph
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RingCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation.RingRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

theorem firstLabel_poly_of {n} {w : (Fin n → Word) → Word} {e i a : (Fin n → Word) → ℕ}
    (hw : Poly w) (he : NatPoly e) (hi : NatPoly i) (ha : NatPoly a) :
    NatPoly (fun S => F.firstLabel (w S) (e S) (i S) (a S)) := by
  have h := F.firstLabel_poly.subst (g := ![w,fun S => unary (e S),fun S => unary (i S),fun S => unary (a S)])
    (by intro j; fin_cases j; exacts [hw,he,hi,ha])
  change NatPoly (fun S => F.firstLabel (w S) (unary (e S)).length (unary (i S)).length (unary (a S)).length) at h
  simpa only [unary, List.length_replicate] using h

theorem secondLabel_poly_of {n} {w : (Fin n → Word) → Word} {e i a : (Fin n → Word) → ℕ}
    (hw : Poly w) (he : NatPoly e) (hi : NatPoly i) (ha : NatPoly a) :
    NatPoly (fun S => F.secondLabel (w S) (e S) (i S) (a S)) := by
  have h := F.secondLabel_poly.subst (g := ![w,fun S => unary (e S),fun S => unary (i S),fun S => unary (a S)])
    (by intro j; fin_cases j; exacts [hw,he,hi,ha])
  change NatPoly (fun S => F.secondLabel (w S) (unary (e S)).length (unary (i S)).length (unary (a S)).length) at h
  simpa only [unary, List.length_replicate] using h

def leftCode (w : Word) (b : ℕ) : ℕ :=
  Nat.pair (F.first.eval w (Nat.unpair b).1) (Nat.pair (Nat.unpair (Nat.unpair b).2).1
    (Nat.pair (F.firstLabel w (Nat.unpair b).1 (Nat.unpair (Nat.unpair b).2).1 (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).1)
      (F.firstLabel w (Nat.unpair b).1 (F.nextRow w (Nat.unpair (Nat.unpair b).2).1) (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).2)))

def rightCode (w : Word) (b : ℕ) : ℕ :=
  Nat.pair (F.second.eval w (Nat.unpair b).1) (Nat.pair (Nat.unpair (Nat.unpair b).2).1
    (Nat.pair (F.secondLabel w (Nat.unpair b).1 (Nat.unpair (Nat.unpair b).2).1 (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).1)
      (F.secondLabel w (Nat.unpair b).1 (F.nextRow w (Nat.unpair (Nat.unpair b).2).1) (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).2)))

def topCode (_F : RingRealizer TP LP r rp R) (b : ℕ) : ℕ :=
  Nat.pair (Nat.unpair b).1 (Nat.pair (Nat.unpair (Nat.unpair b).2).1 (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).1)
def bottomCode (w : Word) (b : ℕ) : ℕ :=
  Nat.pair (Nat.unpair b).1 (Nat.pair (F.nextRow w (Nat.unpair (Nat.unpair b).2).1) (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).2)

theorem leftCode_eq (w : Word) (b : (R w).Square) : F.leftCode w (F.sP.code w b)=F.hP.code w ((R w).leftH b) := by
  simp only [leftCode,F.sP_code,Nat.unpair_pair,F.nextRow_eq,F.firstLabel_eq]
  rw [F.first.correct]
  rfl

theorem rightCode_eq (w : Word) (b : (R w).Square) : F.rightCode w (F.sP.code w b)=F.hP.code w ((R w).rightH b) := by
  simp only [rightCode,F.sP_code,Nat.unpair_pair,F.nextRow_eq,F.secondLabel_eq]
  rw [F.second.correct]
  rfl

theorem topCode_eq (w : Word) (b : (R w).Square) : F.topCode (F.sP.code w b)=F.vP.code w ((R w).topV b) := by
  simp only [topCode,F.sP_code,Nat.unpair_pair]
  rfl

theorem bottomCode_eq (w : Word) (b : (R w).Square) : F.bottomCode w (F.sP.code w b)=F.vP.code w ((R w).bottomV b) := by
  simp only [bottomCode,F.sP_code,Nat.unpair_pair,F.nextRow_eq]
  rfl

theorem leftCode_poly {n} {w : (Fin n → Word) → Word} {b : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) : NatPoly (fun S => F.leftCode (w S) (b S)) := by
  unfold leftCode
  apply NatPoly.pair (F.first.eval_poly hw (NatPoly.unpair_fst hb))
  apply NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
  apply NatPoly.pair
  · exact F.firstLabel_poly_of hw (NatPoly.unpair_fst hb) (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))
  · exact F.firstLabel_poly_of hw (NatPoly.unpair_fst hb) (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb)))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))

theorem rightCode_poly {n} {w : (Fin n → Word) → Word} {b : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) : NatPoly (fun S => F.rightCode (w S) (b S)) := by
  unfold rightCode
  apply NatPoly.pair (F.second.eval_poly hw (NatPoly.unpair_fst hb))
  apply NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
  apply NatPoly.pair
  · exact F.secondLabel_poly_of hw (NatPoly.unpair_fst hb) (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))
  · exact F.secondLabel_poly_of hw (NatPoly.unpair_fst hb) (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb)))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))

variable [∀ w, Fintype (T w)] [∀ w, Fintype (L w)]
noncomputable def hIndex : Number F.hP (fun w x => (R w).hIndex x) where
  eval w i := Nat.pair (F.typeIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by rw [F.hP_code,Nat.unpair_pair,F.typeIndex.correct]; rfl
  poly := NatPoly.pair (F.typeIndex.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
noncomputable def vIndex : Number F.vP (fun w x => (R w).vIndex x) where
  eval w i := Nat.pair (F.linkIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by rw [F.vP_code,Nat.unpair_pair,F.linkIndex.correct]; rfl
  poly := NatPoly.pair (F.linkIndex.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
noncomputable def sIndex : Number F.sP (fun w x => (R w).squareIndex x) where
  eval w i := Nat.pair (F.linkIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by rw [F.sP_code,Nat.unpair_pair,F.linkIndex.correct]; rfl
  poly := NatPoly.pair (F.linkIndex.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))

noncomputable def hcIndex : Number (F.hP.finSigma F.hDim) (fun w x => Nat.pair ((R w).hIndex x.1) x.2.val) where
  eval w i := Nat.pair (F.hIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by
    change Nat.pair (F.hIndex.eval w (Nat.unpair (Nat.pair _ _)).1) (Nat.unpair (Nat.pair _ _)).2=_
    rw [Nat.unpair_pair,F.hIndex.correct]
    rfl
  poly := NatPoly.pair (F.hIndex.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))

noncomputable def colors : Number (F.cP.sum F.bP) (fun w x => (R w).colorIndex x) := by
  let hc := (Number.const (F.hP.finSigma F.hDim) 2).mul F.hcIndex
  let vc := ((Number.const F.vP 2).mul F.vIndex).add (Number.const F.vP 1)
  let bc := Number.sumCases ((Number.const F.hP 2).mul F.hIndex) (((Number.const F.sP 2).mul F.sIndex).add (Number.const F.sP 1))
  exact (Number.sumCases ((Number.const F.cP 2).mul (Number.sumCases hc vc))
    (((Number.const F.bP 2).mul bc).add (Number.const F.bP 1))).congr (by intro w x; cases x with
      | inl c => cases c <;> rfl
      | inr b => cases b <;> rfl)

end FinitePresentation.RingRealizer
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RingMembership
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation.RingRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

theorem hCoord_iff (_F : RingRealizer TP LP r rp R) (w : Word) (h : (R w).HName) (k : Σ h : (R w).HName, Fin ((R w).dimension h.1)) :
    Sum.inl k∈(R w).hCoords h ↔ k.1=h := by
  simp only [RingLayout.hCoords, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j,hj⟩
    exact (congrArg Sigma.fst (Sum.inl.inj hj)).symm
  · intro eh
    rcases k with ⟨k,j⟩
    dsimp only at eh
    subst k
    exact ⟨j,rfl⟩

theorem vCoord_iff (_F : RingRealizer TP LP r rp R) (w : Word) (h : (R w).HName) (v : (R w).VName) :
    Sum.inr v∈(R w).hCoords h ↔ False := by
  simp [RingLayout.hCoords]

def memberEval (w : Word) (b c : ℕ) : Bool :=
  if b%2=0 then if c%2=0 then decide ((Nat.unpair (c/2)).1=b/2) else false
  else if c%2=0 then decide ((Nat.unpair (c/2)).1=F.leftCode w (b/2)) || decide ((Nat.unpair (c/2)).1=F.rightCode w (b/2))
  else decide (c/2=F.topCode (b/2)) || decide (c/2=F.bottomCode w (b/2))

theorem member_ee (w : Word) (b c : ℕ) : F.memberEval w (2*b) (2*c)=decide ((Nat.unpair c).1=b) := by
  simp [memberEval]
theorem member_eo (w : Word) (b c : ℕ) : F.memberEval w (2*b) (2*c+1)=false := by
  simp [memberEval]
theorem member_oe (w : Word) (b c : ℕ) : F.memberEval w (2*b+1) (2*c)=
    (decide ((Nat.unpair c).1=F.leftCode w b) || decide ((Nat.unpair c).1=F.rightCode w b)) := by
  simp [memberEval,AffineRealizer.odd_half]
theorem member_oo (w : Word) (b c : ℕ) : F.memberEval w (2*b+1) (2*c+1)=
    (decide (c=F.topCode b) || decide (c=F.bottomCode w b)) := by
  simp [memberEval,AffineRealizer.odd_half]

theorem memberEval_poly {n} {w : (Fin n → Word) → Word} {b c : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hc : NatPoly c) : BoolPoly (fun S => F.memberEval (w S) (b S) (c S)) := by
  have hb2 := NatPoly.div hb (NatPoly.const 2)
  have hc2 := NatPoly.div hc (NatPoly.const 2)
  have hb0 := NatPoly.eqtest (NatPoly.mod hb (NatPoly.const 2)) (NatPoly.const 0)
  have hc0 := NatPoly.eqtest (NatPoly.mod hc (NatPoly.const 2)) (NatPoly.const 0)
  unfold memberEval
  apply BoolPoly.iteProp hb0
  · exact BoolPoly.iteProp hc0 (NatPoly.eqtest (NatPoly.unpair_fst hc2) hb2) (BoolPoly.const false)
  · apply BoolPoly.iteProp hc0
    · exact BoolPoly.or (NatPoly.eqtest (NatPoly.unpair_fst hc2) (F.leftCode_poly hw hb2))
        (NatPoly.eqtest (NatPoly.unpair_fst hc2) (F.rightCode_poly hw hb2))
    · apply BoolPoly.or
      · exact NatPoly.eqtest hc2 (NatPoly.pair (NatPoly.unpair_fst hb2)
          (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb2))
          (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb2)))))
      · exact NatPoly.eqtest hc2 (NatPoly.pair (NatPoly.unpair_fst hb2)
          (NatPoly.pair (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb2)))
          (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb2)))))

noncomputable def member : Test (F.bP.prod F.cP) (fun w x => decide (x.2∈(R w).coordinates x.1)) where
  eval w i := F.memberEval w (Nat.unpair i).1 (Nat.unpair i).2
  correct w x := by
    rcases x with ⟨b,c⟩
    change F.memberEval w (Nat.unpair (Nat.pair (F.bP.code w b) (F.cP.code w c))).1 (Nat.unpair (Nat.pair (F.bP.code w b) (F.cP.code w c))).2=_
    rw [Nat.unpair_pair]
    cases b with
    | inl h => cases c with
      | inl k =>
        rw [F.bP_inl,F.cP_inl,F.member_ee,Nat.unpair_pair]
        apply Bool.eq_iff_iff.mpr
        simp only [RingLayout.coordinates]
        simp only [decide_eq_true_eq]
        constructor
        · intro he
          exact decide_eq_true ((F.hCoord_iff w h k).mpr ((F.hP.code w).injective he))
        · intro he
          exact congrArg (F.hP.code w) ((F.hCoord_iff w h k).mp (of_decide_eq_true he))
      | inr v =>
        rw [F.bP_inl,F.cP_inr,F.member_eo]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.false_eq_true,decide_eq_true_eq,RingLayout.coordinates,F.vCoord_iff]
    | inr b => cases c with
      | inl k =>
        rw [F.bP_inr,F.cP_inl,F.member_oe,Nat.unpair_pair,F.leftCode_eq,F.rightCode_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true,decide_eq_true_eq,(F.hP.code w).injective.eq_iff,
          RingLayout.coordinates,Finset.mem_union,F.hCoord_iff,Finset.mem_insert,Finset.mem_singleton,Sum.inl_ne_inr,or_false]
      | inr v =>
        rw [F.bP_inr,F.cP_inr,F.member_oo,F.topCode_eq,F.bottomCode_eq]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true,decide_eq_true_eq,(F.vP.code w).injective.eq_iff,
          RingLayout.coordinates,Finset.mem_union,F.vCoord_iff,Finset.mem_insert,Finset.mem_singleton,Sum.inr.injEq,false_or]
  poly := F.memberEval_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.unpair_snd (NatPoly.var 1))

noncomputable def localData : Locals F.cP F.bP :=
  ⟨fun w => (R w).coordinates, fun w b => (R w).coordinates_card b, F.member⟩

end FinitePresentation.RingRealizer
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.RingLegality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation.RingRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

noncomputable def readH (w : Word) (b v h j : ℕ) : ℕ := F.localData.read w b v (2*Nat.pair h j)
noncomputable def readV (w : Word) (b v c : ℕ) : ℕ := F.localData.read w b v (2*c+1)

theorem readH_cast (w : Word) (b v h j : ℕ) : ((F.readH w b v h j : ℕ) : Bit).val=F.readH w b v h j := by
  simp only [readH,Locals.read,NumericKernel.digit,ZMod.val_natCast,Nat.mod_mod]

theorem leftVector (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    vectorTwo ((R w).dimension ((R w).first b.1))
      ((F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 0 : Bit),
       (F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 1 : Bit)) =
      fun j => v ⟨.inl ⟨(R w).leftH b,j⟩,(R w).left_mem b j⟩ := by
  funext j
  apply ZMod.val_injective 2
  have hj : j.val=0 ∨ j.val=1 := by
    have hd := (R w).dimension_bound ((R w).first b.1)
    have hi := j.isLt
    rcases hd with hd|hd <;> omega
  have hh := F.localData.read_value w (.inr b) v ⟨.inl ⟨(R w).leftH b,j⟩,(R w).left_mem b j⟩
  change F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) j.val=_ at hh
  rcases hj with hj|hj <;> simp only [vectorTwo,hj,reduceIte,Nat.one_ne_zero,F.readH_cast] <;> simpa only [hj] using hh

theorem rightVector (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    vectorTwo ((R w).dimension ((R w).second b.1))
      ((F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 0 : Bit),
       (F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 1 : Bit)) =
      fun j => v ⟨.inl ⟨(R w).rightH b,j⟩,(R w).right_mem b j⟩ := by
  funext j
  apply ZMod.val_injective 2
  have hj : j.val=0 ∨ j.val=1 := by
    have hd := (R w).dimension_bound ((R w).second b.1)
    have hi := j.isLt
    rcases hd with hd|hd <;> omega
  have hh := F.localData.read_value w (.inr b) v ⟨.inl ⟨(R w).rightH b,j⟩,(R w).right_mem b j⟩
  change F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) j.val=_ at hh
  rcases hj with hj|hj <;> simp only [vectorTwo,hj,reduceIte,Nat.one_ne_zero,F.readH_cast] <;> simpa only [hj] using hh

noncomputable def firstTerm (w : Word) (b v : ℕ) := F.firstForm.eval w (Nat.pair (Nat.unpair b).1
  (Nat.pair (F.readH w (2*b+1) v (F.leftCode w b) 0) (F.readH w (2*b+1) v (F.leftCode w b) 1)))
noncomputable def secondTerm (w : Word) (b v : ℕ) := F.secondForm.eval w (Nat.pair (Nat.unpair b).1
  (Nat.pair (F.readH w (2*b+1) v (F.rightCode w b) 0) (F.readH w (2*b+1) v (F.rightCode w b) 1)))

theorem firstTerm_eq (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    F.firstTerm w (F.sP.code w b) (F.localData.valueCode w (.inr b) v)=
      ((R w).firstForm b.1 (fun j => v ⟨.inl ⟨(R w).leftH b,j⟩,(R w).left_mem b j⟩)).val := by
  let a := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 0
  let c := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 1
  have h := F.firstForm.correct w (b.1,(a : Bit),(c : Bit))
  change F.firstForm.eval w (Nat.pair (LP.code w b.1) (Nat.pair (a : Bit).val (c : Bit).val))=_ at h
  simp only [a,c,F.readH_cast] at h
  rw [F.leftVector] at h
  unfold firstTerm
  rw [F.leftCode_eq]
  have he : (Nat.unpair (F.sP.code w b)).1=LP.code w b.1 := by rw [F.sP_code,Nat.unpair_pair]
  rw [he]
  exact h

theorem secondTerm_eq (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    F.secondTerm w (F.sP.code w b) (F.localData.valueCode w (.inr b) v)=
      ((R w).secondForm b.1 (fun j => v ⟨.inl ⟨(R w).rightH b,j⟩,(R w).right_mem b j⟩)).val := by
  let a := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 0
  let c := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 1
  have h := F.secondForm.correct w (b.1,(a : Bit),(c : Bit))
  change F.secondForm.eval w (Nat.pair (LP.code w b.1) (Nat.pair (a : Bit).val (c : Bit).val))=_ at h
  simp only [a,c,F.readH_cast] at h
  rw [F.rightVector] at h
  unfold secondTerm
  rw [F.rightCode_eq]
  have he : (Nat.unpair (F.sP.code w b)).1=LP.code w b.1 := by rw [F.sP_code,Nat.unpair_pair]
  rw [he]
  exact h

noncomputable def formEval (w : Word) (b v : ℕ) : ℕ :=
  (F.firstTerm w b v + F.secondTerm w b v + F.readV w (2*b+1) v (F.topCode b) +
    F.readV w (2*b+1) v (F.bottomCode w b))%2

theorem formEval_eq (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    F.formEval w (F.sP.code w b) (F.localData.valueCode w (.inr b) v)=((R w).squareForm b v).val := by
  rw [formEval,F.firstTerm_eq,F.secondTerm_eq,F.topCode_eq,F.bottomCode_eq]
  have ht := F.localData.read_value w (.inr b) v ⟨.inr ((R w).topV b),(R w).top_mem b⟩
  have hb := F.localData.read_value w (.inr b) v ⟨.inr ((R w).bottomV b),(R w).bottom_mem b⟩
  change F.readV w (2*F.sP.code w b+1) (F.localData.valueCode w (.inr b) v) (F.vP.code w ((R w).topV b))=_ at ht
  change F.readV w (2*F.sP.code w b+1) (F.localData.valueCode w (.inr b) v) (F.vP.code w ((R w).bottomV b))=_ at hb
  rw [ht,hb]
  have h := congrArg ZMod.val ((R w).squareForm_apply b v)
  dsimp only [localData, Locals.Value, RingLayout.leftH, RingLayout.rightH] at *
  simpa only [ZMod.val_add,Nat.add_mod_mod,Nat.mod_add_mod] using h.symm

theorem readH_poly {n} {w : (Fin n → Word) → Word} {b v h j : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) (hh : NatPoly h) (hj : NatPoly j) :
    NatPoly (fun S => F.readH (w S) (b S) (v S) (h S) (j S)) :=
  F.localData.read_poly hw hb hv (NatPoly.mul (NatPoly.const 2) (NatPoly.pair hh hj))
theorem readV_poly {n} {w : (Fin n → Word) → Word} {b v h : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) (hh : NatPoly h) :
    NatPoly (fun S => F.readV (w S) (b S) (v S) (h S)) :=
  F.localData.read_poly hw hb hv (NatPoly.add (NatPoly.mul (NatPoly.const 2) hh) (NatPoly.const 1))

theorem firstTerm_poly {n} {w : (Fin n → Word) → Word} {b v : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) : NatPoly (fun S => F.firstTerm (w S) (b S) (v S)) :=
  F.firstForm.eval_poly hw (NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.leftCode_poly hw hb) (NatPoly.const 0))
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.leftCode_poly hw hb) (NatPoly.const 1))))
theorem secondTerm_poly {n} {w : (Fin n → Word) → Word} {b v : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) : NatPoly (fun S => F.secondTerm (w S) (b S) (v S)) :=
  F.secondForm.eval_poly hw (NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.rightCode_poly hw hb) (NatPoly.const 0))
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.rightCode_poly hw hb) (NatPoly.const 1))))

theorem formEval_poly {n} {w : (Fin n → Word) → Word} {b v : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) : NatPoly (fun S => F.formEval (w S) (b S) (v S)) := by
  unfold formEval
  apply NatPoly.mod _ (NatPoly.const 2)
  apply NatPoly.add
  · apply NatPoly.add (NatPoly.add (F.firstTerm_poly hw hb hv) (F.secondTerm_poly hw hb hv))
    apply F.readV_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv
    exact NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb))))
  · apply F.readV_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv
    exact NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair
      (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb)))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb))))

variable [∀ w,Fintype (T w)] [∀ w,Fintype (L w)]
    (hr : ∀ w, 2≤r w)

noncomputable def legal : Test F.localData.values (fun w x => decide (((R w).affine (hr w)).Legal 0 x.1 x.2)) where
  eval w i := if (Nat.unpair i).1%2=0 then true else decide (F.formEval w ((Nat.unpair i).1/2) (Nat.unpair i).2=0)
  correct w x := by
    rcases x with ⟨b,v⟩
    have hc : F.localData.values.code w ⟨b,v⟩=Nat.pair (F.bP.code w b) (F.localData.valueCode w b v) := rfl
    change (if (Nat.unpair (F.localData.values.code w ⟨b,v⟩)).1%2=0 then true else decide (F.formEval w ((Nat.unpair (F.localData.values.code w ⟨b,v⟩)).1/2) (Nat.unpair (F.localData.values.code w ⟨b,v⟩)).2=0))=_
    rw [hc,Nat.unpair_pair]
    cases b with
    | inl h =>
      rw [F.bP_inl]
      simp only [Nat.mul_mod_right,ite_true]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, true_iff]
      intro hf
      change false=true at hf
      contradiction
    | inr b =>
      rw [F.bP_inr]
      simp only [show (2*F.sP.code w b+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,F.formEval_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      change ((R w).squareForm b v).val=0 ↔ (true=true → (R w).squareForm b v=0)
      constructor
      · intro h _
        exact ZMod.val_injective 2 h
      · intro h
        exact congrArg ZMod.val (h rfl)
  poly := BoolPoly.iteProp (NatPoly.eqtest (NatPoly.mod (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 2)) (NatPoly.const 0))
    (BoolPoly.const true) (NatPoly.eqtest (F.formEval_poly (Poly.var 0)
      (NatPoly.div (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 2)) (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0))

noncomputable def affine : AffineRealizer F.cP F.bP (fun w => (R w).affine (hr w)) where
  size w b := (R w).coordinates_card b
  member := F.member
  legal := F.legal hr
  color := F.colors

end FinitePresentation.RingRealizer
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.SchemaPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

structure SchemaRealizer {P E : Word → Type} (PP : Presented P) (EP : Presented E)
    (r : Word → ℕ) (rp : NatPoly (fun S : Fin 1 → Word => r (S 0)))
    (S : ∀ w, ComparisonSchemas (r w) (P w) (E w)) where
  pointIndex : Number PP (fun w p => (S w).pointIndex p)
  edgeIndex : Number EP (fun w e => (S w).edgeIndex e)
  dimension : Number PP (fun w p => (S w).dimension p)
  source : Map EP PP (fun w => (S w).source)
  target : Map EP PP (fun w => (S w).target)
  domain : Test (EP.prod ((Presented.fin r rp).prod Presented.bool)) (fun w x => decide (x.2.2∈(S w).domain x.1 x.2.1))
  mapping : Word → ℕ → ℕ → ℕ → ℕ
  mapping_eq : ∀ w e i (a : {a // a∈(S w).domain e i}), mapping w (EP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((S w).mapping e i a)
  mapping_poly : NatPoly (fun X : Fin 4 → Word => mapping (X 0) (X 1).length (X 2).length (X 3).length)
  left : Number (EP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((S w).left x.1 (vectorTwo _ x.2)).val)
  right : Number (EP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((S w).right x.1 (vectorTwo _ x.2)).val)

namespace SchemaRealizer
variable {P E : Word → Type} {PP : Presented P} {EP : Presented E}
    {r : Word → ℕ} {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {S : ∀ w, ComparisonSchemas (r w) (P w) (E w)} (F : SchemaRealizer PP EP r rp S)
    (n : Word → ℕ) (np : NatPoly (fun X : Fin 1 → Word => n (X 0)))

abbrev internalP (_F : SchemaRealizer PP EP r rp S) := PP.sum (EP.prod (Presented.fin (fun w => n w+1) (NatPoly.succ np)))
abbrev linkP (_F : SchemaRealizer PP EP r rp S) := EP.sum ((EP.prod (Presented.fin n np)).sum EP)

noncomputable def internalIndex : Number (F.internalP n np) (fun w t => ((S w).layout (n w)).typeIndex t) := by
  let e : Number (EP.prod (Presented.fin (fun w => n w+1) (NatPoly.succ np))) (fun w x => Nat.pair ((S w).edgeIndex x.1) x.2.val) :=
    (F.edgeIndex.comp (Map.fst _ _)).pair (Number.code (Presented.fin (fun w => n w+1) (NatPoly.succ np)) |>.comp (Map.snd _ _))
  exact (Number.sumCases ((Number.const PP 2).mul F.pointIndex)
    (((Number.const _ 2).mul e).add (Number.const _ 1))).congr (by intro w t; cases t <;> rfl)

noncomputable def linkIndex : Number (F.linkP n np) (fun w e => ((S w).layout (n w)).linkIndex e) := by
  let e : Number (EP.prod (Presented.fin n np)) (fun w x => Nat.pair ((S w).edgeIndex x.1) x.2.val) :=
    (F.edgeIndex.comp (Map.fst _ _)).pair (Number.code (Presented.fin n np) |>.comp (Map.snd _ _))
  let q := Number.sumCases ((Number.const _ 2).mul e) (((Number.const EP 2).mul F.edgeIndex).add (Number.const EP 1))
  exact (Number.sumCases ((Number.const EP 2).mul F.edgeIndex)
    (((Number.const _ 2).mul q).add (Number.const _ 1))).congr (by intro w t; cases t with
      | inl e => rfl
      | inr e => cases e <;> rfl)

noncomputable def internalDimension : Number (F.internalP n np) (fun w t => ((S w).layout (n w)).dimension t) :=
  (Number.sumCases F.dimension (Number.const _ 1)).congr (by intro w t; cases t <;> rfl)

def wireCode (_F : SchemaRealizer PP EP r rp S) (l : ℕ) :=
  if l%2=0 then l/2 else if (l/2)%2=0 then (Nat.unpair ((l/2)/2)).1 else (l/2)/2

theorem wireCode_eq (w : Word) (l : (S w).Link (n w)) : F.wireCode ((F.linkP n np).code w l)=EP.code w ((S w).wire (n w) l) := by
  cases l with
  | inl e => change F.wireCode (2*EP.code w e)=EP.code w e; simp [wireCode]
  | inr l => cases l with
    | inl p =>
      change F.wireCode (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)=_
      simp [wireCode,AffineRealizer.odd_half]
      rfl
    | inr e =>
      change F.wireCode (2*(2*EP.code w e+1)+1)=_
      simp [wireCode,AffineRealizer.odd_half]
      rfl

def firstEval (w : Word) (l : ℕ) :=
  if l%2=0 then 2*F.source.eval w (l/2)
  else if (l/2)%2=0 then 2*(l/2/2)+1 else 2*Nat.pair (l/2/2) (n w)+1

def secondEval (w : Word) (l : ℕ) :=
  if l%2=0 then 2*Nat.pair (l/2) 0+1
  else if (l/2)%2=0 then 2*Nat.pair (Nat.unpair (l/2/2)).1 ((Nat.unpair (l/2/2)).2+1)+1
  else 2*F.target.eval w (l/2/2)

noncomputable def first : Map (F.linkP n np) (F.internalP n np) (fun w => ((S w).layout (n w)).first) where
  eval := F.firstEval n
  correct w l := by
    cases l with
    | inl e =>
      change F.firstEval n w (2*EP.code w e)=2*PP.code w ((S w).source e)
      simp [firstEval,F.source.correct]
    | inr l => cases l with
      | inl p =>
        change F.firstEval n w (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)=2*Nat.pair (EP.code w p.1) p.2.val+1
        simp [firstEval,AffineRealizer.odd_half]
      | inr e =>
        change F.firstEval n w (2*(2*EP.code w e+1)+1)=2*Nat.pair (EP.code w e) (n w)+1
        simp [firstEval,AffineRealizer.odd_half]
  poly := by
    unfold firstEval
    apply NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    · exact NatPoly.mul (NatPoly.const 2) (F.source.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))
    · apply NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
      exact NatPoly.add (NatPoly.mul (NatPoly.const 2) (NatPoly.pair (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (np.rename (fun _ => 0)))) (NatPoly.const 1)

noncomputable def second : Map (F.linkP n np) (F.internalP n np) (fun w => ((S w).layout (n w)).second) where
  eval := F.secondEval
  correct w l := by
    cases l with
    | inl e =>
      change F.secondEval w (2*EP.code w e)=2*Nat.pair (EP.code w e) 0+1
      simp [secondEval]
    | inr l => cases l with
      | inl p =>
        change F.secondEval w (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)=2*Nat.pair (EP.code w p.1) (p.2.val+1)+1
        simp [secondEval,AffineRealizer.odd_half]
      | inr e =>
        change F.secondEval w (2*(2*EP.code w e+1)+1)=2*PP.code w ((S w).target e)
        simp [secondEval,AffineRealizer.odd_half,F.target.correct]
  poly := by
    unfold secondEval
    apply NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    apply NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    exact NatPoly.mul (NatPoly.const 2) (F.target.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

end SchemaRealizer
end FinitePresentation

namespace FinitePresentation.SchemaRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P E : Word → Type} {PP : Presented P} {EP : Presented E}
    {r : Word → ℕ} {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {S : ∀ w, ComparisonSchemas (r w) (P w) (E w)} (F : SchemaRealizer PP EP r rp S)
    (n : Word → ℕ) (np : NatPoly (fun X : Fin 1 → Word => n (X 0)))

noncomputable def labels : Test ((F.internalP n np).prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((S w).layout (n w)).labels x.1 x.2.1)) where
  eval w i := if (Nat.unpair i).1%2=0 then true
    else F.domain.eval w (Nat.pair (Nat.unpair ((Nat.unpair i).1/2)).1 (Nat.unpair i).2)
  correct w x := by
    simp only [Presented.prod_code,Nat.unpair_pair]
    rcases x with ⟨t,i,a⟩
    cases t with
    | inl p =>
      simp only [internalP,Presented.sum_inl_code,Presented.fin_code,Presented.bool_code]
      change (if (2*PP.code w p)%2=0 then true else _)=_
      simp only [Nat.mul_mod_right,ite_true,ComparisonSchemas.layout,ComparisonSchemas.layoutLabels,Finset.mem_univ,decide_true]
    | inr p =>
      simp only [internalP,Presented.sum_inr_code,Presented.prod_code,Presented.fin_code,Presented.bool_code]
      change (if (2*Nat.pair (EP.code w p.1) p.2.val+1)%2=0 then true else _)=_
      simp only [show (2*Nat.pair (EP.code w p.1) p.2.val+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,Nat.unpair_pair]
      exact F.domain.correct w (p.1,i,a)
  poly := BoolPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (BoolPoly.const true)
    (F.domain.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

noncomputable def matching : Test ((F.linkP n np).prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((S w).layout (n w)).matchLabels x.1 x.2.1)) where
  eval w i := F.domain.eval w (Nat.pair (F.wireCode (Nat.unpair i).1) (Nat.unpair i).2)
  correct w x := by
    simp only [Presented.prod_code,Nat.unpair_pair]
    change F.domain.eval w (Nat.pair (F.wireCode ((F.linkP n np).code w x.1))
      (Nat.pair x.2.1.val (NaturalCode.bool x.2.2)))=_
    rw [F.wireCode_eq n np]
    exact F.domain.correct w ((S w).wire (n w) x.1,x.2.1,x.2.2)
  poly := F.domain.eval_poly (Poly.var 0) (NatPoly.pair (by unfold wireCode; apply NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)); exact NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)))

def secondLabelEval (w : Word) (l i a : ℕ) :=
  if l%2=0 then a else if (l/2)%2=0 then a else F.mapping w (l/2/2) i a

theorem secondLabelEval_eq (w : Word) (e : (S w).Link (n w)) (i : Fin (r w))
    (a : (((S w).layout (n w)).Match e i)) :
    F.secondLabelEval w ((F.linkP n np).code w e) i.val (NaturalCode.bool a.val)=
      NaturalCode.bool (((S w).layout (n w)).secondLabel e i a).val := by
  cases e with
  | inl e =>
    change F.secondLabelEval w (2*EP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool a.val
    simp [secondLabelEval]
  | inr e => cases e with
    | inl p =>
      change F.secondLabelEval w (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1) i.val (NaturalCode.bool a.val)=NaturalCode.bool a.val
      simp [secondLabelEval,AffineRealizer.odd_half]
    | inr e =>
      change F.secondLabelEval w (2*(2*EP.code w e+1)+1) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((S w).mapping e i a)
      simp only [secondLabelEval,show (2*(2*EP.code w e+1)+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,
        show (2*EP.code w e+1)%2≠0 by omega]
      exact F.mapping_eq w e i a

theorem mapping_poly_of {k} {w : (Fin k → Word) → Word} {e i a : (Fin k → Word) → ℕ}
    (hw : Poly w) (he : NatPoly e) (hi : NatPoly i) (ha : NatPoly a) :
    NatPoly (fun X => F.mapping (w X) (e X) (i X) (a X)) := by
  have h := F.mapping_poly.subst (g := ![w,fun X => unary (e X),fun X => unary (i X),fun X => unary (a X)])
    (by intro j; fin_cases j; exacts [hw,he,hi,ha])
  change NatPoly (fun X => F.mapping (w X) (unary (e X)).length (unary (i X)).length (unary (a X)).length) at h
  simpa only [unary,List.length_replicate] using h

noncomputable def firstForm : Number ((F.linkP n np).prod (Presented.bit.prod Presented.bit))
    (fun w x => (((S w).layout (n w)).firstForm x.1 (vectorTwo _ x.2)).val) where
  eval w i := if (Nat.unpair i).1%2=0 then F.left.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
    else (Nat.unpair (Nat.unpair i).2).1
  correct w x := by
    simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
    rcases x with ⟨l,a,b⟩
    cases l with
    | inl e =>
      simp only [linkP,Presented.sum_inl_code]
      change (if (2*EP.code w e)%2=0 then F.left.eval w (Nat.pair ((2*EP.code w e)/2) (Nat.pair a.val b.val)) else _)=_
      simp only [Nat.mul_mod_right,ite_true,Nat.mul_div_cancel_left _ (by omega : 0<2)]
      exact F.left.correct w (e,a,b)
    | inr l => cases l with
      | inl p =>
        simp only [linkP,Presented.sum_inl_code,Presented.sum_inr_code,Presented.prod_code,Presented.fin_code]
        change (if (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)%2=0 then _ else a.val)=_
        simp only [show ∀ z : ℕ, (2*z+1)%2≠0 by omega,ite_false]
        rfl
      | inr e =>
        simp only [linkP,Presented.sum_inr_code]
        change (if (2*(2*EP.code w e+1)+1)%2=0 then _ else a.val)=_
        simp only [show ∀ z : ℕ, (2*z+1)%2≠0 by omega,ite_false]
        rfl
  poly := NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (F.left.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))

noncomputable def secondForm : Number ((F.linkP n np).prod (Presented.bit.prod Presented.bit))
    (fun w x => (((S w).layout (n w)).secondForm x.1 (vectorTwo _ x.2)).val) where
  eval w i := if (Nat.unpair i).1%2=0 then (Nat.unpair (Nat.unpair i).2).1
    else if ((Nat.unpair i).1/2)%2=0 then (Nat.unpair (Nat.unpair i).2).1
    else F.right.eval w (Nat.pair ((Nat.unpair i).1/2/2) (Nat.unpair i).2)
  correct w x := by
    simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
    rcases x with ⟨l,a,b⟩
    cases l with
    | inl e =>
      simp only [linkP,Presented.sum_inl_code]
      change (if (2*EP.code w e)%2=0 then a.val else _)=_
      simp only [Nat.mul_mod_right,ite_true]
      rfl
    | inr l => cases l with
      | inl p =>
        simp only [linkP,Presented.sum_inl_code,Presented.sum_inr_code,Presented.prod_code,Presented.fin_code]
        change (if (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)%2=0 then a.val else if ((2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)/2)%2=0 then a.val else _)=_
        simp only [show ∀ z : ℕ, (2*z+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,Nat.mul_mod_right,ite_true]
        rfl
      | inr e =>
        simp only [linkP,Presented.sum_inr_code]
        change (if (2*(2*EP.code w e+1)+1)%2=0 then a.val else if ((2*(2*EP.code w e+1)+1)/2)%2=0 then a.val else _)=_
        simp only [show (2*(2*EP.code w e+1)+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,
          show (2*EP.code w e+1)%2≠0 by omega]
        exact F.right.correct w (e,a,b)
  poly := NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))
    (NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (F.right.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))))

noncomputable def ring : RingRealizer (F.internalP n np) (F.linkP n np) r rp (fun w => (S w).layout (n w)) where
  typeIndex := F.internalIndex n np
  linkIndex := F.linkIndex n np
  dimension := F.internalDimension n np
  labels := F.labels n np
  matching := F.matching n np
  first := F.first n np
  second := F.second n np
  firstLabel := fun _ _ _ a => a
  secondLabel := F.secondLabelEval
  firstLabel_eq w e i a := by cases e with
    | inl e => rfl
    | inr e => cases e <;> rfl
  secondLabel_eq := F.secondLabelEval_eq n np
  firstLabel_poly := NatPoly.var 3
  secondLabel_poly := by
    unfold secondLabelEval
    exact NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (NatPoly.var 3)
      (NatPoly.iteProp (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (NatPoly.var 3) (F.mapping_poly_of (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (NatPoly.var 2) (NatPoly.var 3)))
  firstForm := F.firstForm n np
  secondForm := F.secondForm n np

end FinitePresentation.SchemaRealizer
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

noncomputable def connectionSource : Map F.connectionP F.primaryP (fun w => (C w).connectionSource) := by
  apply F.casesNumber
  · exact (Map.some PP).comp F.source
  · exact (Map.some PP).comp F.testType
  · exact Map.none _ _
  · exact Map.none _ _
  · exact Map.sigmaFst _ _
  · exact Map.none _ _
noncomputable def connectionTarget : Map F.connectionP F.primaryP (fun w => (C w).connectionTarget) := by
  apply F.casesNumber
  · exact (Map.some PP).comp F.target
  · exact Map.none _ _
  · exact Map.none _ _
  · exact (Map.some PP).comp (Map.sigmaFst _ _)
  · exact Map.sigmaFst _ _
  · exact Map.none _ _

noncomputable abbrev realBase := F.primaryP.sum (F.connectionP.sum Presented.unit)
def realEquiv (w : Word) : (C w).RealType ≃ ((C w).Primary ⊕ ((C w).Connection ⊕ Unit)) where
  toFun | .primary p => .inl p | .buffer l => .inr (.inl l) | .dummy => .inr (.inr ())
  invFun | .inl p => .primary p | .inr (.inl l) => .buffer l | .inr (.inr _) => .dummy
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with p|l|u <;> rfl
noncomputable def realP : Presented (fun w => (C w).RealType) := F.realBase.retype (realEquiv (C := C))

end CircuitRealizer
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

noncomputable def realIndex : Number F.realP (fun w p => (C w).realIndex p) :=
  ((Number.sumCases ((Number.const F.primaryP 0).pair F.primaryIndex)
    (Number.sumCases ((Number.const F.connectionP 1).pair F.connectionIndex) (Number.const Presented.unit (Nat.pair 2 0)))).retype
      (realEquiv (C := C))).congr (by intro w p; cases p <;> rfl)

noncomputable def realDim : Number F.realP (fun w p => (C w).realDimension p) :=
  ((Number.sumCases F.primaryDim (Number.sumCases (Number.const F.connectionP 2) (Number.const Presented.unit 1))).retype
    (realEquiv (C := C))).congr (by intro w p; cases p <;> rfl)

noncomputable def toPrimary : Map F.primaryP F.realP (fun _ => ProductCircuit.RealType.primary) :=
  (Map.untype F.realBase (realEquiv (C := C))).comp (Map.inl F.primaryP (F.connectionP.sum Presented.unit))
noncomputable def toBuffer : Map F.connectionP F.realP (fun _ => ProductCircuit.RealType.buffer) :=
  (Map.untype F.realBase (realEquiv (C := C))).comp
    ((Map.inr F.primaryP (F.connectionP.sum Presented.unit)).comp (Map.inl F.connectionP Presented.unit))
noncomputable def toDummy {A : Word → Type} (AP : Presented A) : Map AP F.realP (fun _ _ => .dummy) :=
  Map.const AP F.realP (fun _ => .dummy) (NatPoly.const 3)

noncomputable def comparisonSource : Map F.comparisonP F.realP (fun w => (C w).comparisonSource) := by
  apply F.comparisonCases
  · exact F.toPrimary.comp ((Map.some PP).comp F.seedType)
  · exact F.toPrimary.comp F.connectionSource
  · exact F.toPrimary.comp F.connectionSource
  · exact F.toBuffer
noncomputable def comparisonTarget : Map F.comparisonP F.realP (fun w => (C w).comparisonTarget) := by
  apply F.comparisonCases
  · exact F.toDummy ZP
  · exact F.toBuffer
  · exact F.toBuffer
  · exact F.toPrimary.comp F.connectionTarget

noncomputable def flipMapping : Map (F.rowP.prod (F.rowP.prod Presented.bool)) Presented.bool
    (fun _w x => (ProductMap.flip x.1).mapping x.2.1 x.2.2) := by
  let H : Test (F.rowP.prod (F.rowP.prod Presented.bool)) (fun _ x => decide (x.2.1=x.1)) :=
    Test.eq ((Map.fst F.rowP Presented.bool).comp (Map.snd F.rowP (F.rowP.prod Presented.bool))) (Map.fst _ _)
  let B := Test.ofBoolMap (F.rightBit F.rowP)
  exact (Map.boolOfTest (Test.ite H B.not B)).congr (by intro w x; simp only [decide_eq_true_eq]; rfl)

noncomputable def connectionMapping : Map (F.connectionP.prod (F.rowP.prod Presented.bool)) Presented.bool
    (fun w x => ((C w).connectionMap x.1).mapping x.2.1 x.2.2) := by
  apply F.casesNumberFst
  · exact F.edgeMapping
  · exact F.rightBit TP
  · exact F.flipMapping
  · exact F.rightBit F.broadcastP
  · exact F.rightBit F.selfP
  · exact F.rightBit Presented.unit

noncomputable def comparisonMapping : Map (F.comparisonP.prod (F.rowP.prod Presented.bool)) Presented.bool
    (fun w x => ((C w).comparisonMap x.1).mapping x.2.1 x.2.2) := by
  apply F.comparisonNumberFst
  · exact F.rightBit ZP
  · exact F.rightBit F.connectionP
  · exact F.rightBit F.connectionP
  · exact F.connectionMapping

end CircuitRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.CircuitForms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Number
variable {A : Word → Type} (AP : Presented A)

noncomputable def vectorSecond : Number (AP.prod (Presented.bit.prod Presented.bit)) (fun _ x => x.2.2.val) where
  eval _ i := (Nat.unpair (Nat.unpair i).2).2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
  poly := by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)

noncomputable def vectorProj {d : ∀ w,A w → ℕ} {j : ∀ w,(a : A w) → Fin (d w a)}
    (J : Number AP (fun w a => (j w a).val)) :
    Number (AP.prod (Presented.bit.prod Presented.bit)) (fun w x => (vectorTwo (d w x.1) x.2 (j w x.1)).val) where
  eval w i := if J.eval w (Nat.unpair i).1=0 then (Nat.unpair (Nat.unpair i).2).1 else (Nat.unpair (Nat.unpair i).2).2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair,J.correct,vectorTwo]; split <;> rfl
  poly := NatPoly.iteProp (NatPoly.eqtest (J.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (NatPoly.const 0)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))

noncomputable def vectorSum {d : ∀ w,A w → ℕ} (D : Number AP d) (hd : ∀ w a, d w a=1 ∨ d w a=2) :
    Number (AP.prod (Presented.bit.prod Presented.bit)) (fun w x => (ProductCircuit.sumForm (d w x.1) (vectorTwo _ x.2)).val) where
  eval w i := if D.eval w (Nat.unpair i).1=1 then (Nat.unpair (Nat.unpair i).2).1
    else ((Nat.unpair (Nat.unpair i).2).1+(Nat.unpair (Nat.unpair i).2).2)%2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair,D.correct,sum_vector _ (hd w x.1)]
  poly := NatPoly.iteProp (NatPoly.eqtest (D.eval_poly (Poly.var 0) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange))) (NatPoly.const 1)) (by (repeat' first | exact WordExpressions.Poly.var _ | exact WordExpressions.NatPoly.var _ | exact WordExpressions.NatPoly.const _ | exact WordExpressions.BoolPoly.const _ | exact WordExpressions.Poly.const _ | apply WordExpressions.NatPoly.add | apply WordExpressions.NatPoly.mul | apply WordExpressions.NatPoly.sub | apply WordExpressions.NatPoly.succ | apply WordExpressions.NatPoly.div | apply WordExpressions.NatPoly.mod | apply WordExpressions.NatPoly.cappedPow | apply WordExpressions.NatPoly.min | apply WordExpressions.NatPoly.max | apply WordExpressions.NatPoly.pair | apply WordExpressions.NatPoly.unpair_fst | apply WordExpressions.NatPoly.unpair_snd | apply WordExpressions.NatPoly.decode | apply WordExpressions.NatPoly.ite | apply WordExpressions.NatPoly.length | apply WordExpressions.BoolPoly.and | apply WordExpressions.BoolPoly.or | apply WordExpressions.BoolPoly.not | apply WordExpressions.NatPoly.eqtest | apply WordExpressions.NatPoly.lt | apply WordExpressions.NatPoly.le | apply WordExpressions.Poly.nth | apply WordExpressions.BoolPoly.allRange | apply WordExpressions.BoolPoly.anyRange | apply WordExpressions.NatPoly.sumRange | apply WordExpressions.Poly.tabulateRange)) (NatPoly.mod (NatPoly.add (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))) (NatPoly.const 2))

noncomputable def vectorAdd : Number (AP.prod (Presented.bit.prod Presented.bit)) (fun _ x => (x.2.1+x.2.2).val) where
  eval _ i := ((Nat.unpair (Nat.unpair i).2).1+(Nat.unpair (Nat.unpair i).2).2)%2
  correct w x := by simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair,ZMod.val_add]
  poly := NatPoly.mod (NatPoly.add (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))) (NatPoly.const 2)

end Number
namespace CircuitRealizer
variable {P E Z T : Word → Type} {PP : Presented P} {EP : Presented E}
    {ZP : Presented Z} {TP : Presented T} {r : Word → ℕ}
    {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {C : ∀ w, ProductCircuit (r w) (P w) (E w) (Z w) (T w)}
    (F : CircuitRealizer PP EP ZP TP r rp C)

noncomputable def sourceForm : Number (F.connectionP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).sourceForm x.1 (vectorTwo _ x.2)).val) := by
  apply F.casesNumberFst
  · exact Number.vectorSum EP (F.dimension.comp F.source) (fun w e => (C w).dimension_bound ((C w).source e))
  · exact Number.vectorSum TP (F.dimension.comp F.testType) (fun w t => (C w).dimension_bound ((C w).testType t))
  · exact Number.vectorFirst F.rowP
  · exact Number.vectorFirst F.broadcastP
  · exact Number.vectorProj F.selfP (Number.sigmaSnd F.primaryDim)
  · exact Number.vectorFirst Presented.unit

noncomputable def targetForm : Number (F.connectionP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).targetForm x.1 (vectorTwo _ x.2)).val) := by
  apply F.casesNumberFst
  · exact Number.vectorProj EP F.port
  · exact Number.vectorFirst TP
  · exact Number.vectorFirst F.rowP
  · exact Number.vectorProj F.broadcastP (Number.sigmaSnd F.dimension)
  · exact Number.vectorProj F.selfP (Number.sigmaSnd F.primaryDim)
  · exact Number.vectorFirst Presented.unit

noncomputable def comparisonLeft : Number (F.comparisonP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).comparisonLeft x.1 (vectorTwo _ x.2)).val) := by
  apply F.comparisonNumberFst
  · exact Number.vectorSum ZP (F.dimension.comp F.seedType) (fun w z => (C w).dimension_bound ((C w).seedType z))
  · exact F.sourceForm
  · exact F.sourceForm
  · exact Number.vectorAdd F.connectionP

noncomputable def comparisonRight : Number (F.comparisonP.prod (Presented.bit.prod Presented.bit))
    (fun w x => ((C w).comparisonRight x.1 (vectorTwo _ x.2)).val) := by
  apply F.comparisonNumberFst
  · exact Number.const _ 0
  · exact Number.vectorFirst F.connectionP
  · exact Number.vectorSecond F.connectionP
  · exact F.targetForm

noncomputable def schemas : SchemaRealizer F.realP F.comparisonP r rp (fun w => (C w).schemas) where
  pointIndex := F.realIndex
  edgeIndex := F.comparisonIndex
  dimension := F.realDim
  source := F.comparisonSource
  target := F.comparisonTarget
  domain := F.comparisonDomain
  mapping w e i a := F.comparisonMapping.eval w (Nat.pair e (Nat.pair i a))
  mapping_eq w e i a := F.comparisonMapping.correct w (e,i,a.val)
  mapping_poly := F.comparisonMapping.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.var 1) (NatPoly.pair (NatPoly.var 2) (NatPoly.var 3)))
  left := F.comparisonLeft
  right := F.comparisonRight

end CircuitRealizer
end FinitePresentation
end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.SeedBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Test
variable {A : Word → Type} {AP : Presented A}
def ofNatBit {n : ∀ w,A w → ℕ} (N : Number AP n) (d : Word → ℕ)
    (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    Test (AP.prod (Presented.fin d dp)) (fun w x => BinaryAddress.ofNat (d w) (n w x.1) x.2) where
  eval w v := decide (NumericKernel.digit 2 (N.eval w (Nat.unpair v).1) (Nat.unpair v).2=1)
  correct w x := by
    simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,N.correct,BinaryAddress.ofNat_apply,NumericKernel.digit]
  poly := NatPoly.eqtest (NatPoly.digit (NatPoly.const 2)
    (N.eval_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.var 1))) (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 1)
end Test
namespace ProductRealizer
variable {A : Word → Type} {AP : Presented A} {d : Word → ℕ}
    {dp : NatPoly (fun X : Fin 1 → Word => d (X 0))}
noncomputable def singletonBits {bits : ∀ w,A w → BinaryAddress.Bits (d w)}
    (B : Map (AP.prod (Presented.fin d dp)) Presented.bool (fun w x => bits w x.1 x.2)) :
    ProductRealizer AP d dp (fun w a => ProductMap.singleton (bits w a) (bits w a)) := by
  let I := Map.pair (Map.fst AP ((Presented.fin d dp).prod Presented.bool)) ((Map.fst _ _).comp (Map.snd _ _))
  exact {
    domain := (Test.eq ((Map.snd _ _).comp (Map.snd _ _)) (B.comp I)).congr (by intro w x; simp only [ProductMap.singleton,Finset.mem_singleton])
    mapping := B.comp I }

noncomputable def aboveBits {bits : ∀ w,BinaryAddress.Bits (d w)}
    (B : Map (Presented.fin d dp) Presented.bool (fun w i => bits w i)) :
    ProductRealizer (Presented.fin d dp) d dp (fun w h => BinaryAddress.aboveMap (bits w) h) := by
  let H := Number.code (Presented.fin d dp) |>.comp (Map.fst (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool))
  let I := (Number.code (Presented.fin d dp)).comp ((Map.fst _ _).comp (Map.snd (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool)))
  let V := (Map.snd _ _).comp (Map.snd (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool))
  let BI := B.comp ((Map.fst _ _).comp (Map.snd (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool)))
  exact {
    domain := (Test.ite (Test.numLt H I) (Test.eq V BI)
      (Test.ite (Test.numEq I H) (Test.ofBoolMap V) (Test.const _ true))).congr (by
        intro w x
        change (if decide (x.1.val<x.2.1.val) then decide (x.2.2=bits w x.2.1) else if decide (x.2.1.val=x.1.val) then x.2.2 else true)=_
        by_cases hi : x.1<x.2.1
        · simp [hi,show x.1.val<x.2.1.val from hi,BinaryAddress.aboveMap]
        · by_cases he : x.2.1=x.1
          · simp [he,BinaryAddress.aboveMap]
          · simp [hi,show ¬x.1.val<x.2.1.val from hi,he,show x.2.1.val≠x.1.val from fun h => he (Fin.ext h),BinaryAddress.aboveMap])
    mapping := V }
end ProductRealizer
namespace InitialRealizer
open Machine BinaryAddress
variable (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
 theorem span_poly : NatPoly (fun X : Fin 1 → Word => inputSpan (X 0)) := NatPoly.max (NatPoly.const 1) (NatPoly.var 0)
abbrev positionP := Presented.fin (fun w => inputSpan w) span_poly
abbrev digitP := Presented.fin d dp
noncomputable def spanBit : Map (digitP d dp) Presented.bool (fun w i => ofNat (d w) (inputSpan w) i) :=
  (Map.boolOfTest ((Test.ofNatBit (Number.param Presented.unit (fun w => inputSpan w) span_poly) d dp).comp
    (Map.pair (Map.const _ Presented.unit (fun _ => ()) (NatPoly.const 0)) (Map.id _)))).congr (by intro w x; rfl)
noncomputable def zeroBit : Test (digitP d dp) (fun w i => decide (ofNat (d w) (inputSpan w) i=false)) :=
  Test.eq (spanBit d dp) (Map.const _ Presented.bool (fun _ => false) (NatPoly.const 0))
noncomputable abbrev thresholdDigitP := (digitP d dp).restrict
  (fun w i => ofNat (d w) (inputSpan w) i=false) (zeroBit d dp)
noncomputable abbrev thresholdP := (thresholdDigitP d dp).option
noncomputable abbrev seedP := positionP.sum (thresholdP d dp)
noncomputable def positionBits : Map (positionP.prod (digitP d dp)) Presented.bool
    (fun w x => ofNat (d w) x.1.val x.2) := Map.boolOfTest (Test.ofNatBit (Number.code positionP) d dp)
noncomputable def thresholdMap : ProductRealizer (thresholdP d dp) d dp
    (fun w h => BinaryAddress.thresholdMap (ofNat (d w) (inputSpan w)) h) := by
  let S := ProductRealizer.singletonBits (AP := Presented.unit) (d := d) (dp := dp) (bits := fun w _ => ofNat (d w) (inputSpan w)) ((spanBit d dp).comp (Map.snd Presented.unit (digitP d dp)))
  let B := (ProductRealizer.aboveBits (spanBit d dp)).comp
    (Map.coe (digitP d dp) (fun w i => ofNat (d w) (inputSpan w) i=false) (zeroBit d dp))
  let U := Map.pair (Map.const ((digitP d dp).prod Presented.bool) Presented.unit (fun _ => ()) (NatPoly.const 0)) (Map.id _)
  exact (B.optionCases (fun w => ProductMap.singleton (ofNat (d w) (inputSpan w)) (ofNat (d w) (inputSpan w)))
    (S.domain.comp U) (S.mapping.comp U)).congr (by intro w x; cases x <;> rfl)
noncomputable def seedMap : ProductRealizer (seedP d dp) d dp (fun w => Machine.initialSeedMap (d w) w) :=
  ((ProductRealizer.singletonBits (positionBits d dp)).sumCases (thresholdMap d dp)).congr (by intro w x; cases x <;> rfl)
end InitialRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.SeedLetter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace Machine
open BinaryAddress
 theorem initialSeedLetter_inl (M : Machine) (d : ℕ) (w : Word) (hsize : inputSpan w<2^d) (i : Fin (inputSpan w)) :
    M.initialSeedLetter d w (.inl i) =
      ((w[i.val]?).elim 0 (inputSymbol M), if i.val=0 then some 0 else none) := by
  have hi : i.val<2^d := i.isLt.trans hsize
  have hz : ofNat d i.val=(fun _ => false) ↔ i.val=0 := by
    constructor
    · intro h
      have := congrArg value h
      simpa only [value_ofNat d i.val hi,value_zero] using this
    · intro h; rw [h,ofNat_zero]
  simp only [initialSeedLetter,TapeConfig.letter,ringInitial,value_ofNat d i.val hi,hz]
end Machine
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace InitialRealizer
open Machine
variable (M : Machine) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
    (hsize : ∀ w,inputSpan w<2^d w)

def letterEval (f : M.Letter → ℕ) (w : Word) (i : ℕ) : ℕ :=
  if i<w.length then
    if i=0 then if w[i]?.getD false then f (inputSymbol M true,some 0) else f (inputSymbol M false,some 0)
    else if w[i]?.getD false then f (inputSymbol M true,none) else f (inputSymbol M false,none)
  else if i=0 then f (0,some 0) else f (0,none)

theorem letterEval_poly (f : M.Letter → ℕ) : NatPoly (fun X : Fin 2 → Word => letterEval M f (X 0) (X 1).length) := by
  unfold letterEval
  apply NatPoly.iteProp (NatPoly.lt (NatPoly.var 1) (NatPoly.var 0))
  · apply NatPoly.iteProp (NatPoly.eqtest (NatPoly.var 1) (NatPoly.const 0))
    · exact NatPoly.ite (Poly.nth (Poly.var 0) (NatPoly.var 1)) (NatPoly.const _) (NatPoly.const _)
    · exact NatPoly.ite (Poly.nth (Poly.var 0) (NatPoly.var 1)) (NatPoly.const _) (NatPoly.const _)
  · exact NatPoly.iteProp (NatPoly.eqtest (NatPoly.var 1) (NatPoly.const 0)) (NatPoly.const _) (NatPoly.const _)

noncomputable def positionLetter (f : M.Letter → ℕ) : Number positionP (fun w i => f (M.initialSeedLetter (d w) w (.inl i))) where
  eval := letterEval M f
  correct w i := by
    rw [M.initialSeedLetter_inl (d w) w (hsize w) i]
    change letterEval M f w i.val=f _
    unfold letterEval
    by_cases hi : i.val<w.length
    · rw [ite_eq_left hi,List.getElem?_eq_getElem hi,Option.getD_some,Option.elim_some]
      by_cases hz : i.val=0 <;> cases w[i.val] <;> simp [hz]
    · rw [ite_eq_right hi,List.getElem?_eq_none (by omega),Option.elim_none]
      split <;> rfl
  poly := letterEval_poly M f

noncomputable def seedLetter (f : M.Letter → ℕ) : Number (seedP d dp) (fun w z => f (M.initialSeedLetter (d w) w z)) :=
  (Number.sumCases (positionLetter M d hsize f) (Number.const _ (f (0,none)))).congr
    (by intro w x; cases x <;> rfl)
end InitialRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.MachinePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace MachineRealizer
open Machine
variable (M : Machine) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
    (hsize : ∀ w,inputSpan w<2^d w)
noncomputable abbrev pointP := CellularRealizer.pointP M.Letter
noncomputable abbrev edgeP := CellularRealizer.edgeP M.Letter d dp
noncomputable abbrev seedP := InitialRealizer.seedP d dp
abbrev TestLetter := {a : M.Letter // a.2=some 1}
noncomputable abbrev testP := Presented.fixed (TestLetter M)

noncomputable def circuit : CircuitRealizer (pointP M) (edgeP M d dp) (seedP d dp) (testP M)
    (fun w => d w+d w) (NatPoly.add dp dp) (fun w => M.compiledCircuit (d w) w) where
  pointIndex := CellularRealizer.pointIndex M.Letter
  edgeIndex := CellularRealizer.edgeIndex M.Letter d dp
  seedIndex := (Number.code (seedP d dp)).congr (by intro w x; rfl)
  testIndex := Number.fixed _ (fun x : TestLetter M => NaturalCode.fixed M.Letter x.val)
  dimension := CellularRealizer.dimension M.Letter
  source := CellularRealizer.source M.Letter d dp
  target := CellularRealizer.target M.Letter d dp M.localRule
  port := CellularRealizer.port M.Letter d dp M.localRule
  seedType := InitialRealizer.seedLetter M d dp hsize (fun a => NaturalCode.fixed (CellularCircuit.Gate M.Letter) (.scalar a))
  testType := Number.fixed _ (fun x : TestLetter M => NaturalCode.fixed (CellularCircuit.Gate M.Letter) (.scalar x.val))
  edgeDomain := (CellularRealizer.edgeMap M.Letter d dp).domain
  seedDomain := ((ProductRealizer.singletonConstant (seedP d dp) d dp false false).concat (InitialRealizer.seedMap d dp)).domain
  testDomain := ((ProductRealizer.singletonConstant (testP M) d dp true true).concat (ProductRealizer.identity (testP M) d dp)).domain
  edgeMapping := (CellularRealizer.edgeMap M.Letter d dp).mapping
end MachineRealizer
end FinitePresentation

end WLIdentification

end OAI
end

section
-- module Solutions.OAIQW_WLIdentification.Hardness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace WLIdentification
namespace FinitePresentation.MachineRealizer
open WordExpressions Machine
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Factor the finite enumerations through the compiled type names so instance
search does not repeatedly expand the entire cellular compiler. -/
noncomputable instance compiledRealTypeFintype (M : Machine) (d : ℕ) (w : Word) :
    Fintype (M.compiledCircuit d w).RealType := by infer_instance

noncomputable instance compiledComparisonFintype (M : Machine) (d : ℕ) (w : Word) :
    Fintype (M.compiledCircuit d w).Comparison := by infer_instance

theorem width_poly (C e : ℕ) : NatPoly (fun X : Fin 1 → Word => addressWidth C e (X 0).length) :=
  NatPoly.add (NatPoly.add (NatPoly.add
    (NatPoly.mul (NatPoly.const C) (NatPoly.pow_const (NatPoly.succ (NatPoly.var 0)) e)) (NatPoly.var 0))
    (NatPoly.const 32)) (NatPoly.const 2)

theorem inputSpan_lt_width (C e : ℕ) (w : Word) : inputSpan w<2^addressWidth C e w.length := by
  have hs : inputSpan w≤w.length+1 := max_le (by omega) (by omega)
  have hd : w.length+1≤addressWidth C e w.length := by unfold addressWidth paddedExponent; omega
  exact hs.trans_lt ((Nat.lt_two_pow_self (n := w.length+1)).trans_le
    (Nat.pow_le_pow_right (by decide) hd))

theorem dimension_poly (C e : ℕ) : NatPoly (fun X : Fin 1 → Word => reductionDimension C e (X 0).length) :=
  NatPoly.add (width_poly C e) (width_poly C e)

noncomputable def compiled (M : Machine) (C e : ℕ) :=
  circuit M (fun w => addressWidth C e w.length) (width_poly C e) (inputSpan_lt_width C e)

theorem wire_poly (C e : ℕ) : NatPoly (fun X : Fin 1 → Word => 4*(reductionDimension C e (X 0).length+1)-1) :=
  NatPoly.sub (NatPoly.mul (NatPoly.const 4) (NatPoly.succ (dimension_poly C e))) (NatPoly.const 1)

noncomputable def ring (M : Machine) (C e : ℕ) := (compiled M C e).schemas.ring
  (fun w => 4*(reductionDimension C e w.length+1)-1) (wire_poly C e)

noncomputable def affine (M : Machine) (C e : ℕ) := (ring M C e).affine
  (fun w => by have := reductionDimension_ge C e w.length; change 2≤reductionDimension C e w.length; omega)

noncomputable def uncolored (M : Machine) (C e : ℕ) := (affine M C e).uncolored

noncomputable def output (M : Machine) (C e : ℕ) : Word → Word :=
  (uncolored M C e).output (fun w => reductionDimension C e w.length)

end FinitePresentation.MachineRealizer

end WLIdentification

end OAI
end


