-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P32
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P32
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:43:05.477724+00:00
-- url     : https://prove2.me/theorems/ba269e8f-7cf8-44ba-ba73-e94190a3f0bb
-- title:
--   Definitions for Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks
-- statement:
--   The objects the formalized statements of *Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks* (arXiv:0907.3925) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsOpenCover`: An ordinary open cover, allowing an empty index type over the empty space (Definition 2.7, PDF p.12; Definition 3.1, PDF p.16).
--   - `IsShrinking`: A shrinking has the SAME index type, remains an open cover, and has each closure contained in the corresponding original member (Definition 2.7, PDF p.12).
--   - `ShrinkingSpace`: Every universe-small open cover has a shrinking (Definition 2.7, PDF p.12).
--   - `CGCover`: The concrete CG-cover condition (Definition 3.1, PDF p.16). The interior is taken INSIDE each compact subspace K. A finite collection has an open-cover refinement precisely when these relative interiors cover K.
--   - `HasOpenRefinement`: An open refinement can canonically be taken to be the interiors of the members of V, indexed by the same set (Proposition 3.3, PDF p.18).
--   - `allCompactSubsets`: The actual family of ALL compact subsets, with no chosen exhaustion (Corollary 3.1, PDF p.18).
--   - `ShrinkableMap`: A continuous section and a homotopy from s composed with f to the identity, with every homotopy stage over the base (Definition 4.2, PDF p.28).
--   - `KelleyShrinkable`: Apply the Kelley correction to both spaces before asserting shrinkability. The source topologies are captured before the local instances are replaced; compact test spaces have universe u (pp.4,10,28).
--   - `restrictedProjection`: Restriction of f over a subset V of its base, prior to Kelley correction (Definition 4.3, PDF p.28).
--   - `LocallyShrinkableMap`: Shrinkability over an ordinary open cover, with CGH restrictions formed by Kelley correction (Definition 4.3, PDF p.28).
--   - `CGLocallyShrinkableMap`: Shrinkability over a CG-cover, with the same restriction construction (Definition 4.3, PDF p.28).
--   - `pullbackProjection`: Projection of the actual topological fiber product, prior to Kelley correction (Definition 4.4, PDF p.28).
--   - `QuasiShrinkableMap`: All pullbacks to locally compact, PARACOMPACT, Hausdorff test spaces are shrinkable (Definition 4.4, PDF p.28). Printed X ×_Y T is corrected to X ×_B T: Y is undefined, while f and the test map both have target B.
-- source:
--   Compactly Generated Stacks: A Cartesian Closed Theory of Topological Stacks, arXiv:0907.3925v3, https://arxiv.org/abs/0907.3925v3

import Mathlib

/-!
Statements from Carchedi, arXiv:0907.3925v3. Local definitions have complete bodies;
only the six source-result declarations use `sorry`. Other planned nodes are explicitly
deferred in this unit's HARD.md and GAPS.json. Compilation is pending the batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P32

universe u

open Set Topology

/-- An ordinary open cover, allowing an empty index type over the empty space
(Definition 2.7, PDF p.12; Definition 3.1, PDF p.16). -/
def IsOpenCover {X : Type u} [TopologicalSpace X] {A : Type u}
    (U : A → Set X) : Prop :=
  (∀ a, IsOpen (U a)) ∧ ∀ x, ∃ a, x ∈ U a

/-- A shrinking has the SAME index type, remains an open cover, and has each
closure contained in the corresponding original member (Definition 2.7, PDF p.12). -/
def IsShrinking {X : Type u} [TopologicalSpace X] {A : Type u}
    (U V : A → Set X) : Prop :=
  IsOpenCover V ∧ ∀ a, closure (V a) ⊆ U a

/-- Every universe-small open cover has a shrinking (Definition 2.7, PDF p.12). -/
def ShrinkingSpace (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ (A : Type u) (U : A → Set X), IsOpenCover U → ∃ V, IsShrinking U V

/-- The concrete CG-cover condition (Definition 3.1, PDF p.16).
The interior is taken INSIDE each compact subspace K. A finite collection has an
open-cover refinement precisely when these relative interiors cover K. -/
def CGCover {X : Type u} [TopologicalSpace X] {A : Type u}
    (V : A → Set X) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ J : Finset A,
    ∀ x : K, ∃ a, a ∈ J ∧ x ∈ interior ((Subtype.val : K → X) ⁻¹' V a)

/-- An open refinement can canonically be taken to be the interiors of the members
of V, indexed by the same set (Proposition 3.3, PDF p.18). -/
def HasOpenRefinement {X : Type u} [TopologicalSpace X] {A : Type u}
    (V : A → Set X) : Prop :=
  ∀ x, ∃ a, x ∈ interior (V a)

/-- The actual family of ALL compact subsets, with no chosen exhaustion
(Corollary 3.1, PDF p.18). -/
def allCompactSubsets (X : Type u) [TopologicalSpace X] :
    {K : Set X // IsCompact K} → Set X := fun K => K.val

/-- A continuous section and a homotopy from s composed with f to the identity,
with every homotopy stage over the base (Definition 4.2, PDF p.28). -/
def ShrinkableMap {X B : Type u} [TopologicalSpace X] [TopologicalSpace B]
    (f : X → B) : Prop :=
  Continuous f ∧ ∃ s : C(B, X),
    (∀ b, f (s b) = b) ∧ ∃ H : C(unitInterval × X, X),
      (∀ x, H (0, x) = s (f x)) ∧
      (∀ x, H (1, x) = x) ∧
      ∀ t x, f (H (t, x)) = f x

/-- Apply the Kelley correction to both spaces before asserting shrinkability.
The source topologies are captured before the local instances are replaced;
compact test spaces have universe u (pp.4,10,28). -/
def KelleyShrinkable {X B : Type u} [TopologicalSpace X] [TopologicalSpace B]
    (f : X → B) : Prop :=
  let tx := TopologicalSpace.compactlyGenerated.{u} X
  let tb := TopologicalSpace.compactlyGenerated.{u} B
  letI : TopologicalSpace X := tx
  letI : TopologicalSpace B := tb
  ShrinkableMap f

/-- Restriction of f over a subset V of its base, prior to Kelley correction
(Definition 4.3, PDF p.28). -/
def restrictedProjection {X B : Type u} (f : X → B) (V : Set B) :
    {x : X // f x ∈ V} → V := fun x => ⟨f x.val, x.property⟩

/-- Shrinkability over an ordinary open cover, with CGH restrictions formed by
Kelley correction (Definition 4.3, PDF p.28). -/
def LocallyShrinkableMap {X B : Type u} [TopologicalSpace X] [TopologicalSpace B]
    (f : X → B) : Prop :=
  Continuous f ∧ ∃ (A : Type u) (U : A → Set B),
    IsOpenCover U ∧ ∀ a, KelleyShrinkable (restrictedProjection f (U a))

/-- Shrinkability over a CG-cover, with the same restriction construction
(Definition 4.3, PDF p.28). -/
def CGLocallyShrinkableMap {X B : Type u} [TopologicalSpace X] [TopologicalSpace B]
    (f : X → B) : Prop :=
  Continuous f ∧ ∃ (A : Type u) (V : A → Set B),
    CGCover V ∧ ∀ a, KelleyShrinkable (restrictedProjection f (V a))

/-- Projection of the actual topological fiber product, prior to Kelley correction
(Definition 4.4, PDF p.28). -/
def pullbackProjection {X B T : Type u} (f : X → B) (g : T → B) :
    {p : X × T // f p.1 = g p.2} → T := fun p => p.val.2

/-- All pullbacks to locally compact, PARACOMPACT, Hausdorff test spaces are
shrinkable (Definition 4.4, PDF p.28). Printed X ×_Y T is corrected to X ×_B T:
Y is undefined, while f and the test map both have target B. -/
def QuasiShrinkableMap {X B : Type u} [TopologicalSpace X] [TopologicalSpace B]
    (f : X → B) : Prop :=
  Continuous f ∧ ∀ (T : Type u) [TopologicalSpace T]
    [T2Space T] [LocallyCompactSpace T] [ParacompactSpace T]
    (g : C(T, B)), KelleyShrinkable (pullbackProjection f g)

/-- Sanity: a one-member universal open cover is its own shrinking. -/
example (X : Type u) [TopologicalSpace X] :
    IsShrinking (fun _ : PUnit => (Set.univ : Set X))
      (fun _ : PUnit => (Set.univ : Set X)) := by
  constructor
  · constructor
    · intro a
      exact isOpen_univ
    · intro x
      exact ⟨PUnit.unit, Set.mem_univ x⟩
  · intro a
    exact Set.subset_univ _

/-- Sanity: the empty family is a CG-cover of the empty space. -/
example : CGCover (fun _ : Empty => (∅ : Set Empty)) := by
  intro K hK
  refine ⟨∅, ?_⟩
  intro x
  exact isEmptyElim x.val

/-- Sanity: a universal singleton family satisfies the finite relative-interior test. -/
example (X : Type u) [TopologicalSpace X] :
    CGCover (fun _ : PUnit => (Set.univ : Set X)) := by
  intro K hK
  refine ⟨{PUnit.unit}, ?_⟩
  intro x
  refine ⟨PUnit.unit, by simp, ?_⟩
  simp

/-- Sanity: a point belongs to the member selected by its own compact singleton. -/
example (X : Type u) [TopologicalSpace X] (x : X) :
    x ∈ allCompactSubsets X ⟨{x}, isCompact_singleton⟩ := by
  exact Set.mem_singleton x

/-- Sanity: identity maps have the identity section and constant fiber homotopy. -/
example (X : Type u) [TopologicalSpace X] : ShrinkableMap (id : X → X) := by
  refine ⟨continuous_id, ContinuousMap.id X, ?_, ⟨Prod.snd, continuous_snd⟩,
    ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro t x
    rfl

/-- Sanity: Kelley correction also permits the identity section and homotopy. -/
example (X : Type u) [TopologicalSpace X] : KelleyShrinkable (id : X → X) := by
  letI : TopologicalSpace X := TopologicalSpace.compactlyGenerated.{u} X
  change ShrinkableMap (id : X → X)
  refine ⟨continuous_id, ContinuousMap.id X, ?_, ⟨Prod.snd, continuous_snd⟩,
    ?_, ?_, ?_⟩
  · intro x
    rfl
  · intro x
    rfl
  · intro x
    rfl
  · intro t x
    rfl

/-- Sanity: identity restrictions and fiber products use the actual coordinates. -/
example {X : Type u} (V : Set X) (x : V) :
    restrictedProjection (id : X → X) V x = x := rfl

/-- Sanity: pullback projection retains the test-space coordinate. -/
example {X : Type u} (x : X) :
    pullbackProjection (id : X → X) (id : X → X) ⟨(x, x), rfl⟩ = x := rfl

/-- Sanity: a one-member family with full interior is an open refinement. -/
example (X : Type u) [TopologicalSpace X] :
    HasOpenRefinement (fun _ : PUnit => (Set.univ : Set X)) := by
  intro x
  exact ⟨PUnit.unit, by simp⟩

/-- Sanity: the identity is locally shrinkable over the universal cover. -/
example (X : Type u) [TopologicalSpace X] : LocallyShrinkableMap (id : X → X) := by
  refine ⟨continuous_id, PUnit, fun _ => Set.univ, ?_, ?_⟩
  · exact ⟨fun _ => isOpen_univ, fun x => ⟨PUnit.unit, Set.mem_univ x⟩⟩
  · intro a
    letI univTopology : TopologicalSpace (Set.univ : Set X) :=
      TopologicalSpace.compactlyGenerated.{u} (Set.univ : Set X)
    change ShrinkableMap (id : ↥(Set.univ : Set X) → ↥(Set.univ : Set X))
    refine ⟨continuous_id, ContinuousMap.id _, ?_, ⟨Prod.snd, continuous_snd⟩,
      ?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x
      rfl
    · intro x
      rfl
    · intro t x
      rfl

/-- Sanity: CG-local shrinkability permits the universal singleton CG-cover. -/
example (X : Type u) [TopologicalSpace X] : CGLocallyShrinkableMap (id : X → X) := by
  refine ⟨continuous_id, PUnit, fun _ => Set.univ, ?_, ?_⟩
  · intro K hK
    refine ⟨{PUnit.unit}, ?_⟩
    intro x
    exact ⟨PUnit.unit, by simp, by simp⟩
  · intro a
    letI univTopology : TopologicalSpace (Set.univ : Set X) :=
      TopologicalSpace.compactlyGenerated.{u} (Set.univ : Set X)
    change ShrinkableMap (id : ↥(Set.univ : Set X) → ↥(Set.univ : Set X))
    refine ⟨continuous_id, ContinuousMap.id _, ?_, ⟨Prod.snd, continuous_snd⟩,
      ?_, ?_, ?_⟩
    · intro x
      rfl
    · intro x
      rfl
    · intro x
      rfl
    · intro t x
      rfl

/-- Sanity: the quasi-shrinkable test includes each point of the base. -/
example {X B : Type u} [TopologicalSpace X] [TopologicalSpace B]
    (f : X → B) (hf : QuasiShrinkableMap f) (b : B) :
    KelleyShrinkable (pullbackProjection f (ContinuousMap.const PUnit b)) := by
  exact hf.2 PUnit (ContinuousMap.const PUnit b)

end QAlgorithms.Papers.Independent.Intakethird100.P32


