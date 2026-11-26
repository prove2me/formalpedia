-- Prove2me | Definitions.Def_Scott1972_ContinuousLattice_FunctionSpaces
-- name    : Scott1972_ContinuousLattice_FunctionSpaces
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:34:13.350397+00:00
-- url     : https://prove2.me/theorems/832ae6f3-44b8-40b6-9ccb-bb0d20de3607
-- title:
--   Function Spaces
-- statement:
--   Definitions and structural lemmas for Function Spaces, from Lars Warren Ericson (catskillsresearch/scott1972; see pinned Apache-2.0 LICENSE and PROVENANCE.md)'s pinned Dana Scott's Continuous Lattices (1972): injective T0-spaces, Scott topology, and D_infinity homeomorphism development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/FunctionSpaces.lean

import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Order
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Theorems.Thm_Scott1972_ContinuousLattice_IsContinuousLattice_sSup_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_le_trans
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_sup
import Theorems.Thm_Scott1972_ContinuousLattice_WayBelow_trans_le
import Theorems.Thm_Scott1972_ContinuousLattice_continuous_of_preservesDirectedSup
import Theorems.Thm_Scott1972_ContinuousLattice_preservesDirectedSup_monotone
import Theorems.Thm_Scott1972_ContinuousLattice_proposition_2_5
import Theorems.Thm_Scott1972_ContinuousLattice_scottOpen_wayBelow
import Theorems.Thm_Scott1972_ContinuousLattice_wayBelow_sSup_iff

set_option autoImplicit true
namespace Scott1972.ContinuousLattice
open Set Topology TopologicalSpace
universe u v
variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']
def scottFunctionEvalSubbasis (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
    Set (Set (C(X, Y))) :=
  { W | ∃ (x : X) (U : Set Y), IsOpen U ∧ W = {f : C(X, Y) | f x ∈ U} }
@[reducible] noncomputable def scottFunctionTopology (X Y : Type*) [TopologicalSpace X]
    [TopologicalSpace Y] : TopologicalSpace (C(X, Y)) :=
  generateFrom (scottFunctionEvalSubbasis X Y)
@[reducible] noncomputable def continuousMapInducedPiTopology (X Y : Type*)
    [TopologicalSpace X] [TopologicalSpace Y] : TopologicalSpace C(X, Y) :=
  TopologicalSpace.induced (fun f : C(X, Y) => (f : X → Y))
    (@Pi.topologicalSpace X (fun _ => Y) (fun _ => inferInstance))
abbrev ScottFunctionSpace (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  C(X, Y)
def specializationLe_generateOpen (f g : C(X, Y)) (hfg : ∀ x, SpecializationLe (f x) (g x))
    {V : Set (C(X, Y))} (hV : GenerateOpen (scottFunctionEvalSubbasis X Y) V) (hf : f ∈ V) :
    g ∈ V :=
  match hV with
  | .basic W hW => by
    obtain ⟨x, U, hU, rfl⟩ := hW
    exact hfg x U hU hf
  | .univ => hf
  | .inter s t hs ht => by
    rcases hf with ⟨hfs, hft⟩
    exact Set.mem_inter (specializationLe_generateOpen f g hfg hs hfs)
      (specializationLe_generateOpen f g hfg ht hft)
  | .sUnion S hS => by
    obtain ⟨W, hWS, hfW⟩ := Set.mem_sUnion.mp hf
    exact Set.mem_sUnion.mpr ⟨W, hWS, specializationLe_generateOpen f g hfg (hS W hWS) hfW⟩
abbrev ScottC (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :=
  @ContinuousMap D D' scottTopologicalSpace scottTopologicalSpace
def ScottMap (D : Type u) (D' : Type v) [CompleteLattice D] [CompleteLattice D'] : Type _ :=
  { f : D → D' // @Continuous D D' scottTopologicalSpace scottTopologicalSpace f }
namespace ScottMap
instance : CoeFun (ScottMap D D') (fun _ => D → D') where
  coe f := f.1
@[ext]
theorem ext {f g : ScottMap D D'} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)
theorem preservesDirectedSup_coe (f : ScottMap D D') (S : Set D) (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) :
    (f : D → D') (sSup S) = sSup (Set.image (f : D → D') S) := by
  have h := (proposition_2_5 (Subtype.val f)).mp f.property
  exact h hS hSdir
theorem monotone (f : ScottMap D D') : Monotone (f : D → D') :=
  preservesDirectedSup_monotone ((proposition_2_5 (Subtype.val f)).mp f.property)
theorem preservesDirectedSup_comp {f : D' → D''} {g : D → D'} (hf : PreservesDirectedSup f)
    (hg : PreservesDirectedSup g) : PreservesDirectedSup (f ∘ g) := by
  intro S hS hSdir
  have hmono : Monotone g := preservesDirectedSup_monotone hg
  have hdir' : DirectedOn (· ≤ ·) (g '' S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨g c, Set.mem_image_of_mem g hc, hmono hac, hmono hbc⟩
  have hne : (g '' S).Nonempty := Set.image_nonempty.2 hS
  rw [Function.comp_apply, hg hS hSdir, hf hne hdir']
  congr 1
  exact (Set.image_comp f g S).symm
def comp (f : ScottMap D' D'') (g : ScottMap D D') : ScottMap D D'' :=
  ⟨f ∘ g, continuous_of_preservesDirectedSup (preservesDirectedSup_comp
    ((proposition_2_5 (Subtype.val f)).mp f.property)
    ((proposition_2_5 (Subtype.val g)).mp g.property))⟩
def const (c : D') : ScottMap D D' :=
  ⟨fun _ => c, continuous_of_preservesDirectedSup fun S hS _ => by
    obtain ⟨x, hx⟩ := hS
    apply le_antisymm
    · exact le_sSup ⟨x, hx, rfl⟩
    · apply sSup_le
      intro b hb
      obtain ⟨y, hy, rfl⟩ := hb
      exact le_rfl⟩
theorem pointwise_sup_preservesDirectedSup (f g : ScottMap D D') :
    PreservesDirectedSup (fun x => f x ⊔ g x) := by
  intro S hS hSdir
  show f (sSup S) ⊔ g (sSup S) = sSup (Set.image (fun x => f x ⊔ g x) S)
  rw [f.preservesDirectedSup_coe S hS hSdir, g.preservesDirectedSup_coe S hS hSdir]
  apply le_antisymm
  · apply sup_le
    · apply sSup_le
      intro b hb
      obtain ⟨s, hsS, rfl⟩ := hb
      exact le_trans le_sup_left (le_sSup (Set.mem_image_of_mem (fun z => f z ⊔ g z) hsS))
    · apply sSup_le
      intro b hb
      obtain ⟨s, hsS, rfl⟩ := hb
      exact le_trans le_sup_right (le_sSup (Set.mem_image_of_mem (fun z => f z ⊔ g z) hsS))
  · apply sSup_le
    intro b hb
    obtain ⟨s, hsS, rfl⟩ := hb
    exact sup_le (le_trans (le_sSup (Set.mem_image_of_mem f hsS)) le_sup_left)
      (le_trans (le_sSup (Set.mem_image_of_mem g hsS)) le_sup_right)
noncomputable def bot : ScottMap D D' :=
  const ⊥
def le {D : Type u} {D' : Type v} [CompleteLattice D] [CompleteLattice D']
    (f g : ScottMap D D') : Prop :=
  letI : LE D' :=
    (ChainCompletePartialOrder.instOfCompleteLattice
      (α := D')).toPartialOrder.toPreorder.toLE
  ∀ x, f x ≤ g x
noncomputable def sup (f g : ScottMap D D') : ScottMap D D' :=
  ⟨fun x => f x ⊔ g x, continuous_of_preservesDirectedSup (pointwise_sup_preservesDirectedSup f g)⟩
theorem pointwise_sSup_preservesDirectedSup (F : Set (ScottMap D D')) :
    PreservesDirectedSup (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) := by
  intro S hS hSdir
  set H := fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)
  show H (sSup S) = sSup (Set.image H S)
  apply le_antisymm
  · apply sSup_le
    intro b hb
    obtain ⟨f, hfF, rfl⟩ := hb
    change f (sSup S) ≤ sSup (Set.image H S)
    rw [f.preservesDirectedSup_coe S hS hSdir]
    apply sSup_le
    intro c hc
    obtain ⟨s, hsS, rfl⟩ := hc
    exact le_trans (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') s) hfF))
      (le_sSup (Set.mem_image_of_mem H hsS))
  · apply sSup_le
    intro b hb
    obtain ⟨s, hsS, rfl⟩ := hb
    apply sSup_le
    intro c hc
    obtain ⟨f, hfF, rfl⟩ := hc
    exact le_trans (ScottMap.monotone f (le_sSup hsS))
      (le_sSup (Set.mem_image_of_mem (fun g : ScottMap D D' => (g : D → D') (sSup S)) hfF))
theorem sSupMaps_continuous {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) :
    @Continuous D D' scottTopologicalSpace scottTopologicalSpace
      (fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F)) :=
  continuous_of_preservesDirectedSup (pointwise_sSup_preservesDirectedSup F)
noncomputable def sSupMaps {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) : ScottMap D D' :=
  ⟨fun x => sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F),
    sSupMaps_continuous F⟩
theorem le_refl' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f : ScottMap D D') :
    ScottMap.le f f :=
  fun _ => le_refl _
theorem le_trans' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g h : ScottMap D D')
    (hfg : ScottMap.le f g)
    (hgh : ScottMap.le g h) : ScottMap.le f h :=
  fun x => le_trans (hfg x) (hgh x)
theorem le_antisymm' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D')
    (hfg : ScottMap.le f g)
    (hgf : ScottMap.le g f) : f = g :=
  ScottMap.ext fun x => le_antisymm (hfg x) (hgf x)
def lt {D : Type u} {D' : Type v} [CompleteLattice D] [CompleteLattice D']
    (f g : ScottMap D D') : Prop :=
  ScottMap.le f g ∧ ¬ ScottMap.le g f
theorem lt_iff_le_not_ge' {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (f g : ScottMap D D') :
    ScottMap.lt f g ↔
      ScottMap.le f g ∧ ¬ ScottMap.le g f :=
  Iff.rfl
instance instPartialOrder {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : PartialOrder (ScottMap D D') where
  le := ScottMap.le
  lt := ScottMap.lt
  le_refl := le_refl'
  le_trans := le_trans'
  lt_iff_le_not_ge := lt_iff_le_not_ge'
  le_antisymm := le_antisymm'
theorem le_def {f g : ScottMap D D'} : f ≤ g ↔ ∀ x, (f : D → D') x ≤ g x := Iff.rfl
noncomputable instance instSupSet {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : SupSet (ScottMap D D') := ⟨sSupMaps⟩
theorem sSup_apply (F : Set (ScottMap D D')) (x : D) :
    ((sSup F : ScottMap D D') : D → D') x =
      sSup (Set.image (fun f : ScottMap D D' => (f : D → D') x) F) :=
  rfl
theorem isLUB_sSup {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] (F : Set (ScottMap D D')) :
    IsLUB F (sSup F) := by
  constructor
  · intro f hf
    rw [le_def]
    intro x
    rw [sSup_apply]
    exact le_sSup (Set.mem_image_of_mem _ hf)
  · intro g hg
    rw [le_def]
    intro x
    rw [sSup_apply]
    refine sSup_le ?_
    rintro _ ⟨f, hfF, rfl⟩
    exact (hg hfF) x
noncomputable instance instCompleteLattice {D : Type u} {D' : Type v}
    [CompleteLattice D] [CompleteLattice D'] : CompleteLattice (ScottMap D D') :=
  completeLatticeOfSup (ScottMap D D') isLUB_sSup
def idMap : ScottMap D D :=
  ⟨fun x => x, continuous_of_preservesDirectedSup fun S _ _ => by
    show sSup S = sSup (Set.image (fun x => x) S)
    rw [Set.image_id']⟩
@[simp] theorem idMap_apply (x : D) : (idMap : ScottMap D D) x = x := rfl
@[simp] theorem comp_apply (f : ScottMap D' D'') (g : ScottMap D D') (x : D) :
    (f.comp g : D → D'') x = f (g x) := rfl
theorem sup_apply (f g : ScottMap D D') (x : D) :
    ((f ⊔ g : ScottMap D D') : D → D') x = f x ⊔ g x := by
  have h : (f ⊔ g : ScottMap D D') = sSup ({f, g} : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_pair]
  exact sSup_pair
theorem bot_apply (x : D) : ((⊥ : ScottMap D D') : D → D') x = ⊥ := by
  have h : (⊥ : ScottMap D D') = sSup (∅ : Set (ScottMap D D')) := rfl
  rw [h, sSup_apply, Set.image_empty, sSup_empty]
@[simp] theorem const_apply (c : D') (x : D) : (ScottMap.const c : D → D') x = c := rfl
end ScottMap
noncomputable def theorem_3_3_sSup (F : Set (ScottMap D D')) : ScottMap D D' :=
  ScottMap.sSupMaps F
noncomputable def theorem_3_3_sup (f g : ScottMap D D') : ScottMap D D' :=
  ScottMap.sup f g
noncomputable def stepFun (e : D) (e' : D') (x : D) : D' := ⨆ _ : e ≪ x, e'
theorem stepFun_of_wayBelow {e : D} {e' : D'} {x : D} (h : e ≪ x) : stepFun e e' x = e' :=
  iSup_pos h
theorem stepFun_of_not_wayBelow {e : D} {e' : D'} {x : D} (h : ¬ e ≪ x) :
    stepFun e e' x = ⊥ :=
  iSup_neg h
theorem stepFun_preservesDirectedSup (e : D) (e' : D') :
    PreservesDirectedSup (stepFun e e') := by
  intro S hS hSdir
  show stepFun e e' (sSup S) = sSup (Set.image (stepFun e e') S)
  by_cases h : e ≪ sSup S
  · rw [stepFun_of_wayBelow h]
    obtain ⟨s, hsS, hes⟩ := (scottOpen_wayBelow e).2 hS hSdir h
    apply le_antisymm
    · refine le_sSup_of_le (Set.mem_image_of_mem _ hsS) ?_
      rw [stepFun_of_wayBelow hes]
    · refine sSup_le ?_
      rintro _ ⟨x, _, rfl⟩
      exact iSup_le fun _ => le_rfl
  · rw [stepFun_of_not_wayBelow h]
    refine (sSup_eq_bot.2 ?_).symm
    rintro _ ⟨x, hxS, rfl⟩
    refine stepFun_of_not_wayBelow (fun hex => ?_)
    exact h (hex.trans_le (le_sSup hxS))
noncomputable def stepMap (e : D) (e' : D') : ScottMap D D' :=
  ⟨stepFun e e', continuous_of_preservesDirectedSup (stepFun_preservesDirectedSup e e')⟩
def scottMapPointwiseSubbasis (D D' : Type*) [CompleteLattice D] [CompleteLattice D'] :
    Set (Set (ScottMap D D')) :=
  { W | ∃ (x : D) (U : Set D'),
      @IsOpen D' scottTopologicalSpace U ∧ W = {f : ScottMap D D' | (f : D → D') x ∈ U} }
@[reducible] noncomputable def scottMapPointwiseTopology (D D' : Type*)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  generateFrom (scottMapPointwiseSubbasis D D')
@[reducible] noncomputable def scottMapInducedPiTopology (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] : TopologicalSpace (ScottMap D D') :=
  TopologicalSpace.induced (fun f : ScottMap D D' => (f : D → D'))
    (@Pi.topologicalSpace D (fun _ => D') (fun _ => scottTopologicalSpace))
theorem sSup_image_prod_mk_left (x : D) (S : Set D') (hS : S.Nonempty) :
    sSup (Set.image (fun y => (x, y)) S) = (x, sSup S) := by
  have himage : Set.image (fun y => (x, y)) S = ({x} : Set D) ×ˢ S := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, hy, h⟩
      obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h
      subst hb
      exact ⟨ha.symm, hy⟩
    · rintro ⟨ha, hb⟩
      refine ⟨b, hb, Prod.ext_iff.mpr ⟨ha.symm, rfl⟩⟩
  have hx : sSup ({x} : Set D) = x := by
    apply le_antisymm
    · exact sSup_le fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]
    · exact le_sSup (Set.mem_singleton x)
  rw [himage, sSup_prod (hs := ⟨x, Set.mem_singleton x⟩) (ht := hS), hx]
theorem curry_right_preservesDirectedSup (f : ScottMap (D × D') D'') (x : D) :
    PreservesDirectedSup (fun y => f (x, y)) := by
  intro S hS hSdir
  have hS' : DirectedOn (· ≤ ·) (Set.image (fun y => (x, y)) S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨(x, c), Set.mem_image_of_mem _ hc, And.intro (And.intro le_rfl hac) (And.intro le_rfl hbc)⟩
  have hS'ne : (Set.image (fun y => (x, y)) S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨(x, s), s, hs, rfl⟩
  rw [show (fun y => f (x, y)) (sSup S) = f (x, sSup S) from rfl,
    ← sSup_image_prod_mk_left x S hS,
    f.preservesDirectedSup_coe (Set.image (fun y => (x, y)) S) hS'ne hS']
  congr 1
  simp [Set.image_image]
noncomputable def scottLambdaAt (f : ScottMap (D × D') D'') (x : D) : ScottMap D' D'' :=
  ⟨fun y => f (x, y), continuous_of_preservesDirectedSup (curry_right_preservesDirectedSup f x)⟩
theorem sSup_image_prod_mk_right (y : D') (S : Set D) (hS : S.Nonempty) :
    sSup (Set.image (fun x => (x, y)) S) = (sSup S, y) := by
  have himage : Set.image (fun x => (x, y)) S = S ×ˢ ({y} : Set D') := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, h⟩
      obtain ⟨ha, hb⟩ := Prod.ext_iff.mp h
      subst ha
      exact ⟨hx, hb.symm⟩
    · rintro ⟨ha, hb⟩
      exact ⟨a, ha, Prod.ext_iff.mpr ⟨rfl, hb.symm⟩⟩
  have hy : sSup ({y} : Set D') = y := by
    apply le_antisymm
    · exact sSup_le fun z hz => by rw [Set.mem_singleton_iff] at hz; rw [hz]
    · exact le_sSup (Set.mem_singleton y)
  rw [himage, sSup_prod (hs := hS) (ht := ⟨y, Set.mem_singleton y⟩), hy]
theorem curry_left_preservesDirectedSup (f : ScottMap (D × D') D'') (y : D') :
    PreservesDirectedSup (fun x => f (x, y)) := by
  intro S hS hSdir
  have hS' : DirectedOn (· ≤ ·) (Set.image (fun x => (x, y)) S) := by
    intro p hp q hq
    obtain ⟨a, ha, rfl⟩ := hp
    obtain ⟨b, hb, rfl⟩ := hq
    obtain ⟨c, hc, hac, hbc⟩ := hSdir a ha b hb
    exact ⟨(c, y), Set.mem_image_of_mem _ hc, And.intro (And.intro hac le_rfl) (And.intro hbc le_rfl)⟩
  have hS'ne : (Set.image (fun x => (x, y)) S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨(s, y), s, hs, rfl⟩
  rw [show (fun x => f (x, y)) (sSup S) = f (sSup S, y) from rfl,
    ← sSup_image_prod_mk_right y S hS,
    f.preservesDirectedSup_coe (Set.image (fun x => (x, y)) S) hS'ne hS']
  congr 1
  simp [Set.image_image]
theorem lambda_outer_preservesDirectedSup (f : ScottMap (D × D') D'') :
    PreservesDirectedSup (fun x => scottLambdaAt f x) := by
  intro S hS hSdir
  apply ScottMap.ext
  intro y
  show f (sSup S, y)
      = ((sSup (Set.image (fun x => scottLambdaAt f x) S) : ScottMap D' D'') : D' → D'') y
  rw [ScottMap.sSup_apply, Set.image_image]
  exact curry_left_preservesDirectedSup f y hS hSdir
noncomputable def scottLambda (f : ScottMap (D × D') D'') : ScottMap D (ScottMap D' D'') :=
  ⟨fun x => scottLambdaAt f x,
    continuous_of_preservesDirectedSup (lambda_outer_preservesDirectedSup f)⟩
@[simp] theorem scottLambda_apply (f : ScottMap (D × D') D'') (x : D) (y : D') :
    ((scottLambda f x : ScottMap D' D'') : D' → D'') y = (f : (D × D') → D'') (x, y) :=
  rfl
structure IsContinuousLatticeRetraction (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D'] where
  incl : ScottMap D D'
  retr : ScottMap D' D
  retr_incl : ∀ d, retr (incl d) = d
structure IsContinuousLatticeProjection (D : Type u) (D' : Type v)
    [CompleteLattice D] [CompleteLattice D']
    extends IsContinuousLatticeRetraction D D' where
  incl_retr_le : ∀ d,
    @LE.le D'
      (ChainCompletePartialOrder.instOfCompleteLattice (α := D')).toPartialOrder.toPreorder.toLE
      (incl (retr d)) d
namespace IsContinuousLatticeRetraction
noncomputable def ambientSSup (R : IsContinuousLatticeRetraction D D') (S : Set D) : D' :=
  sSup (Set.image (R.incl : D → D') S)
end IsContinuousLatticeRetraction
structure ScottMapRetraction (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] where
  incl : ScottMap D₀ D₁ → ScottMap D₀' D₁'
  retr : ScottMap D₀' D₁' → ScottMap D₀ D₁
  retr_incl : ∀ f, retr (incl f) = f
structure ScottMapProjection (D₀ D₀' D₁ D₁' : Type*)
    [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁'] extends
    ScottMapRetraction D₀ D₀' D₁ D₁' where
  incl_retr_le : ∀ f' x, (incl (retr f')) x ≤ f' x
namespace ScottMapRetraction
def functionSpace (R₀ : IsContinuousLatticeRetraction D₀ D₀') (R₁ : IsContinuousLatticeRetraction D₁ D₁') :
    ScottMapRetraction D₀ D₀' D₁ D₁' where
  incl f := ScottMap.comp R₁.incl (ScottMap.comp f R₀.retr)
  retr f' := ScottMap.comp R₁.retr (ScottMap.comp f' R₀.incl)
  retr_incl f := ScottMap.ext fun x => by simp [ScottMap.comp, R₀.retr_incl, R₁.retr_incl]
end ScottMapRetraction
namespace ScottMapProjection
def functionSpace (P₀ : IsContinuousLatticeProjection D₀ D₀') (P₁ : IsContinuousLatticeProjection D₁ D₁') :
    ScottMapProjection D₀ D₀' D₁ D₁' where
  toScottMapRetraction :=
    ScottMapRetraction.functionSpace P₀.toIsContinuousLatticeRetraction P₁.toIsContinuousLatticeRetraction
  incl_retr_le f' y := by
    dsimp only [ScottMapRetraction.functionSpace, ScottMap.comp, Function.comp_def]
    exact le_trans (P₁.incl_retr_le (f' (P₀.incl (P₀.retr y))))
      (ScottMap.monotone f' (P₀.incl_retr_le y))
end ScottMapProjection
def proposition_3_7_retraction (R₀ : IsContinuousLatticeRetraction D₀ D₀')
    (R₁ : IsContinuousLatticeRetraction D₁ D₁') :
    ScottMapRetraction D₀ D₀' D₁ D₁' :=
  ScottMapRetraction.functionSpace R₀ R₁
def proposition_3_7_projection (P₀ : IsContinuousLatticeProjection D₀ D₀')
    (P₁ : IsContinuousLatticeProjection D₁ D₁') :
    ScottMapProjection D₀ D₀' D₁ D₁' :=
  ScottMapProjection.functionSpace P₀ P₁
section Proposition310
open Finset
namespace IsContinuousLatticeProjection
def finsetSupOf (S : Set D) : Set D :=
  { z | ∃ T : Finset D, (∀ x ∈ T, x ∈ S) ∧ z = T.sup id }
theorem mem_finsetSupOf_of_mem {S : Set D} {x : D} (hx : x ∈ S) :
    x ∈ finsetSupOf S :=
  ⟨{x}, by simp [hx], by simp⟩
theorem le_sSup_finsetSupOf (S : Set D) : sSup S ≤ sSup (finsetSupOf S) :=
  sSup_le fun _ hx => le_sSup (mem_finsetSupOf_of_mem hx)
theorem sSup_le_finsetSupOf (S : Set D) : sSup (finsetSupOf S) ≤ sSup S :=
  sSup_le fun z hz => by
    obtain ⟨T, hTS, rfl⟩ := hz
    exact Finset.sup_le fun t ht => le_sSup (hTS t ht)
theorem sSup_finsetSupOf (S : Set D) : sSup S = sSup (finsetSupOf S) :=
  le_antisymm (le_sSup_finsetSupOf S) (sSup_le_finsetSupOf S)
theorem directedOn_finsetSupOf (S : Set D) :
    DirectedOn (· ≤ ·) (finsetSupOf S) := by
  classical
  intro a ha b hb
  obtain ⟨T₁, hT₁, rfl⟩ := ha
  obtain ⟨T₂, hT₂, rfl⟩ := hb
  have hunion : (T₁ ∪ T₂).sup id = T₁.sup id ⊔ T₂.sup id := by
    simpa using Finset.sup_union (s₁ := T₁) (s₂ := T₂) (f := id)
  refine ⟨T₁.sup id ⊔ T₂.sup id, ⟨T₁ ∪ T₂, ?_, hunion.symm⟩, le_sup_left, le_sup_right⟩
  intro x hx
  simp only [Finset.mem_union] at hx
  exact hx.elim (hT₁ x) (hT₂ x)
end IsContinuousLatticeProjection
variable {i : D → D'}
noncomputable def converseRetr (i : D → D') (x' : D') : D :=
  sSup {x | i x ≤ x'}
theorem converseRetr_mono (i : D → D') : Monotone (converseRetr i) := by
  intro a b hab
  exact sSup_le_sSup fun _ hx => le_trans hx hab
theorem incl_sup_of_preservesSSup (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (x y : D) :
    i (x ⊔ y) = i x ⊔ i y := by
  calc i (x ⊔ y) = i (sSup {x, y}) := by rw [sSup_pair]
    _ = sSup (i '' {x, y}) := hi _
    _ = sSup {i x, i y} := by rw [Set.image_pair]
    _ = i x ⊔ i y := sSup_pair
theorem incl_mono_of_preservesSSup (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) :
    Monotone i := by
  intro x y hxy
  have h := incl_sup_of_preservesSSup hi x y
  rw [sup_eq_right.mpr hxy] at h
  rw [h]; exact le_sup_left
theorem le_of_incl_le (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) {x y : D} (h : i x ≤ i y) : x ≤ y := by
  have h1 : i (x ⊔ y) = i y := by rw [incl_sup_of_preservesSSup hi, sup_eq_right.mpr h]
  exact sup_eq_right.mp (hinj h1)
theorem incl_converseRetr_le (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (x' : D') :
    i (converseRetr i x') ≤ x' := by
  show i (sSup {x | i x ≤ x'}) ≤ x'
  rw [hi]
  exact sSup_le (by rintro _ ⟨x, hx, rfl⟩; exact hx)
theorem converseRetr_incl (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hinj : Function.Injective i) (y : D) : converseRetr i (i y) = y := by
  have hset : {x | i x ≤ i y} = Set.Iic y := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    exact ⟨le_of_incl_le hi hinj, fun hx => incl_mono_of_preservesSSup hi hx⟩
  show sSup {x | i x ≤ i y} = y
  rw [hset]
  exact le_antisymm (sSup_le fun _ hx => hx) (le_sSup le_rfl)
theorem converseRetr_preservesDirectedSup
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S))
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    PreservesDirectedSup (converseRetr i) := by
  intro S' hS'ne hS'dir
  apply le_antisymm
  · show sSup {x | i x ≤ sSup S'} ≤ sSup (converseRetr i '' S')
    apply sSup_le
    intro x hx
    have hx' : i x ≤ sSup S' := hx
    rw [← hD.sSup_wayBelow x]
    apply sSup_le
    intro z hz
    have hiz : i z ≪ sSup S' := (hwb hz).trans_le hx'
    obtain ⟨x', hx'S', hzx'⟩ := (wayBelow_sSup_iff hS'ne hS'dir).1 hiz
    have hz_mem : z ∈ {x | i x ≤ x'} := hzx'.le
    exact le_trans (le_sSup hz_mem) (le_sSup ⟨x', hx'S', rfl⟩)
  · apply sSup_le
    rintro _ ⟨x', hx'S', rfl⟩
    exact converseRetr_mono i (le_sSup hx'S')
noncomputable def converseProjection
    (hi : ∀ S : Set D, i (sSup S) = sSup (i '' S)) (hinj : Function.Injective i)
    (hwb : ∀ {x y : D}, x ≪ y → i x ≪ i y) (hD : IsContinuousLattice D) :
    IsContinuousLatticeProjection D D' where
  incl := ⟨i, continuous_of_preservesDirectedSup (fun _ _ _ => hi _)⟩
  retr := ⟨converseRetr i, continuous_of_preservesDirectedSup
    (converseRetr_preservesDirectedSup hi hwb hD)⟩
  retr_incl := fun d => converseRetr_incl hi hinj d
  incl_retr_le := fun x' => incl_converseRetr_le hi x'
end Proposition310
section SubspaceExtension
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompleteLattice Y]
noncomputable def scottSubspaceExtendInf (e : X → Y) (f : X → D) (U : Set Y) : D :=
  sInf (f '' (e ⁻¹' U))
noncomputable def scottSubspaceExtend (e : X → Y) (f : X → D) (y : Y) : D :=
  sSup { d | ∃ U, @IsOpen Y scottTopologicalSpace U ∧ y ∈ U ∧ d = scottSubspaceExtendInf e f U }
end SubspaceExtension
section Projections
def IsProjection (j : ScottMap D D) : Prop :=
  j.comp j = j ∧ j ≤ ScottMap.idMap
theorem isProjection_iff {j : ScottMap D D} :
    IsProjection j ↔ (∀ x, (j : D → D) (j x) = j x) ∧ (∀ x, (j : D → D) x ≤ x) := by
  constructor
  · rintro ⟨hidem, hle⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have h : ((j.comp j : ScottMap D D) : D → D) x = (j : D → D) x := by rw [hidem]
      rwa [ScottMap.comp_apply] at h
    · have h := (ScottMap.le_def.mp hle) x
      rwa [ScottMap.idMap_apply] at h
  · rintro ⟨hidem, hle⟩
    exact ⟨ScottMap.ext fun x => by rw [ScottMap.comp_apply]; exact hidem x,
      ScottMap.le_def.mpr fun x => by rw [ScottMap.idMap_apply]; exact hle x⟩
theorem isProjection_bot : IsProjection (⊥ : ScottMap D D) := by
  rw [isProjection_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · simp only [ScottMap.bot_apply]
  · rw [ScottMap.bot_apply]; exact bot_le
theorem isProjection_sup {j k : ScottMap D D} (hj : IsProjection j) (hk : IsProjection k) :
    IsProjection (j ⊔ k) := by
  rw [isProjection_iff] at hj hk ⊢
  obtain ⟨hjidem, hjle⟩ := hj
  obtain ⟨hkidem, hkle⟩ := hk
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hjkle : (j : D → D) x ⊔ k x ≤ x := sup_le (hjle x) (hkle x)
    have hj_eq : (j : D → D) (j x ⊔ k x) = j x :=
      le_antisymm (j.monotone hjkle) (le_of_eq_of_le (hjidem x).symm (j.monotone le_sup_left))
    have hk_eq : (k : D → D) (j x ⊔ k x) = k x :=
      le_antisymm (k.monotone hjkle) (le_of_eq_of_le (hkidem x).symm (k.monotone le_sup_right))
    rw [ScottMap.sup_apply, ScottMap.sup_apply, hj_eq, hk_eq]
  · rw [ScottMap.sup_apply]; exact sup_le (hjle x) (hkle x)
theorem isProjection_finsetSup {T : Finset (ScottMap D D)} (hT : ∀ j ∈ T, IsProjection j) :
    IsProjection (T.sup id) :=
  Finset.sup_induction isProjection_bot (fun _ ha _ hb => isProjection_sup ha hb) hT
theorem isProjection_directedSup {S : Set (ScottMap D D)} (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) (hS : ∀ j ∈ S, IsProjection j) :
    IsProjection (sSup S) := by
  have hidem : ∀ j ∈ S, ∀ x, (j : D → D) (j x) = j x :=
    fun j hj => (isProjection_iff.mp (hS j hj)).1
  have hle : ∀ j ∈ S, ∀ x, (j : D → D) x ≤ x := fun j hj => (isProjection_iff.mp (hS j hj)).2
  rw [isProjection_iff]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · set A := Set.image (fun j : ScottMap D D => (j : D → D) x) S with hA
    have hAne : A.Nonempty := hSne.image _
    have hAdir : DirectedOn (· ≤ ·) A := by
      rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩
      obtain ⟨m, hm, hjm, hkm⟩ := hSdir j hj k hk
      exact ⟨(m : D → D) x, Set.mem_image_of_mem _ hm, hjm x, hkm x⟩
    have hsSx : ((sSup S : ScottMap D D) : D → D) x = sSup A := ScottMap.sSup_apply S x
    apply le_antisymm
    · rw [hsSx, ScottMap.sSup_apply]
      refine sSup_le ?_
      rintro _ ⟨k, hk, rfl⟩
      show (k : D → D) (sSup A) ≤ sSup A
      rw [k.preservesDirectedSup_coe A hAne hAdir]
      refine sSup_le ?_
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      obtain ⟨m, hm, hjm, hkm⟩ := hSdir j hj k hk
      calc (k : D → D) (j x) ≤ (m : D → D) (j x) := hkm (j x)
        _ ≤ (m : D → D) (m x) := m.monotone (hjm x)
        _ = (m : D → D) x := hidem m hm x
        _ ≤ sSup A := le_sSup (Set.mem_image_of_mem _ hm)
    · rw [hsSx, ScottMap.sSup_apply]
      refine sSup_le ?_
      rintro _ ⟨j, hj, rfl⟩
      have hjxA : (j : D → D) x ≤ sSup A := le_sSup (Set.mem_image_of_mem _ hj)
      calc (j : D → D) x = (j : D → D) (j x) := (hidem j hj x).symm
        _ ≤ (j : D → D) (sSup A) := j.monotone hjxA
        _ ≤ sSup (Set.image (fun f : ScottMap D D => (f : D → D) (sSup A)) S) :=
              le_sSup (Set.mem_image_of_mem _ hj)
  · rw [ScottMap.sSup_apply]
    refine sSup_le ?_
    rintro _ ⟨j, hj, rfl⟩
    exact hle j hj x
theorem isProjection_sSup {T : Set (ScottMap D D)} (hT : ∀ j ∈ T, IsProjection j) :
    IsProjection (sSup T) := by
  rw [IsContinuousLatticeProjection.sSup_finsetSupOf T]
  refine isProjection_directedSup ⟨⊥, ∅, by simp, by simp⟩
    (IsContinuousLatticeProjection.directedOn_finsetSupOf T) ?_
  rintro z ⟨F, hF, rfl⟩
  exact isProjection_finsetSup fun j hj => hT j (hF j hj)
abbrev Projections (D : Type*) [CompleteLattice D] : Type _ := {j : ScottMap D D // IsProjection j}
namespace Projections
noncomputable instance instSupSet : SupSet (Projections D) :=
  ⟨fun T => ⟨sSup (Set.image Subtype.val T), isProjection_sSup (by rintro j ⟨p, _, rfl⟩; exact p.2)⟩⟩
theorem isLUB_sSup (T : Set (Projections D)) : IsLUB T (sSup T) := by
  constructor
  · intro p hp
    apply Subtype.coe_le_coe.mp
    show (p : ScottMap D D) ≤ ((sSup T : Projections D) : ScottMap D D)
    exact le_sSup (Set.mem_image_of_mem _ hp)
  · intro q hq
    apply Subtype.coe_le_coe.mp
    show ((sSup T : Projections D) : ScottMap D D) ≤ (q : ScottMap D D)
    refine sSup_le ?_
    rintro _ ⟨p, hp, rfl⟩
    exact Subtype.coe_le_coe.mpr (hq hp)
noncomputable instance instCompleteLattice : CompleteLattice (Projections D) :=
  completeLatticeOfSup (Projections D) isLUB_sSup
end Projections
end Projections
namespace Proposition313
noncomputable def con : ScottMap D (ScottMap D D) :=
  ⟨fun x => ScottMap.const x, continuous_of_preservesDirectedSup (by
    intro S _ _
    apply ScottMap.ext
    intro y
    rw [ScottMap.sSup_apply, Set.image_image]
    simp only [ScottMap.const_apply, Set.image_id'])⟩
noncomputable def min : ScottMap (ScottMap D D) D :=
  ⟨fun f => (f : D → D) ⊥, continuous_of_preservesDirectedSup (by
    intro F _ _
    show ((sSup F : ScottMap D D) : D → D) ⊥
      = sSup (Set.image (fun f : ScottMap D D => (f : D → D) ⊥) F)
    rw [ScottMap.sSup_apply])⟩
noncomputable def projection : IsContinuousLatticeProjection D (ScottMap D D) where
  incl := con
  retr := min
  retr_incl := fun _ => rfl
  incl_retr_le := fun f => by
    rw [ScottMap.le_def]
    intro y
    show ((ScottMap.const ((f : D → D) ⊥) : ScottMap D D) : D → D) y ≤ (f : D → D) y
    rw [ScottMap.const_apply]
    exact f.monotone bot_le
end Proposition313
namespace Proposition314
def toOrderHom (f : ScottMap D D) : D →o D := ⟨(f : D → D), f.monotone⟩
noncomputable def fix (f : ScottMap D D) : D := (toOrderHom f).lfp
theorem fix_eq (f : ScottMap D D) : (f : D → D) (fix f) = fix f :=
  (toOrderHom f).map_lfp
theorem fix_le {f : ScottMap D D} {x : D} (h : (f : D → D) x ≤ x) : fix f ≤ x :=
  (toOrderHom f).lfp_le h
theorem fix_mono {f f' : ScottMap D D} (hff' : f ≤ f') : fix f ≤ fix f' :=
  fix_le (le_trans (ScottMap.le_def.mp hff' (fix f')) (le_of_eq (fix_eq f')))
theorem fix_preservesDirectedSup : PreservesDirectedSup (fix : ScottMap D D → D) := by
  intro S hSne hSdir
  set T : Set D := Set.image fix S with hTdef
  have hTne : T.Nonempty := hSne.image fix
  have hTdir : DirectedOn (· ≤ ·) T := by
    rintro _ ⟨f, hf, rfl⟩ _ ⟨f', hf', rfl⟩
    obtain ⟨h, hh, hfh, hf'h⟩ := hSdir f hf f' hf'
    exact ⟨fix h, Set.mem_image_of_mem fix hh, fix_mono hfh, fix_mono hf'h⟩
  show fix (sSup S) = sSup T
  apply le_antisymm
  · apply fix_le
    show ((sSup S : ScottMap D D) : D → D) (sSup T) ≤ sSup T
    rw [ScottMap.sSup_apply]
    apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    show (f : D → D) (sSup T) ≤ sSup T
    rw [f.preservesDirectedSup_coe T hTne hTdir]
    apply sSup_le
    rintro _ ⟨_, ⟨f', hf', rfl⟩, rfl⟩
    obtain ⟨h, hh, hfh, hf'h⟩ := hSdir f hf f' hf'
    calc (f : D → D) (fix f')
        ≤ (h : D → D) (fix f') := ScottMap.le_def.mp hfh (fix f')
      _ ≤ (h : D → D) (fix h) := h.monotone (fix_mono hf'h)
      _ = fix h := fix_eq h
      _ ≤ sSup T := le_sSup (Set.mem_image_of_mem fix hh)
  · apply sSup_le
    rintro _ ⟨f, hf, rfl⟩
    exact fix_mono (le_sSup hf)
noncomputable def fixMap : ScottMap (ScottMap D D) D :=
  ⟨fix, continuous_of_preservesDirectedSup fix_preservesDirectedSup⟩
end Proposition314
end Scott1972.ContinuousLattice


