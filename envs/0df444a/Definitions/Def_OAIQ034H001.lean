-- Prove2me | Definitions.Def_OAIQ034H001
-- name    : OAIQ034H001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T05:32:33.867641+00:00
-- url     : https://prove2.me/theorems/a74c5690-127a-4b31-aee4-de6cdfb2737b
-- title:
--   Definitions bundle OAIQ034H001 of the split of OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HyperbolicObstruction.main`, carved from OpenAI's openai/math development (OpenAI, *A hyperbolic group with no geometric CAT(0) action (result family 257)*, OpenAI Math Release, September 25, 2026, result family 257, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 326 declarations of OpenAI's Lean: 122 definitions, 5 inductive types or structures, 2 instances and 197 theorems. The definitions and types are `OAI.HyperbolicObstruction.CoreWordGraph.base`, `OAI.HyperbolicObstruction.CoreWordGraph.common`, `OAI.HyperbolicObstruction.FanLink.B`, `OAI.HyperbolicObstruction.FanLink.D`, `OAI.HyperbolicObstruction.FanLink.IsCyclic`, `OAI.HyperbolicObstruction.FanLink.N`, `OAI.HyperbolicObstruction.FanLink.P`, `OAI.HyperbolicObstruction.FanLink.Q`, `OAI.HyperbolicObstruction.FanLink.State`, `OAI.HyperbolicObstruction.FanLink.State.active`, `OAI.HyperbolicObstruction.FanLink.State.bit`, `OAI.HyperbolicObstruction.FanLink.State.boundary`, `OAI.HyperbolicObstruction.FanLink.State.d`, `OAI.HyperbolicObstruction.FanLink.State.f`, `OAI.HyperbolicObstruction.FanLink.State.n`, `OAI.HyperbolicObstruction.FanLink.State.turn`, `OAI.HyperbolicObstruction.FanLink.T`, `OAI.HyperbolicObstruction.FanLink.allDominant`, `OAI.HyperbolicObstruction.FanLink.enter`, `OAI.HyperbolicObstruction.FanLink.leave`, `OAI.HyperbolicObstruction.FiniteComplex.Chain`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.Facet`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.GraphVertex`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.OldRoutes`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.PolygonGroup`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.Position`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.Vertex`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.apex`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.base`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.baseRoutes`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.capTransport`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.collarFace`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.complex`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.dartStart`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.edgeClass`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.facet`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.firstPosition`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.graph`, `OAI.HyperbolicObstruction.FinitePolygonModel.Data.graphChain` and 87 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/HyperbolicGroups, in whole or in part: `HyperbolicGroups_ActualFragment`, `HyperbolicGroups_ActualLayers`, `HyperbolicGroups_AnnularSeparator`, `HyperbolicGroups_BFSLevels`, `HyperbolicGroups_BFSTree`, `HyperbolicGroups_BalancedGrouping`, `HyperbolicGroups_BoundaryEraseList`, `HyperbolicGroups_BoundaryList`, `HyperbolicGroups_BoundarySplice`, `HyperbolicGroups_ColoredApex`, `HyperbolicGroups_ConnectedLevels`, `HyperbolicGroups_CycleCount`, `HyperbolicGroups_CyclicLink`, `HyperbolicGroups_EdgeChain`, `HyperbolicGroups_EdgeEraseBoundary`, `HyperbolicGroups_FanRoute`, `HyperbolicGroups_FiniteMassTransfer`, `HyperbolicGroups_FinitePolygonModel`, `HyperbolicGroups_FinitePolygonVoltage`, `HyperbolicGroups_FinitePolyhedron`, `HyperbolicGroups_FinitePolyhedronDeck`, `HyperbolicGroups_FinitePolyhedronEdgePaths`, `HyperbolicGroups_FinitePolyhedronLocal`, `HyperbolicGroups_FinitePolyhedronMonodromy`, `HyperbolicGroups_FinitePolyhedronPathAlgebra`, `HyperbolicGroups_FinitePolyhedronPaths`, `HyperbolicGroups_FinitePolyhedronVoltage`, `HyperbolicGroups_Fragment`, `HyperbolicGroups_GraphGroupWalk`, `HyperbolicGroups_GraphSeparatorTransfer`, `HyperbolicGroups_GraphSubstitution`, `HyperbolicGroups_IndexedFillingValue`, `HyperbolicGroups_InvolutionPairs`, `HyperbolicGroups_LinkApex`, `HyperbolicGroups_PairingForest`, `HyperbolicGroups_PathInSet`, `HyperbolicGroups_PathLocalToGlobal`, `HyperbolicGroups_PermErase`, `HyperbolicGroups_PermErasePair`, `HyperbolicGroups_PermEuler`, `HyperbolicGroups_PermSwitch`, `HyperbolicGroups_PicturePartition`, `HyperbolicGroups_PictureTriangulation`, `HyperbolicGroups_PlanarEdgeOrdering`, `HyperbolicGroups_PlanarPartitionBridge`, `HyperbolicGroups_PolygonSphere`, `HyperbolicGroups_SeparatorBudget`, `HyperbolicGroups_SeparatorComponents`, `HyperbolicGroups_SeparatorCutoff`, `HyperbolicGroups_SeparatorDecomposition`, `HyperbolicGroups_SeparatorRecursion`, `HyperbolicGroups_SetoidGlue`, `HyperbolicGroups_SetoidRestrict`, `HyperbolicGroups_Shape`, `HyperbolicGroups_SubpairingGraph`, `HyperbolicGroups_SubpairingTree`, `HyperbolicGroups_TreeCentroid`, `HyperbolicGroups_TreeCentroidComponents`, `HyperbolicGroups_TreeCentroidCut`, `HyperbolicGroups_TreeHull`, `HyperbolicGroups_TreePathHull`, `HyperbolicGroups_TreePathIntDepth`, `HyperbolicGroups_VoltageClosedCells`, `HyperbolicGroups_VoltageEdges`.
--
--   **Imports.** It imports the published bundle `Def_HyperbolicObstruction`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ034H003`, `OAIQ034H004`, `OAIQ034H005` and `OAIQ034H006`.
-- source:
--   OpenAI, A hyperbolic group with no geometric CAT(0) action (result family 257), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 257; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-hyperbolic-group-with-no-geometric-CAT0-action-September-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/HyperbolicGroups at commit adc7f12

import Mathlib
import Definitions.Def_HyperbolicObstruction

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermSwitch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]

/-- Cutting a cyclic vertex-link immediately before two distinct corners
splits it into exactly the displayed two cyclic lists. Singleton cycles are
retained: they are genuine vertex instances, even though their permutation
is the identity. -/
theorem split_list (a b : D) (l m : List D)
    (h : (a :: l ++ b :: m).Nodup) :
    swap a b * (a :: l ++ b :: m).formPerm =
      (a :: l).formPerm * (b :: m).formPerm := by
  induction l generalizing a with
  | nil => simp [List.formPerm_cons_cons,← mul_assoc]
  | cons x l ih =>
    have hab : a ≠ b := by
      intro he; exact (List.nodup_cons.mp h).1 (by simp [he])
    have hxb : x ≠ b := by
      have hx := (List.nodup_cons.mp (List.nodup_cons.mp h).2).1
      intro he; exact hx (by simp [he])
    have hs : swap a b * swap a x = swap a x * swap x b := by
      ext z
      simp [swap_apply_def]
      split_ifs <;> subst_vars <;> simp_all
    change swap a b * (a :: x :: (l ++ b :: m)).formPerm = _
    have hi := ih x (List.nodup_cons.mp h).2
    simp only [List.cons_append] at hi
    rw [List.formPerm_cons_cons, ← mul_assoc, hs, mul_assoc, hi,
      ← mul_assoc, ← List.formPerm_cons_cons]

section Finite
variable [Fintype D]

omit [Fintype D] in
lemma disjoint_lists (l m : List D) (h : l.Disjoint m) :
    l.formPerm.Disjoint m.formPerm := by
  apply disjoint_iff_eq_or_eq.mpr
  intro x
  by_cases hx : x ∈ l
  · right
    exact List.formPerm_apply_of_notMem (fun hm => h hx hm)
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

lemma remainder_disjoint (p : Perm D) (a : D) :
    (p.cycleOf a).Disjoint ((p.cycleOf a)⁻¹ * p) := by
  apply disjoint_iff_eq_or_eq.mpr
  intro x
  by_cases hx : p.SameCycle a x
  · right
    have he : p.cycleOf a x = p x := by simp [cycleOf_apply,hx]
    change (p.cycleOf a).symm (p x) = x
    rw [← he]
    exact (p.cycleOf a).symm_apply_apply x
  · left
    simp [cycleOf_apply,hx]

/-- A cut between two different vertex cycles joins them. The finite
intersection argument handles fixed points without excluding empty links. -/
lemma sameCycle_after_swap (p : Perm D) {a b : D}
    (h : ¬ p.SameCycle a b) : (swap a b * p).SameCycle a b := by
  by_contra hn
  let q := swap a b * p
  have hab : a ≠ b := fun he => h (he.sameCycle p)
  have hp : ∀ x, p.SameCycle a x ∧ q.SameCycle a x →
      p x ≠ a ∧ p x ≠ b ∧ q x = p x := by
    intro x hx
    have hb : p x ≠ b := fun he => h (he ▸ hx.1.apply_right)
    have ha : p x ≠ a := by
      intro he
      have hh := hx.2.apply_right
      have heq : q x = b := by simp [q,mul_apply,he]
      rw [heq] at hh
      exact hn hh
    exact ⟨ha,hb,by simp [q,mul_apply,swap_apply_of_ne_of_ne ha hb]⟩
  let U := {x : D // p.SameCycle a x ∧ q.SameCycle a x}
  let f : U → U := fun x => ⟨p x.val, x.property.1.apply_right,
    by rw [← (hp x.val x.property).2.2]; exact x.property.2.apply_right⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact p.injective (congrArg Subtype.val he)
  have hsurj : Function.Surjective f := Finite.surjective_of_injective hf
  obtain ⟨x,hx⟩ := hsurj ⟨a,SameCycle.rfl,SameCycle.rfl⟩
  exact (hp x.val x.property).1 (congrArg Subtype.val hx)

end Finite
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CycleCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D] [Fintype D]

abbrev VertexClasses (p : Perm D) := Quotient (SameCycle.setoid p)
abbrev Classifier (p : Perm D) := Function.fixedPoints p ⊕ p.cycleFactorsFinset

def classify (p : Perm D) (d : D) : Classifier p :=
  if h : p d = d then .inl ⟨d,h⟩ else
    .inr ⟨p.cycleOf d,cycleOf_mem_cycleFactorsFinset_iff.mpr (mem_support.mpr h)⟩

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SetoidGlue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
attribute [local instance] Classical.propDecidable

/-- Identifying two classes, without making any other identifications. -/
def glue {D : Type*} (s : Setoid D) (a b : D) : Setoid D := by
  classical
  exact Setoid.ker (fun x => if (Quotient.mk s x : Quotient s) = Quotient.mk s b
    then Quotient.mk s a else Quotient.mk s x)

variable {D : Type*} (s : Setoid D) (a b : D)

lemma glue_iff (x y : D) : glue s a b x y ↔
    (if s x b then (Quotient.mk s a : Quotient s) else Quotient.mk s x) =
    (if s y b then (Quotient.mk s a : Quotient s) else Quotient.mk s y) := by
  classical
  change ((if (Quotient.mk s x : Quotient s) = Quotient.mk s b then Quotient.mk s a else Quotient.mk s x) =
    (if (Quotient.mk s y : Quotient s) = Quotient.mk s b then Quotient.mk s a else Quotient.mk s y)) ↔ _
  simp only [Quotient.eq]

lemma le_glue : s ≤ glue s a b := by
  classical
  intro x y h
  rw [glue_iff]
  have ee : (Quotient.mk s x : Quotient s) = Quotient.mk s y := Quotient.sound h
  have hh : s x b ↔ s y b := ⟨fun hx => s.trans' (s.symm' h) hx,fun hy => s.trans' h hy⟩
  simp only [hh,ee]

lemma glue_pair : glue s a b a b := by
  classical
  rw [glue_iff]
  simp

lemma glue_le {t : Setoid D} (hs : s ≤ t) (hab : t a b) : glue s a b ≤ t := by
  classical
  intro x y h
  rw [glue_iff] at h
  split_ifs at h with hx hy hy
  · exact t.trans' (hs hx) (t.symm' (hs hy))
  · exact t.trans' (t.trans' (hs hx) (t.symm' hab)) (hs (Quotient.exact h))
  · exact t.trans' (t.trans' (hs (Quotient.exact h)) hab) (t.symm' (hs hy))
  · exact hs (Quotient.exact h)

lemma glue_eq_of_rel (h : s a b) : glue s a b = s :=
  le_antisymm (glue_le s a b le_rfl h) (le_glue s a b)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

/-- Components after adjoining a finite list of side pairings. -/
def joins (s : Setoid D) : List (D × D) → Setoid D
  | [] => s
  | (a,b)::l => joins (glue s a b) l

def swaps (l : List (D × D)) : Perm D := (l.map (fun ab => swap ab.1 ab.2)).prod

omit [DecidableEq D] [Fintype D] in
lemma le_joins (s : Setoid D) (l : List (D × D)) : s ≤ joins s l := by
  induction l generalizing s with
  | nil => exact le_rfl
  | cons ab l ih => exact (le_glue s ab.1 ab.2).trans (ih _)

omit [DecidableEq D] [Fintype D] in
lemma joins_le (s t : Setoid D) (l : List (D × D)) (hs : s ≤ t)
    (hl : ∀ ab ∈ l, t ab.1 ab.2) : joins s l ≤ t := by
  induction l generalizing s with
  | nil => exact hs
  | cons ab l ih =>
    exact ih _ (glue_le s ab.1 ab.2 hs (hl ab (by simp)))
      (fun cd hc => hl cd (by simp [hc]))

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ColoredApex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
lemma sameCycle_subtypePerm_iff {P : D → Prop} (p : Perm D)
    (hp : ∀ x, P (p x) ↔ P x) (a b : Subtype P) :
    (p.subtypePerm hp).SameCycle a b ↔ p.SameCycle a.val b.val := by
  constructor
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    have h := congrArg Subtype.val hn
    simpa only [subtypePerm_zpow,subtypePerm_apply] using h
  · rintro ⟨n,hn⟩
    refine ⟨n,?_⟩
    apply Subtype.ext
    simpa only [subtypePerm_zpow,subtypePerm_apply] using hn

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_InvolutionPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
variable {D : Type*} [DecidableEq D]

lemma involution_swap_sq (p : Perm D) (hp : p * p = 1) (a : D) :
    (swap a (p a) * p) * (swap a (p a) * p) = 1 := by
  have haa : p (p a) = a := congrArg (fun q : Perm D => q a) hp
  have hc : p * swap a (p a) = swap a (p a) * p := by
    rw [mul_swap_eq_swap_mul,haa,swap_comm (p a) a]
  calc
    _ = swap a (p a) * (p * swap a (p a)) * p := by group
    _ = swap a (p a) * (swap a (p a) * p) * p := by rw [hc]
    _ = 1 := by rw [← mul_assoc,swap_mul_self,one_mul,hp]

variable [Fintype D]

lemma involution_swap_support (p : Perm D) (hp : p * p = 1) (a : D) :
    (swap a (p a) * p).support = p.support \ {a,p a} := by
  have hh : ∀ x, p (p x) = x := fun x => congrArg (fun q : Perm D => q x) hp
  ext x
  by_cases ha : x = a
  · subst x; simp
  by_cases hb : x = p a
  · subst x; simp [hh]
  have hpa : p x ≠ a := fun he => hb (by rw [← hh x,he])
  have hpb : p x ≠ p a := p.injective.ne ha
  simp [mem_support,mul_apply,swap_apply_of_ne_of_ne hpa hpb,ha,hb]

lemma involution_swap_card (p : Perm D) (hp : p * p = 1) {a : D} (ha : p a ≠ a) :
    (swap a (p a) * p).support.card + 2 = p.support.card := by
  rw [involution_swap_support p hp]
  have hs : ({a,p a} : Finset D) ⊆ p.support := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x; exact mem_support.mpr ha
    · have he := Finset.mem_singleton.mp hx
      subst x
      have hh : p (p a) = a := congrArg (fun q : Perm D => q a) hp
      exact mem_support.mpr (by rw [hh]; exact ha.symm)
  have hc := Finset.card_sdiff_add_card_eq_card hs
  simpa [ha,ha.symm] using hc

/-- Every finite involution is a product of its actual paired points, with
exactly half the support cardinal many transpositions. -/
theorem involution_pairs (p : Perm D) (hp : p * p = 1) :
    ∃ l : List (D × D),
      (l.map (fun ab => swap ab.1 ab.2)).prod = p ∧
      2 * l.length = p.support.card ∧
      ∀ ab ∈ l, ab.1 ≠ ab.2 ∧ p ab.1 = ab.2 := by
  generalize hn : p.support.card = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases he : p = 1
    · subst p
      exact ⟨[],by simp,by simpa using hn,by simp⟩
    obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr (fun hh => he (support_eq_empty_iff.mp hh))
    have hpa : p a ≠ a := mem_support.mp ha
    let q := swap a (p a) * p
    have hq : q * q = 1 := involution_swap_sq p hp a
    have hlt : q.support.card < n := by
      rw [← hn]
      exact card_support_swap_mul hpa
    obtain ⟨l,hl,hcard,hpairs⟩ := ih q.support.card hlt q hq rfl
    refine ⟨(a,p a)::l,?_,?_,?_⟩
    · simp only [List.map_cons,List.prod_cons]
      rw [hl]
      simp [q,← mul_assoc]
    · have hc := involution_swap_card p hp hpa
      simp only [List.length_cons]
      dsimp only [q] at hcard
      omega
    · intro ab hab
      rcases List.mem_cons.mp hab with rfl | hab
      · exact ⟨hpa.symm,rfl⟩
      obtain ⟨hnab,heab⟩ := hpairs ab hab
      have hmem : ab.1 ∈ q.support := mem_support.mpr (by rw [heab]; exact hnab.symm)
      have houtside : ab.1 ≠ a ∧ ab.1 ≠ p a := by
        change ab.1 ∈ (swap a (p a) * p).support at hmem
        rw [involution_swap_support p hp] at hmem
        simpa only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hmem).2
      have hpp : p (p ab.1) = ab.1 := congrArg (fun q : Perm D => q ab.1) hp
      have hza : p ab.1 ≠ a := fun he => houtside.2 (by rw [← hpp,he])
      have hzb : p ab.1 ≠ p a := p.injective.ne houtside.1
      exact ⟨hnab,by simpa [q,mul_apply,swap_apply_of_ne_of_ne hza hzb] using heab⟩

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SetoidRestrict
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv
attribute [local instance] Classical.propDecidable
variable {D : Type*}

/-- Restricting an equivalence relation to an invariant part and its complement
partitions its actual quotient, not merely its representatives. -/
theorem card_quotient_split [Finite D] (s : Setoid D) (P : D → Prop)
    (hP : ∀ {x y}, s x y → (P x ↔ P y)) :
    Nat.card (Quotient s) =
      Nat.card (Quotient (s.comap (Subtype.val : Subtype P → D))) +
      Nat.card (Quotient (s.comap (Subtype.val : {x : D // ¬ P x} → D))) := by
  classical
  let qP : Quotient s → Prop := Quotient.lift P (fun _ _ h => propext (hP h))
  let e₁ := Equiv.subtypeQuotientEquivQuotientSubtype P (s₁ := s)
    (s₂ := s.comap Subtype.val) qP (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  let e₂ := Equiv.subtypeQuotientEquivQuotientSubtype (fun x => ¬ P x) (s₁ := s)
    (s₂ := s.comap Subtype.val) (fun q => ¬ qP q) (fun _ => Iff.rfl) (fun _ _ => Iff.rfl)
  have hc := Nat.card_congr (Equiv.Set.sumCompl {q : Quotient s | qP q})
  rw [Nat.card_sum] at hc
  rw [← Nat.card_congr e₁,← Nat.card_congr e₂]
  exact hc.symm

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Shape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace IncidenceTemplate
namespace Occurrences

namespace Shape
variable {s u q v : ℕ}

abbrev Trial (s u q v : ℕ) := Fin s ⊕ (Fin u ⊕ (Fin q ⊕ Fin v))

end Shape
end Occurrences
end IncidenceTemplate
end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermErase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

/-- Fix the punctured point and bypass it in its original cycle. Restricting
this permutation to the complement literally erases that indexed corner. -/
def bypass (p : Perm D) (a : D) : Perm D := swap a (p a) * p

@[simp] lemma bypass_fixed (p : Perm D) (a : D) : bypass p a a = a := by
  simp [bypass]

lemma bypass_away (p : Perm D) (a x : D) (hx : x ≠ a) :
    bypass p a x = if p x = a then p a else p x := by
  by_cases he : p x = a
  · simp [bypass,he]
  · simp [bypass,swap_apply_of_ne_of_ne he (p.injective.ne hx),he]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PermErasePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}

def OffPair (a b x : D) : Prop := x ≠ a ∧ x ≠ b

lemma offPair_invariant {p : Perm D} {a b : D} (ha : p a = a) (hb : p b = b) (x : D) :
    OffPair a b (p x) ↔ OffPair a b x := by
  change (p x ≠ a ∧ p x ≠ b) ↔ (x ≠ a ∧ x ≠ b)
  have h₁ : p x = a ↔ x = a := by simpa only [ha] using (p.apply_eq_iff_eq (x := x) (y := a))
  have h₂ : p x = b ↔ x = b := by simpa only [hb] using (p.apply_eq_iff_eq (x := x) (y := b))
  simp only [ne_eq,h₁,h₂]

variable [DecidableEq D]

def bypassPair (p : Perm D) (a b : D) : Perm D := bypass (bypass p a) b

lemma bypassPair_b (p : Perm D) (a b : D) : bypassPair p a b b = b := bypass_fixed _ _

variable [Fintype D]

lemma card_offPair {a b : D} (hab : a ≠ b) :
    Fintype.card {x : D // OffPair a b x} + 2 = Fintype.card D := by
  have hc : Fintype.card {x : D // ¬ OffPair a b x} = 2 := by
    rw [Fintype.card_of_subtype ({a,b} : Finset D) (by intro x; simp only [Finset.mem_insert,Finset.mem_singleton,OffPair]; tauto)]
    simp [hab]
  have h := Fintype.card_subtype_compl (OffPair a b)
  omega

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PolygonSphere
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable

variable {D B : Type*}

lemma card_quotient_of_classifier (s : Setoid D) (j : D → B)
    (h : ∀ x y, s x y ↔ j x = j y) (hs : Function.Surjective j) :
    Nat.card (Quotient s) = Nat.card B := by
  have he : s = Setoid.ker j := by ext x y; exact h x y
  rw [he]
  exact Nat.card_congr (Setoid.quotientKerEquivOfSurjective j hs)


end HyperbolicObstruction.PictureSwitch
end
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_CyclicLink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


/-! Finite cyclic-link counting used at the literal fan apices.  No planarity,
normal-form, or diagram conclusions are postulated here. -/
noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FanLink

inductive State
  | absent | triangle | other | dominant
  deriving DecidableEq

namespace State

def active : State → Bool
  | absent => false
  | _ => true

def d : State → ℕ
  | dominant => 1
  | _ => 0

def n : State → ℕ
  | other => 1
  | _ => 0

def f : State → ℕ
  | triangle => 1
  | _ => 0

def turn : State → ℕ
  | other | dominant => 1
  | _ => 0

def bit (b : Bool) : ℕ := if b then 1 else 0

def boundary (a b : State) : ℕ := if a.active = b.active then 0 else 1

lemma endpoint_bound (a b : State) (L : Bool)
    (h : ¬ (a = dominant ∧ b = dominant)) :
    d a + d b ≤ n a + n b + f a * bit L + f b * bit L +
      turn a * bit (!L) + turn b * bit (!L) + boundary a b := by
  cases a <;> cases b <;> cases L <;>
    simp_all [d,n,f,turn,bit,boundary,active]

lemma fan_partition (s : State) (L R : Bool)
    (h : s = triangle → L ≠ R) :
    f s * bit L + f s * bit R = f s := by
  cases s <;> cases L <;> cases R <;> simp_all [f,bit]

end State
open State

variable {V : Type*} [Fintype V]

def D (s : V → State) : ℕ := ∑ i, (s i).d
def N (s : V → State) : ℕ := ∑ i, (s i).n
def Q (s : V → State) : ℕ := ∑ i, (s i).f
def P (next : Equiv.Perm V) (s : V → State) (line : V → Bool) : ℕ :=
  ∑ i, (s i).turn * (bit (!(line i)) + bit (!(line (next i))))
def B (next : Equiv.Perm V) (s : V → State) : ℕ :=
  ∑ i, State.boundary (s i) (s (next i))

/-- Direct endpoint charging proves the dominant-turn bound. A selected
triangle has one line endpoint. A nonline endpoint of a top turn incurs its
exceptional loose-side payment. No two dominant turns share a radial side.
This works even before the five-step bound and allows any selection of steps. -/
theorem dominant_endpoint_bound (next : Equiv.Perm V) (s : V → State) (line : V → Bool)
    (hcancel : ∀ i, ¬ (s i = dominant ∧ s (next i) = dominant))
    (hbip : ∀ i, s i = triangle → line i ≠ line (next i)) :
    2 * D s ≤ 2 * N s + Q s + P next s line + B next s := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => endpoint_bound (s i) (s (next i)) (line (next i)) (hcancel i))
  have hfan : (∑ i, (s i).f * bit (line i)) +
      (∑ i, (s i).f * bit (line (next i))) = Q s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => fan_partition _ _ _ (hbip i))
  have hpay : (∑ i, (s i).turn * bit (!(line i))) +
      (∑ i, (s i).turn * bit (!(line (next i)))) = P next s line := by
    simp only [P,Nat.mul_add,Finset.sum_add_distrib]
  simp only [Finset.sum_add_distrib] at h
  rw [Equiv.sum_comp next (fun i => (s i).d),
    Equiv.sum_comp next (fun i => (s i).n),
    Equiv.sum_comp next (fun i => (s i).f * bit (line i)),
    Equiv.sum_comp next (fun i => (s i).turn * bit (!(line i)))] at h
  dsimp [D,N,B] at *
  omega

/-- One connected cyclic order, including the one-element cycle. -/
def IsCyclic (next : Equiv.Perm V) : Prop :=
  ∀ i j, ∃ k : ℕ, (next ^ k) i = j

def enter (a b : Bool) : ℕ := if a = false ∧ b = true then 1 else 0
def leave (a b : Bool) : ℕ := if a = true ∧ b = false then 1 else 0

lemma transition_balance (a b : Bool) : bit a + enter a b = bit b + leave a b := by
  cases a <;> cases b <;> decide

lemma transition_split (a b : State) :
    boundary a b = enter a.active b.active + leave a.active b.active := by
  cases a <;> cases b <;> decide

lemma total_balance (next : Equiv.Perm V) (sel : V → Bool) :
    (∑ i, enter (sel i) (sel (next i))) = ∑ i, leave (sel i) (sel (next i)) := by
  have h := congrArg (fun f : V → ℕ => ∑ i, f i)
    (funext (fun i => transition_balance (sel i) (sel (next i))))
  simp only [Finset.sum_add_distrib] at h
  rw [Equiv.sum_comp next (fun i => bit (sel i))] at h
  omega

lemma boundary_eq_twice (next : Equiv.Perm V) (s : V → State) :
    B next s = 2 * ∑ i, leave (s i).active (s (next i)).active := by
  simp only [B,transition_split,Finset.sum_add_distrib,total_balance,two_mul]

lemma boundary_le_four (next : Equiv.Perm V) (s : V → State)
    (hcard : Fintype.card V ≤ 5) : B next s ≤ 4 := by
  have ha : (∑ i, leave (s i).active (s (next i)).active) ≤ ∑ i, bit (s i).active := by
    apply Finset.sum_le_sum
    intro i _
    cases h : (s i).active <;> cases h' : (s (next i)).active <;> decide
  have hb : (∑ i, enter (s i).active (s (next i)).active) ≤ ∑ i, bit (!(s i).active) := by
    apply Finset.sum_le_sum
    intro i _
    cases h : (s i).active <;> cases h' : (s (next i)).active <;> decide
  have hab : (∑ i, bit (s i).active) + (∑ i, bit (!(s i).active)) = Fintype.card V := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : V, 1 := Finset.sum_congr rfl (fun i _ => by cases (s i).active <;> decide)
      _ = _ := by simp
  rw [total_balance] at hb
  rw [boundary_eq_twice]
  omega

lemma selected_of_no_leave (next : Equiv.Perm V) (sel : V → Bool)
    (hz : (∑ i, leave (sel i) (sel (next i))) = 0) {i : V} (hi : sel i = true) :
    sel (next i) = true := by
  have hz' : leave (sel i) (sel (next i)) = 0 :=
    (Finset.sum_eq_zero_iff.mp hz) i (Finset.mem_univ _)
  cases h : sel (next i)
  · simp [leave,hi,h] at hz'
  · rfl

lemma partial_boundary (next : Equiv.Perm V) (hc : IsCyclic next) (s : V → State)
    (ha : ∃ i, (s i).active = true) (hb : ∃ j, (s j).active = false) :
    2 ≤ B next s := by
  rw [boundary_eq_twice]
  suffices 0 < ∑ i, leave (s i).active (s (next i)).active by omega
  by_contra! hz
  have hz' : (∑ i, leave (s i).active (s (next i)).active) = 0 := Nat.eq_zero_of_le_zero hz
  obtain ⟨i,hi⟩ := ha
  obtain ⟨j,hj⟩ := hb
  obtain ⟨k,hk⟩ := hc i j
  have hi' : ∀ k : ℕ, (s ((next^k) i)).active = true := by
    intro k
    induction k with
    | zero => simpa using hi
    | succ k ih =>
      simpa [pow_succ',Equiv.Perm.mul_apply] using selected_of_no_leave next (fun i => (s i).active) hz' ih
  have := hi' k
  rw [hk,hj] at this
  cases this

lemma boundary_full (next : Equiv.Perm V) (s : V → State)
    (h : ∀ i, (s i).active = true) : B next s = 0 := by
  simp [B,boundary,h]

end FanLink
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_LinkApex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.FanLink
open State
variable {V : Type*} [Fintype V]

def T (s : V → State) : ℕ := ∑ i, (s i).turn

def allDominant : State → State
  | .other => .dominant
  | a => a

lemma turn_eq (a : State) : a.turn = a.d + a.n := by cases a <;> rfl
lemma T_eq (s : V → State) : T s = D s + N s := by
  simp only [T,turn_eq,Finset.sum_add_distrib,D,N]
lemma D_allDominant (s : V → State) : D (allDominant ∘ s) = T s := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma N_allDominant (s : V → State) : N (allDominant ∘ s) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma Q_allDominant (s : V → State) : Q (allDominant ∘ s) = Q s := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma P_allDominant (next : Equiv.Perm V) (s : V → State) (line : V → Bool) :
    P next (allDominant ∘ s) line = P next s line := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_apply]
  cases s i <;> rfl
lemma active_allDominant (a : State) : (allDominant a).active = a.active := by
  cases a <;> rfl

lemma two_turns_le (s : V → State) {i j : V} (hne : i ≠ j)
    (hi : (s i).turn = 1) (hj : (s j).turn = 1) : 2 ≤ T s := by
  classical
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (show ({i,j} : Finset V) ⊆ Finset.univ from Finset.subset_univ _)
    (fun i _ _ => Nat.zero_le ((s i).turn))
  simpa [T,hne,hi,hj] using h

/-- A full triangle-only normalized fan link has at least four steps. The
normality condition rules out immediate reversal of the same indexed triangle;
the fan's bipartition rules out odd circuits. -/
lemma triangle_only_four (next : Equiv.Perm V) (line : V → Bool) [Nonempty V]
    (hbip : ∀ i, line i ≠ line (next i))
    (hback : ∀ i, next (next i) ≠ i) : 4 ≤ Fintype.card V := by
  classical
  obtain ⟨i⟩ := ‹Nonempty V›
  have h01 : i ≠ next i := fun h => hbip i (congrArg line h)
  have h12 : next i ≠ next (next i) := fun h => hbip (next i) (congrArg line h)
  have h02 : i ≠ next (next i) := (hback i).symm
  have hcard : 3 ≤ Fintype.card V := by
    have h := Finset.card_le_card (show ({i,next i,next (next i)} : Finset V) ⊆ Finset.univ from
      Finset.subset_univ _)
    simpa [h01,h12,h02] using h
  have parity : 2 * (∑ i, bit (line i)) = Fintype.card V := by
    have hh : (∑ i, (bit (line i) + bit (line (next i)))) = ∑ _ : V, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hbip i
      cases he : line i <;> cases he' : line (next i) <;> simp_all [bit]
    simp only [Finset.sum_add_distrib] at hh
    rw [Equiv.sum_comp next (fun i => bit (line i))] at hh
    simpa [two_mul] using hh
  omega

/-- The full-link inequality in the r-dominant case.
The assumptions are only the ordinary indexed-side normality and the fan's
bipartition, not a pre-assumed apex or isoperimetric inequality. -/
theorem full_instance_bound (next : Equiv.Perm V) (s : V → State) (line : V → Bool)
    [Nonempty V] (hfull : ∀ i, (s i).active = true)
    (hfix : ∀ i, next i ≠ i)
    (hbip : ∀ i, s i = triangle → line i ≠ line (next i))
    (hback : ∀ i, s i = triangle → s (next i) = triangle → next (next i) ≠ i) :
    (4 : ℝ) - 2 * T s ≤ (Q s : ℝ) + P next s line := by
  rcases Nat.lt_trichotomy (T s) 1 with ht | ht | ht
  · have ht0 : T s = 0 := by omega
    have htri : ∀ i, s i = triangle := by
      intro i
      have hi : (s i).turn = 0 := (Finset.sum_eq_zero_iff.mp ht0) i (Finset.mem_univ _)
      have ha := hfull i
      cases he : s i <;> simp_all [State.turn,State.active]
    have hh := triangle_only_four next line (fun i => hbip i (htri i))
      (fun i => hback i (htri i) (htri (next i)))
    have hq : Q s = Fintype.card V := by simp [Q,htri,State.f]
    rw [ht0,hq]
    have hq' : (4:ℝ) ≤ Fintype.card V := by exact_mod_cast hh
    have hp : (0:ℝ) ≤ P next s line := Nat.cast_nonneg _
    linarith
  · have hcancel : ∀ i, ¬ (allDominant (s i) = dominant ∧
        allDominant (s (next i)) = dominant) := by
      intro i ⟨hi,hj⟩
      have hai : (s i).turn = 1 := by cases he : s i <;> simp_all [allDominant,State.turn]
      have haj : (s (next i)).turn = 1 := by cases he : s (next i) <;> simp_all [allDominant,State.turn]
      have hh := two_turns_le s (hfix i).symm hai haj
      omega
    have hbip' : ∀ i, (allDominant ∘ s) i = triangle → line i ≠ line (next i) := by
      intro i hi
      apply hbip i
      cases he : s i <;> simp_all [allDominant]
    have hh := dominant_endpoint_bound next (allDominant ∘ s) line hcancel hbip'
    rw [D_allDominant,N_allDominant,Q_allDominant,P_allDominant,
      boundary_full next (allDominant ∘ s) (fun i => (active_allDominant _).trans (hfull i)),ht] at hh
    have hh' : (2:ℝ) ≤ (Q s:ℝ) + P next s line := by exact_mod_cast (by simpa using hh : 2 ≤ Q s + P next s line)
    rw [ht]
    norm_num
    exact hh'
  · have hh : (2:ℝ) ≤ (T s:ℝ) := by exact_mod_cast (show 2 ≤ T s by omega)
    have hq : (0:ℝ) ≤ Q s := Nat.cast_nonneg _
    have hp : (0:ℝ) ≤ P next s line := Nat.cast_nonneg _
    linarith

end HyperbolicObstruction.FanLink
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualLayers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction

lemma card_layer_le_support {I : Type*} [Fintype I] (r s : I → ℕ) (j : ℕ)
    (h : ∀ i, 0 < r i → 1 ≤ s i) : Fintype.card {i // j < r i} ≤ ∑ i, s i := by
  rw [Fintype.card_subtype]
  have he := Finset.sum_boole (R := ℕ) (fun i => j < r i) Finset.univ
  simp only [Nat.cast_id] at he
  rw [← he]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact h i (lt_of_le_of_lt (Nat.zero_le j) hi)
  · exact Nat.zero_le _

end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_Fragment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
namespace IncidenceTemplate.Occurrences.Shape

/-- Exact source defect constant. It depends on the fixed parameters, not on
alphabet size, the picture or fragment. -/
def defectConstant (α β δ : ℝ) : ℝ := min (β-7*α) (min (α/5) δ)

end IncidenceTemplate.Occurrences.Shape
end HyperbolicObstruction
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ActualFragment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction
open IncidenceTemplate.Occurrences.Shape

lemma fragment_numeric_bound {α β δ : ℝ} (ha : 0 ≤ α)
    (T Q E V W S J I Br Bd : ℕ)
    (hI : (I : ℝ) ≤ ((3-β)-7*(2-α))*T + (2-α)*W + (2-δ)*E + (3-δ)*V)
    (hA : 3*(T : ℝ) + 2*((W : ℝ)-7*T) ≤ ((Q : ℝ)+S)/2 + 2*J)
    (hQ : Q ≤ 5*W) (hJ : 2*J ≤ Bd)
    (hR : S+Q+4*E+6*V ≤ Br+2*I) :
    defectConstant α β δ * (T+Q+E+V : ℕ) ≤ (Br+Bd : ℕ) := by
  have h1 : defectConstant α β δ ≤ β-7*α := min_le_left _ _
  have h2 : defectConstant α β δ ≤ α/5 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : defectConstant α β δ ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  have hQ' : (Q : ℝ) ≤ 5*W := by exact_mod_cast hQ
  have hQa : α/5*(Q : ℝ) ≤ α*W := by nlinarith
  have ht1 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) T)
  have ht2 := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg (α := ℝ) Q)
  have ht3 := mul_le_mul_of_nonneg_right h3 (show (0:ℝ) ≤ (E:ℝ)+V by positivity)
  have hJ' : 2*(J : ℝ) ≤ Bd := by exact_mod_cast hJ
  have hR' : (S : ℝ)+Q+4*E+6*V ≤ (Br : ℝ)+2*I := by exact_mod_cast hR
  have hBr : (0 : ℝ) ≤ Br := Nat.cast_nonneg _
  push_cast
  nlinarith

end HyperbolicObstruction
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BFSLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {V : Type*}

/-- A median BFS level, with both strict exterior sides at most half.
This applies to any specified vertex subset, not just the full graph. -/
theorem median_level (U : Finset V) (depth : V → ℕ) :
    ∃ m : ℕ, 2*(U.filter (fun v => depth v < m)).card ≤ U.card ∧
      2*(U.filter (fun v => m < depth v)).card ≤ U.card := by
  have hex : ∃ m : ℕ, U.card ≤ 2*(U.filter (fun v => depth v ≤ m)).card := by
    refine ⟨U.sup depth,?_⟩
    have he : U.filter (fun v => depth v ≤ U.sup depth) = U :=
      Finset.filter_eq_self.mpr (fun v hv => Finset.le_sup hv)
    rw [he]; omega
  let m := Nat.find hex
  have hm : U.card ≤ 2*(U.filter (fun v => depth v ≤ m)).card := Nat.find_spec hex
  refine ⟨m,?_,?_⟩
  · by_cases hz : m = 0
    · simp [hz]
    · have hmin := Nat.find_min hex (show m-1 < m by omega)
      have he : U.filter (fun v => depth v ≤ m-1) = U.filter (fun v => depth v < m) := by
        ext v
        simp only [Finset.mem_filter]
        have hmpos : 0 < m := Nat.pos_of_ne_zero hz
        rw [Nat.le_sub_one_iff_lt hmpos]
      rw [he] at hmin
      omega
  · have hh := U.card_filter_add_card_filter_not (fun v => depth v ≤ m)
    simp only [not_le] at hh
    omega

lemma sparse_level_in_interval (U : Finset V) (depth : V → ℤ) (l h : ℤ) (hlh : l ≤ h) :
    ∃ t ∈ Finset.Icc l h, (Finset.Icc l h).card * (U.filter (fun v => depth v = t)).card ≤ U.card := by
  classical
  obtain ⟨t,ht,hmin⟩ := Finset.exists_min_image (Finset.Icc l h)
    (fun t => (U.filter (fun v => depth v = t)).card) ⟨l,Finset.mem_Icc.mpr ⟨le_rfl,hlh⟩⟩
  refine ⟨t,ht,?_⟩
  calc
    _ = ∑ s ∈ Finset.Icc l h, (U.filter (fun v => depth v = t)).card := by simp
    _ ≤ ∑ s ∈ Finset.Icc l h, (U.filter (fun v => depth v = s)).card :=
      Finset.sum_le_sum (fun s hs => hmin s hs)
    _ = (U.filter (fun v => depth v ∈ Finset.Icc l h)).card :=
      Finset.sum_card_fiberwise_eq_card_filter U _ depth
    _ ≤ U.card := Finset.card_filter_le _ _

/-- Two sparse integer levels bracketing an arbitrary median. Negative
levels are permitted (their fibers are empty for graph distances), avoiding
an endpoint exception at the root. -/
theorem two_sparse_levels (U : Finset V) (depth : V → ℤ) (m : ℤ) (a : ℕ) :
    ∃ L H : ℤ, L ≤ m ∧ m ≤ H ∧ H-L ≤ 2*a ∧
      (a+1)*(U.filter (fun v => depth v = L)).card ≤ U.card ∧
      (a+1)*(U.filter (fun v => depth v = H)).card ≤ U.card := by
  have ha : (0 : ℤ) ≤ a := by positivity
  obtain ⟨L,hL,hLc⟩ := sparse_level_in_interval U depth (m-a) m (by omega)
  obtain ⟨H,hH,hHc⟩ := sparse_level_in_interval U depth m (m+a) (by omega)
  have hcardL : (Finset.Icc (m-(a : ℤ)) m).card = a+1 := by rw [Int.card_Icc]; omega
  have hcardH : (Finset.Icc m (m+(a : ℤ))).card = a+1 := by rw [Int.card_Icc]; omega
  rw [hcardL] at hLc
  rw [hcardH] at hHc
  have hLd := Finset.mem_Icc.mp hL
  have hHd := Finset.mem_Icc.mp hH
  exact ⟨L,H,hLd.2,hHd.1,by omega,hLc,hHc⟩

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_ConnectedLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V C : Type*}

lemma preconnected_color_constant (G : SimpleGraph V) (U : Set V)
    (hc : (G.induce U).Preconnected) (color : V → C)
    (hcolor : ∀ v ∈ U, ∀ w ∈ U, G.Adj v w → color v = color w) :
    ∀ v ∈ U, ∀ w ∈ U, color v = color w := by
  have hp : ∀ {v w : U}, (G.induce U).Walk v w → color v.val = color w.val := by
    intro v w p
    induction p with
    | nil => rfl
    | @cons v w u h p ih => exact (hcolor _ v.property _ w.property h).trans ih
  intro v hv w hw
  obtain ⟨p⟩ := hc ⟨v,hv⟩ ⟨w,hw⟩
  exact hp p

/-- A connected set avoiding an integer level cannot pass from below to
above it when adjacent depths differ by at most one. Isolated/empty
induced graphs are covered by Preconnected, with no global connectedness
or positivity assumption. -/
theorem connected_avoids_level (G : SimpleGraph V) (depth : V → ℤ)
    (hd : ∀ v w, G.Adj v w → depth v ≤ depth w+1 ∧ depth w ≤ depth v+1)
    (U : Set V) (hc : (G.induce U).Preconnected) (z : ℤ)
    (hz : ∀ v ∈ U, depth v ≠ z) :
    ∀ v ∈ U, ∀ w ∈ U, (depth v < z ↔ depth w < z) := by
  have hh := preconnected_color_constant G U hc (fun v => depth v < z) (by
    intro v hv w hw hadj
    apply propext
    have hvz := hz v hv
    have hwz := hz w hw
    have hdist := hd v w hadj
    omega)
  intro v hv w hw
  exact Iff.of_eq (hh v hv w hw)

lemma graph_dist_int_adj (G : SimpleGraph V) (r : V) :
    ∀ v w, G.Adj v w → (G.dist r v : ℤ) ≤ (G.dist r w : ℤ)+1 ∧
      (G.dist r w : ℤ) ≤ (G.dist r v : ℤ)+1 := by
  intro v w h
  have hh := h.diff_dist_adj (u := r)
  omega

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_AnnularSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V]

/-- Truncate a root-path separator between two sparse BFS levels.  No
contraction, new embedding, or connectedness of the specified set is needed. -/
theorem annular_separator (G : SimpleGraph V) (U B : Finset V) (depth : V → ℤ)
    (hd : ∀ v w, G.Adj v w → depth v ≤ depth w+1 ∧ depth w ≤ depth v+1)
    (m L H : ℤ) (hLm : L ≤ m) (hmH : m ≤ H)
    (hbelow : 2*(U.filter (fun v => depth v < m)).card ≤ U.card)
    (habove : 2*(U.filter (fun v => m < depth v)).card ≤ U.card)
    (hB : ∀ W : Finset V, W ⊆ U → Disjoint W B →
      (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    ∃ S : Finset V, S ⊆ U ∧
      S.card ≤ (U.filter (fun v => depth v = L)).card +
        (U.filter (fun v => depth v = H)).card +
        (B.filter (fun v => L ≤ depth v ∧ depth v ≤ H)).card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card := by
  classical
  let A := U.filter (fun v => depth v = L)
  let C := U.filter (fun v => depth v = H)
  let I := B.filter (fun v => L ≤ depth v ∧ depth v ≤ H)
  let S := (A ∪ C) ∪ (U ∩ I)
  have hSU : S ⊆ U := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_filter.mp hv).1
      · exact (Finset.mem_filter.mp hv).1
    · exact (Finset.mem_inter.mp hv).1
  refine ⟨S,hSU,?_,?_⟩
  · calc
      S.card ≤ (A ∪ C).card + (U ∩ I).card := Finset.card_union_le _ _
      _ ≤ A.card+C.card+I.card := Nat.add_le_add (Finset.card_union_le _ _) (Finset.card_le_card Finset.inter_subset_right)
  · intro W hWU hWS hc
    have hWL : ∀ v ∈ (W : Set V), depth v ≠ L := by
      intro v hv he
      apply Finset.disjoint_left.mp hWS hv
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hWU hv,he⟩))
    have hWH : ∀ v ∈ (W : Set V), depth v ≠ H := by
      intro v hv he
      apply Finset.disjoint_left.mp hWS hv
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hWU hv,he⟩))
    have hcl := connected_avoids_level G depth hd (W : Set V) hc L hWL
    have hch := connected_avoids_level G depth hd (W : Set V) hc H hWH
    by_cases he : W.Nonempty
    · obtain ⟨v,hv⟩ := he
      by_cases hvl : depth v < L
      · have hsub : W ⊆ U.filter (fun w => depth w < m) := by
          intro w hw
          have hwl := (hcl v hv w hw).mp hvl
          exact Finset.mem_filter.mpr ⟨hWU hw,lt_of_lt_of_le hwl hLm⟩
        exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans hbelow
      · by_cases hvh : H < depth v
        · have hsub : W ⊆ U.filter (fun w => m < depth w) := by
            intro w hw
            have hwne := hWH w hw
            have hiff := hch v hv w hw
            exact Finset.mem_filter.mpr ⟨hWU hw,by omega⟩
          exact (Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)).trans habove
        · apply hB W hWU _ hc
          apply Finset.disjoint_left.mpr
          intro w hw hwB
          have hwL := hWL w hw
          have hwH := hWH w hw
          have hvL := hWL v hv
          have hvH := hWH v hv
          have hliff := hcl v hv w hw
          have hhiff := hch v hv w hw
          have hband : L ≤ depth w ∧ depth w ≤ H := by omega
          apply Finset.disjoint_left.mp hWS hw
          exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hWU hw,
            Finset.mem_filter.mpr ⟨hwB,hband⟩⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp

/-- Uniform sqrt-cardinality bound from one balanced root-path hull; the
hull may be arbitrarily large, provided each integer depth strip has k
vertices per level. -/
theorem sqrt_separator_of_banded_hull (G : SimpleGraph V) (U B : Finset V)
    (depth : V → ℕ) (k : ℕ)
    (hd : ∀ v w, G.Adj v w → (depth v : ℤ) ≤ (depth w : ℤ)+1 ∧
      (depth w : ℤ) ≤ (depth v : ℤ)+1)
    (hband : ∀ L H : ℤ, (B.filter (fun v => L ≤ (depth v : ℤ) ∧ (depth v : ℤ) ≤ H)).card ≤
      k*(H-L+1).toNat)
    (hB : ∀ W : Finset V, W ⊆ U → Disjoint W B →
      (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card) :
    ∃ S : Finset V, S ⊆ U ∧ S.card ≤ (3*k+2)*Nat.sqrt U.card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card := by
  classical
  by_cases hU : U = ∅
  · subst U
    refine ⟨∅,Finset.Subset.refl _,by simp,?_⟩
    intro W hW _ _
    have : W = ∅ := Finset.subset_empty.mp hW
    simp [this]
  let a := Nat.sqrt U.card
  obtain ⟨m,hml,hmh⟩ := median_level U depth
  obtain ⟨L,H,hLm,hmH,hwidth,hLc,hHc⟩ := two_sparse_levels U (fun v => (depth v : ℤ)) m a
  have hml' : 2*(U.filter (fun v => (depth v : ℤ) < (m : ℤ))).card ≤ U.card := by
    simpa only [Nat.cast_lt] using hml
  have hmh' : 2*(U.filter (fun v => (m : ℤ) < (depth v : ℤ))).card ≤ U.card := by
    simpa only [Nat.cast_lt] using hmh
  obtain ⟨S,hSU,hSc,hsep⟩ := annular_separator G U B (fun v => (depth v : ℤ)) hd m L H hLm hmH hml' hmh' hB
  refine ⟨S,hSU,?_,hsep⟩
  have hroot : U.card < (a+1)*(a+1) := Nat.lt_succ_sqrt U.card
  have hLsmall : (U.filter (fun v => (depth v : ℤ) = L)).card ≤ a := by nlinarith
  have hHsmall : (U.filter (fun v => (depth v : ℤ) = H)).card ≤ a := by nlinarith
  have ha : 1 ≤ a := Nat.sqrt_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU))
  have hwidth' : (H-L+1).toNat ≤ 2*a+1 := by omega
  have hh := (hband L H).trans (Nat.mul_le_mul_left k hwidth')
  nlinarith

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BFSTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*}

lemma exists_distance_parent (G : SimpleGraph V) (hG : G.Connected)
    (root v : V) (hv : v ≠ root) :
    ∃ w, G.Adj v w ∧ G.dist root w + 1 = G.dist root v := by
  obtain ⟨p,hp⟩ := hG.exists_walk_length_eq_dist v root
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v w root h p =>
    refine ⟨w,h,?_⟩
    have hh := dist_le p
    have hd := h.diff_dist_adj (u := root)
    rw [G.dist_comm (u := w) (v := root)] at hh
    rw [G.dist_comm (u := v) (v := root)] at hp
    simp only [Walk.length_cons] at hp
    omega

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BalancedGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Group blocks of size at most half into two groups of size at most two
thirds. The total may be less than n because removed vertices are absent. -/
theorem balanced_grouping (w : I → ℕ) (n : ℕ) (htotal : ∑ i, w i ≤ n)
    (hblock : ∀ i, 2*w i ≤ n) :
    ∃ A : Finset I, 3*(∑ i ∈ A, w i) ≤ 2*n ∧ 3*(∑ i ∈ Aᶜ, w i) ≤ 2*n := by
  classical
  by_cases hsmall : 3*(∑ i, w i) ≤ 2*n
  · exact ⟨∅,by simp,by simpa using hsmall⟩
  by_cases hlarge : ∃ i, n ≤ 3*w i
  · obtain ⟨i,hi⟩ := hlarge
    refine ⟨{i},?_,?_⟩
    · simp only [Finset.sum_singleton]
      have hh := hblock i
      omega
    · have hs := Finset.sum_add_sum_compl ({i} : Finset I) w
      simp only [Finset.sum_singleton] at hs
      omega
  push Not at hlarge
  let P := (Finset.univ : Finset I).powerset.filter (fun A => n ≤ 3*(∑ i ∈ A, w i))
  have hP : P.Nonempty := ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),by omega⟩⟩
  obtain ⟨A,hAP,hmin⟩ := Finset.exists_min_image P Finset.card hP
  have hAn := (Finset.mem_filter.mp hAP).2
  have hAne : A.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he,Finset.sum_empty,mul_zero] at hAn
    omega
  obtain ⟨a,ha⟩ := hAne
  have hremove : 3*(∑ i ∈ A.erase a, w i) < n := by
    by_contra h
    have hm := hmin (A.erase a) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),by omega⟩)
    have hcard := Finset.card_erase_lt_of_mem ha
    omega
  have hs : w a + ∑ i ∈ A.erase a, w i = ∑ i ∈ A, w i := Finset.add_sum_erase A w ha
  have ha' := hlarge a
  have hcompl := Finset.sum_add_sum_compl A w
  exact ⟨A,by omega,by omega⟩

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

lemma bypass_formPerm_head (a : D) (xs : List D) (hn : (a::xs).Nodup) :
    bypass (a::xs).formPerm a = xs.formPerm := by
  cases xs with
  | nil => simp [bypass]; rfl
  | cons b xs =>
    rw [bypass,List.formPerm_apply_head _ _ _ hn,List.formPerm_cons_cons]
    rw [← mul_assoc,swap_mul_self,one_mul]

lemma bypassPair_formPerm_head (a b : D) (xs : List D) (hn : (a::b::xs).Nodup) :
    bypassPair (a::b::xs).formPerm a b = xs.formPerm := by
  rw [bypassPair,bypass_formPerm_head _ _ hn,bypass_formPerm_head _ _ hn.of_cons]

lemma bypassPair_formPerm (l r : List D) (a b : D) (hn : (l++a::b::r).Nodup) :
    bypassPair (l++a::b::r).formPerm a b = (l++r).formPerm := by
  have hr : (l++a::b::r) ~r (a::b::(r++l)) := by
    simpa using (List.isRotated_append : (l++a::b::r) ~r ((a::b::r)++l))
  have hn' : (a::b::(r++l)).Nodup := hr.nodup_iff.mp hn
  rw [List.formPerm_eq_of_isRotated hn hr,bypassPair_formPerm_head _ _ _ hn']
  exact List.formPerm_eq_of_isRotated hn'.of_cons.of_cons List.isRotated_append

lemma formPerm_map_apply {E : Type*} [DecidableEq E] (j : D → E)
    (hj : Function.Injective j) (xs : List D) (x : D) :
    (xs.map j).formPerm (j x) = j (xs.formPerm x) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      simp only [List.map_cons,List.formPerm_cons_cons,mul_apply] at ih ⊢
      rw [ih,← hj.map_swap]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundaryEraseList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

namespace IsBoundary
variable {f : Perm D}
  {xs : List D}

omit [DecidableEq D] in
lemma middle_offpair {l r : List D} {a b : D} (hn : (l++a::b::r).Nodup) :
    ∀ x ∈ l++r, OffPair a b x := by
  have hh := List.nodup_append.mp hn
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨hh.2.2 x hx a (by simp),hh.2.2 x hx b (by simp)⟩
  · have ha := (List.nodup_cons.mp hh.2.1).1
    have hb := (List.nodup_cons.mp (List.nodup_cons.mp hh.2.1).2).1
    exact ⟨fun he => ha (by simp [← he,hx]),fun he => hb (he ▸ hx)⟩

end IsBoundary

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_BoundarySplice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]

lemma formPerm_append_join (l : List D) (a b : D) (r : List D) :
    (l++a::b::r).formPerm = (l++[a]).formPerm * swap a b * (b::r).formPerm := by
  induction l with
  | nil => simp only [List.nil_append,List.formPerm_singleton,one_mul,List.formPerm_cons_cons]
  | cons x l ih =>
    cases l with
    | nil => simp only [List.cons_append,List.nil_append,List.formPerm_cons_cons,List.formPerm_singleton,mul_one,mul_assoc]
    | cons y l =>
      simp only [List.cons_append,List.formPerm_cons_cons] at ih ⊢
      rw [ih]; simp only [mul_assoc]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedron
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section


/-! Literal barycentric realizations of finite abstract complexes. No abstract
CW or homotopy replacement is used in the definitions. -/
noncomputable section
open scoped Topology
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V]

def simplex (s : Finset V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ ∀ i, i ∉ s → x i = 0}

def carrierSet (K : AbstractSimplicialComplex V) : Set (V → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
    ∃ s ∈ K.faces, ∀ i, i ∉ s → x i = 0}

abbrev Carrier (K : AbstractSimplicialComplex V) := carrierSet K

lemma simplex_convex (s : Finset V) : Convex ℝ (simplex s) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ←Finset.mul_sum, hx.2.1, hy.2.1, mul_one, hab]
  · intro i hi
    simp [hx.2.2 i hi, hy.2.2 i hi]

def vertex (K : AbstractSimplicialComplex V) (v : V) : Carrier K := by
  classical
  exact ⟨Pi.single v 1, by
    refine ⟨?_, ?_, {v}, K.singleton_mem v, ?_⟩
    · intro i
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp
    · intro i hi
      simp only [Finset.mem_singleton] at hi
      simp [hi]⟩

lemma vertex_mem_simplex (K : AbstractSimplicialComplex V) {s : Finset V} {v : V} (hv : v ∈ s) :
    (vertex K v).val ∈ simplex s := by
  refine ⟨(vertex K v).property.1, (vertex K v).property.2.1, ?_⟩
  intro i hi
  have hne : i ≠ v := by rintro rfl; exact hi hv
  simp [vertex, hne]

lemma simplex_subset_carrier (K : AbstractSimplicialComplex V) {s : Finset V} (hs : s ∈ K.faces) :
    simplex s ⊆ carrierSet K :=
  fun _ hx => ⟨hx.1,hx.2.1,s,hs,hx.2.2⟩

end HyperbolicObstruction.FinitePolyhedron
end
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite barycentric carriers are strongly locally contractible. The
contracting neighborhoods retain every positive coordinate of their center,
so straight contraction never crosses a missing simplex. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] (K : AbstractSimplicialComplex V)

def wideStar (x : Carrier K) : Set (V → ℝ) :=
  {y | ∀ i, 0 < x.val i → 0 < y i}

lemma supported_on_face (x : Carrier K) {y : V → ℝ} (hy : y ∈ wideStar K x)
    {s : Finset V} (hs : ∀ i, i ∉ s → y i = 0) : x.val ∈ simplex s := by
  refine ⟨x.property.1, x.property.2.1, ?_⟩
  intro i hi
  have hn : ¬ 0 < x.val i := by
    intro h
    have hp := hy i h
    rw [hs i hi] at hp
    exact lt_irrefl _ hp
  exact le_antisymm (not_lt.mp hn) (x.property.1 i)

lemma wideStar_starConvex (x : Carrier K) :
    StarConvex ℝ x.val (carrierSet K ∩ wideStar K x) := by
  rintro y ⟨hy,hxy⟩ a b ha hb hab
  obtain ⟨s,hs,hys⟩ := hy.2.2
  have hx := supported_on_face K x hxy hys
  have hi := simplex_convex s hx ⟨hy.1,hy.2.1,hys⟩ ha hb hab
  refine ⟨simplex_subset_carrier K hs hi,?_⟩
  intro i hxi
  change 0 < a * x.val i + b * y i
  have hyi := hxy i hxi
  by_cases hap : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [hap,hb1] using hyi
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm hap)) hxi) (mul_nonneg hb hyi.le)

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A literal flat principal covering of a barycentric polyhedron, obtained
from edge voltages satisfying exactly the two-dimensional face relations.
The topology is Mathlib's fiber-bundle gluing topology, not the product.
This construction does not assert that the cover is simply connected. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] (K : AbstractSimplicialComplex V)

/-- The open star of a vertex in the actual barycentric realization. -/
def openStar (v : V) : Set (Carrier K) := {x | 0 < x.val v}

lemma openStar_isOpen (v : V) : IsOpen (openStar K v) :=
  isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)

lemma exists_positive (x : Carrier K) : ∃ v, 0 < x.val v := by
  by_contra! h
  have hz : ∀ v, x.val v = 0 := fun v => le_antisymm (h v) (x.property.1 v)
  have hh := x.property.2.1
  simp only [hz,Finset.sum_const_zero] at hh
  norm_num at hh

variable [DecidableEq V]

lemma face_of_positive (x : Carrier K) {s : Finset V} (hs : s.Nonempty)
    (hpos : ∀ v ∈ s, 0 < x.val v) : s ∈ K.faces := by
  obtain ⟨t,ht,hxt⟩ := x.property.2.2
  refine (K.isRelLowerSet_faces ht).2 ?_ hs
  intro v hv
  by_contra hn
  have hp := hpos v hv
  rw [hxt v hn] at hp
  exact lt_irrefl _ hp

lemma triangle_of_positive (x : Carrier K) {a b c : V}
    (ha : 0 < x.val a) (hb : 0 < x.val b) (hc : 0 < x.val c) :
    {a,b,c} ∈ K.faces := by
  apply face_of_positive K x (by simp)
  intro v hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl|rfl|rfl <;> assumption

variable (G : Type*) [Group G]

/-- An edge-voltage cocycle. Values off the edge set are immaterial. -/
structure Voltage where
  value : V → V → G
  self : ∀ v, value v v = 1
  triangle : ∀ a b c, {a,b,c} ∈ K.faces → value a b * value b c = value a c

namespace Voltage
variable {K G} (v : Voltage K G)

omit [Fintype V] in
lemma reverse {a b : V} (h : {a,b} ∈ K.faces) : v.value b a = (v.value a b)⁻¹ := by
  have hh := v.triangle a b a (by
    have hf : ({a,b,a} : Finset V) = {a,b} := by ext z; simp; tauto
    rw [hf]; exact h)
  rw [v.self] at hh
  exact eq_inv_of_mul_eq_one_right hh

variable [TopologicalSpace G] [DiscreteTopology G]

/-- Charts retain the positive barycentric coordinate of their chosen vertex.
Multiplicative transition functions are locally constant, with the literal
triangular relation providing their cocycle identity. -/
def core : FiberBundleCore V (Carrier K) G where
  baseSet := openStar K
  isOpen_baseSet := openStar_isOpen K
  indexAt x := (exists_positive K x).choose
  mem_baseSet_at x := (exists_positive K x).choose_spec
  coordChange i j _ g := g * v.value i j
  coordChange_self i _ _ g := by rw [v.self,mul_one]
  continuousOn_coordChange i j :=
    ((continuous_of_discreteTopology : Continuous (fun g : G => g * v.value i j)).comp continuous_snd).continuousOn
  coordChange_comp i j k x hx g := by
    rw [mul_assoc,v.triangle i j k (triangle_of_positive K x hx.1.1 hx.1.2 hx.2)]

abbrev TotalSpace := v.core.TotalSpace
abbrev proj : v.TotalSpace → Carrier K := v.core.proj

end Voltage
end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PathInSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint-preserving restrictions and homotopies inside a simply connected
subspace. Used to turn coordinate-star homotopies into actual path homotopies. -/
noncomputable section

open Set
namespace HyperbolicObstruction.PathInSet
variable {X : Type*} [TopologicalSpace X] {x y : X} (s : Set X)

def restrict (p : Path x y) (hx : x ∈ s) (hy : y ∈ s) (hp : ∀ t, p t ∈ s) :
    Path (⟨x,hx⟩ : s) ⟨y,hy⟩ where
  toFun t := ⟨p t,hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] lemma restrict_map (p : Path x y) (hx : x ∈ s) (hy : y ∈ s) (hp : ∀ t, p t ∈ s) :
    (restrict s p hx hy hp).map continuous_subtype_val = p := by ext; rfl

lemma homotopic [SimplyConnectedSpace s] (p q : Path x y)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) : p.Homotopic q := by
  have hx : x ∈ s := p.source ▸ hp 0
  have hy : y ∈ s := p.target ▸ hp 1
  have hh := SimplyConnectedSpace.paths_homotopic
    (restrict s p hx hy hp) (restrict s q hx hy hq)
  simpa using hh.map ⟨Subtype.val,continuous_subtype_val⟩

end HyperbolicObstruction.PathInSet
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Canonical straight paths and the actual contractible open vertex stars.
There are no combinatorial-to-topological equivalences assumed here. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

lemma wideStar_vertex (v : V) : wideStar K (vertex K v) = {y | 0 < y v} := by
  ext y
  simp only [wideStar,vertex,mem_ofPred_eq,Pi.single_apply]
  constructor
  · intro h; simpa using h v (by simp)
  · intro h i hi
    by_cases hv : i = v
    · subst i; exact h
    · simp [hv] at hi

lemma openStar_ambient_starConvex (v : V) :
    StarConvex ℝ (vertex K v).val (carrierSet K ∩ {y | 0 < y v}) := by
  simpa only [wideStar_vertex] using wideStar_starConvex K (vertex K v)

omit [DecidableEq V] in
lemma vertex_mem_openStar (v : V) : vertex K v ∈ openStar K v := by
  simp [openStar,vertex]

def openStarHomeomorph (v : V) :
    openStar K v ≃ₜ ((carrierSet K ∩ {y : V → ℝ | 0 < y v}) : Set (V → ℝ)) where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

instance openStar_contractible (v : V) : ContractibleSpace (openStar K v) := by
  have : ContractibleSpace ((carrierSet K ∩ {y : V → ℝ | 0 < y v}) : Set (V → ℝ)) :=
    (openStar_ambient_starConvex K v).contractibleSpace
      ⟨(vertex K v).val,(vertex K v).property,vertex_mem_openStar K v⟩
  exact (openStarHomeomorph K v).contractibleSpace

/-- The affine path when its entire segment lies in the actual carrier. -/
def straight (x y : Carrier K) (h : segment ℝ x.val y.val ⊆ carrierSet K) : Path x y where
  toFun t := ⟨Path.segment x.val y.val t,h (Path.range_segment x.val y.val ▸ mem_range_self t)⟩
  continuous_toFun := (Path.segment x.val y.val).continuous.subtype_mk _
  source' := Subtype.ext (Path.segment x.val y.val).source
  target' := Subtype.ext (Path.segment x.val y.val).target

omit [DecidableEq V] in
@[simp] lemma straight_val (x y : Carrier K) (h) (t) :
    (straight K x y h t).val = AffineMap.lineMap x.val y.val (t : ℝ) := rfl

omit [DecidableEq V] in
lemma straight_in_face {s : Finset V} (hs : s ∈ K.faces) (x y : Carrier K)
    (hx : x.val ∈ simplex s) (hy : y.val ∈ simplex s) :
    segment ℝ x.val y.val ⊆ carrierSet K :=
  ((simplex_convex s).segment_subset hx hy).trans (simplex_subset_carrier K hs)

def facePath {s : Finset V} (hs : s ∈ K.faces) (x y : Carrier K)
    (hx : x.val ∈ simplex s) (hy : y.val ∈ simplex s) : Path x y :=
  straight K x y (straight_in_face K hs x y hx hy)

def edgePath {a b : V} (h : {a,b} ∈ K.faces) : Path (vertex K a) (vertex K b) :=
  facePath K h _ _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp))

/-- The radial path from a star-center to a point in its open star. -/
def starPath (v : V) (x : Carrier K) (hx : x ∈ openStar K v) : Path (vertex K v) x :=
  straight K _ _ (((openStar_ambient_starConvex K v).segment_subset ⟨x.property,hx⟩).trans inter_subset_left)

lemma starPath_mem (v : V) (x : Carrier K) (hx : x ∈ openStar K v) (t) :
    starPath K v x hx t ∈ openStar K v :=
  ((openStar_ambient_starConvex K v).segment_subset ⟨x.property,hx⟩
    (Path.range_segment (vertex K v).val x.val ▸ mem_range_self t)).2

lemma homotopic_in_star (v : V) {x y : Carrier K} (p q : Path x y)
    (hp : ∀ t, p t ∈ openStar K v) (hq : ∀ t, q t ∈ openStar K v) : p.Homotopic q :=
  PathInSet.homotopic (openStar K v) p q hp hq

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronEdgePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Edge paths generate the actual path homotopy groupoid of a finite
barycentric realization. The proof uses the literal open stars, not an
unproved simplicial-approximation principle. -/
noncomputable section

open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

abbrev inFace (s : Finset V) : Set (Carrier K) := {x | x.val ∈ simplex s}

def inFaceHomeomorph {s : Finset V} (hs : s ∈ K.faces) : inFace K s ≃ₜ simplex s where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,simplex_subset_carrier K hs x.property⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

omit [DecidableEq V] in
lemma inFace_contractible {s : Finset V} (hs : s ∈ K.faces) : ContractibleSpace (inFace K s) := by
  obtain ⟨i,hi⟩ := (K.isRelLowerSet_faces hs).1
  have : Nonempty (simplex s) := ⟨⟨(vertex K i).val,vertex_mem_simplex K hi⟩⟩
  have : ContractibleSpace (simplex s) := (simplex_convex s).contractibleSpace ⟨(vertex K i).val,vertex_mem_simplex K hi⟩
  exact (inFaceHomeomorph K hs).contractibleSpace

omit [DecidableEq V] in
lemma homotopic_in_face {s : Finset V} (hs : s ∈ K.faces) {x y : Carrier K}
    (p q : Path x y) (hp : ∀ t, p t ∈ inFace K s) (hq : ∀ t, q t ∈ inFace K s) : p.Homotopic q := by
  have := inFace_contractible K hs
  exact PathInSet.homotopic (inFace K s) p q hp hq

omit [DecidableEq V] in
lemma straight_mem_face {s : Finset V} {x y : Carrier K} (h)
    (hx : x ∈ inFace K s) (hy : y ∈ inFace K s) (t) : straight K x y h t ∈ inFace K s :=
  (simplex_convex s).segment_subset hx hy
    (Path.range_segment x.val y.val ▸ mem_range_self t)

lemma positive_mem_face {s : Finset V} (x : Carrier K)
    (hx : x ∈ inFace K s) {a : V} (ha : x ∈ openStar K a) : a ∈ s := by
  by_contra hn
  have hp : 0 < x.val a := ha
  rw [hx.2.2 a hn] at hp
  exact lt_irrefl _ hp

lemma commonStar_edge (x : Carrier K) {a b : V}
    (ha : x ∈ openStar K a) (hb : x ∈ openStar K b) : {a,b} ∈ K.faces := by
  apply face_of_positive K x (by simp)
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> assumption

lemma radial_bridge (x : Carrier K) {a b : V}
    (ha : x ∈ openStar K a) (hb : x ∈ openStar K b) :
    ((starPath K a x ha).trans (starPath K b x hb).symm).Homotopic
      (edgePath K (commonStar_edge K x ha hb)) := by
  obtain ⟨s,hs,hxs⟩ := x.property.2.2
  have hx : x ∈ inFace K s := ⟨x.property.1,x.property.2.1,hxs⟩
  have hsa := vertex_mem_simplex K (positive_mem_face K x hx ha)
  have hsb := vertex_mem_simplex K (positive_mem_face K x hx hb)
  apply homotopic_in_face K hs
  · intro t
    have ht := mem_range_self (f := (starPath K a x ha).trans (starPath K b x hb).symm) t
    rw [Path.trans_range] at ht
    rcases ht with ⟨u,heq⟩|⟨u,heq⟩
    · rw [←heq]; exact straight_mem_face K _ hsa hx u
    · rw [←heq]
      change starPath K b x hb (unitInterval.symm u) ∈ inFace K s
      exact straight_mem_face K _ hsb hx _
  · intro t
    unfold edgePath facePath
    exact straight_mem_face K _ hsa hsb t

/-- A genuine finite vertex edge path. -/
inductive EdgeChain : V → V → Type _
  | nil (a) : EdgeChain a a
  | cons {a b c} (edge : {a,b} ∈ K.faces) (tail : EdgeChain b c) : EdgeChain a c

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PathLocalToGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite-partition local-to-global principle for homotopy classes of actual
continuous paths. This will convert open-star control into edge generation. -/
noncomputable section

open Set
open scoped unitInterval
namespace HyperbolicObstruction.PathLocalToGlobal
variable {X : Type*} [TopologicalSpace X]
abbrev Q (x y : X) := Path.Homotopic.Quotient x y
variable (R : ∀ x y : X, Q x y → Prop)

lemma cast {x y x' y' : X} {p : Q x y} (hx : x' = x) (hy : y' = y)
    (h : R x y p) : R x' y' (p.cast hx hy) := by
  subst x'; subst y'; simpa using h

/-- No subdivision or simplicial approximation assumption is made: the
partition is obtained from compactness of the actual unit interval. -/
theorem of_open_cover {ι : Type*} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (cover : ∀ x, ∃ i, x ∈ U i)
    (hrefl : ∀ x, R x x (.refl x))
    (htrans : ∀ {x y z} {p : Q x y} {q : Q y z}, R x y p → R y z q → R x z (p.trans q))
    (hlocal : ∀ i {x y} (p : Path x y), (∀ t, p t ∈ U i) → R x y (.mk p))
    {x y : X} (p : Path x y) : R x y (.mk p) := by
  obtain ⟨t,ht0,hmono,⟨N,hN⟩,ht⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hU i).preimage p.continuous)
      (show univ ⊆ ⋃ i, p ⁻¹' U i from by
        intro s _
        obtain ⟨i,hi⟩ := cover (p s)
        exact mem_iUnion.mpr ⟨i,hi⟩)
  have hall (n : ℕ) : R (p (t 0)) (p (t n)) (.mk (p.subpath (t 0) (t n))) := by
    induction n with
    | zero => simpa using hrefl (p (t 0))
    | succ n ih =>
      obtain ⟨i,hi⟩ := ht n
      have hs : ∀ s, p.subpath (t n) (t (n+1)) s ∈ U i := by
        intro s
        have hr := mem_range_self (f := p.subpath (t n) (t (n+1))) s
        rw [p.range_subpath_of_le _ _ (hmono (Nat.le_succ n))] at hr
        obtain ⟨r,hr,he⟩ := hr
        exact he ▸ hi hr
      have hh := htrans ih (hlocal i _ hs)
      have he : Path.Homotopic.Quotient.mk ((p.subpath (t 0) (t n)).trans (p.subpath (t n) (t (n+1)))) =
          Path.Homotopic.Quotient.mk (p.subpath (t 0) (t (n+1))) :=
        Path.Homotopic.Quotient.eq.mpr ⟨Path.Homotopy.subpathTransSubpath p _ _ _⟩
      exact he ▸ hh
  have hlast := hall N
  rw [ht0,hN N le_rfl,Path.subpath_zero_one] at hlast
  have hh := cast R p.source.symm p.target.symm hlast
  simpa using hh

end HyperbolicObstruction.PathLocalToGlobal
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeChain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

namespace EdgeChain
variable {K}
def append {a b c : V} : EdgeChain K a b → EdgeChain K b c → EdgeChain K a c
  | .nil _, q => q
  | .cons h p, q => .cons h (append p q)

def path {a b : V} : EdgeChain K a b → Path (vertex K a) (vertex K b)
  | .nil _ => .refl _
  | .cons h p => (edgePath K h).trans p.path

abbrev pathClass {a b : V} (p : EdgeChain K a b) :
    Path.Homotopic.Quotient (vertex K a) (vertex K b) := .mk p.path

@[simp] lemma pathClass_nil (a : V) : pathClass (.nil a : EdgeChain K a a) = .refl _ := rfl
@[simp] lemma pathClass_cons {a b c : V} (h : {a,b} ∈ K.faces) (p : EdgeChain K b c) :
    pathClass (.cons h p) = (Path.Homotopic.Quotient.mk (edgePath K h)).trans p.pathClass := rfl

@[simp] lemma pathClass_append {a b c : V} (p : EdgeChain K a b) (q : EdgeChain K b c) :
    (p.append q).pathClass = p.pathClass.trans q.pathClass := by
  induction p with
  | nil _ => simp [append]
  | cons h p ih => simp only [append,pathClass_cons,ih,Path.Homotopic.Quotient.trans_assoc]
end EdgeChain

/-- Normal form with one radial segment at each endpoint. -/
def EdgeTame {x y : Carrier K} (p : Path.Homotopic.Quotient x y) : Prop :=
  ∃ (a b : V) (ha : x ∈ openStar K a) (hb : y ∈ openStar K b) (c : EdgeChain K a b),
    p = (Path.Homotopic.Quotient.mk (starPath K a x ha)).symm.trans
      (c.pathClass.trans (Path.Homotopic.Quotient.mk (starPath K b y hb)))

lemma edgeTame_of_star {x y : Carrier K} (v : V) (p : Path x y)
    (hp : ∀ t, p t ∈ openStar K v) : EdgeTame K (.mk p) := by
  have hx : x ∈ openStar K v := p.source ▸ hp 0
  have hy : y ∈ openStar K v := p.target ▸ hp 1
  refine ⟨v,v,hx,hy,.nil v,?_⟩
  simp only [EdgeChain.pathClass_nil,Path.Homotopic.Quotient.refl_trans,
    ←Path.Homotopic.Quotient.mk_symm,←Path.Homotopic.Quotient.mk_trans]
  apply Path.Homotopic.Quotient.eq.mpr
  apply homotopic_in_star K v p _ hp
  intro t
  have ht := mem_range_self (f := (starPath K v x hx).symm.trans (starPath K v y hy)) t
  rw [Path.trans_range] at ht
  rcases ht with ⟨u,heq⟩|⟨u,heq⟩
  · rw [←heq]; exact starPath_mem K v x hx (unitInterval.symm u)
  · rw [←heq]; exact starPath_mem K v y hy u

lemma edgeTame_refl (x : Carrier K) : EdgeTame K (.refl x) := by
  obtain ⟨v,hv⟩ := exists_positive K x
  exact edgeTame_of_star K v (.refl x) (fun _ => hv)

lemma edgeTame_trans {x y z : Carrier K} {p : Path.Homotopic.Quotient x y}
    {q : Path.Homotopic.Quotient y z} (hp : EdgeTame K p) (hq : EdgeTame K q) :
    EdgeTame K (p.trans q) := by
  obtain ⟨a,b,ha,hb,c,rfl⟩ := hp
  obtain ⟨d,e,hd,he,f,rfl⟩ := hq
  refine ⟨a,e,ha,he,c.append (.cons (commonStar_edge K y hb hd) f),?_⟩
  have hbridge := Path.Homotopic.Quotient.eq.mpr (radial_bridge K y hb hd)
  change (Path.Homotopic.Quotient.mk (starPath K b y hb)).trans
    (Path.Homotopic.Quotient.mk (starPath K d y hd)).symm = _ at hbridge
  simp only [EdgeChain.pathClass_append,EdgeChain.pathClass_cons,
    Path.Homotopic.Quotient.trans_assoc]
  rw [←hbridge]
  simp only [Path.Homotopic.Quotient.trans_assoc]

theorem all_paths_edgeTame {x y : Carrier K} (p : Path x y) : EdgeTame K (.mk p) :=
  PathLocalToGlobal.of_open_cover (fun _ _ => EdgeTame K) (openStar K)
    (openStar_isOpen K) (exists_positive K) (edgeTame_refl K)
    (fun hp hq => edgeTame_trans K hp hq)
    (fun index {_ _} path hypothesis => edgeTame_of_star K index path hypothesis) p

lemma vertex_in_openStar {a b : V} (h : vertex K a ∈ openStar K b) : a = b := by
  by_contra hn
  have he : b ≠ a := Ne.symm hn
  change 0 < (vertex K a).val b at h
  simp [vertex,he] at h

@[simp] lemma starPath_self (a : V) (h : vertex K a ∈ openStar K a) :
    starPath K a (vertex K a) h = Path.refl (vertex K a) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact AffineMap.lineMap_same_apply _ _

/-- Every actual continuous path between vertices has a finite edge-chain
representative, with the same endpoints and in its actual homotopy class. -/
theorem edgePath_representative {a b : V} (p : Path (vertex K a) (vertex K b)) :
    ∃ c : EdgeChain K a b, p.Homotopic c.path := by
  obtain ⟨x,y,hx,hy,c,hc⟩ := all_paths_edgeTame K p
  have ha := vertex_in_openStar K hx
  have hb := vertex_in_openStar K hy
  subst x; subst y
  refine ⟨c,Path.Homotopic.Quotient.eq.mp ?_⟩
  have hr : (Path.Homotopic.Quotient.refl (vertex K a)).symm = .refl _ := rfl
  simpa only [starPath_self, Path.Homotopic.Quotient.mk_refl, hr,
    Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl] using hc

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_EdgeEraseBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D]
namespace IsBoundary

omit [DecidableEq D] in
lemma splice_heads_offpair {a b : D} {l r : List D}
    (hn : (a::(r++b::l)).Nodup) : ∀ x ∈ r++l, OffPair a b x := by
  intro x hx
  have hh := List.nodup_cons.mp hn
  have hrl := List.nodup_append.mp hh.2
  refine ⟨?_,?_⟩
  · intro he
    apply hh.1
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (he ▸ hx)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (he ▸ hx))
  · intro he
    rcases List.mem_append.mp hx with hx | hx
    · exact hrl.2.2 x hx b (by simp) he
    · exact (List.nodup_cons.mp hrl.2.1).1 (he ▸ hx)

end IsBoundary
end HyperbolicObstruction.PictureSwitch
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphGroupWalk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphGroupWalk
open SimpleGraph
variable {V H : Type*} {G : SimpleGraph V} [Group H]

def eval (c : G.Dart → H) {u v : V} (p : G.Walk u v) : H := (p.darts.map c).prod
@[simp] lemma eval_nil (c : G.Dart → H) (u : V) : eval c (.nil : G.Walk u u) = 1 := rfl
@[simp] lemma eval_cons (c : G.Dart → H) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    eval c (.cons h p) = c ⟨(u,v),h⟩ * eval c p := rfl
@[simp] lemma eval_append (c : G.Dart → H) {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    eval c (p.append q) = eval c p * eval c q := by simp [eval]

lemma short_loop_eval (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    {u v : V} (h : G.Adj u v) (p : G.Walk v u) (hp : p.length + 1 < 3) :
    eval c (.cons h p) = 1 := by
  cases p with
  | nil => exact (h.ne rfl).elim
  | @cons v w u h' p =>
    have hp0 : p.length = 0 := by simp only [Walk.length_cons] at hp; omega
    have hn := Walk.length_eq_zero_iff.mp hp0
    cases hn
    have hh := hc ⟨(u,v),h⟩
    simp only [eval_cons,eval_nil,mul_one]
    rw [show c ⟨(v,u),h'⟩ = (c ⟨(u,v),h⟩)⁻¹ from hh,mul_inv_cancel]

/-- Noncommutative loop erasure. Killing all elementary cycles suffices;
commutativity, a commutator relation, or graph connectedness is not assumed. -/
theorem reduce_to_path (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    (hcycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → eval c p = 1)
    {u v : V} (p : G.Walk u v) :
    ∃ q : G.Walk u v, q.IsPath ∧ eval c p = eval c q := by
  classical
  induction p with
  | nil => exact ⟨.nil,Walk.IsPath.nil,rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨q,hq,he⟩ := ih
    by_cases hu : u ∈ q.support
    · let a := q.takeUntil u hu
      let b := q.dropUntil u hu
      have hab : a.append b = q := q.take_spec hu
      have ha : a.IsPath := hq.takeUntil hu
      have hb : b.IsPath := hq.dropUntil hu
      have heab : eval c a * eval c b = eval c q := by rw [← eval_append,hab]
      have hz : eval c (Walk.cons h a) = 1 := by
        by_cases hlen : 3 ≤ a.length + 1
        · apply hcycle
          apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
          exact ⟨by simpa using ha,hlen⟩
        · exact short_loop_eval c hc h a (by omega)
      refine ⟨b,hb,?_⟩
      rw [eval_cons,he,← heab,← mul_assoc]
      change eval c (Walk.cons h a) * eval c b = eval c b
      rw [hz,one_mul]
    · exact ⟨.cons h q,hq.cons hu,by simp only [eval_cons,he]⟩

theorem closed_eval_one (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    (hcycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → eval c p = 1)
    {u : V} (p : G.Walk u u) : eval c p = 1 := by
  obtain ⟨q,hq,he⟩ := reduce_to_path c hc hcycle p
  have hn := Walk.isPath_iff_nil.mp hq
  cases hn
  exact he

lemma eval_reverse (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    {u v : V} (p : G.Walk u v) : eval c p.reverse = (eval c p)⁻¹ := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [Walk.reverse_cons,eval_append,ih]
    simp only [eval_cons,eval_nil,mul_one,mul_inv_rev]
    rw [show c ⟨(v,u),h.symm⟩ = (c ⟨(u,v),h⟩)⁻¹ from hc ⟨(u,v),h⟩]

/-- Route potentials under elementary-cycle relations. Only the chosen
routes, not a spanning-tree axiom, are needed. -/
theorem route_edge (c : G.Dart → H) (hc : ∀ d, c d.symm = (c d)⁻¹)
    (hcycle : ∀ (u : V) (p : G.Walk u u), p.IsCycle → eval c p = 1)
    {r u v : V} (p : G.Walk r u) (q : G.Walk r v) (h : G.Adj u v) :
    eval c p * c ⟨(u,v),h⟩ = eval c q := by
  have hz := closed_eval_one c hc hcycle (p.append ((Walk.cons h Walk.nil).append q.reverse))
  simp only [eval_append,eval_cons,eval_nil,mul_one,eval_reverse c hc] at hz
  exact mul_inv_eq_one.mp (by simpa only [mul_assoc] using hz)

end HyperbolicObstruction.GraphGroupWalk
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FanRoute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.CoreWordGraph
open IncidenceTemplate SimpleGraph

def base (i : Fin 7) : Fin 11 := ⟨i.val,lt_trans i.isLt (by decide)⟩
def common (i : Fin 7) : Fin 7 := ![1,2,1,6,2,1,6] i

end HyperbolicObstruction.CoreWordGraph
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FiniteMassTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {A B : Type*} [Fintype A]

/-- Push a nonnegative mass along an actual finite map. -/
def pushMass (f : A → B) (weight : A → ℝ) (b : B) : ℝ :=
  ∑ a : A, if f a = b then weight a else 0

lemma pushMass_nonneg (f : A → B) (weight : A → ℝ) (hw : ∀ a, 0 ≤ weight a) :
    ∀ b, 0 ≤ pushMass f weight b := by
  classical
  intro b
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact hw a
  · exact le_rfl

lemma pushMass_total [Fintype B] (f : A → B) (weight : A → ℝ) :
    ∑ b : B, pushMass f weight b = ∑ a : A, weight a := by
  classical
  unfold pushMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

lemma pushMass_sum (f : A → B) (weight : A → ℝ) (C : Finset B) :
    ∑ b ∈ C, pushMass f weight b =
      ∑ a ∈ Finset.univ.filter (fun a => f a ∈ C), weight a := by
  classical
  unfold pushMass
  rw [Finset.sum_comm,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]

/-- If the image of a set lies in one dual component, its primal mass is
bounded by that component's pushed-forward mass, with no injectivity of
the assignment assumed or needed. -/
theorem mass_le_pushMass (f : A → B) (weight : A → ℝ) (hw : ∀ a, 0 ≤ weight a)
    (U : Finset A) (C : Finset B) (hUC : ∀ a ∈ U, f a ∈ C) :
    ∑ a ∈ U, weight a ≤ ∑ b ∈ C, pushMass f weight b := by
  classical
  rw [pushMass_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hUC a ha⟩
  · exact fun a _ _ => hw a

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolygonModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite simplicial model of a literal finite polygon incidence system.
All edges are split three times, and every boundary occurrence has its own
collar vertex. Thus loops, repeated boundary vertices and parallel edges are
not silently identified. The carrier/homotopy comparison is a later theorem. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel
open FinitePolyhedron

structure Data (V E C : Type*) where
  size : C → ℕ
  positive : ∀ c, 0 < size c
  start : E × Bool → V
  side : (c : C) → Fin (size c) → E × Bool
  closed : ∀ c i, start (side c (finRotate (size c) i)) =
    start ((side c i).1, !(side c i).2)

namespace Data
variable {V E C : Type*}
variable (P : Data V E C)

abbrev Position := (c : C) × (Fin (P.size c) × Fin 3)
abbrev GraphVertex := V ⊕ (E × Bool)
abbrev Vertex := GraphVertex (V := V) (E := E) ⊕ (C ⊕ P.Position)

abbrev graph (v : GraphVertex (V := V) (E := E)) : P.Vertex := .inl v
abbrev old (v : V) : P.Vertex := P.graph (.inl v)
abbrev mid (e : E) (b : Bool) : P.Vertex := P.graph (.inr (e,b))
abbrev apex (c : C) : P.Vertex := .inr (.inl c)
abbrev outer (q : P.Position) : P.Vertex := .inr (.inr q)

def next (q : P.Position) : P.Position :=
  ⟨q.1, if h : q.2.2.val = 2 then (finRotate (P.size q.1) q.2.1,0)
    else (q.2.1,⟨q.2.2.val+1,by omega⟩)⟩

/-- Start of one of the three subdivided segments of a signed old edge. -/
def dartStart (e : E × Bool) (j : Fin 3) : P.Vertex :=
  if j.val = 0 then P.old (P.start e)
  else if j.val = 1 then P.mid e.1 e.2 else P.mid e.1 (!e.2)

def base (q : P.Position) : P.Vertex := P.dartStart (P.side q.1 q.2.1) q.2.2

variable [DecidableEq V] [DecidableEq E] [DecidableEq C]

/-- The three positive graph segments. -/
def graphFace (e : E) (j : Fin 3) : Finset P.Vertex :=
  if j.val = 0 then {P.old (P.start (e,true)),P.mid e true}
  else if j.val = 1 then {P.mid e true,P.mid e false}
  else {P.mid e false,P.old (P.start (e,false))}

/-- Two simplices in each mapping-cylinder rectangle and one cap simplex. -/
def collarFace (q : P.Position) (j : Fin 3) : Finset P.Vertex :=
  if j.val = 0 then {P.outer q,P.base q,P.base (P.next q)}
  else if j.val = 1 then {P.outer q,P.outer (P.next q),P.base (P.next q)}
  else {P.outer q,P.outer (P.next q),P.apex q.1}

abbrev Facet := (E × Fin 3) ⊕ (P.Position × Fin 3)
def facet : P.Facet → Finset P.Vertex
  | .inl e => P.graphFace e.1 e.2
  | .inr q => P.collarFace q.1 q.2

def complex : AbstractSimplicialComplex P.Vertex where
  faces := {s | s.Nonempty ∧ (s.card ≤ 1 ∨ ∃ f : P.Facet, s ⊆ P.facet f)}
  isRelLowerSet_faces := by
    rintro s ⟨hs,h⟩
    refine ⟨hs,fun t hts ht => ⟨ht,?_⟩⟩
    rcases h with h|⟨f,hf⟩
    · exact Or.inl ((Finset.card_le_card hts).trans h)
    · exact Or.inr ⟨f,hts.trans hf⟩
  singleton_mem := fun v => ⟨Finset.singleton_nonempty v,Or.inl (by simp)⟩

lemma edge_of_facet (f : P.Facet) {a b : P.Vertex} (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) :
    {a,b} ∈ P.complex.faces := by
  refine ⟨by simp,Or.inr ⟨f,?_⟩⟩
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> assumption

end Data
end HyperbolicObstruction.FinitePolygonModel
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolygonVoltage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal source voltages on the mapping-cylinder triangulation. -/
noncomputable section

namespace HyperbolicObstruction.FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C G : Type*} [Group G]
variable (P : Data V E C) (v : E → G)

def signed (e : E × Bool) : G := if e.2 then v e.1 else (v e.1)⁻¹

lemma base_next (q : P.Position) : P.base (P.next q) =
    if q.2.2.val = 2 then P.old (P.start ((P.side q.1 q.2.1).1, !(P.side q.1 q.2.1).2))
    else if q.2.2.val = 0 then P.mid (P.side q.1 q.2.1).1 (P.side q.1 q.2.1).2
    else P.mid (P.side q.1 q.2.1).1 (!(P.side q.1 q.2.1).2) := by
  rcases q with ⟨c,i,j⟩
  fin_cases j
  · simp [base,next,dartStart]
  · simp [base,next,dartStart]
  · simpa [base,next,dartStart] using congrArg P.old (P.closed c i)

end HyperbolicObstruction.FinitePolygonModel.Data
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronDeck
attribute [-instance] _root_.OAI.HyperbolicObstruction.FinitePolyhedron.openStar_contractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal voltage cover has a free transitive deck action. This supplies
an actual quotient covering to Mathlib's monodromy theorems. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def coordinate (e : v.TotalSpace) : G := e.snd

lemma totalSpace_ext {e f : v.TotalSpace} (h₁ : e.proj = f.proj)
    (h₂ : v.coordinate e = v.coordinate f) : e = f := by
  cases e with | mk a g =>
  cases f with | mk b h =>
  dsimp at h₁
  subst b
  congr

instance deckAction : MulAction G v.TotalSpace where
  smul g e := ⟨e.proj,g * v.coordinate e⟩
  one_smul e := v.totalSpace_ext rfl (one_mul (v.coordinate e))
  mul_smul g h e := v.totalSpace_ext rfl (mul_assoc g h (v.coordinate e))

@[simp] lemma deck_proj (g : G) (e : v.TotalSpace) : v.proj (g • e) = v.proj e := rfl
@[simp] lemma deck_coordinate (g : G) (e : v.TotalSpace) :
    v.coordinate (g • e) = g * v.coordinate e := rfl

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronMonodromy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual path-homotopy invariance of edge voltages, obtained from the
constructed covering and its literal charts. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def inChart (a : V) (x : Carrier K) (g : G) : v.TotalSpace :=
  (v.core.localTriv a).toOpenPartialHomeomorph.symm (x,g)

@[simp] lemma inChart_proj (a : V) (x : Carrier K) (g : G) :
    v.proj (v.inChart a x g) = x := rfl

@[simp] lemma inChart_coordinate (a : V) (x : Carrier K) (g : G) :
    v.coordinate (v.inChart a x g) = g * v.value a (v.core.indexAt x) := rfl

def chartFiber (a : V) (x : Carrier K) (g : G) : v.proj ⁻¹' {x} :=
  ⟨v.inChart a x g,rfl⟩

def vertexFiber (a : V) (g : G) : v.proj ⁻¹' {vertex K a} :=
  ⟨⟨vertex K a,g⟩,rfl⟩

lemma indexAt_vertex (a : V) : v.core.indexAt (vertex K a) = a :=
  (vertex_in_openStar K (v.core.mem_baseSet_at (vertex K a))).symm

@[simp] lemma chartFiber_vertex (a : V) (g : G) :
    v.chartFiber a (vertex K a) g = v.vertexFiber a g := by
  apply Subtype.ext
  apply v.totalSpace_ext
  · rfl
  · change g * v.value a (v.core.indexAt (vertex K a)) = g
    rw [indexAt_vertex,v.self,mul_one]

namespace EdgeChain
variable {v} {a b : V}
def eval (v : Voltage K G) {a b : V} (p : FinitePolyhedron.EdgeChain K a b) : G := by
  induction p with
  | nil _ => exact 1
  | @cons a b c h q ih => exact v.value a b * ih

omit [Fintype V] [TopologicalSpace G] [DiscreteTopology G] in
@[simp] lemma eval_nil (a : V) : eval v (.nil a) = 1 := rfl
omit [Fintype V] [TopologicalSpace G] [DiscreteTopology G] in
@[simp] lemma eval_cons {a b c : V} (h : {a,b} ∈ K.faces) (q : FinitePolyhedron.EdgeChain K b c) :
    eval v (.cons h q) = v.value a b * eval v q := rfl

end EdgeChain

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_FinitePolyhedronPathAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The triangle relations and rooted path groupoid calculations in the
actual realization. -/
noncomputable section

open Set
attribute [local instance] Classical.propDecidable
namespace HyperbolicObstruction.FinitePolyhedron
variable {V : Type*} [Fintype V] [DecidableEq V] (K : AbstractSimplicialComplex V)

omit [Fintype V] in
lemma edge_self (a : V) : {a,a} ∈ K.faces := by simpa using K.singleton_mem a

@[simp] lemma edgePath_self (a : V) (h : {a,a} ∈ K.faces) :
    edgePath K h = Path.refl (vertex K a) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  exact AffineMap.lineMap_same_apply _ _

namespace RootedPaths
variable {K} (o : V) (R : ∀ a : V, Path.Homotopic.Quotient (vertex K o) (vertex K a))

abbrev PiOne := (FundamentalGroup (Carrier K) (vertex K o))ᵐᵒᵖ

def based {a b : V} (p : Path.Homotopic.Quotient (vertex K a) (vertex K b)) : PiOne (K := K) o :=
  MulOpposite.op ((R a).trans (p.trans (R b).symm))

omit [DecidableEq V] in
lemma based_refl (a : V) : based o R (.refl (vertex K a)) = 1 := by
  apply MulOpposite.unop_injective
  change (R a).trans ((Path.Homotopic.Quotient.refl _).trans (R a).symm) = .refl _
  simp

/-- Every edge yields the actual loop obtained by the fixed endpoint routes. -/
def edgeLoop (a b : V) : PiOne (K := K) o :=
  if h : {a,b} ∈ K.faces then based o R (.mk (edgePath K h)) else 1

end RootedPaths

/-- Actual edge-chain routes exist in every path-connected finite realization. -/
def edgeRoutes [PathConnectedSpace (Carrier K)] (o : V) (a : V) : EdgeChain K o a :=
  if h : a = o then h.symm ▸ .nil o else
    (edgePath_representative K (PathConnectedSpace.somePath (vertex K o) (vertex K a))).choose

@[simp] lemma edgeRoutes_self [PathConnectedSpace (Carrier K)] (o : V) :
    edgeRoutes K o o = .nil o := by simp [edgeRoutes]

end HyperbolicObstruction.FinitePolyhedron
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphSeparatorTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V W : Type*} [DecidableEq W]

lemma preconnected_image (G : SimpleGraph V) (H : SimpleGraph W) (f : G →g H)
    (U : Finset V) (hc : (G.induce (U : Set V)).Preconnected) :
    (H.induce (U.image f : Set W)).Preconnected := by
  let g : G.induce (U : Set V) →g H.induce (U.image f : Set W) := {
    toFun := fun v => ⟨f v,Finset.mem_image.mpr ⟨v,v.property,rfl⟩⟩
    map_rel' := fun h => f.map_adj h }
  apply hc.map g
  intro w
  obtain ⟨v,hv,he⟩ := Finset.mem_image.mp w.property
  exact ⟨⟨v,hv⟩,Subtype.ext he⟩

/-- Stability of the actual component-separator conclusion under an
injective graph homomorphism; separator vertices outside the given carrier
are not charged. -/
theorem component_separator_pullback (G : SimpleGraph V) (H : SimpleGraph W)
    (f : G →g H) (hinj : Function.Injective f) (c : ℕ)
    (hH : ∀ U : Finset W, ∃ S : Finset W, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ A : Finset W, A ⊆ U → Disjoint A S →
        (H.induce (A : Set W)).Preconnected → 2*A.card ≤ U.card)
    (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ A : Finset V, A ⊆ U → Disjoint A S →
        (G.induce (A : Set V)).Preconnected → 2*A.card ≤ U.card := by
  classical
  obtain ⟨S,hSU,hSc,hsep⟩ := hH (U.image f)
  let S' := U.filter (fun v => f v ∈ S)
  have he : S'.image f = S := by
    apply Finset.Subset.antisymm
    · intro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact (Finset.mem_filter.mp hv).2
    · intro w hw
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp (hSU hw)
      exact Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hw⟩,rfl⟩
  have hcS : S'.card = S.card := (Finset.card_image_of_injective S' hinj).symm.trans (congrArg Finset.card he)
  have hcU := Finset.card_image_of_injective U hinj
  refine ⟨S',Finset.filter_subset _ _,?_,?_⟩
  · rw [hcS]
    simpa only [hcU] using hSc
  · intro A hAU hAS hconn
    have hh := hsep (A.image f) (Finset.image_mono f hAU) (by
      apply Finset.disjoint_left.mpr
      intro w hw hwS
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
      exact Finset.disjoint_left.mp hAS hv (Finset.mem_filter.mpr ⟨hAU hv,hwS⟩))
      (preconnected_image G H f A hconn)
    simpa only [Finset.card_image_of_injective _ hinj] using hh

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_GraphSubstitution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.GraphWordFilling
open SimpleGraph
variable {V W A : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Replace each oriented edge by a prescribed genuine edge-path. Endpoints
are enforced in the type, thereby preserving closedness exactly. -/
def expand (f : V → W) (r : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v)) :
    {u v : V} → G.Walk u v → H.Walk (f u) (f v)
  | _,_,.nil => .nil
  | _,_,.cons h p => (r h).append (expand f r p)

lemma expand_length (f : V → W) (r : ∀ {u v}, G.Adj u v → H.Walk (f u) (f v))
    (L : ℕ) (hr : ∀ {u v} (h : G.Adj u v), (r h).length ≤ L)
    {u v : V} (p : G.Walk u v) : (expand f r p).length ≤ L * p.length := by
  induction p with
  | nil => simp [expand]
  | cons h p ih =>
    simp only [expand,Walk.length_append,Walk.length_cons,Nat.mul_add,Nat.mul_one]
    exact (Nat.add_le_add (hr h) ih).trans_eq (Nat.add_comm _ _)

end HyperbolicObstruction.GraphWordFilling
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PicturePartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {X I F : Type*} [Fintype X] [Fintype I] [Fintype F]

lemma sum_part_sizes (part : F → I) :
    (∑ i, Fintype.card {x : F // part x = i}) = Fintype.card F := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv part)

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarEdgeOrdering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [DecidableEq D] [Fintype D] in
lemma joins_append (s : Setoid D) (l r : List (D × D)) :
    joins s (l ++ r) = joins (joins s l) r := by
  induction l generalizing s with
  | nil => rfl
  | cons ab l ih => exact ih _

omit [Fintype D] in
lemma swaps_append (l r : List (D × D)) : swaps (l ++ r) = swaps l * swaps r := by
  simp only [swaps,List.map_append,List.prod_append]

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PairingForest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}

/-- Kruskal's spanning forest, retaining literal paired-side indices. -/
def forestEdges (s : Setoid D) : List (D × D) → List (D × D)
  | [] => []
  | (a,b)::l => if s a b then forestEdges s l else (a,b)::forestEdges (glue s a b) l

lemma forestEdges_sublist (s : Setoid D) (l : List (D × D)) : (forestEdges s l).Sublist l := by
  induction l generalizing s with
  | nil => exact List.Sublist.refl _
  | cons ab l ih =>
    simp only [forestEdges]
    split_ifs
    · exact (ih s).cons _
    · exact (ih _).cons_cons _

variable [Fintype D]

variable [DecidableEq D]

omit [DecidableEq D] in
lemma setoid_eq_of_card_eq {s t : Setoid D} (hle : s ≤ t)
    (hc : Nat.card (Quotient s) = Nat.card (Quotient t)) : s = t := by
  let f : Quotient s → Quotient t := Quotient.map id (fun _ _ h => hle h)
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    exact ⟨Quotient.mk s x,rfl⟩
  have hi : Function.Injective f := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩).1
  apply le_antisymm hle
  intro x y h
  exact Quotient.exact (hi (show f (Quotient.mk s x) = f (Quotient.mk s y) from Quotient.sound h))

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D]

omit [Fintype D] in
lemma swaps_fix_of_outside (l : List (D × D)) (x : D)
    (h : ∀ ab ∈ l, x ≠ ab.1 ∧ x ≠ ab.2) : swaps l x = x := by
  induction l with
  | nil => rfl
  | cons ab l ih =>
    change swap ab.1 ab.2 (swaps l x) = x
    rw [ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]
    exact swap_apply_of_ne_of_ne (h ab List.mem_cons_self).1
      (h ab List.mem_cons_self).2

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SubpairingTree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [DecidableEq D] [Fintype D] [Nonempty D]

omit [DecidableEq D] [Fintype D] in
lemma card_quotient_top_one : Nat.card (Quotient (⊤ : Setoid D)) = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro a b
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound trivial
  · exact ⟨Quotient.mk _ (Classical.arbitrary D)⟩

end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeCentroid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset
variable {V : Type*} [Fintype V]

/-- The side of an oriented tree edge towards its second endpoint. -/
def treeBranch (G : SimpleGraph V) (v w : V) : Finset V :=
  Finset.univ.filter (fun x => G.dist x w < G.dist x v)

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeCentroidCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset SimpleGraph
variable {V : Type*}

lemma tree_path_length_eq_dist {G : SimpleGraph V} (hG : G.IsTree) {x y : V}
    (p : G.Walk x y) (hp : p.IsPath) : p.length = G.dist x y := by
  obtain ⟨q,hq,hql⟩ := hG.connected.exists_path_of_dist x y
  have heq := hG.isAcyclic.subsingleton_path x y |>.elim ⟨p,hp⟩ ⟨q,hq⟩
  have hwalk : p = q := congrArg Subtype.val heq
  rwa [hwalk]

variable [Fintype V] [DecidableEq V]

lemma treeBranch_of_avoiding_walk {G : SimpleGraph V} (hG : G.IsTree) {v w x : V}
    (hadj : G.Adj v w) (p : G.Walk x w) (havoid : v ∉ p.support) :
    x ∈ treeBranch G v w := by
  let q := p.bypass
  have hq : q.IsPath := p.bypass_isPath
  have hv : v ∉ q.support := fun h => havoid (p.support_bypass_subset_support h)
  obtain ⟨r,hr,hrl⟩ := hG.connected.exists_path_of_dist x v
  have hw : w ∈ r.support :=
    hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hr hq hadj hv
  have hid := hG.isAcyclic.path_concat hq hr hadj.symm hw
  have hql := tree_path_length_eq_dist hG q hq
  rw [hid,Walk.length_concat,hql] at hrl
  simp only [treeBranch,Finset.mem_filter,Finset.mem_univ,true_and]
  omega

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma tree_closer_neighbor_mem_path {G : SimpleGraph V} (hG : G.IsTree)
    {r v w : V} (p : G.Walk r v) (hp : p.IsPath) (hadj : G.Adj v w)
    (hd : G.dist r w < G.dist r v) : w ∈ p.support := by
  by_contra hw
  obtain ⟨q,hq,hql⟩ := hG.connected.exists_path_of_dist r w
  have hv := hG.isAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp hadj.symm hw
  have heq := hG.isAcyclic.path_concat hp hq hadj hv
  have hpl := tree_path_length_eq_dist hG p hp
  rw [heq,Walk.length_concat,hpl] at hql
  omega

lemma tree_closer_neighbor_unique {G : SimpleGraph V} (hG : G.IsTree)
    {r v a b : V} (ha : G.Adj v a) (hb : G.Adj v b)
    (hda : G.dist r a < G.dist r v) (hdb : G.dist r b < G.dist r v) : a = b := by
  obtain ⟨p,hp,_⟩ := hG.connected.exists_path_of_dist r v
  exact (hG.isAcyclic.eq_penultimate_of_adj_end hp ha
    (tree_closer_neighbor_mem_path hG p hp ha hda)).trans
      (hG.isAcyclic.eq_penultimate_of_adj_end hp hb
        (tree_closer_neighbor_mem_path hG p hp hb hdb)).symm

/-- Root closure is the exact property satisfied by a union of root paths.
It says every predecessor of a protected vertex is protected. -/
def RootClosed (G : SimpleGraph V) (root : V) (S : Set V) : Prop :=
  ∀ v ∈ S, ∀ w, G.Adj v w → G.dist root w < G.dist root v → w ∈ S

variable [Fintype V]

/-- Any finite boundary supported on a tree must lie in a root-closed hull
of its possible ends. The hypothesis outside the hull asks for two DISTINCT
boundary neighbors; the proof uses a furthest unprotected boundary vertex.
This is a tree theorem, not a planar separator assumed by an interface. -/
theorem tree_boundary_in_hull {G : SimpleGraph V} (hG : G.IsTree)
    (root : V) (S : Set V) (hS : RootClosed G root S) (B : V → Prop)
    (hB : ∀ v, B v → v ∉ S → ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b ∧ B a ∧ B b) :
    ∀ v, B v → v ∈ S := by
  classical
  by_contra h
  push Not at h
  obtain ⟨v,hv,hvS⟩ := h
  let U := Finset.univ.filter (fun x => B x ∧ x ∉ S)
  have hU : U.Nonempty := ⟨v,by simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hv,hvS⟩⟩
  obtain ⟨x,hx,hmax⟩ := Finset.exists_max_image U (G.dist root) hU
  have hxB : B x ∧ x ∉ S := by simpa only [U,Finset.mem_filter,Finset.mem_univ,true_and] using hx
  obtain ⟨a,b,hab,ha,hb,haB,hbB⟩ := hB x hxB.1 hxB.2
  have hdown : ∀ y, G.Adj x y → B y → G.dist root y < G.dist root x := by
    intro y hxy hyB
    rcases hG.dist_eq_dist_add_one_of_adj root hxy with hd | hd
    · omega
    · have hyS : y ∉ S := by
        intro hy
        exact hxB.2 (hS y hy x hxy.symm (by omega))
      have hyU : y ∈ U := by
        simp only [U,Finset.mem_filter,Finset.mem_univ,true_and]
        exact ⟨hyB,hyS⟩
      have hm := hmax y hyU
      omega
  exact hab (tree_closer_neighbor_unique hG ha hb (hdown a ha haB) (hdown b hb hbB))

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreePathHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*}

/-- The unique actual tree path; uniqueness is proved, not assumed by a
surrogate tree structure. The distance-minimizing library witness fixes it. -/
def rootedTreePath (G : SimpleGraph V) (hG : G.IsTree) (r a : V) : G.Walk r a :=
  (hG.connected.exists_path_of_dist r a).choose

lemma rootedTreePath_isPath (G : SimpleGraph V) (hG : G.IsTree) (r a : V) :
    (rootedTreePath G hG r a).IsPath :=
  (hG.connected.exists_path_of_dist r a).choose_spec.1

variable [DecidableEq V]

/-- Union of the root paths to a finite collection of terminals. -/
def treePathHull (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V) : Finset V :=
  A.biUnion (fun a => (rootedTreePath G hG r a).support.toFinset)

lemma mem_treePathHull {G : SimpleGraph V} {hG : G.IsTree} {r v : V} {A : Finset V} :
    v ∈ treePathHull G hG r A ↔ ∃ a ∈ A, v ∈ (rootedTreePath G hG r a).support := by
  simp only [treePathHull,Finset.mem_biUnion,List.mem_toFinset]

lemma subset_treePathHull (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V) :
    A ⊆ treePathHull G hG r A := by
  intro a ha
  exact mem_treePathHull.mpr ⟨a,ha,(rootedTreePath G hG r a).end_mem_support⟩

lemma treePathHull_rootClosed (G : SimpleGraph V) (hG : G.IsTree) (r : V) (A : Finset V) :
    RootClosed G r (treePathHull G hG r A : Set V) := by
  intro v hv w hvw hd
  obtain ⟨a,ha,hva⟩ := mem_treePathHull.mp hv
  let p := rootedTreePath G hG r a
  have hp : p.IsPath := rootedTreePath_isPath G hG r a
  have hw : w ∈ (p.takeUntil v hva).support :=
    tree_closer_neighbor_mem_path hG (p.takeUntil v hva) (hp.takeUntil hva) hvw hd
  exact mem_treePathHull.mpr ⟨a,ha,p.support_takeUntil_subset_support hva hw⟩

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreeCentroidComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
open SimpleGraph
variable {V : Type*}

lemma deleteIncidence_reachable_center_iff (G : SimpleGraph V) (v w : V) :
    (G.deleteIncidenceSet v).Reachable v w ↔ v = w := by
  constructor
  · rintro ⟨p⟩
    cases p with
    | nil => rfl
    | cons h p => exact ((deleteIncidenceSet_adj.mp h).2.1 rfl).elim
  · rintro rfl; exact .rfl

lemma deleteIncidence_center_component_iff (G : SimpleGraph V) (v w : V) :
    (G.deleteIncidenceSet v).connectedComponentMk w =
      (G.deleteIncidenceSet v).connectedComponentMk v ↔ w = v := by
  constructor
  · intro h
    exact ((deleteIncidence_reachable_center_iff G v w).mp
      (ConnectedComponent.exact h.symm)).symm
  · rintro rfl; rfl

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_TreePathIntDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma rootedTreePath_depth_injOn (G : SimpleGraph V) (hG : G.IsTree) (r a : V) :
    Set.InjOn (fun v => G.dist r v) ((rootedTreePath G hG r a).support.toFinset : Set V) := by
  intro v hv w hw he
  have hv' := List.mem_toFinset.mp hv
  have hw' := List.mem_toFinset.mp hw
  have hvget := (rootedTreePath G hG r a).getVert_length_takeUntil hv'
  have hwget := (rootedTreePath G hG r a).getVert_length_takeUntil hw'
  rw [tree_path_length_eq_dist hG _ ((rootedTreePath_isPath G hG r a).takeUntil hv')] at hvget
  rw [tree_path_length_eq_dist hG _ ((rootedTreePath_isPath G hG r a).takeUntil hw')] at hwget
  exact hvget.symm.trans ((congrArg (rootedTreePath G hG r a).getVert he).trans hwget)

lemma tree_path_intBand_card_le (G : SimpleGraph V) (hG : G.IsTree) (r a : V) (L H : ℤ) :
    ((rootedTreePath G hG r a).support.toFinset.filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)).card ≤ (H-L+1).toNat := by
  classical
  calc
    _ ≤ (Finset.Icc L H).card := by
      apply Finset.card_le_card_of_injOn (fun v => (G.dist r v : ℤ))
      · intro v hv
        exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hv).2
      · intro v hv w hw he
        apply rootedTreePath_depth_injOn G hG r a
          (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
        change (G.dist r v : ℤ) = (G.dist r w : ℤ) at he
        exact_mod_cast he
    _ = (H-L+1).toNat := by rw [Int.card_Icc]; congr 1; omega

/-- Integer-level version including empty negative BFS levels. -/
theorem treePathHull_intBand_card_le (G : SimpleGraph V) (hG : G.IsTree)
    (r : V) (A : Finset V) (L H : ℤ) :
    ((treePathHull G hG r A).filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)).card ≤ A.card*(H-L+1).toNat := by
  classical
  have he : (treePathHull G hG r A).filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H) =
      A.biUnion (fun a => (rootedTreePath G hG r a).support.toFinset.filter
        (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)) := by
    ext v
    simp only [Finset.mem_filter,mem_treePathHull,Finset.mem_biUnion,List.mem_toFinset]
    aesop
  rw [he]
  calc
    _ ≤ ∑ a ∈ A, ((rootedTreePath G hG r a).support.toFinset.filter
      (fun v => L ≤ (G.dist r v : ℤ) ∧ (G.dist r v : ℤ) ≤ H)).card := Finset.card_biUnion_le
    _ ≤ ∑ a ∈ A, (H-L+1).toNat :=
      Finset.sum_le_sum (fun a _ => tree_path_intBand_card_le G hG r a L H)
    _ = A.card*(H-L+1).toNat := by simp

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PictureTriangulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*}
namespace PictureMap

/-- Three individually indexed sides for each old side: its old edge, and
two radii to the new center of the old face. This is literal face starring. -/
abbrev StarDart (D : Type*) := D ⊕ (D ⊕ D)

def starFace : Perm (StarDart D) where
  toFun := fun x => match x with
    | .inl x => .inr (.inl x)
    | .inr (.inl x) => .inr (.inr x)
    | .inr (.inr x) => .inl x
  invFun := fun x => match x with
    | .inl x => .inr (.inr x)
    | .inr (.inl x) => .inl x
    | .inr (.inr x) => .inr (.inl x)
  left_inv := by rintro (x | (x | x)) <;> rfl
  right_inv := by rintro (x | (x | x)) <;> rfl

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SeparatorBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion

/-- A charging potential for the recursive separator construction. The
constant is deliberately inessential: only existence of K is required. -/
def budget (c K n : ℝ) : ℝ := 16 * c * n / Real.sqrt K - 8 * c * Real.sqrt n

lemma budget_nonneg {c K n : ℝ} (hc : 0 ≤ c) (hK : 0 < K)
    (hn : 0 ≤ n) (hlow : K ≤ 4 * n) : 0 ≤ budget c K n := by
  have hk := Real.sqrt_pos.2 hK
  have hx := Real.sqrt_nonneg n
  have hks := Real.sq_sqrt hK.le
  have hxs := Real.sq_sqrt hn
  have hbound : Real.sqrt K ≤ 2 * Real.sqrt n := by nlinarith
  have hprod : Real.sqrt n * Real.sqrt K ≤ 2 * n := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr hbound)]
  have hmul := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8*c by positivity)
  unfold budget
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hk).mpr
  nlinarith

lemma sqrt_split_gain {n s a b : ℝ} (hn : 0 ≤ n) (ha : n/4 ≤ a) (hb : n/4 ≤ b)
    (hs : s ≤ n/12) (hsum : s+a+b=n) :
    (9/8 : ℝ) * Real.sqrt n ≤ Real.sqrt a + Real.sqrt b := by
  have ha0 : 0 ≤ a := le_trans (by positivity) ha
  have hb0 : 0 ≤ b := le_trans (by positivity) hb
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have hz := Real.sqrt_nonneg n
  have hxs := Real.sq_sqrt ha0
  have hys := Real.sq_sqrt hb0
  have hzs := Real.sq_sqrt hn
  have hzx : Real.sqrt n / 2 ≤ Real.sqrt a := by nlinarith
  have hzy : Real.sqrt n / 2 ≤ Real.sqrt b := by nlinarith
  have hp := mul_le_mul hzx hzy (by positivity : 0 ≤ Real.sqrt n / 2) hx
  apply le_of_sq_le_sq _ (by positivity)
  nlinarith

lemma split_numeric {c K n s a b : ℝ} (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hK : 144*c^2 ≤ K) (hKn : K ≤ n) (hsep : s ≤ c * Real.sqrt n)
    (hsum : s+a+b=n) (ha : 3*a ≤ 2*n) (hb : 3*b ≤ 2*n) :
    s ≤ n/12 ∧ n/4 ≤ a ∧ n/4 ≤ b := by
  have hz := Real.sqrt_nonneg n
  have hzs := Real.sq_sqrt hn
  have hzc : 12*c ≤ Real.sqrt n := by
    apply (mul_self_le_mul_self_iff (mul_nonneg (by norm_num) hc) hz).mpr
    nlinarith
  have hs : s ≤ n/12 := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg n) (sub_nonneg.mpr hzc)]
  exact ⟨hs,by linarith,by linarith⟩

lemma budget_step {c K n s a b : ℝ} (hc : 0 ≤ c) (hK : 0 < K) (hn : 0 ≤ n)
    (hs0 : 0 ≤ s) (ha : n/4 ≤ a) (hb : n/4 ≤ b)
    (hs : s ≤ n/12) (hsep : s ≤ c * Real.sqrt n) (hsum : s+a+b=n) :
    s + budget c K a + budget c K b ≤ budget c K n := by
  have hg := sqrt_split_gain hn ha hb hs hsum
  have hp : s ≤ 8*c*(Real.sqrt a+Real.sqrt b-Real.sqrt n) := by
    have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ 8*c by positivity)
    nlinarith
  have hnon : 0 ≤ 16*c*s/Real.sqrt K := by positivity
  have hid : s + budget c K a + budget c K b = budget c K n +
      (s-8*c*(Real.sqrt a+Real.sqrt b-Real.sqrt n)-16*c*s/Real.sqrt K) := by
    unfold budget
    rw [← hsum]
    ring
  rw [hid]
  linarith

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SeparatorRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finite partition with a recorded set of removed separator vertices.
Edges between distinct labels must meet that set. This is only the recursive
combinatorial stage; no planar separator is supplied by this definition. -/
structure CutPartition (G : SimpleGraph V) (U : Finset V) (K : ℕ) where
  label : V → ℕ
  removed : Finset V
  removed_subset : removed ⊆ U
  small : ∀ i, (U.filter (fun x => label x = i)).card ≤ K
  edge_const : ∀ x ∈ U, ∀ y ∈ U, G.Adj x y → x ∉ removed → y ∉ removed → label x = label y

namespace CutPartition
variable {G : SimpleGraph V} {U : Finset V} {K : ℕ}

def trivial (h : U.card ≤ K) : CutPartition G U K where
  label := fun _ => 0
  removed := ∅
  removed_subset := Finset.empty_subset _
  small := fun i => (Finset.card_le_card (Finset.filter_subset _ _)).trans h
  edge_const := by intros; rfl

end CutPartition

def region (U : Finset V) (t : V → Fin 3) (i : Fin 3) := U.filter (fun x => t x = i)

omit [Fintype V] [DecidableEq V] in
lemma mem_region {U : Finset V} {t : V → Fin 3} {i : Fin 3} {x : V} :
    x ∈ region U t i ↔ x ∈ U ∧ t x = i := Finset.mem_filter

def vertexNumber (x : V) : ℕ := (Fintype.equivFin V x).val

omit [DecidableEq V] in
lemma vertexNumber_injective : Function.Injective (vertexNumber (V := V)) :=
  fun _ _ h => (Fintype.equivFin V).injective (Fin.ext h)

def coloredLabel (t : V → Fin 3) (p q : V → ℕ) (x : V) : ℕ :=
  if t x = 0 then 3 * vertexNumber x else if t x = 1 then 3 * p x + 1 else 3 * q x + 2

omit [DecidableEq V] in
lemma coloredLabel_mod (t : V → Fin 3) (p q : V → ℕ) (x : V) :
    coloredLabel t p q x % 3 = (t x).val := by
  have hx := (t x).isLt
  have h0 : t x = 0 ↔ (t x).val = 0 := Fin.ext_iff
  have h1 : t x = 1 ↔ (t x).val = 1 := Fin.ext_iff
  simp only [coloredLabel]
  split_ifs <;> omega

omit [DecidableEq V] in
lemma coloredLabel_tag {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (h : coloredLabel t p q x = coloredLabel t p q y) : t x = t y := by
  apply Fin.ext
  rw [← coloredLabel_mod t p q x,← coloredLabel_mod t p q y,h]

omit [DecidableEq V] in
lemma coloredLabel_zero {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (hx : t x = 0) (h : coloredLabel t p q x = coloredLabel t p q y) : x = y := by
  have hy : t y = 0 := (coloredLabel_tag h).symm.trans hx
  simp only [coloredLabel,hx,hy,ite_true] at h
  exact vertexNumber_injective (by omega)

omit [DecidableEq V] in
lemma coloredLabel_one {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (hx : t x = 1) (h : coloredLabel t p q x = coloredLabel t p q y) : p x = p y := by
  have hy : t y = 1 := (coloredLabel_tag h).symm.trans hx
  norm_num [coloredLabel,hx,hy] at h
  omega

omit [DecidableEq V] in
lemma coloredLabel_two {t : V → Fin 3} {p q : V → ℕ} {x y : V}
    (hx : t x = 2) (h : coloredLabel t p q x = coloredLabel t p q y) : q x = q y := by
  have hy : t y = 2 := (coloredLabel_tag h).symm.trans hx
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [coloredLabel,hx,hy,h20,h21,ite_false] at h
  omega

omit [Fintype V] [DecidableEq V] in
/-- The three literal regions partition the carrier. -/
lemma region_card (U : Finset V) (t : V → Fin 3) :
    (region U t 0).card + (region U t 1).card + (region U t 2).card = U.card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter U (Finset.univ : Finset (Fin 3)) t
  simp only [Finset.mem_univ,Finset.filter_true] at h
  simpa only [Fin.sum_univ_three,region] using h

lemma tag_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

namespace CutPartition
variable {G : SimpleGraph V} {U : Finset V} {K : ℕ} (t : V → Fin 3)
variable (P : CutPartition G (region U t 1) K) (Q : CutPartition G (region U t 2) K)

omit [DecidableEq V] in
lemma merge_small (hK : 0 < K) (i : ℕ) :
    (U.filter (fun x => coloredLabel t P.label Q.label x = i)).card ≤ K := by
  let F := U.filter (fun x => coloredLabel t P.label Q.label x = i)
  by_cases hF : F.Nonempty
  · obtain ⟨x,hxF⟩ := hF
    obtain ⟨hxU,hxi⟩ := Finset.mem_filter.mp hxF
    rcases tag_cases (t x) with hx | hx | hx
    · have hsub : F ⊆ {x} := by
        intro y hy
        obtain ⟨hyU,hyi⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_singleton.mpr (coloredLabel_zero hx (hxi.trans hyi.symm)).symm
      exact (Finset.card_le_card hsub).trans (by simpa only [Finset.card_singleton] using (show 1 ≤ K by omega))
    · apply (Finset.card_le_card (show F ⊆ (region U t 1).filter (fun y => P.label y = P.label x) from ?_)).trans (P.small _)
      intro y hy
      obtain ⟨hyU,hyi⟩ := Finset.mem_filter.mp hy
      have hxy := hxi.trans hyi.symm
      exact Finset.mem_filter.mpr ⟨mem_region.mpr ⟨hyU,(coloredLabel_tag hxy).symm.trans hx⟩,
        (coloredLabel_one hx hxy).symm⟩
    · apply (Finset.card_le_card (show F ⊆ (region U t 2).filter (fun y => Q.label y = Q.label x) from ?_)).trans (Q.small _)
      intro y hy
      obtain ⟨hyU,hyi⟩ := Finset.mem_filter.mp hy
      have hxy := hxi.trans hyi.symm
      exact Finset.mem_filter.mpr ⟨mem_region.mpr ⟨hyU,(coloredLabel_tag hxy).symm.trans hx⟩,
        (coloredLabel_two hx hxy).symm⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ K
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- One literal recursive step: every separator vertex becomes a singleton,
while the two nonadjacent sides retain their recursively constructed parts. -/
def merge (hK : 0 < K)
    (hsep : ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬ G.Adj x y) :
    CutPartition G U K where
  label := coloredLabel t P.label Q.label
  removed := region U t 0 ∪ P.removed ∪ Q.removed
  removed_subset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact (mem_region.mp hx).1
      · exact (mem_region.mp (P.removed_subset hx)).1
    · exact (mem_region.mp (Q.removed_subset hx)).1
  small := merge_small t P Q hK
  edge_const := by
    intro x hxU y hyU hxy hxR hyR
    have hxr : x ∉ region U t 0 ∧ x ∉ P.removed ∧ x ∉ Q.removed := by
      simpa only [Finset.mem_union,not_or,and_assoc] using hxR
    have hyr : y ∉ region U t 0 ∧ y ∉ P.removed ∧ y ∉ Q.removed := by
      simpa only [Finset.mem_union,not_or,and_assoc] using hyR
    have hx0 : t x ≠ 0 := fun h => hxr.1 (mem_region.mpr ⟨hxU,h⟩)
    have hy0 : t y ≠ 0 := fun h => hyr.1 (mem_region.mpr ⟨hyU,h⟩)
    rcases (tag_cases (t x)).resolve_left hx0 with hx | hx
    <;> rcases (tag_cases (t y)).resolve_left hy0 with hy | hy
    · have h := P.edge_const x (mem_region.mpr ⟨hxU,hx⟩) y (mem_region.mpr ⟨hyU,hy⟩) hxy hxr.2.1 hyr.2.1
      simp [coloredLabel,hx,hy,h]
    · exact (hsep x (mem_region.mpr ⟨hxU,hx⟩) y (mem_region.mpr ⟨hyU,hy⟩) hxy).elim
    · exact (hsep y (mem_region.mpr ⟨hyU,hy⟩) x (mem_region.mpr ⟨hxU,hx⟩) hxy.symm).elim
    · have h := Q.edge_const x (mem_region.mpr ⟨hxU,hx⟩) y (mem_region.mpr ⟨hyU,hy⟩) hxy hxr.2.2 hyr.2.2
      have h20 : (2 : Fin 3) ≠ 0 := by decide
      have h21 : (2 : Fin 3) ≠ 1 := by decide
      simp only [coloredLabel,hx,hy,h20,h21,ite_false,h]

lemma merge_removed_card (hK : 0 < K)
    (hsep : ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬ G.Adj x y) :
    (merge t P Q hK hsep).removed.card ≤
      (region U t 0).card + P.removed.card + Q.removed.card := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)

end CutPartition
end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SeparatorDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Balanced vertex separators of size at most the square-root bound. -/
def HasBalancedSeparators (G : SimpleGraph V) (c : ℝ) : Prop :=
  ∀ U : Finset V, ∃ t : V → Fin 3,
    ((region U t 0).card : ℝ) ≤ c * Real.sqrt U.card ∧
    3 * (region U t 1).card ≤ 2 * U.card ∧
    3 * (region U t 2).card ≤ 2 * U.card ∧
    ∀ x ∈ region U t 1, ∀ y ∈ region U t 2, ¬G.Adj x y

/-- Recursive charging for finite parts and removed vertices using balanced
separators and a finite cutoff. -/
theorem partition_of_balanced_separators {G : SimpleGraph V} {c : ℝ} (hc : 0 ≤ c)
    (hsep : HasBalancedSeparators G c) (K : ℕ) (hK : 0 < K)
    (hcap : 144*c^2 ≤ (K : ℝ)) (U : Finset V) :
    ∃ P : CutPartition G U K, (P.removed.card : ℝ) ≤ 16*c*U.card/Real.sqrt K := by
  have strong : ∀ n : ℕ, ∀ W : Finset V, W.card = n → (K : ℝ) ≤ 4*(n : ℝ) →
      ∃ P : CutPartition G W K, (P.removed.card : ℝ) ≤ budget c K n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W hW hlow
      subst n
      by_cases hsmall : W.card ≤ K
      · refine ⟨CutPartition.trivial hsmall,?_⟩
        simpa only [CutPartition.trivial,Finset.card_empty,Nat.cast_zero] using
          (budget_nonneg hc (by exact_mod_cast hK) (by positivity) hlow)
      · have hlarge : K < W.card := Nat.lt_of_not_ge hsmall
        obtain ⟨t,hs,ha,hb,hnoedge⟩ := hsep W
        have hsum : ((region W t 0).card : ℝ) + (region W t 1).card +
            (region W t 2).card = W.card := by exact_mod_cast region_card W t
        have hnum := split_numeric hc (show 0 ≤ (W.card : ℝ) by positivity) hcap
          (show (K : ℝ) ≤ W.card by exact_mod_cast hlarge.le) hs hsum
          (show (3 : ℝ)*(region W t 1).card ≤ 2*W.card by exact_mod_cast ha)
          (show (3 : ℝ)*(region W t 2).card ≤ 2*W.card by exact_mod_cast hb)
        have ha_lt : (region W t 1).card < W.card := by omega
        have hb_lt : (region W t 2).card < W.card := by omega
        have hKr : (K : ℝ) ≤ W.card := by exact_mod_cast hlarge.le
        have ha_low : (K : ℝ) ≤ 4*((region W t 1).card : ℝ) := by linarith [hnum.2.1]
        have hb_low : (K : ℝ) ≤ 4*((region W t 2).card : ℝ) := by linarith [hnum.2.2]
        obtain ⟨P,hP⟩ := ih _ ha_lt (region W t 1) rfl ha_low
        obtain ⟨Q,hQ⟩ := ih _ hb_lt (region W t 2) rfl hb_low
        refine ⟨P.merge t Q hK hnoedge,?_⟩
        have hcount : ((P.merge t Q hK hnoedge).removed.card : ℝ) ≤
            (region W t 0).card + (P.removed.card : ℝ) + Q.removed.card := by
          exact_mod_cast CutPartition.merge_removed_card t P Q hK hnoedge
        have hstep := budget_step hc (show (0 : ℝ) < K by exact_mod_cast hK)
          (show 0 ≤ (W.card : ℝ) by positivity)
          (show 0 ≤ ((region W t 0).card : ℝ) by positivity)
          hnum.2.1 hnum.2.2 hnum.1 hs hsum
        linarith
  by_cases hsmall : U.card ≤ K
  · refine ⟨CutPartition.trivial hsmall,?_⟩
    simp only [CutPartition.trivial,Finset.card_empty,Nat.cast_zero]
    positivity
  · have hlarge : K < U.card := Nat.lt_of_not_ge hsmall
    have hlow : (K : ℝ) ≤ 4*(U.card : ℝ) := by
      have hh : (K : ℝ) ≤ U.card := by exact_mod_cast hlarge.le
      linarith [show 0 ≤ (U.card : ℝ) by positivity]
    obtain ⟨P,hP⟩ := strong U.card U rfl hlow
    refine ⟨P,hP.trans ?_⟩
    unfold budget
    exact sub_le_self _ (by positivity)

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SeparatorCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
universe vertexUniverse
namespace HyperbolicObstruction.PlanarRecursion

lemma exists_separator_cutoff (c d eta : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ 144*c^2 ≤ (K : ℝ) ∧ d*(16*c/Real.sqrt K) ≤ eta := by
  let r := 16*c*d/eta
  obtain ⟨K,hK⟩ := exists_nat_gt (max (144*c^2) (max 1 (r^2)))
  have hcap : 144*c^2 ≤ (K : ℝ) := le_trans (le_max_left _ _) hK.le
  have hpos : (1 : ℝ) < K := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hK
  have hk : 0 < K := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 1) hpos)
  have hsq : r^2 ≤ (K : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hK.le
  have hroot : r ≤ Real.sqrt K := by
    exact (Real.le_sqrt (by dsimp [r]; positivity) (by positivity)).mpr hsq
  have hh := mul_le_mul_of_nonneg_right hroot heta.le
  have hid : r*eta = 16*c*d := by dsimp only [r]; field_simp
  rw [hid] at hh
  refine ⟨K,hk,hcap,?_⟩
  calc
    d*(16*c/Real.sqrt K) = (16*c*d)/Real.sqrt K := by ring
    _ ≤ eta := (div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast hk))).mpr (by nlinarith)

/-- Uniform recursive partition theorem from balanced separators. The cutoff is
chosen before the finite vertex type, graph, and all recursive subproblems. -/
theorem uniform_bounded_partition (c d eta : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d) (heta : 0 < eta) :
    ∃ K : ℕ, 0 < K ∧ ∀ (V : Type vertexUniverse) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      HasBalancedSeparators G c → ∀ U : Finset V,
      ∃ P : CutPartition G U K, d*(P.removed.card : ℝ) ≤ eta*U.card := by
  obtain ⟨K,hK,hcap,hcoef⟩ := exists_separator_cutoff c d eta hc hd heta
  refine ⟨K,hK,?_⟩
  intro V _ _ G hsep U
  obtain ⟨P,hP⟩ := partition_of_balanced_separators hc hsep K hK hcap U
  refine ⟨P,?_⟩
  calc
    d*(P.removed.card : ℝ) ≤ d*(16*c*U.card/Real.sqrt K) := mul_le_mul_of_nonneg_left hP hd
    _ = (d*(16*c/Real.sqrt K))*U.card := by ring
    _ ≤ eta*U.card := mul_le_mul_of_nonneg_right hcoef (by positivity)

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_PlanarPartitionBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CutPartition
variable {G : SimpleGraph V} {U : Finset V} {K : ℕ} (P : CutPartition G U K)

abbrev Label := ↑(Finset.univ.image P.label)
def finiteLabel (v : V) : P.Label :=
  ⟨P.label v,Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩⟩

omit [DecidableEq V] in
lemma finiteLabel_small (i : P.Label) :
    (U.filter (fun x => P.finiteLabel x = i)).card ≤ K := by
  have he : U.filter (fun x => P.finiteLabel x = i) = U.filter (fun x => P.label x = i.val) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => Subtype.ext_iff)
  rw [he]
  exact P.small _

end CutPartition
end HyperbolicObstruction.PlanarRecursion

end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_SeparatorComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PlanarRecursion
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- At most one original connected component can occupy more than half of
a specified carrier. Thus a uniform separator theorem for the actual
connected components extends with the SAME constant to disconnected graphs. -/
theorem component_separators_union (G : SimpleGraph V) (c : ℕ)
    (hcomp : ∀ C : G.ConnectedComponent, ∀ U : Finset C.supp,
      ∃ S : Finset C.supp, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
        ∀ W : Finset C.supp, W ⊆ U → Disjoint W S →
          (C.toSimpleGraph.induce (W : Set C.supp)).Preconnected → 2*W.card ≤ U.card)
    (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ S.card ≤ c*Nat.sqrt U.card ∧
      ∀ W : Finset V, W ⊆ U → Disjoint W S →
        (G.induce (W : Set V)).Preconnected → 2*W.card ≤ U.card := by
  classical
  have hcolor (W : Finset V) (hc : (G.induce (W : Set V)).Preconnected) :
      ∀ v ∈ W, ∀ w ∈ W, G.connectedComponentMk v = G.connectedComponentMk w :=
    preconnected_color_constant G (W : Set V) hc G.connectedComponentMk
      (fun _ _ _ _ hadj => ConnectedComponent.sound hadj.reachable)
  by_cases hbig : ∃ C : G.ConnectedComponent, U.card < 2*(U.filter (fun v => G.connectedComponentMk v = C)).card
  · obtain ⟨C,hbig⟩ := hbig
    let UC : Finset C.supp := Finset.univ.filter (fun v => v.val ∈ U)
    have hUCimage : UC.image Subtype.val = U.filter (fun v => G.connectedComponentMk v = C) := by
      ext v
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,UC]
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact ⟨hw,w.property⟩
      · intro hv
        exact ⟨⟨v,hv.2⟩,hv.1,rfl⟩
    have hUCcard : UC.card = (U.filter (fun v => G.connectedComponentMk v = C)).card := by
      rw [← hUCimage,Finset.card_image_of_injective _ Subtype.val_injective]
    have hUCle : UC.card ≤ U.card := hUCcard.trans_le (Finset.card_filter_le _ _)
    obtain ⟨SC,hSCU,hSCcard,hSCsep⟩ := hcomp C UC
    let S := SC.image Subtype.val
    have hSU : S ⊆ U := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp (hSCU hw)).2
    refine ⟨S,hSU,?_,?_⟩
    · rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact hSCcard.trans (Nat.mul_le_mul_left c (Nat.sqrt_le_sqrt hUCle))
    · intro W hWU hWS hc
      by_cases hmeet : ∃ v ∈ W, G.connectedComponentMk v = C
      · obtain ⟨v,hv,hvC⟩ := hmeet
        have hall : ∀ w ∈ W, w ∈ C.supp := by
          intro w hw
          exact (hcolor W hc w hw v hv).trans hvC
        let WC : Finset C.supp := Finset.univ.filter (fun w => w.val ∈ W)
        have hWCimage : WC.image Subtype.val = W := by
          ext w
          simp only [Finset.mem_image,WC,Finset.mem_filter,Finset.mem_univ,true_and]
          constructor
          · rintro ⟨z,hz,rfl⟩; exact hz
          · intro hw; exact ⟨⟨w,hall w hw⟩,hw,rfl⟩
        have hWCcard : WC.card = W.card := by
          rw [← hWCimage,Finset.card_image_of_injective _ Subtype.val_injective]
        have hWCU : WC ⊆ UC := by
          intro w hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hWU (Finset.mem_filter.mp hw).2⟩
        have hWCdisj : Disjoint WC SC := by
          apply Finset.disjoint_left.mpr
          intro w hw hwS
          exact Finset.disjoint_left.mp hWS (Finset.mem_filter.mp hw).2
            (Finset.mem_image.mpr ⟨w,hwS,rfl⟩)
        have hWCconn : (C.toSimpleGraph.induce (WC : Set C.supp)).Preconnected := by
          let g : G.induce (W : Set V) →g C.toSimpleGraph.induce (WC : Set C.supp) := {
            toFun := fun w => ⟨⟨w.val,hall w.val w.property⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _,w.property⟩⟩
            map_rel' := fun h => h }
          apply hc.map g
          intro w
          exact ⟨⟨w.val.val,(Finset.mem_filter.mp w.property).2⟩,Subtype.ext (Subtype.ext rfl)⟩
        have hh := hSCsep WC hWCU hWCdisj hWCconn
        rw [hWCcard] at hh
        exact hh.trans hUCle
      · have hdisj : Disjoint W (U.filter (fun v => G.connectedComponentMk v = C)) := by
          apply Finset.disjoint_left.mpr
          intro v hv hvC
          exact hmeet ⟨v,hv,(Finset.mem_filter.mp hvC).2⟩
        have hsub : W ∪ U.filter (fun v => G.connectedComponentMk v = C) ⊆ U :=
          Finset.union_subset hWU (Finset.filter_subset _ _)
        have hh := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj] at hh
        omega
  · refine ⟨∅,Finset.empty_subset _,by simp,?_⟩
    intro W hWU _ hc
    by_cases he : W.Nonempty
    · obtain ⟨v,hv⟩ := he
      have hsub : W ⊆ U.filter (fun w => G.connectedComponentMk w = G.connectedComponentMk v) := by
        intro w hw
        exact Finset.mem_filter.mpr ⟨hWU hw,hcolor W hc w hw v hv⟩
      have hh := Nat.mul_le_mul_left 2 (Finset.card_le_card hsub)
      have hn := not_lt.mp (fun h => hbig ⟨G.connectedComponentMk v,h⟩)
      exact hh.trans hn
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp

end HyperbolicObstruction.PlanarRecursion
end
end

end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageClosedCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Closed simplices in the actual voltage cover. The extended chart formula is
continuous even when its anchor coordinate is zero, by the triangle cocycle. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def closedFace (s : Finset V) : Set (Carrier K) := {x | x.val ∈ simplex s}

lemma member_of_positive {s : Finset V} (x : closedFace (K := K) s) {a : V}
    (ha : 0 < x.val.val a) : a ∈ s := by
  by_contra hn
  have hz := x.property.2.2 a hn
  exact (ne_of_gt ha) hz

lemma inChart_change_face {s : Finset V} (hs : s ∈ K.faces)
    {a b : V} (ha : a ∈ s) (hb : b ∈ s) (x : closedFace (K := K) s) (g : G) :
    v.inChart b x.val (g * v.value a b) = v.inChart a x.val g := by
  apply v.totalSpace_ext
  · rfl
  simp only [inChart_coordinate,mul_assoc]
  congr 1
  apply v.triangle
  apply (K.isRelLowerSet_faces hs).2 _ (by simp)
  intro z hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact ha
  · exact hb
  · exact member_of_positive x (v.core.mem_baseSet_at x.val)

lemma inChart_continuous_face {s : Finset V} (hs : s ∈ K.faces)
    {a : V} (ha : a ∈ s) (g : G) :
    Continuous (fun x : closedFace (K := K) s => v.inChart a x.val g) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  let j := v.core.indexAt x.val
  have hx : x.val ∈ openStar K j := v.core.mem_baseSet_at x.val
  have hj : j ∈ s := member_of_positive x hx
  have he : (fun z : closedFace (K := K) s => v.inChart a z.val g) =
      fun z => v.inChart j z.val (g * v.value a j) := by
    funext z
    exact (v.inChart_change_face hs ha hj z g).symm
  rw [he]
  apply ((v.core.localTriv j).toOpenPartialHomeomorph.continuousAt_symm ?_).comp
    (continuousAt_subtype_val.prodMk continuousAt_const)
  exact (v.core.localTriv j).mem_target.mpr hx

def faceLift {s : Finset V} (hs : s ∈ K.faces) {a : V} (ha : a ∈ s) (g : G) :
    C(closedFace (K := K) s,v.TotalSpace) :=
  ⟨fun x => v.inChart a x.val g,v.inChart_continuous_face hs ha g⟩

@[simp] lemma faceLift_proj {s : Finset V} (hs : s ∈ K.faces) {a : V}
    (ha : a ∈ s) (g : G) (x : closedFace (K := K) s) :
    v.proj (v.faceLift hs ha g x) = x.val := rfl

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_VoltageEdges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal oriented edges and triangles of the genuine voltage cover. -/
noncomputable section

open scoped Topology unitInterval
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def vertexLift (a : V) (g : G) : v.TotalSpace := (v.vertexFiber a g).val
@[simp] lemma vertexLift_proj (a : V) (g : G) : v.proj (v.vertexLift a g) = vertex K a := rfl
@[simp] lemma vertexLift_coordinate (a : V) (g : G) : v.coordinate (v.vertexLift a g) = g := rfl
lemma inChart_vertex (a b : V) (g : G) :
    v.inChart a (vertex K b) g = v.vertexLift b (g * v.value a b) := by
  apply v.totalSpace_ext
  · rfl
  · simp [indexAt_vertex]

variable {v}
def edgePoint {a b : V} (h : {a,b} ∈ K.faces) : C(I,closedFace (K := K) {a,b}) where
  toFun t := ⟨edgePath K h t,
    straight_mem_face K (straight_in_face K h _ _ (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp))) (vertex_mem_simplex K (by simp)) (vertex_mem_simplex K (by simp)) t⟩
  continuous_toFun := (edgePath K h).continuous.subtype_mk _
variable (v)

def edgeLift {a b : V} (h : {a,b} ∈ K.faces) (g : G) :
    Path (v.vertexLift a g) (v.vertexLift b (g * v.value a b)) where
  toFun t := v.faceLift h (a:=a) (by simp) g (edgePoint h t)
  continuous_toFun := (v.faceLift h (a:=a) (by simp) g).continuous.comp (edgePoint h).continuous
  source' := by
    change v.inChart a (edgePath K h 0) g = _
    rw [Path.source,inChart_vertex,v.self,mul_one]
  target' := by
    change v.inChart a (edgePath K h 1) g = _
    rw [Path.target,inChart_vertex]

@[simp] lemma edgeLift_proj {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.proj (v.edgeLift h g t) = edgePath K h t := rfl
@[simp] lemma edgeLift_apply {a b : V} (h : {a,b} ∈ K.faces) (g : G) (t : I) :
    v.edgeLift h g t = v.inChart a (edgePath K h t) g := rfl

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
end

section
-- module Solutions.OAIQ034_HG.HyperbolicGroups_IndexedFillingValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace HyperbolicObstruction

/-! The integral filling value of a literal nullword. This is a consequence
of constructed disks and sphere vanishing, not a replacement hypothesis. -/

/-! Literal walks in a signed incidence graph, with componentwise root paths.
No connectedness or universal-cover assertion is assumed. -/

/-! A literal disk-chain left inverse for the integral cell boundary. The
rooted-edge construction avoids assuming an arbitrary-cycle sphere producer. -/

/-! Subdivision of permutation cycles, with exact orbit-count preservation. -/
namespace PictureSwitch

section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D : Type*} [Fintype D] [DecidableEq D]

namespace PermInsertion
variable (f : Perm D) (p : D → Prop)

/-- Insert exactly one separately indexed point after every point satisfying p. -/
def perm : Perm (D ⊕ Subtype p) where
  toFun := fun x => match x with
    | .inl d => if h : p d then .inr ⟨d,h⟩ else .inl (f d)
    | .inr t => .inl (f t.val)
  invFun := fun x => match x with
    | .inl d => if h : p (f⁻¹ d) then .inr ⟨f⁻¹ d,h⟩ else .inl (f⁻¹ d)
    | .inr t => .inl t.val
  left_inv := by
    rintro (d|t)
    · by_cases h : p d <;> simp [h]
    · simp [t.property]
  right_inv := by
    rintro (d|t)
    · by_cases h : p (f.symm d) <;> simp [h]
    · simp [t.property]

def collapse : D ⊕ Subtype p → D := Sum.elim id Subtype.val

end PermInsertion
end

/-! Literal radial triangulation of the free polygon faces of a finite map.
This section concerns genuine permutations; no topological genus assertion is
included in the input. -/
section
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
variable {D E : Type*} [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

namespace ConeExpansion
variable (p : D → Prop)

abbrev Point := D ⊕ (Subtype p ⊕ Subtype p)

def collapse : Point p → D := Sum.elim id (Sum.elim Subtype.val Subtype.val)

end ConeExpansion
end

/-! Exact contraction of radial triangle stars. -/
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
end PictureSwitch

/-! Local elementary triangle incidence induces the exact radial contraction. -/

/-! Lifting actual word homotopies to the voltage cover, with the negative
orientation based at the positive lift's initial endpoint. -/

/-!
The actual elementary triangles imply the compressed cone polygon equations.
Unlike the redundant polygon bouquet, this presentation retains exactly the
elementary indexed top triangles.
-/

section
namespace GraphGroupWalk
open SimpleGraph
variable {V H : Type*} {G : SimpleGraph V} [Group H]

lemma eval_potential (c : G.Dart → H) (p : V → H)
    (he : ∀ e : G.Dart, p e.fst * c e = p e.snd)
    {u v : V} (q : G.Walk u v) : p u * eval c q = p v := by
  induction q with
  | nil => exact mul_one _
  | @cons u v z h q ih =>
    rw [eval_cons, ← mul_assoc, he ⟨(u,v),h⟩, ih]
end GraphGroupWalk
end

/-! Actual genus-zero disks for every closed elementary loop in the original
letter voltage cover. No cycle-representation or asphericity hypothesis. -/

/-! No reselection: the same final arrays already have the precise uniform
lifted-picture estimate. Apply the new disk-chain left inverse to those arrays. -/

section

/-! Reindex the literal finite barycentric carrier onto the frozen challenge's
vertex type `Fin n`. No change of realization or topology is involved. -/

open scoped Topology
namespace FinitePolyhedron
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def reindex (K : AbstractSimplicialComplex V) (e : V ≃ W) : AbstractSimplicialComplex W :=
  { K.toPreAbstractSimplicialComplex.map e with
    singleton_mem := fun w => ⟨{e.symm w},K.singleton_mem _,by simp⟩ }

omit [DecidableEq V] in
lemma rename_mem (K : AbstractSimplicialComplex V) (e : V ≃ W) (x : V → ℝ) :
    x ∈ carrierSet K ↔ (fun j => x (e.symm j)) ∈ carrierSet (reindex K e) := by
  constructor
  · rintro ⟨h0,h1,s,hs,hx⟩
    refine ⟨fun j => h0 _,?_,s.image e,⟨s,hs,rfl⟩,?_⟩
    · simpa only [e.symm.sum_comp] using h1
    · intro j hj
      apply hx
      contrapose! hj
      exact Finset.mem_image.mpr ⟨e.symm j,hj,e.apply_symm_apply j⟩
  · rintro ⟨h0,h1,t,⟨s,hs,rfl⟩,hx⟩
    refine ⟨fun i => ?_,?_,s,hs,?_⟩
    · simpa using h0 (e i)
    · simpa only [e.symm.sum_comp] using h1
    · intro i hi
      simpa only [e.symm_apply_apply] using hx (e i) (by simpa using hi)

omit [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W] in
/-- Coordinate permutation, restricted to the exact two carrier subtypes. -/
lemma reindexPi_apply (e : V ≃ W) (x : V → ℝ) (j : W) :
    Homeomorph.piCongrLeft (Y := fun _ : W => ℝ) e x j = x (e.symm j) := by
  simpa using Homeomorph.piCongrLeft_apply_apply (Y := fun _ : W => ℝ) e x (e.symm j)

def reindexHomeomorph (K : AbstractSimplicialComplex V) (e : V ≃ W) :
    Carrier K ≃ₜ Carrier (reindex K e) :=
  (Homeomorph.piCongrLeft (Y := fun _ : W => ℝ) e).subtype (fun x => by
    have he := funext (reindexPi_apply e x)
    rw [he]
    exact rename_mem K e x)

omit [DecidableEq V] in
@[simp] lemma reindexHomeomorph_apply (K : AbstractSimplicialComplex V) (e : V ≃ W)
    (x : Carrier K) (j : W) : (reindexHomeomorph K e x).val j = x.val (e.symm j) :=
  reindexPi_apply e x.val j

omit [DecidableEq V] in
@[simp] lemma reindexHomeomorph_vertex (K : AbstractSimplicialComplex V) (e : V ≃ W) (v : V) :
    reindexHomeomorph K e (vertex K v) = vertex (reindex K e) (e v) := by
  ext j
  rw [reindexHomeomorph_apply]
  simp only [vertex,Pi.single_apply]
  by_cases h : j = e v
  · subst j; simp
  · have hi : e.symm j ≠ v := fun he => h (by simpa [he] using e.apply_symm_apply j |>.symm)
    simp [h,hi]

/-- The exact finite-complex representation in the release reference. -/
def toFiniteComplex (K : AbstractSimplicialComplex V) : FiniteComplex :=
  ⟨Fintype.card V,reindex K (Fintype.equivFin V)⟩

def toFiniteComplexHomeomorph (K : AbstractSimplicialComplex V) :
    Carrier K ≃ₜ (toFiniteComplex K).Carrier :=
  reindexHomeomorph K (Fintype.equivFin V)

end FinitePolyhedron

end

/-! The actual elementary incidence data now defines an actual finite
barycentric polyhedron. This file proves compactness and connectivity only;
no CW-universal-cover comparison is smuggled in as a structure field. -/

section
variable {G : Type*} [Group G]

lemma group_cycle_transport {m : ℕ} (u v : Fin m → G)
    (h : ∀ i, u i * v i = u (finRotate m i)) : (List.ofFn v).prod = 1 := by
  cases m with
  | zero => simp
  | succ m =>
    have hp : ∀ i : Fin (m+1), u 0 * ((List.ofFn v).take i.val).prod = u i := by
      apply Fin.induction
      · simp
      · intro i ih
        simp only [Fin.val_castSucc] at ih
        have ht := List.prod_take_succ (List.ofFn v) i.val
          (by simpa only [List.length_ofFn] using i.isLt.trans (Nat.lt_succ_self m))
        have he : (List.ofFn v)[i.val] = v i.castSucc := List.getElem_ofFn _
        rw [he] at ht
        change u 0 * ((List.ofFn v).take (i.val+1)).prod = _
        rw [ht,←mul_assoc,ih,h]
        exact congrArg u (finRotate_of_lt i.isLt)
    have ht := List.prod_take_succ (List.ofFn v) m (by simp)
    have he : (List.ofFn v)[m] = v (Fin.last m) := List.getElem_ofFn _
    rw [he] at ht
    have hh := h (Fin.last m)
    rw [finRotate_last,←hp (Fin.last m),mul_assoc] at hh
    simp only [Fin.val_last] at hh
    rw [←ht] at hh
    have hlen : (List.ofFn v).length = m+1 := List.length_ofFn
    have ht0 : (List.ofFn v).take (m+1) = List.ofFn v := List.take_of_length_le hlen.le
    rw [ht0] at hh
    exact mul_left_cancel (hh.trans (mul_one (u 0)).symm)

end

/-! Restricting any flat voltage on the actual triangulation to the original
indexed graph. Literal cap triangles prove every original boundary relation. -/

namespace FinitePolygonModel.Data

section
open FinitePolyhedron
variable {V E C G : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C] [Group G]
variable (P : Data V E C) (W : Voltage P.complex G)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma triangle_of_facet (f : P.Facet) {a b c : P.Vertex}
    (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) (hc : c ∈ P.facet f) :
    {a,b,c} ∈ P.complex.faces := by
  refine ⟨by simp,Or.inr ⟨f,?_⟩⟩
  intro x hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl|rfl|rfl <;> assumption

omit [Fintype V] [Fintype E] [Fintype C] in
lemma voltage_on_facet (f : P.Facet) {a b c : P.Vertex}
    (ha : a ∈ P.facet f) (hb : b ∈ P.facet f) (hc : c ∈ P.facet f) :
    W.value a b * W.value b c = W.value a c :=
  W.triangle a b c (P.triangle_of_facet f ha hb hc)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graph_edge_first (e : E) (b : Bool) :
    {P.old (P.start (e,b)),P.mid e b} ∈ P.complex.faces := by
  cases b
  · exact P.edge_of_facet (.inl (e,2)) (by simp [facet,graphFace]) (by simp [facet,graphFace])
  · exact P.edge_of_facet (.inl (e,0)) (by simp [facet,graphFace]) (by simp [facet,graphFace])

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graph_edge_middle (e : E) (b : Bool) :
    {P.mid e b,P.mid e (!b)} ∈ P.complex.faces := by
  cases b <;> exact P.edge_of_facet (.inl (e,1)) (by simp [facet,graphFace]) (by simp [facet,graphFace])

/-- A full signed original edge is exactly its three path segments. -/
def graphTransport (e : E × Bool) : G :=
  W.value (P.old (P.start e)) (P.mid e.1 e.2) *
    W.value (P.mid e.1 e.2) (P.mid e.1 (!e.2)) *
      W.value (P.mid e.1 (!e.2)) (P.old (P.start (e.1,!e.2)))

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphTransport_reverse (e : E × Bool) :
    P.graphTransport W (e.1,!e.2) = (P.graphTransport W e)⁻¹ := by
  have h0 := W.reverse (P.graph_edge_first e.1 e.2)
  have h1 := W.reverse (P.graph_edge_middle e.1 e.2)
  have h2 := W.reverse (P.graph_edge_first e.1 (!e.2))
  rcases e with ⟨e,b⟩
  simp only [graphTransport,Bool.not_not,mul_inv_rev] at *
  rw [h0,h1,h2]
  group

omit [Fintype V] [Fintype E] [Fintype C] in
lemma graphTransport_signed (e : E × Bool) :
    P.graphTransport W e = signed (fun e => P.graphTransport W (e,true)) e := by
  rcases e with ⟨e,b⟩
  cases b
  · exact P.graphTransport_reverse W (e,true)
  · rfl

/-- A cap supplies a literal potential at every actual boundary occurrence. -/
def capTransport (q : P.Position) : G :=
  W.value (P.apex q.1) (P.outer q) * W.value (P.outer q) (P.base q)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma capTransport_next (q : P.Position) :
    P.capTransport W q * W.value (P.base q) (P.base (P.next q)) = P.capTransport W (P.next q) := by
  have h0 := P.voltage_on_facet W (.inr (q,0))
    (a := P.outer q) (b := P.base q) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  have h1 := P.voltage_on_facet W (.inr (q,1))
    (a := P.outer q) (b := P.outer (P.next q)) (c := P.base (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  have h2 := P.voltage_on_facet W (.inr (q,2))
    (a := P.apex q.1) (b := P.outer q) (c := P.outer (P.next q))
    (by simp [facet,collarFace]) (by simp [facet,collarFace]) (by simp [facet,collarFace])
  change (W.value (P.apex q.1) (P.outer q) * W.value (P.outer q) (P.base q)) * _ =
    W.value (P.apex q.1) (P.outer (P.next q)) * W.value (P.outer (P.next q)) (P.base (P.next q))
  rw [mul_assoc,h0,←h1,←mul_assoc,h2]

omit [Fintype V] [Fintype E] [Fintype C] in
lemma capTransport_side (c : C) (i : Fin (P.size c)) :
    P.capTransport W ⟨c,(i,0)⟩ * P.graphTransport W (P.side c i) =
      P.capTransport W ⟨c,(finRotate _ i,0)⟩ := by
  have h0 := P.capTransport_next W ⟨c,(i,0)⟩
  have h1 := P.capTransport_next W ⟨c,(i,1)⟩
  have h2 := P.capTransport_next W ⟨c,(i,2)⟩
  rw [base_next] at h2
  change P.capTransport W ⟨c,(i,0)⟩ *
    W.value (P.old (P.start (P.side c i))) (P.mid (P.side c i).1 (P.side c i).2) =
      P.capTransport W ⟨c,(i,1)⟩ at h0
  change P.capTransport W ⟨c,(i,1)⟩ *
    W.value (P.mid (P.side c i).1 (P.side c i).2) (P.mid (P.side c i).1 (!(P.side c i).2)) =
      P.capTransport W ⟨c,(i,2)⟩ at h1
  change P.capTransport W ⟨c,(i,2)⟩ *
    W.value (P.mid (P.side c i).1 (!(P.side c i).2))
      (P.old (P.start ((P.side c i).1,!(P.side c i).2))) =
      P.capTransport W ⟨c,(finRotate _ i,0)⟩ at h2
  rw [graphTransport,←mul_assoc,←mul_assoc,h0,h1,h2]

omit [Fintype V] [Fintype E] [Fintype C] in
/-- No relation in the original polygon presentation is merely assumed. -/
lemma graphTransport_cell (c : C) :
    (List.ofFn (fun i => P.graphTransport W (P.side c i))).prod = 1 :=
  group_cycle_transport (fun i => P.capTransport W ⟨c,(i,0)⟩)
    (fun i => P.graphTransport W (P.side c i)) (P.capTransport_side W c)

end

/-! Literal graph paths and canonical extensions of chosen old-vertex routes. -/

open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

omit [Fintype V] [Fintype E] [Fintype C] in
lemma outer_base_edge (q : P.Position) : {P.outer q,P.base q} ∈ P.complex.faces :=
  P.edge_of_facet (.inr (q,0)) (by simp [facet,collarFace]) (by simp [facet,collarFace])

omit [Fintype V] [Fintype E] [Fintype C] in
lemma apex_outer_edge (q : P.Position) : {P.apex q.1,P.outer q} ∈ P.complex.faces :=
  P.edge_of_facet (.inr (q,2)) (by simp [facet,collarFace]) (by simp [facet,collarFace])

abbrev edgeClass {a b : P.Vertex} (h : {a,b} ∈ P.complex.faces) :=
  Path.Homotopic.Quotient.mk (edgePath P.complex h)

/-- All three literal subdivisions of an indexed signed graph edge. -/
def graphChain (e : E × Bool) :
    EdgeChain P.complex (P.old (P.start e)) (P.old (P.start (e.1,!e.2))) :=
  .cons (P.graph_edge_first e.1 e.2)
    (.cons (P.graph_edge_middle e.1 e.2)
      (.cons (by simpa only [Finset.pair_comm] using P.graph_edge_first e.1 (!e.2)) (.nil _)))

variable (o : V)
abbrev OldRoutes := ∀ a : V,
  Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.old a))
variable (R : P.OldRoutes o)

def graphRoutes : ∀ a : V ⊕ (E × Bool),
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.graph a))
  | .inl a => R a
  | .inr (e,b) => (R (P.start (e,b))).trans (P.edgeClass (P.graph_edge_first e b))

def baseRoutes (q : P.Position) :
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.base q)) := by
  unfold base dartStart
  split_ifs
  · exact R (P.start (P.side q.1 q.2.1))
  · exact P.graphRoutes o R (.inr (P.side q.1 q.2.1))
  · exact P.graphRoutes o R (.inr ((P.side q.1 q.2.1).1,!(P.side q.1 q.2.1).2))

def outerRoutes (q : P.Position) :
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex (P.outer q)) :=
  (P.baseRoutes o R q).trans (P.edgeClass (P.outer_base_edge q)).symm

def firstPosition (c : C) : P.Position := ⟨c,(⟨0,P.positive c⟩,0)⟩

/-- Contracting only the new subdivision/collar tree; no original edge is
collapsed by this choice. -/
def routes : ∀ a : P.Vertex,
    Path.Homotopic.Quotient (vertex P.complex (P.old o)) (vertex P.complex a)
  | .inl a => P.graphRoutes o R a
  | .inr (.inr q) => P.outerRoutes o R q
  | .inr (.inl c) => (P.outerRoutes o R (P.firstPosition c)).trans
      (P.edgeClass (P.apex_outer_edge (P.firstPosition c))).symm

end FinitePolygonModel.Data

/-! Genuine continuous fundamental groups are generated by the finite edges. -/

/-! New subdivision, collar and cone edges do not create fundamental-group
generators. This concerns the actual barycentric realization. -/

/-! The literal polygon presentation maps to the actual pi1, and its tree
normalization has no hidden van Kampen hypothesis. -/

namespace FinitePolygonModel.Data
open FinitePolyhedron
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
  [DecidableEq V] [DecidableEq E] [DecidableEq C]
variable (P : Data V E C)

variable (o : V) (R : P.OldRoutes o)

abbrev PolygonGroup := PresentedGroup (FreeGroup.mk '' Set.range (fun c => List.ofFn (P.side c)))

end FinitePolygonModel.Data

/-! Identification of the actual finite elementary polyhedron's pi1 with the
original letter presentation, using actual path classes and voltage covers. -/

/-! The actual voltage cover is universal whenever its proved monodromy
comparison is bijective. No simple-connectivity premise on the total space
is substituted for the producer. -/

/-! The literal voltage bundle is an actual simply connected covering
of the actual finite polygon realization. We construct its connectivity from
monodromy, rather than naming an abstract universal cover as a hypothesis. -/

/-! Exact higher homotopy identification for the constructed simply connected
voltage covering of the actual frozen finite polyhedron. -/

section

/-! Literal area-counted edge-disk calculus on the frozen finite-complex
model. All path algebra below uses only the challenge's stutters and spurs. -/
namespace FiniteComplex
variable (K : FiniteComplex)

abbrev Chain := FinitePolyhedron.EdgeChain K.complex
end FiniteComplex
end

/-! Rooted path algebra with exact zero-cost spur cancellations. This is a
literal triangular disk calculus, not an appeal to topological equivalence. -/

/-! Quantitative finite-presentation change, with all word substitutions and
comparison disks constructed. Relator disks are used only after establishing
that the corresponding literal words are null. -/

/-! Literal finite relator words for the proved actual fundamental-group
presentation, including exact rooted route words. -/

/-! Realization of ordinary word disks as literal triangular edge disks over
the frozen finite polyhedron. Free-group folds become actual zero-cost spurs. -/

/-! Group-isomorphism transport for geometric actions. -/

/-! Actual homotopy-equivalence invariance of the fundamental group. -/

/-! The literal finite barycentric complex has exactly the original letter group,
not a conditional presentation of it. -/

/-! The same supplied final arrays yield infinite groups unconditionally.
This discharges the last group-action-side hypothesis; the finite-polyhedron
realization and group-to-topology consequences are still separate obligations. -/

/-! Elementary facts about WordLength and WordDistance for the four-point
characterization of hyperbolicity. -/

/-! Cochains are evaluated on the actual area-counted word homotopies.
Free folds contribute exactly zero; each literal relator contributes its
own cochain integral. No planar realization hypothesis is needed. -/

/-! Finite unit-speed vertex paths; all indices are bounded explicitly. -/

/-! A quantitative proof that linear word-homotopy filling bounds imply
four-point hyperbolicity. -/

/-! All clauses of the exact main except exclusion of compatible locally
CAT(-1) finite homotopy models. The complete literal hyperbolicity consequence
is now unconditional, on the SAME finite aspherical complex. -/

/-! The real comparison inequality needed to pass the manuscript's exact
cosh-midpoint CAT(-1) definition to the Euclidean CN midpoint inequality. -/

/-! The global cosh-midpoint comparison implies whole-segment CAT(0)
comparison. No completeness or globalization
hypothesis is hidden in this elementary curvature-monotonicity step. -/

/-! The finite difference maximum principle required for local geodesic
continuation. Endpoint estimates are literal, with no convergence assumption. -/

/-! Literal equal-time interpolation of finite geodesic polygons. -/
open Set Metric

end HyperbolicObstruction

end

end OAI
end


