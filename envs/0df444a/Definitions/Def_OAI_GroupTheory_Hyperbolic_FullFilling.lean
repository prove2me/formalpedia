-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling
-- name    : OAI_GroupTheory_Hyperbolic_FullFilling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:58:36.720427+00:00
-- url     : https://prove2.me/theorems/2ded5679-c1bd-49fb-a75c-017dcb94a678
-- title:
--   Full fillings keeping every component
-- statement:
--   A variant of triangle fillings that keeps all connected components, used when folding the boundary.
--
--   1. **Full fillings.** A full filling of a word $w$ has the data of a triangle filling: darts with reverse involution $r$ and face permutation $n$ forming a planar map, flip-compatible labels with colours constant along $rn$, and a boundary list of $n$ spelling $w$. Every non-boundary dart, in every component, lies either on a triangular face or on an isolated two-dart bigon:
--   $$
--   \bigl(n^3a=a,\ na\ne a,\ \mathrm{face}(\ldots)\bigr)\quad\text{or}\quad\bigl(na=ra,\ n^2a=a\bigr).
--   $$
--   2. **From fillings.** Discarding the components that miss the boundary turns a triangle filling into a full filling without bigons.
--   3. **Trace.** For $F:E^3\to M$ into an abelian group, the trace sums $F$ over the corners of all non-boundary darts, i.e. over the inner faces:
--   $$
--   \sum_{a\notin\text{boundary}}F\bigl(\mathrm{label}(a),\mathrm{label}(na),\mathrm{label}(n^2a)\bigr).
--   $$
--   It is unchanged by rotating the word.
--   4. **Operations.** Full fillings can be rotated with their word, and mirrored (inverting $n$ and flipping labels) when flip is an involution and faces are flip-reversible. Boundaries pull back along injective intertwining maps.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullFilling.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres

namespace OAI

namespace Release075
open Equiv PermCycles

/-- Unlike an ordinary filling, this records *every* connected component.
The only nontriangular interior faces allowed are isolated two-dart spheres,
created when an exterior cancellable pair is folded. -/
structure FullFilling {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) (w : List E) where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ a, reverse a ≠ a
  label : Dart → E
  reverse_label : ∀ a, label (reverse a) = flip (label a)
  color_next : ∀ a, color (label ((reverse*next) a)) = color (label a)
  planar : PlanarMap reverse next
  boundary : List Dart
  boundary_cycle : IsBoundary next boundary
  boundary_word : boundary.map label = w
  cells : ∀ a, a ∉ boundary →
    ((next^3) a = a ∧ next a ≠ a ∧ face (label a) (label (next a)) (label ((next^2) a))) ∨
      (next a = reverse a ∧ (next^2) a = a)

attribute [instance] FullFilling.dartFintype

theorem IsBoundary.of_injective_map {A B : Type*} {f : Perm A} {g : Perm B}
    {l : List B} {e : B → A} (he : Function.Injective e) (hg : ∀ b, e (g b) = f (e b))
    (h : IsBoundary f (l.map e)) : IsBoundary g l := by
  classical
  refine ⟨h.1.of_map _,?_⟩
  intro b hb
  apply he
  rw [hg,h.2 _ (List.mem_map.mpr ⟨b,hb,rfl⟩)]
  exact formPerm_embedding ⟨e,he⟩ l b

namespace TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Discarding components disjoint from the outer face makes an ordinary
filling into a full filling, with no exceptional faces. -/
noncomputable abbrev full {w : List E} (D : TriangleFilling flip color face w) :
    FullFilling flip color face w where
  Dart := D.ActiveDart
  reverse := D.activeReverse
  next := D.activeNext
  reverse_involutive := D.activeReverse_involutive
  reverse_ne := D.activeReverse_ne
  label a := D.label a.val
  reverse_label a := D.reverse_label a.val
  color_next a := D.color_next a.val
  planar := D.active_planar
  boundary := D.boundary.pmap (fun a h => ⟨a,D.active_of_mem h⟩) (fun _ h => h)
  boundary_cycle := by
    apply IsBoundary.of_injective_map (f := D.next) Subtype.val_injective (fun _ => rfl)
    simpa only [List.map_pmap,List.pmap_eq_map,List.map_id_fun',id_eq] using D.boundary_cycle
  boundary_word := by simpa only [List.map_pmap,List.pmap_eq_map] using D.boundary_word
  cells := by
    intro a ha
    have hn : a.val ∉ D.boundary := by
      intro h
      apply ha
      exact List.mem_pmap.mpr ⟨a.val,h,rfl⟩
    have ht := D.triangular a.val a.property hn
    exact Or.inl ⟨Subtype.ext ht.1,fun he => ht.2.1 (congrArg Subtype.val he),ht.2.2⟩

end TriangleFilling

namespace FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : FullFilling flip color face w)

def Bigon (a : D.Dart) : Prop := D.next a = D.reverse a ∧ (D.next^2) a = a

/-- Integral corner evaluation, with the outer face omitted. -/
noncomputable def trace (F : E → E → E → M) : M :=
  ∑ a, if a ∈ D.boundary then 0 else
    F (D.label a) (D.label (D.next a)) (D.label ((D.next^2) a))

noncomputable abbrev rotate (n : ℕ) : FullFilling flip color face (w.rotate n) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := D.label
  reverse_label := D.reverse_label
  color_next := D.color_next
  planar := D.planar
  boundary := D.boundary.rotate n
  boundary_cycle := D.boundary_cycle.rotate n
  boundary_word := by rw [List.map_rotate,D.boundary_word]
  cells := by intro a ha; exact D.cells a (by simpa only [List.mem_rotate] using ha)

theorem trace_rotate (n : ℕ) (F : E → E → E → M) : (D.rotate n).trace F = D.trace F := by
  unfold trace
  dsimp only [rotate]
  simp only [List.mem_rotate]

noncomputable abbrev mirror (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    FullFilling flip color face (w.reverse.map flip) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next⁻¹
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := flip ∘ D.label
  reverse_label := by intro a; simp only [Function.comp_apply,D.reverse_label]
  color_next := by
    intro a
    simp only [Function.comp_apply,Perm.mul_apply,D.reverse_label]
    rw [hflip]
    have h := D.color_next (D.next⁻¹ a)
    simpa only [Perm.mul_apply,perm_apply_inv,D.reverse_label] using h.symm
  planar := D.planar.inv_right D.reverse_involutive
  boundary := D.boundary.reverse
  boundary_cycle := D.boundary_cycle.reverse
  boundary_word := by rw [← List.map_map,List.map_reverse,D.boundary_word]
  cells := by
    intro a hn
    rcases D.cells a (by simpa only [List.mem_reverse] using hn) with ht | hb
    · have he := inv_cycle_three D.next ht.1
      refine Or.inl ⟨he.2.2,?_,?_⟩
      · intro h
        apply ht.2.1
        have hh := congrArg D.next h
        simpa only [perm_apply_inv] using hh.symm
      · simp only [Function.comp_apply,he.1,he.2.1]
        exact hface _ _ _ ht.2.2
    · have he : D.next⁻¹ a = D.next a := by
        apply D.next.injective
        simpa only [perm_apply_inv,pow_two,Perm.mul_apply] using hb.2.symm
      refine Or.inr ⟨he.trans hb.1,?_⟩
      rw [pow_two,Perm.mul_apply,he]
      exact D.next.symm_apply_apply a

end FullFilling
end Release075

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

end OAI


