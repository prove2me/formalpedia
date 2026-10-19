-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
-- name    : OAI_GroupTheory_Hyperbolic_TriangleFilling
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:43:17.077007+00:00
-- url     : https://prove2.me/theorems/a24bc5a8-4b94-4509-a939-530e7738d0f8
-- title:
--   Triangular genus-zero fillings of boundary words
-- statement:
--   Finite labelled planar maps that fill a word by triangles, a combinatorial form of van Kampen diagrams.
--
--   1. **Fillings.** Fix an edge alphabet $E$ with a flip $E\to E$, a vertex colouring $E\to V$, and a ternary face relation on $E$. A triangle filling of a word $w\in E^*$ consists of:
--   - a finite set of darts with a fixed-point-free reverse involution $r$ and a face permutation $n$ forming a planar map;
--   - edge labels with $\mathrm{label}(r d)=\mathrm{flip}(\mathrm{label}(d))$ and $\mathrm{color}(\mathrm{label}(rn\,d))=\mathrm{color}(\mathrm{label}(d))$;
--   - a boundary list for $n$ whose labels spell $w$.
--   Every dart off the boundary in a component meeting the boundary lies on a triangular face:
--   $$
--   n^3d=d,\qquad nd\ne d,\qquad \mathrm{face}\bigl(\mathrm{label}(d),\mathrm{label}(nd),\mathrm{label}(n^2d)\bigr).
--   $$
--   Components not meeting the boundary are allowed and ignored.
--   2. **Basic fillings.** The empty word, a backtrack $[e,\mathrm{flip}(e)]$ (two darts) and a single triangle $[a,b,c]$ (the dipole on six darts, under compatibility of colours and the flipped face) are fillable. Fillings can be rotated with the word. When flip is an involution and faces are flip-reversible, mirroring a filling (inverting $n$ and flipping labels) fills the reversed flipped word.
--   3. **Active darts.** A dart is active if it lies in a component meeting the boundary; activity is invariant under $r$ and $n$.
--   4. **Fillability.** A word is fillable if a triangle filling of it exists.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/TriangleFilling.lean by skeleton subtraction
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

namespace OAI

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

/-- A finite genus-zero map with a prescribed exterior walk. Other components
are allowed but ignored; only the component meeting the boundary must be filled.
This handles components detached by folds, spurs, and empty boundary words. -/
structure TriangleFilling {E V : Type} (flip : E → E) (color : E → V)
    (face : E → E → E → Prop) (w : List E) where
  Dart : Type
  [finiteDart : Fintype Dart]
  reverse : Perm Dart
  next : Perm Dart
  reverse_involutive : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d
  label : Dart → E
  reverse_label : ∀ d, label (reverse d) = flip (label d)
  color_next : ∀ d, color (label ((reverse*next) d)) = color (label d)
  planar : PlanarMap reverse next
  boundary : List Dart
  boundary_cycle : IsBoundary next boundary
  boundary_word : boundary.map label = w
  triangular : ∀ d, (∃ b ∈ boundary, components reverse next d b) → d ∉ boundary →
    (next^3) d = d ∧ next d ≠ d ∧ face (label d) (label (next d)) (label ((next^2) d))

attribute [instance] TriangleFilling.finiteDart

namespace TriangleFilling
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def empty : TriangleFilling flip color face [] where
  Dart := Fin 0
  reverse := 1
  next := 1
  reverse_involutive := fun _ => rfl
  reverse_ne := by intro d; exact Fin.elim0 d
  label := Fin.elim0
  reverse_label := by intro d; exact Fin.elim0 d
  color_next := by intro d; exact Fin.elim0 d
  planar := by
    simp only [PlanarMap,one_mul,cycleCount_one,componentCount_one,Fintype.card_fin]
  boundary := []
  boundary_cycle := ⟨by simp,by simp⟩
  boundary_word := rfl
  triangular := by intro d; exact Fin.elim0 d

noncomputable def rotate {w : List E} (D : TriangleFilling flip color face w) (n : ℕ) :
    TriangleFilling flip color face (w.rotate n) where
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
  triangular := by
    intro d hd hn
    apply D.triangular d
    · obtain ⟨b,hb,hdb⟩ := hd
      exact ⟨b,List.mem_rotate.mp hb,hdb⟩
    · simpa only [List.mem_rotate] using hn

end TriangleFilling
end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem PlanarMap.involution (r : Perm A) (h : Function.Involutive r) : PlanarMap r r := by
  have hr : r*r = 1 := Equiv.ext h
  have hc : componentCount r r = cycleCount r := by
    simp only [componentCount,components,sup_idem,cycleCount,Cycles]
  simp only [PlanarMap,hr,cycleCount_one,hc]
  omega

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable def backtrack (hflip : Function.Involutive flip) (e : E) :
    TriangleFilling flip color face [e,flip e] where
  Dart := Fin 2
  reverse := Equiv.swap 0 1
  next := Equiv.swap 0 1
  reverse_involutive := Equiv.swap_apply_self 0 1
  reverse_ne := by intro a; fin_cases a <;> norm_num [Equiv.swap_apply_def,Fin.ext_iff]
  label := fun d => if d = 0 then e else flip e
  reverse_label := by
    intro d
    fin_cases d <;> norm_num [Equiv.swap_apply_def,Fin.ext_iff]
    exact (hflip e).symm
  color_next := by intro d; simp only [Perm.mul_apply,Equiv.swap_apply_self]
  planar := PlanarMap.involution _ (Equiv.swap_apply_self 0 1)
  boundary := [0,1]
  boundary_cycle := ⟨by decide,by intro a _; fin_cases a <;> simp⟩
  boundary_word := by simp
  triangular := by intro d _ hn; fin_cases d <;> simp at hn

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

def Active {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) : Prop :=
  ∃ b ∈ D.boundary, components D.reverse D.next a b

theorem active_iff_of_components {w : List E} (D : TriangleFilling flip color face w)
    {a b : D.Dart} (h : components D.reverse D.next a b) : D.Active a ↔ D.Active b := by
  constructor <;> rintro ⟨c,hc,hc'⟩
  · exact ⟨c,hc,(components D.reverse D.next).trans ((components D.reverse D.next).symm h) hc'⟩
  · exact ⟨c,hc,(components D.reverse D.next).trans h hc'⟩

theorem active_reverse {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) :
    D.Active (D.reverse a) ↔ D.Active a :=
  D.active_iff_of_components ((show Perm.SameCycle.setoid D.reverse ≤
    components D.reverse D.next from le_sup_left)
      (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _)))

theorem active_next {w : List E} (D : TriangleFilling flip color face w) (a : D.Dart) :
    D.Active (D.next a) ↔ D.Active a :=
  D.active_iff_of_components ((show Perm.SameCycle.setoid D.next ≤
    components D.reverse D.next from le_sup_right)
      (Perm.sameCycle_apply_left.mpr (Perm.SameCycle.refl _ _)))

theorem active_of_mem {w : List E} (D : TriangleFilling flip color face w)
    {a : D.Dart} (ha : a ∈ D.boundary) : D.Active a :=
  ⟨a,ha,(components D.reverse D.next).refl _⟩

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq

theorem dipoleReverse_involutive : Function.Involutive dipoleReverse := by
  intro j; fin_cases j <;> simp

theorem dipoleReverse_ne (j : Fin 6) : dipoleReverse j ≠ j := by
  fin_cases j <;> norm_num [dipoleReverse,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]

theorem dipoleReverse_count : cycleCount dipoleReverse = 3 := by
  have h := card_eq_mul_cycles dipoleReverse 2 (orbit_card_involution dipoleReverse
    dipoleReverse_involutive dipoleReverse_ne)
  have hh : (6:ℕ) = 2 * cycleCount dipoleReverse := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

theorem dipoleVertex_count : cycleCount (dipoleReverse*dipoleFace) = 3 := by
  have hi : Function.Involutive (dipoleReverse*dipoleFace) := by
    intro j; fin_cases j <;> simp [Perm.mul_apply]
  have hn : ∀ j, (dipoleReverse*dipoleFace) j ≠ j := by
    intro j; fin_cases j <;> norm_num [dipoleReverse,dipoleFace,Perm.mul_apply,Equiv.swap_apply_def,Fin.ext_iff]
  have h := card_eq_mul_cycles (dipoleReverse*dipoleFace) 2
    (orbit_card_involution _ hi hn)
  have hh : (6:ℕ) = 2 * cycleCount (dipoleReverse*dipoleFace) := by
    simpa only [Fintype.card_fin,cycleCount,Nat.card_eq_fintype_card] using h
  omega

theorem dipole_components (a b : Fin 6) : components dipoleReverse dipoleFace a b := by
  let s := components dipoleReverse dipoleFace
  have hr (j : Fin 6) : s j (dipoleReverse j) :=
    (show Perm.SameCycle.setoid dipoleReverse ≤ s from le_sup_left)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have hf (j : Fin 6) : s j (dipoleFace j) :=
    (show Perm.SameCycle.setoid dipoleFace ≤ s from le_sup_right)
      (Perm.sameCycle_apply_right.mpr (Perm.SameCycle.refl _ _))
  have h01 : s 0 1 := by simpa only [dipoleFace_zero] using hf 0
  have h12 : s 1 2 := by simpa only [dipoleFace_one] using hf 1
  have h03 : s 0 3 := by simpa only [dipoleReverse_zero] using hr 0
  have h34 : s 3 4 := by simpa only [dipoleFace_three] using hf 3
  have h45 : s 4 5 := by simpa only [dipoleFace_four] using hf 4
  have h0 (j : Fin 6) : s 0 j := by
    fin_cases j
    · exact s.refl 0
    · exact h01
    · exact s.trans h01 h12
    · exact h03
    · exact s.trans h03 h34
    · exact s.trans (s.trans h03 h34) h45
  exact s.trans (s.symm (h0 a)) (h0 b)

theorem dipoleComponent_count : componentCount dipoleReverse dipoleFace = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨Quotient.mk _ 0,?_⟩
  intro z
  obtain ⟨j,rfl⟩ := Quotient.mk_surjective z
  exact Quotient.sound (dipole_components j 0)

theorem dipole_planar : PlanarMap dipoleReverse dipoleFace := by
  simp only [PlanarMap,dipoleReverse_count,dipoleFace_count,dipoleVertex_count,
    dipoleComponent_count,Fintype.card_fin]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

def triLabel (a b c : E) (j : Fin 6) : E :=
  if j=0 then a else if j=1 then b else if j=2 then c else
  if j=3 then flip a else if j=4 then flip c else flip b

noncomputable def triangle (hflip : Function.Involutive flip)
    (hrot : ∀ a b c, face a b c → face b c a)
    (a b c : E) (hab : color a = color (flip b))
    (hbc : color b = color (flip c)) (hca : color c = color (flip a))
    (hface : face (flip a) (flip c) (flip b)) :
    TriangleFilling flip color face [a,b,c] where
  Dart := Fin 6
  reverse := dipoleReverse
  next := dipoleFace
  reverse_involutive := dipoleReverse_involutive
  reverse_ne := dipoleReverse_ne
  label := triLabel (flip := flip) a b c
  reverse_label := by
    intro j; fin_cases j <;> simp [triLabel]
    all_goals exact (hflip _).symm
  color_next := by
    intro j; fin_cases j <;> simp [Perm.mul_apply,triLabel,hab,hbc,hca]
  planar := dipole_planar
  boundary := [0,1,2]
  boundary_cycle := by
    constructor
    · decide
    · intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl|rfl|rfl <;> simp [List.formPerm_cons_cons,Equiv.swap_apply_def]
  boundary_word := by simp [triLabel]
  triangular := by
    intro j _ hj
    fin_cases j
    · simp at hj
    · simp at hj
    · simp at hj
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hface
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hrot _ _ _ hface
    · norm_num [pow_succ',Perm.mul_apply,triLabel,dipoleFace,Equiv.swap_apply_def,Fin.ext_iff]
      exact hrot _ _ _ (hrot _ _ _ hface)

end Release075.TriangleFilling

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

omit [Fintype A] in
theorem cycleCount_inv (f : Perm A) : cycleCount f⁻¹ = cycleCount f := by
  apply Nat.card_congr
  exact Quotient.congr (Equiv.refl A) (fun _ _ => Perm.sameCycle_inv)

omit [Fintype A] in
theorem components_inv_right (r f : Perm A) : components r f⁻¹ = components r f := by
  have hf : Perm.SameCycle.setoid f⁻¹ = Perm.SameCycle.setoid f :=
    Setoid.ext (fun _ _ => Perm.sameCycle_inv)
  simp only [components,hf]

theorem PlanarMap.inv_right {r f : Perm A} (hi : Function.Involutive r)
    (hp : PlanarMap r f) : PlanarMap r f⁻¹ := by
  have hr : r⁻¹ = r := by
    apply inv_eq_of_mul_eq_one_left
    exact Equiv.ext hi
  have hc : cycleCount (r*f⁻¹) = cycleCount (r*f) := by
    rw [cycleCount_mul_comm]
    have he : f⁻¹*r = (r*f)⁻¹ := by rw [mul_inv_rev,hr]
    rw [he,cycleCount_inv]
  simpa only [PlanarMap,cycleCount_inv,hc,componentCount,components_inv_right] using hp

omit [Fintype A] in
theorem perm_apply_inv (f : Perm A) (a : A) : f (f⁻¹ a) = a := f.apply_symm_apply a

omit [Fintype A] in
theorem inv_cycle_three (f : Perm A) {a : A} (h : (f^3) a = a) :
    f⁻¹ a = (f^2) a ∧ (f⁻¹^2) a = f a ∧ (f⁻¹^3) a = a := by
  have he : f⁻¹ a = (f^2) a := by
    apply f.injective
    rw [perm_apply_inv]
    exact h.symm
  refine ⟨he,?_,?_⟩
  · rw [pow_two,Perm.mul_apply,he]
    change f⁻¹ (f (f a)) = f a
    exact f.symm_apply_apply _
  · rw [inv_pow]
    apply (f^3).injective
    rw [perm_apply_inv,h]

end Release075.PermCycles

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*}

theorem IsBoundary.reverse {f : Perm A} {l : List A} (h : IsBoundary f l) :
    IsBoundary f⁻¹ l.reverse := by
  refine ⟨List.nodup_reverse.mpr h.1,?_⟩
  intro a ha
  have ha' := List.mem_reverse.mp ha
  have hb : f⁻¹ a ∈ l := by
    apply (h.mem_iff _).mp
    simpa only [perm_apply_inv] using ha'
  rw [List.formPerm_reverse]
  apply l.formPerm.injective
  rw [←h.2 _ hb,perm_apply_inv,perm_apply_inv]

end Release075

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Reverse the orientation of the whole filling, not just its boundary word. -/
noncomputable def mirror {w : List E} (D : TriangleFilling flip color face w)
    (hflip : Function.Involutive flip)
    (hface : ∀ a b c, face a b c → face (flip a) (flip c) (flip b)) :
    TriangleFilling flip color face (w.reverse.map flip) where
  Dart := D.Dart
  reverse := D.reverse
  next := D.next⁻¹
  reverse_involutive := D.reverse_involutive
  reverse_ne := D.reverse_ne
  label := flip ∘ D.label
  reverse_label := by
    intro a
    simp only [Function.comp_apply,D.reverse_label]
  color_next := by
    intro a
    simp only [Function.comp_apply,Perm.mul_apply,D.reverse_label]
    rw [hflip]
    have h := D.color_next (D.next⁻¹ a)
    simpa only [Perm.mul_apply,perm_apply_inv,D.reverse_label] using h.symm
  planar := D.planar.inv_right D.reverse_involutive
  boundary := D.boundary.reverse
  boundary_cycle := D.boundary_cycle.reverse
  boundary_word := by rw [←List.map_map,List.map_reverse,D.boundary_word]
  triangular := by
    intro a ha hn
    have ha' : ∃ b ∈ D.boundary, components D.reverse D.next a b := by
      obtain ⟨b,hb,hab⟩ := ha
      refine ⟨b,List.mem_reverse.mp hb,?_⟩
      rw [components_inv_right] at hab
      exact hab
    have ht := D.triangular a ha' (by simpa only [List.mem_reverse] using hn)
    have he := inv_cycle_three D.next ht.1
    refine ⟨he.2.2,?_,?_⟩
    · intro h
      apply ht.2.1
      have hh := congrArg D.next h
      simpa only [perm_apply_inv] using hh.symm
    · simp only [Function.comp_apply,he.1,he.2.1]
      exact hface _ _ _ ht.2.2

end Release075.TriangleFilling

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

/-- Existence of a finite labelled genus-zero filling. This abbreviation contains
no geometric assertion outside the fully specified finite map. -/
def Fillable (flip : E → E) (color : E → V) (face : E → E → E → Prop) (w : List E) : Prop :=
  Nonempty (TriangleFilling flip color face w)

namespace Fillable

end Fillable
end Release075

end OAI


