-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
-- name    : OAI_GroupTheory_Hyperbolic_Ribbons
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:51:23.762506+00:00
-- url     : https://prove2.me/theorems/78faf5e8-80c4-431c-9f23-0ad25040e1d1
-- title:
--   Triangle ribbons and their angle counts
-- statement:
--   Oriented triangulated disks with corner angles, for a combinatorial Gauss–Bonnet count.
--
--   1. **Angle disk counts.** These record a finite vertex set, numbers of edges and faces, boundary visits and nonnegative real angles at vertices with
--   $$
--   |V|+F=E+1,\qquad \sum_v\mathrm{visits}(v)+3F=2E,\qquad \sum_v\mathrm{angle}(v)=5F.
--   $$
--   The curvature of $v$ is $10-5\,\mathrm{visits}(v)-\mathrm{angle}(v)$, and the boundary length is the total number of visits.
--   2. **Triangle ribbons.** A triangle ribbon is a finite set of darts with a fixed-point-free involution `reverse`, a face permutation, and a distinguished outer face. The vertices are the cycles of $\mathrm{reverse}\cdot\mathrm{face}$ and carry colours in $\{0,1,2\}$. On every other face the colours of its corners are a bijection onto $\{0,1,2\}$, and
--   $$
--   \#\text{vertices}+\#\text{inner faces}=\#\text{edges}+1 .
--   $$
--   3. **Angles.** A corner on an inner face has angle $3$ at a vertex of colour $0$ and $1$ otherwise, so each inner face has angle sum $5$; outer corners have angle $0$ and count as boundary visits. The resulting counts are angle disk counts.
--   4. **From fillings.** For a triangle filling whose face relation has three distinct colours, the active darts (the component of the boundary) form a triangle ribbon with the boundary cycle as outer face. Walks in a sum of graphs restrict to either summand, and boundary darts form a single face cycle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Ribbons.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace Release075
open scoped BigOperators

/-- The numerical incidence identities of a nonempty planar triangle disk, with
boundary visits counted with multiplicity (including both sides of naked edges).
All fields are finite counts or angle data. No group conclusion is assumed. -/
structure AngleDiskCounts where
  Vertex : Type
  [vertexFintype : Fintype Vertex]
  edges : ℕ
  faces : ℕ
  visits : Vertex → ℕ
  angles : Vertex → ℝ
  angles_nonneg : ∀ v, 0 ≤ angles v
  euler : Fintype.card Vertex + faces = edges + 1
  exterior : (∑ v, visits v) + 3*faces = 2*edges
  angle_sum : (∑ v, angles v) = 5*faces

attribute [instance] AngleDiskCounts.vertexFintype
namespace AngleDiskCounts
variable (D : AngleDiskCounts)

def curvature (v : D.Vertex) : ℝ := 10 - 5*(D.visits v) - D.angles v

noncomputable def interior : Finset D.Vertex := by
  classical
  exact Finset.univ.filter (fun v => D.visits v = 0)

noncomputable def boundary : Finset D.Vertex := by
  classical
  exact Finset.univ.filter (fun v => D.visits v ≠ 0)

def boundaryLength : ℕ := ∑ v, D.visits v

end AngleDiskCounts
end Release075

namespace Release075
open scoped BigOperators
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq

/-- An oriented combinatorial triangle filling. Darts are incoming at the
corner they carry; `reverse * face` rotates those corners about a vertex.
This records finite incidence data, NOT existence of a filling for a nullword.
Its single distinguished face is the prescribed exterior walk, including spurs. -/
structure TriangleRibbon where
  Dart : Type
  [dartFintype : Fintype Dart]
  reverse : Perm Dart
  face : Perm Dart
  reverse_involution : Function.Involutive reverse
  reverse_ne : ∀ d, reverse d ≠ d
  outer : Cycles face
  color : Cycles (reverse * face) → Fin 3
  face_colors : ∀ c : Cycles face, c ≠ outer →
    Function.Bijective (fun d : {d : Dart // cl face d = c} => color (cl (reverse * face) d))
  euler : Fintype.card (Cycles (reverse * face)) +
      Fintype.card {c : Cycles face // c ≠ outer} = Fintype.card (Cycles reverse) + 1
attribute [instance] TriangleRibbon.dartFintype

namespace TriangleRibbon
variable (R : TriangleRibbon)
abbrev vertexPerm := R.reverse * R.face
abbrev Vertex := Cycles R.vertexPerm
abbrev Edge := Cycles R.reverse
abbrev Face := {c : Cycles R.face // c ≠ R.outer}

noncomputable def weight (c : Fin 3) : ℝ := if c = 0 then 3 else 1

noncomputable def cornerAngle (d : R.Dart) : ℝ :=
  if cl R.face d = R.outer then 0 else weight (R.color (cl R.vertexPerm d))

noncomputable def visits (v : R.Vertex) : ℕ :=
  ∑ d : R.Dart, if cl R.vertexPerm d = v ∧ cl R.face d = R.outer then 1 else 0

noncomputable def angles (v : R.Vertex) : ℝ :=
  ∑ d : R.Dart, if cl R.vertexPerm d = v then R.cornerAngle d else 0

@[simp] theorem cornerAngle_nonneg (d : R.Dart) : 0 ≤ R.cornerAngle d := by
  dsimp [cornerAngle,weight]
  split_ifs <;> norm_num

theorem angles_nonneg (v : R.Vertex) : 0 ≤ R.angles v := by
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact R.cornerAngle_nonneg d
  · rfl

theorem card_face_fiber (c : Cycles R.face) (hc : c ≠ R.outer) :
    Fintype.card {d : R.Dart // cl R.face d = c} = 3 := by
  have h := Fintype.card_congr (Equiv.ofBijective _ (R.face_colors c hc))
  simpa only [Fintype.card_fin] using h

theorem face_angle_sum (c : Cycles R.face) (hc : c ≠ R.outer) :
    (∑ d : {d : R.Dart // cl R.face d = c}, R.cornerAngle d) = 5 := by
  have hh : (∑ d : {d : R.Dart // cl R.face d = c},
      weight (R.color (cl R.vertexPerm d))) = ∑ i : Fin 3, weight i :=
    (Equiv.ofBijective _ (R.face_colors c hc)).sum_comp weight
  have he (d : {d : R.Dart // cl R.face d = c}) : R.cornerAngle d =
      weight (R.color (cl R.vertexPerm d)) := by
    simp only [cornerAngle,d.property,ite_eq_right hc]
  simp only [he]
  rw [hh]
  norm_num [Fin.sum_univ_succ,weight]

theorem dart_card : Fintype.card R.Dart = 2 * Fintype.card R.Edge :=
  card_eq_mul_cycles R.reverse 2 (orbit_card_involution R.reverse R.reverse_involution R.reverse_ne)

theorem visits_sum : (∑ v : R.Vertex, R.visits v) =
    Fintype.card {d : R.Dart // cl R.face d = R.outer} := by
  simp only [visits]
  rw [Finset.sum_comm]
  have hs (d : R.Dart) :
      (∑ v : R.Vertex, if cl R.vertexPerm d = v ∧ cl R.face d = R.outer then 1 else 0) =
      if cl R.face d = R.outer then 1 else 0 := by
    by_cases h : cl R.face d = R.outer <;> simp [h]
  simp only [hs]
  rw [← Finset.card_filter]
  exact (Fintype.card_subtype _).symm

theorem exterior_count : (∑ v : R.Vertex, R.visits v) + 3 * Fintype.card R.Face =
    2 * Fintype.card R.Edge := by
  rw [R.visits_sum,← R.dart_card,← sum_card_fibers R.face,
    Fintype.sum_eq_add_sum_subtype_ne _ R.outer]
  congr 1
  have h3 (c : R.Face) : Fintype.card {d : R.Dart // cl R.face d = c.val} = 3 :=
    R.card_face_fiber c.val c.property
  simp only [h3,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_comm]

theorem all_angles_sum : (∑ v : R.Vertex, R.angles v) = 5 * Fintype.card R.Face := by
  simp only [angles]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hh : (∑ c : Cycles R.face, ∑ d : {d : R.Dart // cl R.face d = c},
      R.cornerAngle d) = ∑ d : R.Dart, R.cornerAngle d := by
    simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
      (Equiv.sigmaFiberEquiv (cl R.face)).sum_comp R.cornerAngle
  rw [← hh,Fintype.sum_eq_add_sum_subtype_ne _ R.outer]
  have h0 : (∑ d : {d : R.Dart // cl R.face d = R.outer}, R.cornerAngle d) = 0 := by
    apply Finset.sum_eq_zero
    intro d _
    simp [cornerAngle,d.property]
  rw [h0,zero_add]
  have h5 (c : R.Face) : (∑ d : {d : R.Dart // cl R.face d = c.val}, R.cornerAngle d) = 5 :=
    R.face_angle_sum c.val c.property
  simp only [h5,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_comm]

/-- All arithmetic hypotheses of the earlier curvature identity are now derived
from actual edge/face/vertex permutations and face-color bijections. -/
noncomputable def counts : AngleDiskCounts where
  Vertex := R.Vertex
  edges := Fintype.card R.Edge
  faces := Fintype.card R.Face
  visits := R.visits
  angles := R.angles
  angles_nonneg := R.angles_nonneg
  euler := R.euler
  exterior := R.exterior_count
  angle_sum := R.all_angles_sum

end TriangleRibbon
end Release075

namespace Release075.SumWalk
variable {U V : Type*} {G : SimpleGraph U} {H : SimpleGraph V}

/-- Forget the disjoint summand tag from a walk in the left component. -/
def left {a b : U} : (G.sum H).Walk (.inl a) (.inl b) → G.Walk a b
  | .nil => .nil
  | .cons (v := .inl _) h p => (left p).cons (SimpleGraph.sum_adj_inl.mp h)
  | .cons (v := .inr _) h _ => by simp at h

@[simp] theorem left_length {a b : U} (p : (G.sum H).Walk (.inl a) (.inl b)) :
    (left p).length = p.length := by
  fun_induction left p <;> simp_all only [SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_nil]

@[simp] theorem map_left {a b : U} (p : (G.sum H).Walk (.inl a) (.inl b)) :
    (left p).map SimpleGraph.Embedding.sumInl.toHom = p := by
  fun_induction left p <;> simp_all only [SimpleGraph.Walk.map_cons,SimpleGraph.Walk.map_nil] <;> rfl

/-- The right-component extraction is left extraction after the graph sum swap. -/
def right {a b : V} (p : (G.sum H).Walk (.inr a) (.inr b)) : H.Walk a b :=
  left (p.map SimpleGraph.Iso.sumComm.toHom)

@[simp] theorem right_length {a b : V} (p : (G.sum H).Walk (.inr a) (.inr b)) :
    (right p).length = p.length :=
  (left_length _).trans (SimpleGraph.Walk.length_map _ _)

end Release075.SumWalk

namespace Release075
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem IsBoundary.sameCycle {f : Perm A} {l : List A} (h : IsBoundary f l)
    {a b : A} (ha : a ∈ l) (hb : b ∈ l) : f.SameCycle a b := by
  by_cases hab : a = b
  · subst b; exact .refl _ _
  have hlen : 2 ≤ l.length := by
    cases l with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons y ys => simp
  have hform : l.formPerm.SameCycle a b :=
    (List.isCycle_formPerm h.1 hlen).sameCycle
      ((List.formPerm_apply_mem_ne_self_iff l h.1 a ha).mpr hlen)
      ((List.formPerm_apply_mem_ne_self_iff l h.1 b hb).mpr hlen)
  apply sameCycle_le_of_step l.formPerm (Perm.SameCycle.setoid f) _ hform
  intro x
  by_cases hx : x ∈ l
  · rw [← h.2 x hx]
    exact (Perm.SameCycle.refl f x).apply_right
  · rw [List.formPerm_apply_of_notMem hx]

theorem IsBoundary.mem_iff_sameCycle {f : Perm A} {l : List A} (h : IsBoundary f l)
    {b : A} (hb : b ∈ l) (a : A) : a ∈ l ↔ f.SameCycle a b := by
  refine ⟨fun ha => h.sameCycle ha hb,fun hh => ?_⟩
  exact (invariant_pred_sameCycle f (· ∈ l) h.mem_iff hh).mpr hb

end Release075

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

theorem three_color_bijective (f : Perm A) (a : A) (q : A → Fin 3)
    (hp : (f^3) a = a) (hne : f a ≠ a)
    (hab : q a ≠ q (f a)) (hbc : q (f a) ≠ q ((f^2) a))
    (hca : q ((f^2) a) ≠ q a) :
    Function.Bijective (fun x : {x : A // cl f x = cl f a} => q x) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro x y hxy
    have hx : x.val ∈ orbit f a := (mem_orbit f a x).mpr ((cl_eq_iff f _ _).mp x.property).symm
    have hy : y.val ∈ orbit f a := (mem_orbit f a y).mpr ((cl_eq_iff f _ _).mp y.property).symm
    rw [orbit_eq_image f a (by omega : 0 < 3) hp] at hx hy
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hy
    apply Subtype.ext
    rw [← hi,← hj]
    change q x.val = q y.val at hxy
    rw [← hi,← hj] at hxy
    fin_cases i <;> fin_cases j <;>
      norm_num only [pow_zero,pow_one,Perm.one_apply] at hxy ⊢
    all_goals first | exact (hab hxy).elim | exact (hab hxy.symm).elim |
      exact (hbc hxy).elim | exact (hbc hxy.symm).elim |
      exact (hca hxy).elim | exact (hca hxy.symm).elim
  · rw [card_fiber,orbit_card_three f a hp hne,Fintype.card_fin]

end Release075.PermCycles

namespace Release075.TriangleFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}
variable {w : List E} (D : TriangleFilling flip color face w)

abbrev ActiveDart := {a : D.Dart // D.Active a}
noncomputable def activeReverse : Perm D.ActiveDart := D.reverse.subtypePerm D.active_reverse
noncomputable def activeNext : Perm D.ActiveDart := D.next.subtypePerm D.active_next

@[simp] theorem activeReverse_val (a : D.ActiveDart) : (D.activeReverse a).val = D.reverse a := rfl
@[simp] theorem activeNext_val (a : D.ActiveDart) : (D.activeNext a).val = D.next a := rfl

 theorem activeReverse_involutive : Function.Involutive D.activeReverse := by
  intro a
  apply Subtype.ext
  exact D.reverse_involutive a

 theorem activeReverse_ne (a : D.ActiveDart) : D.activeReverse a ≠ a := by
  intro h
  exact D.reverse_ne a (congrArg Subtype.val h)

 theorem active_planar : PlanarMap D.activeReverse D.activeNext :=
  D.planar.restrict D.Active D.active_reverse D.active_next

 theorem active_components (a b : D.ActiveDart) :
    components D.activeReverse D.activeNext a b := by
  rw [activeReverse,activeNext,components_subtype]
  obtain ⟨x,hx,hax⟩ := a.property
  obtain ⟨y,hy,hby⟩ := b.property
  have hxy : components D.reverse D.next x y :=
    (show Perm.SameCycle.setoid D.next ≤ components D.reverse D.next from le_sup_right)
      (D.boundary_cycle.sameCycle hx hy)
  exact (components D.reverse D.next).trans hax
    ((components D.reverse D.next).trans hxy ((components D.reverse D.next).symm hby))

 theorem active_componentCount {b : D.Dart} (hb : b ∈ D.boundary) :
    componentCount D.activeReverse D.activeNext = 1 := by
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · refine ⟨?_⟩
    intro x y
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        exact Quotient.sound (D.active_components x y)
  · exact ⟨Quotient.mk _ ⟨b,D.active_of_mem hb⟩⟩

 theorem active_color_step (q : V → Fin 3) (a : D.ActiveDart) :
    q (color (D.label ((D.activeReverse*D.activeNext) a))) = q (color (D.label a)) :=
  congrArg q (D.color_next a)

noncomputable def activeColor (q : V → Fin 3) : Cycles (D.activeReverse*D.activeNext) → Fin 3 :=
  descend _ (fun a => q (color (D.label a))) (D.active_color_step q)

 theorem active_boundary_iff {b : D.Dart} (hb : b ∈ D.boundary) (a : D.ActiveDart) :
    cl D.activeNext a = cl D.activeNext ⟨b,D.active_of_mem hb⟩ ↔ a.val ∈ D.boundary := by
  rw [cl_eq_iff,activeNext,Perm.sameCycle_subtypePerm]
  exact (D.boundary_cycle.mem_iff_sameCycle hb a.val).symm

/-- A nonempty labeled filling has its connected boundary component as an actual
Euler-characteristic-one triangle ribbon. No geometric embedding is postulated. -/
noncomputable def ribbon (q : V ≃ Fin 3)
    (hf : ∀ a b c, face a b c → color a ≠ color b ∧ color b ≠ color c ∧ color c ≠ color a)
    (b : D.Dart) (hb : b ∈ D.boundary) : TriangleRibbon where
  Dart := D.ActiveDart
  reverse := D.activeReverse
  face := D.activeNext
  reverse_involution := D.activeReverse_involutive
  reverse_ne := D.activeReverse_ne
  outer := cl D.activeNext ⟨b,D.active_of_mem hb⟩
  color := D.activeColor q
  face_colors := by
    intro c hc
    obtain ⟨a,rfl⟩ := cl_surjective D.activeNext c
    have ha : a.val ∉ D.boundary := fun h => hc ((D.active_boundary_iff hb a).mpr h)
    obtain ⟨hp,hn,hface⟩ := D.triangular a a.property ha
    obtain ⟨h01,h12,h20⟩ := hf _ _ _ hface
    have hp' : (D.activeNext^3) a = a := by
      apply Subtype.ext
      exact hp
    have hn' : D.activeNext a ≠ a := fun h => hn (congrArg Subtype.val h)
    exact three_color_bijective D.activeNext a (fun x => q (color (D.label x))) hp' hn'
      (fun h => h01 (q.injective h)) (fun h => h12 (q.injective h))
      (fun h => h20 (q.injective h))
  euler := by
    have hp := D.active_planar
    have hr := card_eq_mul_cycles D.activeReverse 2
      (orbit_card_involution D.activeReverse D.activeReverse_involutive D.activeReverse_ne)
    have hc := D.active_componentCount hb
    have hf' := card_subtype_ne_add_one (cl D.activeNext ⟨b,D.active_of_mem hb⟩)
    simp only [PlanarMap,cycleCount,Nat.card_eq_fintype_card] at hp hc hf'
    omega

end Release075.TriangleFilling

namespace Release075.SequenceWalk
variable {E : Type*} (L : SimpleGraph E)

def walk (a : ℕ → E) : (n : ℕ) → (∀ i, i < n → L.Adj (a i) (a (i+1))) → L.Walk (a 0) (a n)
  | 0, _ => .nil
  | n+1, h => (walk (fun i => a (i+1)) n (fun i hi => h (i+1) (by omega))).cons (h 0 (by omega))

@[simp] theorem length_walk (a : ℕ → E) (n : ℕ) (h) : (walk L a n h).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp only [walk,SimpleGraph.Walk.length_cons,ih]

end Release075.SequenceWalk

namespace Release075.PermCycles
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A : Type*} [Fintype A]

end Release075.PermCycles

namespace Release075.TriangleRibbon
open Equiv PermCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
variable (R : TriangleRibbon)

def IsOuter (a : R.Dart) : Prop := cl R.face a = R.outer

noncomputable def outerCorners (a : R.Dart) : Finset R.Dart :=
  (orbit R.vertexPerm a).filter R.IsOuter
noncomputable def innerCorners (a : R.Dart) : Finset R.Dart :=
  (orbit R.vertexPerm a).filter (fun b => ¬ R.IsOuter b)

variable {E : Type*} (L : SimpleGraph E) (label : R.Dart → E)
variable (hadj : ∀ a, ¬ R.IsOuter a → L.Adj (label a) (label (R.vertexPerm a)))
variable (hred : ∀ a, ¬ R.IsOuter a → ¬ R.IsOuter (R.vertexPerm a) →
  label a ≠ label (R.vertexPerm (R.vertexPerm a)))

include hadj hred

end Release075.TriangleRibbon

end OAI


