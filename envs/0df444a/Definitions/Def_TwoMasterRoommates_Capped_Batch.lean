-- Prove2me | Definitions.Def_TwoMasterRoommates_Capped_Batch
-- name    : TwoMasterRoommates_Capped_Batch
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:51:20.696429+00:00
-- url     : https://prove2.me/theorems/0a41787d-00b2-4b52-95e8-ac11a9a6b6bf
-- title:
--   Explicit alternating batch graph and constructed local kernel
-- statement:
--   The batch graph uses dense integer masters. A state records an orientation, two integer cuts, a donor count, three optional actual unordered edges, and a set of at most two deleted boundary identities. Coordinates and record names are stored relative to the orientation. An $A$ batch is defined literally by §§B.2–B.4; a $B$ batch uses the swapped instance.
--
--   The free region is the boundary $T_{i,j}=\{v:b(v)=j,a(v)>i\}$ together with the unseen rectangle $R_{i,j}=\{v:a(v)>i,b(v)>j\}$, removing deletions and reserved actual endpoints. An arc advances the current own cut strictly. Its explicit tests cover new-edge availability, shapes of outgoing and bridge edges, endpoint caps, output activity and ownership, prescribed qualities, all fixed pairs and fixed-versus-token and terminal pairs, and the synthetic receiver rejection test.
--
--   The local active, marked, optional and mandatory actual sets are constructed by the printed formulas. Distinct inherited and synthetic tokens are added with ranks $i$ and the new cut, respectively. The exact active cap is
--
--   $$c(w)=\min\bigl(\{I,\kappa(w)\}\cup\{a(f): f\in V(F),\ r_f(w)<Q_f\}\bigr).$$
--
--   An arc also requires a solution of this constructed kernel. The old opposite own-active edge remains in the fixed family through the next batch, so equation (10) tests the concrete receiver before the guard expires. Inherited tokens are mandatory and all are consumed at that step. Initial cuts are $-1$ with empty records; acceptance requires both maximal cuts and no donors, records or deletions. This is the explicit graph, not a graph defined by global matching feasibility.
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), pp. 13–18 (PDF pp. 14–19), §§B.2–B.7, equations (9)–(10)

import Mathlib
import Definitions.Def_TwoMasterRoommates_Capped_Residual
import Definitions.Def_TwoMasterRoommates_Capped_NormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped

abbrev ActualEdge (n : ℕ) := Fin n × Fin n

structure BatchState (n : ℕ) where
  orientA : Bool
  i : ℤ
  j : ℤ
  q : ℕ
  ea : Option (ActualEdge n)
  eb : Option (ActualEdge n)
  z : Option (ActualEdge n)
  h : Finset (Fin n)

noncomputable def optEdges {n : ℕ} (e : Option (ActualEdge n)) : Finset (ActualEdge n) :=
  e.toList.toFinset

noncomputable def inputEdges {n : ℕ} (s : BatchState n) : Finset (ActualEdge n) :=
  optEdges s.ea ∪ optEdges s.eb ∪ optEdges s.z

noncomputable def maxRank {n : ℕ} (f : Fin n → ℤ) : ℤ :=
  (attained f).toList.foldl max (-1)

noncomputable def localInstance {n : ℕ} (I : Instance ℤ n) (s : BatchState n) : Instance ℤ n :=
  if s.orientA then I else I.swap

noncomputable def boundary {n : ℕ} (I : Instance ℤ n) (i j : ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => I.b v = j ∧ i < I.a v

noncomputable def rectangle {n : ℕ} (I : Instance ℤ n) (i j : ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => i < I.a v ∧ j < I.b v

noncomputable def freeRegion {n : ℕ} (I : Instance ℤ n) (s : BatchState n) : Finset (Fin n) :=
  (boundary I s.i s.j ∪ rectangle I s.i s.j) \ (s.h ∪ endpoints (inputEdges s))

noncomputable def terminalA {n : ℕ} (I : Instance ℤ n) (t j : ℤ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => I.isA v = true ∧ I.a v = t ∧ j < I.b v

noncomputable def batchW {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (t : ℤ) (F : Finset (ActualEdge n)) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun x => I.isA x = true ∧
    ((I.b x = s.j ∧ s.i < I.a x) ∨ (s.i < I.a x ∧ I.a x < t ∧ s.j < I.b x))) \ endpoints F

noncomputable def batchU {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (t : ℤ) (F : Finset (ActualEdge n)) : Finset (Fin n) := by
  classical
  exact (batchW I s t F).filter fun x => I.b x = s.j

noncomputable def batchJ {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (F : Finset (ActualEdge n)) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun y => I.isA y = false ∧ I.b y = s.j ∧ s.i < I.a y) \ (s.h ∪ endpoints F)

noncomputable def batchD {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (t : ℤ) (F : Finset (ActualEdge n)) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun y => I.isA y = false ∧ s.i < I.a y ∧ I.a y < t ∧ s.j < I.b y) \ endpoints F

noncomputable def actualMate {n : ℕ} (F : Finset (ActualEdge n)) (v : Fin n) : Fin n :=
  match F.toList.find? (fun e => decide (e.1 = v ∨ e.2 = v)) with
  | none => v
  | some e => if e.1 = v then e.2 else e.1

noncomputable def actualQ {n : ℕ} (I : Instance ℤ n) (F : Finset (ActualEdge n)) (v : Fin n) : ℤ :=
  I.r v (actualMate F v)

noncomputable def batchCap {n : ℕ} (I : Instance ℤ n) (t : ℤ)
    (F : Finset (ActualEdge n)) (w : Fin n) : WithTop ℤ := by
  classical
  exact min (min (t : WithTop ℤ) (I.κ w)) ((endpoints F).inf fun f =>
    if I.r f w < actualQ I F f then (I.a f : WithTop ℤ) else ⊤)

noncomputable def batchActual {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (t : ℤ) (F : Finset (ActualEdge n)) : Finset (Fin n) :=
  batchW I s t F ∪ batchJ I s F ∪ batchD I s t F

/-- Actual local identities and separately labelled inherited and synthetic tokens. -/
abbrev BatchPopulation {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (t : ℤ) (F : Finset (ActualEdge n)) (qp : ℕ) :=
  {v // v ∈ batchActual I s t F} ⊕ (Fin s.q ⊕ Fin qp)

noncomputable def kernelOf {n : ℕ} (I : Instance ℤ n) (s : BatchState n)
    (t : ℤ) (F : Finset (ActualEdge n)) (qp : ℕ) : Kernel (BatchPopulation I s t F qp) ℤ := by
  classical
  exact {
    kind := fun v => match v with
      | .inl x => if x.val ∈ batchW I s t F then .active else if x.val ∈ batchJ I s F then .optional else .token
      | .inr _ => .token
    marked := fun v => match v with
      | .inl x => decide (x.val ∈ batchU I s t F)
      | .inr _ => false
    r := fun v => match v with
      | .inl x => I.a x.val
      | .inr (.inl _) => s.i
      | .inr (.inr _) => t
    c := fun v => match v with
      | .inl x => batchCap I t F x.val
      | .inr _ => ⊤ }

def EdgeShape {n : ℕ} (e : ActualEdge n) (p : Fin n → Fin n → Prop) : Prop :=
  p e.1 e.2 ∨ p e.2 e.1

noncomputable def DisjointEdges {n : ℕ} (F : Finset (ActualEdge n)) : Prop :=
  (∀ e ∈ F, e.1 < e.2) ∧ (F : Set (ActualEdge n)).Pairwise
    (fun e f => Disjoint ({e.1, e.2} : Set (Fin n)) {f.1, f.2})

noncomputable def inactive {n : ℕ} (I : Instance ℤ n) (F : Finset (ActualEdge n))
    (t j : ℤ) (v : Fin n) : Prop := actualQ I F v ≤ if I.isA v then t else j

noncomputable def StateBounds {n : ℕ} (I : Instance ℤ n) (s : BatchState n) : Prop :=
  -1 ≤ s.i ∧ s.i ≤ maxRank I.a ∧ -1 ≤ s.j ∧ s.j ≤ maxRank I.b ∧ s.q ≤ n ∧ s.h.card ≤ 2 ∧
  ∀ v ∈ s.h, I.isA v = false ∧ v ∈ boundary I s.i s.j

/-- All literal shape, availability, cap, ownership, and pair tests of §§B.3–B.4.
The successor uses exchanged names, hence t.i = s.j and t.j is the new a cut. -/
noncomputable def ABatch {n : ℕ} (I : Instance ℤ n) (s t : BatchState n) : Prop :=
  StateBounds I s ∧ s.i < t.j ∧ t.j ≤ maxRank I.a ∧ t.i = s.j ∧
  t.q ≤ n ∧ t.ea = s.eb ∧
  ∃ (hl ht : Option (ActualEdge n)),
    let F := inputEdges s ∪ optEdges t.eb ∪ optEdges t.z ∪ optEdges hl ∪ optEdges ht
    let out := optEdges t.eb ∪ optEdges s.eb ∪ optEdges t.z
    let V := endpoints F
    let LA := terminalA I t.j s.j
    DisjointEdges F ∧
    (∀ e ∈ F, e ∈ inputEdges s ∨ endpoints {e} ⊆ freeRegion I s) ∧
    (∀ e ∈ optEdges hl ∪ optEdges ht, e ∉ inputEdges s) ∧
    (∀ e ∈ optEdges t.eb, EdgeShape e fun u v => I.isA u = true ∧ I.a u ≤ t.j ∧ t.j < I.a v) ∧
    (∀ e ∈ optEdges t.z, EdgeShape e fun u v => I.isA u = true ∧ I.isA v = false ∧
      I.a u < t.j ∧ I.a v = t.j ∧ s.j < I.b v) ∧
    (∀ e ∈ optEdges hl, EdgeShape e fun u v => u ∈ freeRegion I s ∧ I.isA u = true ∧ I.a u < t.j ∧ v ∈ LA) ∧
    (∀ e ∈ optEdges ht, EdgeShape e fun u v => u ∈ freeRegion I s ∧ I.isA u = true ∧
      I.a u = t.j ∧ I.b u = s.j ∧ v ∈ LA) ∧
    (∀ v ∈ V, (actualQ I F v : WithTop ℤ) ≤ I.κ v) ∧
    (∀ v ∈ V, v ∈ freeRegion I s → I.isA v = false → I.b v = s.j → actualQ I F v = s.j) ∧
    (∀ v ∈ V, I.isA v = true → I.a v ≤ t.j → t.j < actualQ I F v → v ∈ endpoints (optEdges t.eb)) ∧
    (∀ v ∈ V, I.isA v = false → I.b v ≤ s.j → s.j < actualQ I F v → v ∈ endpoints (optEdges s.eb)) ∧
    (∀ v ∈ V, I.isA v = true → t.j < I.a v → I.b v ≤ s.j → actualQ I F v ≤ t.j) ∧
    (∀ v ∈ V, I.isA v = false → s.j < I.b v → I.a v ≤ t.j → s.j < actualQ I F v →
      I.a v = t.j ∧ v ∈ endpoints (optEdges t.z)) ∧
    (∀ v ∈ V, t.j < I.a v → s.j < I.b v → v ∈ endpoints (optEdges t.eb ∪ optEdges s.eb)) ∧
    (∀ v ∈ V, I.isA v = false → I.a v = t.j → s.j < I.b v → v ∈ endpoints out) ∧
    t.h = (LA ∩ V) \ endpoints out ∧ t.h.card ≤ 2 ∧
    (∀ v ∈ V \ endpoints out, inactive I F t.j s.j v) ∧
    (∀ y ∈ batchJ I s F ∪ batchD I s t.j F, (s.j : WithTop ℤ) ≤ I.κ y) ∧
    (∀ y ∈ LA \ V, (t.j : WithTop ℤ) ≤ I.κ y) ∧
    t.q ≤ ((Finset.univ.filter fun y => I.isA y = false ∧ I.a y = t.j ∧ s.j < I.b y) \ V).card ∧
    (∀ u ∈ V, ∀ v ∈ V, u ≠ v → ¬ (I.r u v < actualQ I F u ∧ I.r v u < actualQ I F v)) ∧
    (∀ y ∈ batchJ I s F ∪ batchD I s t.j F, ∀ f ∈ V,
      ¬ (I.r y f < s.j ∧ I.r f y < actualQ I F f)) ∧
    (∀ y ∈ LA \ V, ∀ f ∈ V, ¬ (I.r y f < t.j ∧ I.r f y < actualQ I F f)) ∧
    (0 < t.q → ∀ f ∈ V, I.isA f = true → ¬ (t.j < actualQ I F f ∧ I.b f < s.j)) ∧
    ∃ M, KSolution (kernelOf I s t.j F t.q) M

/-- Names are exchanged once per handoff; no zero-length batches. -/
noncomputable def BatchArc {n : ℕ} (I : Instance ℤ n) (s t : BatchState n) : Prop :=
  t.orientA = !s.orientA ∧ ABatch (localInstance I s) s t

def init {n : ℕ} (_I : Instance ℤ n) : BatchState n :=
  ⟨true, -1, -1, 0, none, none, none, ∅⟩

noncomputable def Accepting {n : ℕ} (I : Instance ℤ n) (s : BatchState n) : Prop :=
  let J := localInstance I s
  s.i = maxRank J.a ∧ s.j = maxRank J.b ∧ s.q = 0 ∧
  s.ea = none ∧ s.eb = none ∧ s.z = none ∧ s.h = ∅

end TwoMasterRoommates.Capped


