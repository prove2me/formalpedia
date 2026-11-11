-- Prove2me | Definitions.Def_PlanarDFVS_SingleExp_Graphs
-- name    : PlanarDFVS_SingleExp_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:07:28.003263+00:00
-- url     : https://prove2.me/theorems/2dee9503-8603-4eea-9eeb-5a1fb1e972ad
-- title:
--   §2–§3.1 — directed cycles, geometric embeddings and facial corners
-- statement:
--   A finite directed multigraph has vertices $\{0,\ldots,n-1\}$, distinct arc identities $\{0,\ldots,m-1\}$, and tail and head maps. The carrier is the published general directed-multigraph definition; loops, parallel arcs and antiparallel arcs are allowed. A directed closed walk has positive length. A vertex set $X$ is a directed feedback vertex set precisely when no such walk remains in $V\setminus X$.
--
--   A drawing places vertices at distinct complex coordinates and represents each arc by a continuous curve with disjoint interiors avoiding all vertices. Endpoint germs are straight nonzero rays. Their counterclockwise order gives the rotation permutation on arc incidences. A face is an orbit of the facial successor on corners, including the outer orbit; repeated appearances of a vertex remain distinct corners. A degree-one incidence succeeds itself. The alternating count at $v$ is $2b(v)$ and the consistent count at $f$ is $2a(f)$; a circular face has $a(f)=0$. The shared weight is
--
--   $$w(v)=b(v)-1\in\mathbb Z,\qquad L=\sum_v w(v).$$
--
--   The graph deletion and feedback-arc predicates use actual closed walks. Adjacency support forgets only duplicate copies and retains loops.
--
--   **Formalization Note** Finite labels change no instance. Local straightness expresses the standard rotation of a topological embedding after local straightening, without changing its corners or faces. Planarity requires an actual crossing-free drawing, not an Euler identity. Face sums are used only with nonempty-arc hypotheses; disconnected cyclic components have separate inherited face systems.
--   The cyclic-core components are computed from mutual directed reachability and actual cyclic arcs. Inherited drawings restrict vertex positions, arc curves and endpoint rays along injective incidence maps. Marked-face transport succeeds only when the entire old dart set survives and is a current face; a disappeared face returns no identifier. No transport-success theorem or algorithm invariant is built into these definitions.
-- source:
--   Daniel Lokshtanov, Saket Saurabh, Jie Xue, STOC 2027 submission #1569 (October 2026), pp. 4–7 (PDF pp. 4–7), §2 and §3.1–§3.3

import Mathlib
import Definitions.Def_CombOpt_ShortestPath_Digraph

namespace PlanarDFVS.SingleExp

abbrev Graph (n m : ℕ) := CombOpt.ShortestPath.Digraph (Fin n) (Fin m)
abbrev Dart (m : ℕ) := Fin m × Bool

def origin {n m : ℕ} (G : Graph n m) (d : Dart m) : Fin n :=
  if d.2 then G.head d.1 else G.tail d.1

def reverseDart {m : ℕ} (d : Dart m) : Dart m := (d.1, !d.2)

def Walk {n m : ℕ} (G : Graph n m) : Fin n → Fin n → List (Fin m) → Prop
  | u, v, [] => u = v
  | u, v, e :: es => G.tail e = u ∧ Walk G (G.head e) v es

def InducedAcyclic {n m : ℕ} (G : Graph n m) (A : Finset (Fin n)) : Prop :=
  ∀ v es, Walk G v v es → es ≠ [] → ¬ ∀ e ∈ es, G.tail e ∈ A

def IsDFVS {n m : ℕ} (G : Graph n m) (X : Finset (Fin n)) : Prop :=
  InducedAcyclic G (Finset.univ \ X)

def Feasible {n m : ℕ} (G : Graph n m) (k : ℕ) : Prop :=
  ∃ X : Finset (Fin n), IsDFVS G X ∧ X.card ≤ k

noncomputable def loopVertices {n m : ℕ} (G : Graph n m) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => ∃ e, G.tail e = v ∧ G.head e = v

def Loopless {n m : ℕ} (G : Graph n m) : Prop := ∀ e, G.tail e ≠ G.head e

def WeaklyConnected {n m : ℕ} (G : Graph n m) : Prop :=
  ∀ u v, Relation.ReflTransGen
    (fun x y => ∃ e, (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x)) u v

def StronglyConnected {n m : ℕ} (G : Graph n m) : Prop :=
  ∀ u v, ∃ es, Walk G u v es

/-- An actual crossing-free drawing, locally straight at every incidence. Rotation is
    the counterclockwise successor of the initial rays, not an Euler certificate. -/
structure Drawing {n m : ℕ} (G : Graph n m) where
  pos : Fin n → ℂ
  pos_injective : Function.Injective pos
  curve : Fin m → ℝ → ℂ
  continuous : ∀ e, ContinuousOn (curve e) (Set.Icc 0 1)
  start : ∀ e, curve e 0 = pos (G.tail e)
  finish : ∀ e, curve e 1 = pos (G.head e)
  avoid_vertices : ∀ e t, t ∈ Set.Ioo (0 : ℝ) 1 → ∀ v, curve e t ≠ pos v
  disjoint : ∀ e e' t t', t ∈ Set.Ioo (0 : ℝ) 1 → t' ∈ Set.Ioo (0 : ℝ) 1 →
    curve e t = curve e' t' → e = e' ∧ t = t'
  ray : Dart m → ℂ
  ray_ne_zero : ∀ d, ray d ≠ 0
  local_ray : ∀ d, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ t, 0 ≤ t → t ≤ ε →
    curve d.1 (if d.2 then 1 - t else t) = pos (origin G d) + (t : ℂ) * ray d
  distinct_angles : ∀ d d', origin G d = origin G d' → (ray d).arg = (ray d').arg → d = d'
  rot : Equiv.Perm (Dart m)
  rot_origin : ∀ d, origin G (rot d) = origin G d
  rot_angle : ∀ d,
    if ∃ e, origin G e = origin G d ∧ (ray d).arg < (ray e).arg then
      (ray d).arg < (ray (rot d)).arg ∧
        ∀ e, origin G e = origin G d → (ray d).arg < (ray e).arg →
          (ray (rot d)).arg ≤ (ray e).arg
    else ∀ e, origin G e = origin G d → (ray (rot d)).arg ≤ (ray e).arg

def Planar {n m : ℕ} (G : Graph n m) : Prop := Nonempty (Drawing G)

def faceNext {n m : ℕ} {G : Graph n m} (E : Drawing G) (d : Dart m) : Dart m :=
  reverseDart (E.rot d)

noncomputable def faceOrbit {n m : ℕ} {G : Graph n m} (E : Drawing G) (d : Dart m) :
    Finset (Dart m) := by
  classical
  exact Finset.univ.filter fun e => ∃ i ≤ 2 * m, (faceNext E)^[i] d = e

noncomputable def faces {n m : ℕ} {G : Graph n m} (E : Drawing G) : Finset (Finset (Dart m)) := by
  classical
  exact Finset.univ.image (faceOrbit E)

def alternating {n m : ℕ} {G : Graph n m} (E : Drawing G) (d : Dart m) : Prop :=
  d.2 ≠ (E.rot d).2

noncomputable def b {n m : ℕ} {G : Graph n m} (E : Drawing G) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter fun d : Dart m => origin G d = v ∧ alternating E d).card / 2

noncomputable def consistentCount {n m : ℕ} {G : Graph n m} (E : Drawing G)
    (f : Finset (Dart m)) : ℕ := by
  classical
  exact (f.filter fun d => ¬ alternating E d).card

noncomputable def a {n m : ℕ} {G : Graph n m} (E : Drawing G) (f : Finset (Dart m)) : ℕ :=
  consistentCount E f / 2

noncomputable def circularFaces {n m : ℕ} {G : Graph n m} (E : Drawing G) :
    Finset (Finset (Dart m)) := by
  classical
  exact (faces E).filter fun f => a E f = 0

noncomputable def weight {n m : ℕ} {G : Graph n m} (E : Drawing G) (v : Fin n) : ℤ :=
  (b E v : ℤ) - 1

noncomputable def totalWeight {n m : ℕ} {G : Graph n m} (E : Drawing G) : ℤ :=
  ∑ v, weight E v

noncomputable def positive {n m : ℕ} {G : Graph n m} (E : Drawing G) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun v => 0 < weight E v

noncomputable def incidentVertices {n m : ℕ} {G : Graph n m} (f : Finset (Dart m)) :
    Finset (Fin n) := f.image (origin G)

/-- The cyclic core retains precisely arcs whose head can reach their tail. -/
noncomputable def cyclicArcs {n m : ℕ} (G : Graph n m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun e => ∃ es, Walk G (G.head e) (G.tail e) es

def SameSCC {n m : ℕ} (G : Graph n m) (u v : Fin n) : Prop :=
  (∃ es, Walk G u v es) ∧ (∃ es, Walk G v u es)

/-- Maximal strongly connected vertex sets containing a directed cycle. Each
    component has its own inherited embedding and its own outer face. -/
noncomputable def cyclicComponents {n m : ℕ} (G : Graph n m) : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.powerset.filter fun C => C.Nonempty ∧
    (∀ u ∈ C, ∀ v ∈ C, SameSCC G u v) ∧
    (∀ u ∈ C, ∀ v, SameSCC G u v → v ∈ C) ∧
    ∃ e ∈ cyclicArcs G, G.tail e ∈ C ∧ G.head e ∈ C

/-- Structural restriction of an actual drawing. This asserts only incidence
    preservation and restriction of its geometric data, not any algorithm invariant. -/
structure InheritedDrawing {n m n' m' : ℕ} {G : Graph n m} {H : Graph n' m'}
    (E : Drawing G) (F : Drawing H) where
  vertex : Fin n' → Fin n
  arc : Fin m' → Fin m
  vertex_injective : Function.Injective vertex
  arc_injective : Function.Injective arc
  tails : ∀ e, G.tail (arc e) = vertex (H.tail e)
  heads : ∀ e, G.head (arc e) = vertex (H.head e)
  positions : ∀ v, F.pos v = E.pos (vertex v)
  curves : ∀ e, F.curve e = E.curve (arc e)
  rays : ∀ d, F.ray d = E.ray (arc d.1, d.2)

/-- Transport a still-intact face by its original corner incidences. A face that
    has disappeared does not retain a valid identifier. No existence is assumed. -/
noncomputable def transportFace {n m n' m' : ℕ} {G : Graph n m} {H : Graph n' m'}
    {E : Drawing G} {F : Drawing H} (I : InheritedDrawing E F)
    (f : Finset (Dart m)) : Option (Finset (Dart m')) := by
  classical
  let g := Finset.univ.filter fun d : Dart m' => (I.arc d.1, d.2) ∈ f
  exact if f ∈ faces E ∧ g ∈ faces F ∧ g.image (fun d => (I.arc d.1, d.2)) = f
    then some g else none

/-- Arc deletion has its own semantics; negative costs never become infinities. -/
def IsFAS {n m : ℕ} (G : Graph n m) (A : Finset (Fin m)) : Prop :=
  ∀ v es, Walk G v v es → es ≠ [] → ∃ e ∈ es, e ∈ A

/-- Adjacency support retains loops and forgets only duplicate arc identities. -/
noncomputable def support {n m : ℕ} (G : Graph n m) (u v : Fin n) : Bool := by
  classical
  exact decide (∃ e, G.tail e = u ∧ G.head e = v)

/-- The same cycle property directly on a support matrix. -/
def SupportAcyclic {n : ℕ} (S : Fin n → Fin n → Bool) (A : Finset (Fin n)) : Prop :=
  ∀ (r : ℕ) (hr : 0 < r) (v : Fin r → Fin n),
    (∀ i, v i ∈ A) → ¬ ∀ i, S (v i) (v ⟨(i.val + 1) % r, Nat.mod_lt _ hr⟩) = true

end PlanarDFVS.SingleExp


