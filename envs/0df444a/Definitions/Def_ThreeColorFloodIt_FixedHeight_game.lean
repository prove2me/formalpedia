-- Prove2me | Definitions.Def_ThreeColorFloodIt_FixedHeight_game
-- name    : ThreeColorFloodIt_FixedHeight_game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:49:48.695866+00:00
-- url     : https://prove2.me/theorems/901deeb6-8ff8-4d6d-bd17-4c7cde339bde
-- title:
--   Free flooding, connected strokes and actual optimization values
-- statement:
--   A board assigns one of three available colors to each cell of a complete rectangular grid. A legal move changes a whole maximal monochromatic component to a different color. Legal sequences are checked in their evolving states. A connected painting stroke overwrites its region, starting from a blank graph; last-painted sets and saturation use the target coloring.
--
--   For a graph $G$ and coloring $f$, the two values are
--   $$F(G,f)=\inf\{|L|:L\text{ is a legal flooding solution}\},\qquad p(G,f)=\inf\{|P|:P\text{ paints }f\}.$$
--   The general game layer allows any finite palette for Proposition 1. Values lie in the extended naturals; an empty feasible family has value infinity. On the connected finite inputs in the theorems the minima are attained. The normalization predicate includes the first later stroke on every residual connected component.
--
--   These definitions separate the free game from painting and fixed-pivot flooding. Zero-based coordinates encode the source's one-based coordinates.
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 4 (PDF 5), §2.2 and §4.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf Additional definition location: printed p. 7 (PDF 8), §4.1 (saturation, last-painted sets and normalization).

import Mathlib

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

/-- Connectivity uses all graph edges inside the specified vertex set, including
length-zero paths. A connected stroke is also required to be nonempty. -/
def Within {V : Type} (G : SimpleGraph V) (S : Set V) (u v : V) : Prop :=
  u ∈ S ∧ v ∈ S ∧ Relation.ReflTransGen
    (fun x y => x ∈ S ∧ y ∈ S ∧ G.Adj x y) u v

def ConnectedSet {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ ∀ u ∈ S, ∀ v ∈ S, Within G S u v

def Boundary {V : Type} (G : SimpleGraph V) (S : Set V) : Set V :=
  {u | u ∉ S ∧ ∃ v ∈ S, G.Adj u v}

abbrev Cell (k n : ℕ) := Fin k × Fin n

/-- Zero-based coordinates; every horizontal and vertical edge is present. -/
def Grid (k n : ℕ) : SimpleGraph (Cell k n) where
  Adj u v := (u.1 = v.1 ∧ (u.2.val + 1 = v.2.val ∨ v.2.val + 1 = u.2.val)) ∨
    (u.2 = v.2 ∧ (u.1.val + 1 = v.1.val ∨ v.1.val + 1 = u.1.val))
  symm := ⟨by intro u v h; aesop⟩
  loopless := ⟨by intro u h; rcases h with h | h <;> omega⟩

abbrev Board (k n : ℕ) := Cell k n → Fin 3

def Column {k n : ℕ} (j : Fin n) : Set (Cell k n) := {v | v.2 = j}
def Prefix {k n : ℕ} (j : Fin n) : Set (Cell k n) := {v | v.2 ≤ j}

def Mono {V C : Type} (g : V → C) : Prop := ∃ a, ∀ v, g v = a

def Component {V C : Type} (G : SimpleGraph V) (g : V → C) (v : V) : Set V :=
  {u | Within G {w | g w = g v} v u}

abbrev Move (V C : Type) := V × C

noncomputable def recolor {V C : Type} (G : SimpleGraph V) (g : V → C)
    (m : Move V C) : V → C := by
  classical
  exact fun u => if u ∈ Component G g m.1 then m.2 else g u

/-- Legality is checked against each evolving coloring, not the target input. -/
inductive Floods {V C : Type} (G : SimpleGraph V) :
    (V → C) → List (Move V C) → (V → C) → Prop
  | nil (g) : Floods G g [] g
  | cons (g h) (m) (ms) (different : m.2 ≠ g m.1)
      (rest : Floods G (recolor G g m) ms h) : Floods G g (m :: ms) h

def Solves {V C : Type} (G : SimpleGraph V) (f : V → C)
    (ms : List (Move V C)) : Prop := ∃ g, Floods G f ms g ∧ Mono g

/-- An infeasible problem has value infinity, never a default natural zero. -/
noncomputable def floodOpt {V C : Type} (G : SimpleGraph V) (f : V → C) : WithTop ℕ :=
  sInf {d | ∃ ms, Solves G f ms ∧ d = (ms.length : WithTop ℕ)}

abbrev Stroke (V C : Type) := Set V × C

noncomputable def paintStroke {V C : Type} (g : V → Option C)
    (s : Stroke V C) : V → Option C := by
  classical
  exact fun v => if v ∈ s.1 then some s.2 else g v

noncomputable def paint {V C : Type} (ps : List (Stroke V C)) : V → Option C :=
  ps.foldl paintStroke (fun _ => none)

def Paints {V C : Type} (G : SimpleGraph V) (f : V → C)
    (ps : List (Stroke V C)) : Prop :=
  (∀ s ∈ ps, ConnectedSet G s.1) ∧ paint ps = fun v => some (f v)

noncomputable def paintOpt {V C : Type} (G : SimpleGraph V) (f : V → C) : WithTop ℕ :=
  sInf {d | ∃ ps, Paints G f ps ∧ d = (ps.length : WithTop ℕ)}

def OptimalPainting {V C : Type} (G : SimpleGraph V) (f : V → C)
    (ps : List (Stroke V C)) : Prop := Paints G f ps ∧
  ∀ qs, Paints G f qs → ps.length ≤ qs.length

def LastPainted {V C : Type} (ps : List (Stroke V C)) (i : Fin ps.length) : Set V :=
  (ps.get i).1 \ {v | ∃ j : Fin ps.length, i < j ∧ v ∈ (ps.get j).1}

def Saturated {V C : Type} (G : SimpleGraph V) (f : V → C) (s : Stroke V C) : Prop :=
  ∀ v ∈ Boundary G s.1, f v ≠ s.2

def Normalized {V C : Type} (G : SimpleGraph V) (f : V → C)
    (ps : List (Stroke V C)) : Prop :=
  (∃ h : 0 < ps.length, (ps.get ⟨0, h⟩).1 = Set.univ) ∧
  (∀ i j : Fin ps.length, i < j → ((ps.get i).1 ∩ (ps.get j).1).Nonempty →
    (ps.get j).1 ⊆ (ps.get i).1) ∧
  (∀ s ∈ ps, Saturated G f s) ∧
  (∀ (i : Fin ps.length) (v : V), v ∈ (ps.get i).1 \ LastPainted ps i →
    ∃ j : Fin ps.length, i < j ∧
      ((ps.get j).1 ∩ {u | Within G ((ps.get i).1 \ LastPainted ps i) v u}).Nonempty ∧
      (∀ l : Fin ps.length, i < l → l < j →
        ¬ ((ps.get l).1 ∩ {u | Within G ((ps.get i).1 \ LastPainted ps i) v u}).Nonempty) ∧
      (ps.get j).1 = {u | Within G ((ps.get i).1 \ LastPainted ps i) v u})

end ThreeColorFloodIt.FixedHeight


