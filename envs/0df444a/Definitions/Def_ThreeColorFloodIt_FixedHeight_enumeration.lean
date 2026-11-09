-- Prove2me | Definitions.Def_ThreeColorFloodIt_FixedHeight_enumeration
-- name    : ThreeColorFloodIt_FixedHeight_enumeration
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:51:33.711057+00:00
-- url     : https://prove2.me/theorems/a8771b29-d315-4821-8068-b3b537b69077
-- title:
--   Direct skeleton recursion and alternating-chain generation
-- statement:
--   A marked rose tree stores a color, directly owned named vertices, and children. The generator chooses a node color outside the forbidden boundary colors, chooses its owned marks, groups whole connected components of the remaining named set, and recurses on strictly smaller child sets. Unmarked skeleton nodes must branch.
--
--   Each skeleton edge is expanded by alternating words generated from their first colors and lengths. Expansions are filtered by the actual parent-child color condition and the node budget:
--   $$|V(K)|\le M.$$
--   The empty chain word and single-color words are included. Parent-child paths are retained in full. A flattening relation compares the resulting child-index paths with finite rooted trees preserving named owners. The output encodes the concrete generator list, including harmless repeated representations; choices are ordered explicitly on finite named sets. Polynomial generation is a theorem obligation, not a field of the generator.
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 10 (PDF 11), §4.2, Eq. (2), Lemma 14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf Additional locations: printed p. 9 (PDF 10), Definition 11 and skeleton terminology; printed p. 11 (PDF 12), enumeration proof and canonical arrays.

import Definitions.Def_ThreeColorFloodIt_FixedHeight_trees
import Definitions.Def_ThreeColorFloodIt_FixedHeight_machine

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

inductive MarkTree (s : ℕ) where
  | node (color : Fin 3) (marks : Finset (Fin s)) (children : List (MarkTree s))

def markColor {s : ℕ} : MarkTree s → Fin 3
  | .node a _ _ => a

def markDomain {s : ℕ} : MarkTree s → Finset (Fin s)
  | .node _ Z cs => Z ∪ (cs.map markDomain).foldl (· ∪ ·) ∅

def markSize {s : ℕ} : MarkTree s → ℕ
  | .node _ _ cs => 1 + (cs.map markSize).sum

def markProper {s : ℕ} : MarkTree s → Prop
  | .node a _ cs => ∀ c ∈ cs, markColor c ≠ a ∧ markProper c

/-- Nodes have child-index paths; this retains every internal path node. -/
def markNodes {s : ℕ} : MarkTree s → List (List ℕ × Fin 3 × Finset (Fin s))
  | .node a Z cs => ([], a, Z) ::
    (((cs.map markNodes).zipIdx).flatMap fun (nodes, i) =>
      nodes.map fun (p, b, W) => (i :: p, b, W))

def Flattens {s : ℕ} (K : TreeData (Fin s) (Fin 3)) (t : MarkTree s) : Prop :=
  ∃ e : Fin K.tree.size ≃ Fin (markNodes t).length,
    ((markNodes t).get (e K.tree.root)).1 = [] ∧
    (∀ x, ((markNodes t).get (e x)).2.1 = K.color x) ∧
    (∀ v x, v ∈ ((markNodes t).get (e x)).2.2 ↔ K.owner v = x) ∧
    (∀ x y, Child K.tree x y ↔
      ∃ i, ((markNodes t).get (e y)).1 = ((markNodes t).get (e x)).1 ++ [i])

/-- Lists of a prescribed length over an explicitly supplied finite alphabet. -/
def words {A : Type} (alphabet : List A) : ℕ → List (List A)
  | 0 => [[]]
  | n + 1 => alphabet.flatMap fun a => (words alphabet n).map (a :: ·)

def choices {A : Type} : List (List A) → List (List A)
  | [] => [[]]
  | xs :: xss => xs.flatMap fun x => (choices xss).map (x :: ·)

def subsets {s : ℕ} (L : Finset (Fin s)) : List (Finset (Fin s)) :=
  ((List.finRange s).filter fun v => v ∈ L).sublists.map List.toFinset

noncomputable def forbFin {s : ℕ} (G : SimpleGraph (Fin s))
    (f : Fin s → Fin 3) (L : Finset (Fin s)) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter fun a => a ∈ Forbidden G f (L : Set (Fin s))

/-- Ordered nonempty groups partition L, with no graph edge split across groups.
This is precisely grouping the connected components of G[L]. -/
def Groups {s : ℕ} (G : SimpleGraph (Fin s)) (L : Finset (Fin s))
    (gs : List (Finset (Fin s))) : Prop :=
  (∀ A ∈ gs, A.Nonempty) ∧ gs.Pairwise Disjoint ∧
    gs.foldl (· ∪ ·) ∅ = L ∧
    ∀ A ∈ gs, ∀ B ∈ gs, A ≠ B → ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v

noncomputable def allGroups {s : ℕ} (G : SimpleGraph (Fin s))
    (L : Finset (Fin s)) : List (List (Finset (Fin s))) := by
  classical
  exact ((List.range (s + 1)).flatMap fun m => words (subsets L) m).filter (Groups G L)

/-- The recursion chooses exactly the node color, owned marks, and a grouping
of the remaining components on pp.10--11. Fuel s suffices because each child
has a strictly smaller nonempty descendant-mark set. -/
noncomputable def skeletonGenerate {s : ℕ} (G : SimpleGraph (Fin s))
    (f : Fin s → Fin 3) : ℕ → Finset (Fin s) → List (MarkTree s)
  | 0, _ => []
  | fuel + 1, L => by
      classical
      exact ((List.finRange 3).filter fun a => a ∉ forbFin G f L).flatMap fun a =>
        (subsets (L.filter fun v => f v = a)).flatMap fun Z =>
          (allGroups G (L \ Z)).flatMap fun gs =>
            if (Z.Nonempty ∨ 2 ≤ gs.length) ∧ (∀ B ∈ gs, B.card < L.card) then
              (choices (gs.map fun B => skeletonGenerate G f fuel B)).map (MarkTree.node a Z)
            else []

/-- Alternating words, including the empty word and one-color words, are
generated from lengths and their first two colors, never from all 3^M words. -/
noncomputable def chainWords {s : ℕ} (G : SimpleGraph (Fin s)) (f : Fin s → Fin 3)
    (L : Finset (Fin s)) (M : ℕ) : List (List (Fin 3)) := by
  classical
  exact ([] :: ((List.range M).flatMap fun l =>
    (List.finRange 3).flatMap fun a => (List.finRange 3).map fun b =>
      (List.range (l + 1)).map fun i => if i % 2 = 0 then a else b)).filter fun w =>
        w.IsChain (· ≠ ·) ∧ ∀ a ∈ w, a ∉ forbFin G f L

def prependChain {s : ℕ} (cs : List (Fin 3)) (t : MarkTree s) : MarkTree s :=
  cs.foldr (fun a child => .node a ∅ [child]) t

noncomputable def expandChains {s : ℕ} (G : SimpleGraph (Fin s)) (f : Fin s → Fin 3)
    (M : ℕ) : MarkTree s → List (MarkTree s)
  | .node a Z cs =>
      (choices (cs.map fun c =>
        (expandChains G f M c).flatMap fun t =>
          (chainWords G f (markDomain c) M).map fun w => prependChain w t)).map (MarkTree.node a Z)

noncomputable def generateTemplates {s : ℕ} (G : SimpleGraph (Fin s))
    (f : Fin s → Fin 3) (M : ℕ) : List (MarkTree s) := by
  classical
  exact ((skeletonGenerate G f s Finset.univ).flatMap (expandChains G f M)).filter fun t =>
    markSize t ≤ M ∧ markProper t

def markCode {s : ℕ} (t : MarkTree s) : List ℕ :=
  (markNodes t).flatMap fun (p, a, Z) =>
    p.length :: p ++ [a.val, Z.card] ++ ((List.finRange s).filter fun v => v ∈ Z).map Fin.val

noncomputable def generatedCode {s : ℕ} (G : SimpleGraph (Fin s))
    (f : Fin s → Fin 3) (M : ℕ) : List (Option Bool) :=
  encodeNaturals ((generateTemplates G f M).length ::
    (generateTemplates G f M).flatMap fun t => (markCode t).length :: markCode t)

/-- Input for the direct generator: named window size, node budget, dense
adjacency table and target colors. The graph is not supplied by an oracle. -/
noncomputable def windowInput {s : ℕ} (G : SimpleGraph (Fin s))
    (f : Fin s → Fin 3) (M : ℕ) : List (Option Bool) := by
  classical
  exact encodeNaturals (s :: M ::
    (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten ++
      List.ofFn fun v => (f v).val)

end ThreeColorFloodIt.FixedHeight


