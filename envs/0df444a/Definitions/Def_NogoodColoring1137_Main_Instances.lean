-- Prove2me | Definitions.Def_NogoodColoring1137_Main_Instances
-- name    : NogoodColoring1137_Main_Instances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T17:00:43.058384+00:00
-- url     : https://prove2.me/theorems/ec733bc4-b4cf-40b9-bcc0-773f677eafcd
-- title:
--   Finite coloring instances and anchor graphs
-- statement:
--   Let $V=\mathrm{Fin}(n)$ and $C=\mathrm{Fin}(3)$. Lists $L(v)\subseteq C$ may be empty. Solutions use the published proper-list-coloring code:
--   $$\mathcal C(G,L)=\{c:V\to C:c(v)\in L(v),\ c(v)\ne c(w)\text{ on every edge}\}.$$
--   The diameter promise requires every distinct pair to be adjacent or have a common neighbor. Full lists give ordinary coloring. Propagated lists exclude singleton neighbor colors. The anchor graph adds the existing anchors' triangle and all forbidden-color edges, symmetrically, without adding vertices.
--
--   These are the shared instance conventions. **Formalization Note** Empty graphs are included. Symmetry and adjacency-decidability proofs are structural and impose no further graph condition.
-- source:
--   Philip Whittington, STOC 2027 submission #1137 (October 2026), §§2.1.1,6,7, pp.4–5,19,21

import Mathlib
import Definitions.Def_ConeL2G_properColorings

namespace NogoodColoring1137.Main

abbrev Color := Fin 3
abbrev Lists (n : ℕ) := Fin n → Finset Color

/-- §2.1.1: the path formulation avoids natural diameter's disconnected default. -/
def DiameterTwo {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ v w, v ≠ w → G.Adj v w ∨ ∃ u, G.Adj v u ∧ G.Adj u w

def FullLists (n : ℕ) : Lists n := fun _ => Finset.univ

/-- The solution code is the published proper-list-coloring definition at palette size 3. -/
abbrev Solutions {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) := ConeL2G.properColorings G L

/-- Fixed-point invariant of §6; all vertices remain present. -/
def Propagated {n : ℕ} (G : SimpleGraph (Fin n)) (L : Lists n) : Prop :=
  ∀ v w a, G.Adj v w → L v = {a} → a ∉ L w

/-- §7: the actual graph constructed from anchors, with symmetrized forbidden-color edges. -/
def AnchorGraph {n : ℕ} (G : SimpleGraph (Fin n)) (L : Lists n)
    (r : Color → Fin n) : SimpleGraph (Fin n) where
  Adj v w := v ≠ w ∧ (G.Adj v w ∨
    (∃ a b : Color, a ≠ b ∧ v = r a ∧ w = r b) ∨
    (∃ a : Color, w = r a ∧ a ∉ L v) ∨
    (∃ a : Color, v = r a ∧ a ∉ L w))
  symm := ⟨by
    intro v w h
    refine ⟨Ne.symm h.1, ?_⟩
    rcases h.2 with h | h | h | h
    · exact Or.inl (G.adj_symm h)
    · rcases h with ⟨a,b,hab,hv,hw⟩
      exact Or.inr (Or.inl ⟨b,a,Ne.symm hab,hw,hv⟩)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

instance anchorAdjDecidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (L : Lists n) (r : Color → Fin n) : DecidableRel (AnchorGraph G L r).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

end NogoodColoring1137.Main


