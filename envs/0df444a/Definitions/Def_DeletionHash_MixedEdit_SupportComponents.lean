-- Prove2me | Definitions.Def_DeletionHash_MixedEdit_SupportComponents
-- name    : DeletionHash_MixedEdit_SupportComponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:04.538144+00:00
-- url     : https://prove2.me/theorems/68294d30-80b7-45bb-8a83-8876d6fe084b
-- title:
--   Support component counts and rule blocks
-- statement:
--   For a finite rule set $F$, retain the edges in $S(F)$ and exactly their incident de Bruijn vertices; ignore directions. Let $c(F)$ be the number of connected components of this finite graph. Edges contributed by different rules never cancel, and other isolated vertices are excluded. Two rules are adjacent when their supports share a vertex, equivalently when two of their bubbles share a vertex. A connected rule set is nonempty and connected under these adjacencies; its connected components are the rule blocks. Support components group gram edges, whereas rule blocks group whole rules. Finite alphabets ensure the support graph and its component type are finite.
-- source:
--   Eyal En Gad, STOC 2027 submission #408 (October 2026), Definition 4.1, printed p. 11 (PDF p. 13); Definition 4.4, printed p. 13 (PDF p. 15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/408.pdf

import Definitions.Def_DeletionHash_MixedEdit_Rules

namespace DeletionHash.MixedEdit

universe u

/-- Only incident vertices are kept. Loops do not affect undirected connectivity. -/
def supportGraph {α : Type u} {L : ℕ} (F : Finset (Spectrum α L)) :
    SimpleGraph {v : Gram α (L-1) // v ∈ incidentVertices F} where
  Adj v w := v ≠ w ∧ ∃ g ∈ supportUnion F,
    (v.val = gramPrefix g ∧ w.val = gramSuffix g) ∨
    (w.val = gramPrefix g ∧ v.val = gramSuffix g)
  symm := by
    constructor
    rintro v w ⟨hne,g,hg,h⟩
    exact ⟨hne.symm,g,hg,h.symm⟩
  loopless := by constructor; intro v h; exact h.1 rfl

noncomputable def componentCount {α : Type u} {L : ℕ} (F : Finset (Spectrum α L)) : ℕ :=
  Nat.card (supportGraph F).ConnectedComponent

def RuleAdjacent {α : Type u} {L : ℕ} (w z : Spectrum α L) : Prop :=
  ∃ v, v ∈ incidentVertices {w} ∧ v ∈ incidentVertices {z}

def ruleGraph {α : Type u} {L : ℕ} (F : Finset (Spectrum α L)) :
    SimpleGraph {w : Spectrum α L // w ∈ F} where
  Adj w z := w ≠ z ∧ RuleAdjacent w.val z.val
  symm := by
    constructor
    rintro w z ⟨hne,v,hw,hz⟩
    exact ⟨hne.symm,v,hz,hw⟩
  loopless := by constructor; intro w h; exact h.1 rfl

def ConnectedRules {α : Type u} {L : ℕ} (F : Finset (Spectrum α L)) : Prop :=
  F.Nonempty ∧ ∀ w z : {w : Spectrum α L // w ∈ F}, (ruleGraph F).Reachable w z

end DeletionHash.MixedEdit


