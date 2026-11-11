-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_routing
-- name    : LiuHelsenDesigns_OneD_routing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:08:17.575458+00:00
-- url     : https://prove2.me/theorems/3ad9842f-f5d6-4bed-9523-456f8ba2482e
-- title:
--   General local gates and bounded-cell routing
-- statement:
--   A placed unitary gives an actual unitary matrix and an injective list of physical sites. Layers have disjoint wire supports. Cells are contiguous intervals of bounded size; every gate meets a bounded number of adjacent cells and every cell participates in a bounded number of gates.
--
--   $$\operatorname{eval}(C)=\operatorname{eval}(\text{input layer}).$$
--
--   Nearest-neighbor output gates have one or two adjacent sites. Arbitrary local unitary gates remain available in the gluing lemma, so that its domain is not restricted to Clifford+T laws. The headline theorem uses its separate elementary alphabet and charges every actual T or T†.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p.31, Observation 1 and Fig.3; p.5, Lemma 1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_designs

noncomputable section
open scoped Matrix

namespace LiuHelsenDesigns.OneD
attribute [local instance] Classical.propDecidable Classical.decEq

/-- General local gates for the routing observation; the headline circuit alphabet
remains the elementary Clifford+T alphabet defined separately. -/
structure PlacedUnitary (n : ℕ) where
  width : ℕ
  sites : Fin width ↪ Fin n
  op : Matrix.unitaryGroup (Basis width) ℂ

def placedMatrix {n : ℕ} (g : PlacedUnitary n) : Mat n := fun x y =>
  if ∀ i : Fin n, i ∉ Set.range g.sites → x i = y i then
    (g.op : Mat g.width) (x ∘ g.sites) (y ∘ g.sites) else 0

def placedLayerMatrix {n : ℕ} (gs : List (PlacedUnitary n)) : Mat n :=
  gs.foldl (fun U g => placedMatrix g * U) 1
def placedCircuitMatrix {n : ℕ} (cs : List (List (PlacedUnitary n))) : Mat n :=
  cs.foldl (fun U gs => placedLayerMatrix gs * U) 1

def DisjointLayer {n : ℕ} (gs : List (PlacedUnitary n)) : Prop :=
  gs.Pairwise fun g h => Disjoint (Set.range g.sites) (Set.range h.sites)
def nearestGate {n : ℕ} (g : PlacedUnitary n) : Prop :=
  (g.width = 1 ∨ g.width = 2) ∧
    ∀ i j : Fin g.width, (g.sites i).val ≤ (g.sites j).val+1

def NearestCircuit {n : ℕ} (cs : List (List (PlacedUnitary n))) : Prop :=
  ∀ layer ∈ cs, DisjointLayer layer ∧ ∀ g ∈ layer, nearestGate g

def boundedCellLayer {n : ℕ} (b r p : ℕ) (gs : List (PlacedUnitary n)) : Prop :=
  DisjointLayer gs ∧ (∀ g ∈ gs, 0 < g.width ∧
    ∃ a : ℕ, ∀ i : Fin g.width, a ≤ (g.sites i).val/b ∧ (g.sites i).val/b < a+r) ∧
  ∀ a : ℕ, (gs.filter fun g => ∃ i : Fin g.width, (g.sites i).val/b = a).length ≤ p

end LiuHelsenDesigns.OneD


