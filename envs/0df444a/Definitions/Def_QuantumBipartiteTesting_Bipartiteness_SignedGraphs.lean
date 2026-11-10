-- Prove2me | Definitions.Def_QuantumBipartiteTesting_Bipartiteness_SignedGraphs
-- name    : QuantumBipartiteTesting_Bipartiteness_SignedGraphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T06:06:38.284639+00:00
-- url     : https://prove2.me/theorems/cfa6cc97-096a-4bd9-ab46-114ac47b2bc4
-- title:
--   Colored signed patterns, balance, frustration, and signing probabilities
-- statement:
--   Colored edges retain their color identifier, so two edges of different colors can have identical endpoints. Each color class is a matching. A signing assigns one bit to each distinct edge. Balance and frustration are computed from vertex labelings:
--   $$\operatorname{fr}(F,b)=\min_x|\{uv\in E(F):x_u\oplus x_v\ne b_{uv}\}|.$$
--   The incident vertices, connected components and integer cycle rank $e-v+c$ are computed from the edge set. The empty pattern has zero incident vertices and zero components. NO sign probabilities average independent uniform actual-edge bits; YES sign probabilities average independent uniform vertex bits. These definitions assert no signing lemma.
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Definition 2.7, §2.3 and §2.4, PDF = printed page 10–11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Graphs

namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev ColoredEdge (N : ℕ) (colors : ℕ := 3) := Fin N × Fin N × Fin colors

def Endpoints {N colors : ℕ} (e : ColoredEdge N colors) : Fin N × Fin N := (e.1, e.2.1)

def Incident {N colors : ℕ} (e : ColoredEdge N colors) (u : Fin N) : Prop :=
  e.1 = u ∨ e.2.1 = u

def Consistent {N colors : ℕ} (F : Finset (ColoredEdge N colors)) : Prop :=
  (∀ e ∈ F, e.1 < e.2.1) ∧
  ∀ e ∈ F, ∀ f ∈ F, e.2.2 = f.2.2 →
    (∃ u, Incident e u ∧ Incident f u) → e = f

def Balanced {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool) : Prop :=
  ∃ x : Fin N → Bool, ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e

def Frustration {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool) : ℕ :=
  sInf {k | ∃ x : Fin N → Bool,
    k = (F.filter fun e => xor (x e.1) (x e.2.1) ≠ b e).card}

/-- A color-port oracle may have holes. Distinct colors retain parallel constraints. -/
def SignedResponse {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool)
    (a : Fin N × Fin colors) : Option (Fin N × Bool) :=
  if h : ∃ e ∈ F, e.2.2 = a.2 ∧ Incident e a.1 then
    let e := h.choose
    some (if e.1 = a.1 then e.2.1 else e.1, b e)
  else none

def Vertices {N colors : ℕ} (F : Finset (ColoredEdge N colors)) : Finset (Fin N) :=
  univ.filter fun u => ∃ e ∈ F, Incident e u

def Adj {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (u v : Fin N) : Prop :=
  ∃ e ∈ F, (e.1 = u ∧ e.2.1 = v) ∨ (e.1 = v ∧ e.2.1 = u)

def Components {N colors : ℕ} (F : Finset (ColoredEdge N colors)) : Finset (Finset (Fin N)) :=
  (Vertices F).image fun u => (Vertices F).filter fun v => Relation.ReflTransGen (Adj F) u v

def CycleRank {N colors : ℕ} (F : Finset (ColoredEdge N colors)) : ℤ :=
  (F.card : ℤ) - (Vertices F).card + (Components F).card

def Forest {N colors : ℕ} (F : Finset (ColoredEdge N colors)) : Prop := CycleRank F = 0

/-- Uniform edge bits are sampled on the actual edge subtype, not unused potential edges. -/
def SignProbNo {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool) : ℝ :=
  ((univ : Finset ({e // e ∈ F} → Bool)).filter
    (fun s => ∀ e, s e = b e.val)).card / (2 : ℝ) ^ F.card

def SignProbYes {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (b : ColoredEdge N colors → Bool) : ℝ :=
  ((univ : Finset (Fin N → Bool)).filter
    (fun x => ∀ e ∈ F, xor (x e.1) (x e.2.1) = b e)).card / (2 : ℝ) ^ N

def BinaryEntropy (t : ℝ) : ℝ :=
  -(t * Real.log t + (1-t) * Real.log (1-t)) / Real.log 2

def FrustrationTail {N colors : ℕ} (F : Finset (ColoredEdge N colors)) (t : ℝ) : ℝ :=
  ((univ : Finset ({e // e ∈ F} → Bool)).filter (fun s =>
    (Frustration F (fun e => if h : e ∈ F then s ⟨e,h⟩ else false) : ℝ) ≤ t)).card /
    (2 : ℝ) ^ F.card

end
end QuantumBipartiteTesting.Bipartiteness


