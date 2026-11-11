-- Prove2me | Definitions.Def_BeyondConvexity_APTAS_Packing
-- name    : BeyondConvexity_APTAS_Packing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:08:36.480192+00:00
-- url     : https://prove2.me/theorems/3cd2e8dd-0c35-4d49-bc70-44f75b04cfc8
-- title:
--   Labeled translation packings and their actual optimum
-- statement:
--   An instance is a finite list of polygonal regions. Its positions are occurrence labels, including when geometries repeat. A packing lists one bin index and translation for every occurrence. Each index is smaller than the number of bins; each translated region lies in its unit square; and different occurrences in the same bin have disjoint interiors. Boundary contact is permitted. A rational packing uses rational translations, interpreted exactly as real coordinates.
--
--   For an instance $I$, the optimum is
--
--   $$\operatorname{OPT}(I)=\min\{m\in\mathbb N: I\text{ packs into }m\text{ unit squares with real translations}\}.$$
--
--   Valid input objects fit individually, so this set is nonempty; the empty instance has optimum zero. Local feasibility uses an arbitrary polygonal container with holes, without normalization or a unit-square restriction. These notions preserve the distinction between real witnesses and rational algorithmic outputs.
-- source:
--   Lucas de Oliveira Silva, Elisa Dell'Arriva, Flávio Keidi Miyazawa, STOC 2027 submission #890 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/890.pdf, Section 2, printed p.5 / PDF p.6; Section 2.1, printed p.8 / PDF p.9.

import Definitions.Def_BeyondConvexity_APTAS_Polygon

noncomputable section

namespace BeyondConvexity.APTAS

/-- List positions are occurrence labels; equal regions remain distinct. -/
abbrev Instance := List Polygon

def Instance.InClass (I : Instance) (P : Set Polygon) : Prop :=
  ∀ p ∈ I, p ∈ P ∧ p.InputValid

structure Packing (F : Type) where
  bins : ℕ
  placements : List (ℕ × (F × F))

def Packing.entry {F : Type} [Zero F] (p : Packing F) (i : ℕ) : ℕ × (F × F) :=
  p.placements.getD i (0, (0, 0))

def Packing.Realize (p : Packing ℚ) : Packing ℝ :=
  ⟨p.bins, p.placements.map (fun q => (q.1, ((q.2.1 : ℝ), (q.2.2 : ℝ))))⟩

def Packing.Feasible (I : Instance) (p : Packing ℝ) : Prop :=
  p.placements.length = I.length ∧
    (∀ i : Fin I.length, (p.entry i).1 < p.bins ∧
      translate (p.entry i).2 (I.get i).region ⊆ square 1) ∧
    ∀ i j : Fin I.length, i ≠ j → (p.entry i).1 = (p.entry j).1 →
      Disjoint (interior (translate (p.entry i).2 (I.get i).region))
        (interior (translate (p.entry j).2 (I.get j).region))

def Packable (I : Instance) (m : ℕ) : Prop :=
  ∃ p : Packing ℝ, p.bins = m ∧ p.Feasible I

/-- The actual minimum over all real translations. Valid inputs fit one object per bin. -/
def OPT (I : Instance) : ℕ := sInf {m | Packable I m}

def RationalPacking (I : Instance) (p : Packing ℚ) : Prop := p.Realize.Feasible I

/-- Local queries use an arbitrary polygonal container, without normalization or unit fit. -/
def LocalFeasible (I : Instance) (Q : Polygon) (v : List Point) : Prop :=
  v.length = I.length ∧
    (∀ i : Fin I.length, translate (v.getD i.val 0) (I.get i).region ⊆ Q.region) ∧
    ∀ i j : Fin I.length, i ≠ j →
      Disjoint (interior (translate (v.getD i.val 0) (I.get i).region))
        (interior (translate (v.getD j.val 0) (I.get j).region))

end BeyondConvexity.APTAS


