-- Prove2me | Definitions.Def_PoSUndirected_gadgetRegion
-- name    : PoSUndirected_gadgetRegion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:59:29.955134+00:00
-- url     : https://prove2.me/theorems/4a881c34-023d-4bba-bbf6-fd52d0b881e4
-- title:
--   Block, gadget and unit regions, confinement, external users and crossing payments in the host
-- statement:
--   Fix the host of depth $d$ and a profile $A$.
--
--   1. The **block region** of a block consists of its seven gadgets and all their descendants, excluding its ceiling. The **gadget region** of a gadget consists of its floor units, its chords and its floor descendants. For a floor unit $e$, $D(e)$ is $e$ together with its child block, if any; the region of a whole nominal segment is the union of $D(e)$ over its seven units.
--   2. **Confinement**: a floor owner's path lies in $D(e)$, and a chord owner's path lies in her gadget region.
--   3. The **external users** of a region are the players owning an edge outside it whose path uses an edge of it; a player's **payment inside** a region $R$ is $\sum_{f\in A_i\cap R}c_f/\ell_f(A)$.
--   4. A block $b$ satisfies the **crossing bound** if it charges each of its $r\ge1$ external users more than its ceiling cost divided by $r$ inside its block region. The **smaller-height conclusions** for $b$ say that every block of smaller height (greater depth) has confined owners and satisfies the crossing bound, in the same profile.
--   5. The **regional players** of a gadget are its six chord owners and the external users of its gadget region.
--   6. The **projected core** has vertices $0,\dots,11$, the floors $r$–$(r+1)$ and the chords $x=08$, $y=17$, $z=2\,11$, $u=36$, $v=4\,10$, $w=59$. The **projected route** of an edge set in a gadget consists of the floors whose segment region it meets and the chords of that gadget it contains; the regions of the pendants $Y$, $Z$ have no image.
--
--   These notions carry the height induction that proves the unique equilibrium of the construction.
--
--   **Formalization Note** The height of a block at depth $r$ is $d-r$; height one means its floor units have no children.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §3, pp.4–5 (PDF pp.6–7); §A.1, p.13 (PDF p.15); Lemma A.2 and §A.2, p.14 (PDF p.16); pp.15, 20 (PDF pp.17, 22)

import Mathlib
import Definitions.Def_PoSUndirected_hostGame

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

variable {d : ℕ}

/-- A block of the depth-`d` host: its depth `r < d` and its address `β : Fin r → Addr`. Its
height is `d − r`; height one means its floor units have no children (§A.2, p.14 (PDF p.16)). -/
abbrev HBlock (d : ℕ) : Type := Σ r : Fin d, (Fin r → Addr)

/-- The block whose seven gadgets contain the edge (the roof lies in no block). -/
def edgeBlock : HEdge d → Option (HBlock d)
  | .roof => none
  | .floor r β _ _ _ => some ⟨r, β⟩
  | .chord r β _ _ => some ⟨r, β⟩

/-- The gadget (block and gadget index) that immediately contains a floor unit or chord. -/
def edgeGadget : HEdge d → Option (HBlock d × Fin 7)
  | .roof => none
  | .floor r β g _ _ => some (⟨r, β⟩, g)
  | .chord r β g _ => some (⟨r, β⟩, g)

/-- `b'` is `b` or a descendant block of `b`: its address extends that of `b`. -/
def IsDesc (b' b : HBlock d) : Prop :=
  ∃ h : b.1.val ≤ b'.1.val,
    ∀ (i : ℕ) (hi : i < b.1.val), b'.2 ⟨i, lt_of_lt_of_le hi h⟩ = b.2 ⟨i, hi⟩

/-- `b'` is a strict descendant of `b` lying below gadget `g` of `b`. -/
def IsDescIn (b' b : HBlock d) (g : Fin 7) : Prop :=
  ∃ h : b.1.val < b'.1.val,
    (∀ (i : ℕ) (hi : i < b.1.val), b'.2 ⟨i, lt_trans hi h⟩ = b.2 ⟨i, hi⟩) ∧
      (b'.2 ⟨b.1.val, h⟩).1 = g

/-- `b'` is the child block of floor unit `u` of segment `σ` of gadget `g` of the block at depth
`r` with address `β`, or a descendant of that child. -/
def IsDescOfUnit (b' : HBlock d) (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (σ : Fin 13)
    (u : Fin 7) : Prop :=
  ∃ h : r.val < b'.1.val,
    (∀ (i : ℕ) (hi : i < r.val), b'.2 ⟨i, lt_trans hi h⟩ = β ⟨i, hi⟩) ∧
      ∃ s : Fin 6, recSeg s = σ ∧ b'.2 ⟨r.val, h⟩ = (g, s, u)

/-- The **block region** of `b` (§A.1, p.13 (PDF p.15)): the seven gadgets of `b` and all their
descendants, excluding the ceiling of `b`. -/
noncomputable def blockRegion (b : HBlock d) : Finset (HEdge d) := by
  classical exact Finset.univ.filter (fun e => ∃ b', edgeBlock e = some b' ∧ IsDesc b' b)

/-- The **gadget region** of gadget `g` of block `b` (§A.1, p.13 (PDF p.15)): its floor units,
its chords, and its floor descendants. -/
noncomputable def gadgetRegion (b : HBlock d) (g : Fin 7) : Finset (HEdge d) := by
  classical
  exact Finset.univ.filter (fun e =>
    edgeGadget e = some (b, g) ∨ ∃ b', edgeBlock e = some b' ∧ IsDescIn b' b g)

/-- `D(e)` for the floor unit `e = floor r β g σ u` (§A.1, p.13 (PDF p.15)): `e` together with its
child block (the child's region), if any. -/
noncomputable def unitRegion (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (σ : Fin 13)
    (u : Fin 7) : Finset (HEdge d) := by
  classical
  exact insert (HEdge.floor r β g σ u)
    (Finset.univ.filter (fun e => ∃ b', edgeBlock e = some b' ∧ IsDescOfUnit b' r β g σ u))

/-- The region of a whole nominal segment `σ` of gadget `g` of block `b`: the union of `D(e)` over
its seven units `e`. -/
noncomputable def segRegion (b : HBlock d) (g : Fin 7) (σ : Fin 13) : Finset (HEdge d) := by
  classical exact Finset.univ.biUnion (fun u : Fin 7 => unitRegion b.1 b.2 g σ u)

/-- The region an owner is confined to (§A.1, p.13 (PDF p.15): "Confinement means that a floor
owner's path lies in `D(e)` and that a chord owner's path lies in her gadget"); the roof owner is
not subject to confinement. -/
noncomputable def confRegion : HEdge d → Finset (HEdge d)
  | .roof => Finset.univ
  | .floor r β g σ u => unitRegion r β g σ u
  | .chord r β g _ => gadgetRegion ⟨r, β⟩ g

/-- All immediate floor owners and chord owners of block `b` are confined in profile `A`. -/
def OwnersConfined (A : HEdge d → Finset (HEdge d)) (b : HBlock d) : Prop :=
  ∀ e : HEdge d, edgeBlock e = some b → A e ⊆ confRegion e

/-- The **external users** of a region `R` in profile `A` (§A.1, p.13 (PDF p.15): "A player
external to a region owns an edge outside it"): the players whose own edge is outside `R` and
whose path uses an edge of `R`. -/
noncomputable def extUsers (A : HEdge d → Finset (HEdge d)) (R : Finset (HEdge d)) :
    Finset (HEdge d) := by
  classical exact Finset.univ.filter (fun i => i ∉ R ∧ (A i ∩ R).Nonempty)

/-- The payment of player `i` inside the region `R` in profile `A`: `Σ_{f ∈ Aᵢ ∩ R} c_f/ℓ_f(A)`. -/
noncomputable def payIn {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
    (G : CongestionGame ι E) (A : ι → Finset E) (i : ι) (R : Finset E) : ℝ :=
  ∑ f ∈ A i ∩ R, G.latency f (load A f)

/-- The ceiling cost `ρ` of block `b`. -/
def ceilCost (p : Params) (b : HBlock d) : ℚ := ceilCostAux p b.1.val b.2

/-- The crossing bound for block `b` (Lemma A.2, p.14 (PDF p.16)): it charges each of its
`r ≥ 1` external users more than its ceiling cost divided by `r`, inside its block region. -/
def CrossBound (p : Params) (A : HEdge d → Finset (HEdge d)) (b : HBlock d) : Prop :=
  ∀ i ∈ extUsers A (blockRegion b),
    (ceilCost p b : ℝ) / (extUsers A (blockRegion b)).card <
      payIn (hostGame p d) A i (blockRegion b)

/-- The smaller-height conclusions for block `b` (Lemma A.2, p.14 (PDF p.16); §A.2): every block of
smaller height than `b` (greater depth) has confined owners and satisfies the crossing bound, in
the same profile `A`. -/
def SmallerHeightConcl (p : Params) (A : HEdge d → Finset (HEdge d)) (b : HBlock d) : Prop :=
  ∀ b' : HBlock d, b.1.val < b'.1.val → OwnersConfined A b' ∧ CrossBound p A b'

/-- The **regional players** of gadget `g` of block `b` (§3, p.5 (PDF p.7): "regional users are the
gadget's chord owners and external crossers"): its six chord owners and the external users of its
gadget region. -/
noncomputable def regionalPlayers (A : HEdge d → Finset (HEdge d)) (b : HBlock d) (g : Fin 7) :
    Finset (HEdge d) :=
  (Finset.univ.image (fun κ : Fin 6 => HEdge.chord b.1 b.2 g κ)) ∪ extUsers A (gadgetRegion b g)

/-- The edges of the projected core (§A.6, p.20 (PDF p.22)): the eleven floors `a, …, k` and the
six projected chords `x, y, z, u, v, w`. -/
abbrev CoreEdge : Type := Fin 11 ⊕ Fin 6

/-- The endpoints of the six projected chords `x = 08`, `y = 17`, `z = 2 11`, `u = 36`,
`v = 4 10`, `w = 59` (§A.6, p.20 (PDF p.22)): the physical chords with the pendant vertices `12`,
`13` contracted to `1`, `2`. -/
def coreChordEnds : Fin 6 → Fin 12 × Fin 12 :=
  ![(0, 8), (1, 7), (2, 11), (3, 6), (4, 10), (5, 9)]

/-- The endpoints of the edges of the projected core, on the vertices `0, …, 11`: floor `σ` joins
`σ` and `σ + 1` (§A.6, p.20 (PDF p.22): "floors 0–1–⋯–11"). -/
def coreEnds : CoreEdge → Sym2 (Fin 12)
  | .inl σ => s(⟨σ.val, by have := σ.isLt; omega⟩, ⟨σ.val + 1, by have := σ.isLt; omega⟩)
  | .inr κ => s((coreChordEnds κ).1, (coreChordEnds κ).2)

/-- The projection of the edge set `P` to the core of gadget `g` of block `b` (p.15 (PDF p.17)):
the floors whose segment region `P` meets and the chords `P` contains. Traversed floor-unit regions
are replaced by their endpoint pairs, subdivision vertices are suppressed, and the pendants `Y`, `Z`
are contracted, so edges of their regions have no image.

**Formalization Note.** This is total on edge sets. That a route meets a segment only by crossing
all of it is part of what makes the projected route a simple path, hence a conclusion of Lemma A.4
and not a condition of this definition. A nonowner's traversal of `y` or `z` projects to the chord
alone, which is the paper's convention that the pendant is included in the effective coordinate. -/
noncomputable def projRoute (b : HBlock d) (g : Fin 7) (P : Finset (HEdge d)) :
    Finset CoreEdge := by
  classical
  exact Finset.univ.filter (Sum.elim
    (fun σ : Fin 11 => (P ∩ segRegion b g (Fin.castLE (by omega) σ)).Nonempty)
    (fun κ : Fin 6 => HEdge.chord b.1 b.2 g κ ∈ P))

end PoSUndirected


