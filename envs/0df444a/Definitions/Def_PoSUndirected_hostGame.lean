-- Prove2me | Definitions.Def_PoSUndirected_hostGame
-- name    : PoSUndirected_hostGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:58:25.921071+00:00
-- url     : https://prove2.me/theorems/e8d86bbd-7ed1-4d34-9133-0348f6f86a5a
-- title:
--   The recursive six-chord host of depth $d$, its costs, its owned-edge game and the tree $T_d$
-- statement:
--   **The gadget.** Its floor is the path $0,1,\dots,11$ with segments $a=01,\dots,k=10\,11$; two pendant branches $Y=(1,12)$ and $Z=(2,13)$; and six physical chords $A=(0,8)$, $B=(12,7)$, $C=(13,11)$, $D=(3,6)$, $E=(4,10)$, $F=(5,9)$. Its portals are $0$ and $11$.
--
--   **A block** under a retained ceiling of cost $\rho$ consists of seven gadgets placed in series between the ceiling's endpoints, each at scale $\lambda=\rho/(7\alpha)$. Each of the thirteen nominal segments ($a,\dots,k,Y,Z$) of nominal cost $s$ is subdivided into seven units of cost $\lambda s/7$; a chord of physical cost $c$ costs $\lambda c$. Every unit of $a,b,j,k,Y,Z$ becomes the ceiling of a child block; the units of $c,\dots,i$ never get children.
--
--   **The host of depth $d$.** Start with one roof edge of cost $1$ and stop after $d$ layers of blocks: the top block hangs under the roof, and the units of recursive segments in layers $1,\dots,d-1$ carry child blocks. All block interiors are fresh vertices; the only identifications are the attachments and the shared portals of consecutive gadgets. Depth $0$ is the roof alone.
--
--   The **owned-edge game** on this host gives every edge (roof, unit, chord) its own endpoint owner, who may use every simple path of the host between her edge's endpoints. The **all-direct profile** has every player on her own edge; its cost $E_d$ is the total cost of the host. The tree $T_d$ replaces every expanded ceiling by its seven serial floor trees: it consists of all units that are not ceilings of a block (and of the roof when $d=0$), and $O_d$ is its cost. Finally $G_d=\sum_{r=0}^{d-1}B_{\rm rec}^r$.
--
--   **Formalization Note** A block at depth $r<d$ is addressed by the sequence of (gadget, recursive segment, unit) choices leading to it from the top. Vertices are listed without repetition: the roof endpoints, the six inner portals of each block, the twelve non-portal gadget vertices and the six subdivision vertices of each segment; the outer portals of a block are the endpoints of its ceiling unit. Costs are rational; the game uses their real casts.
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §3, pp.4–6 (PDF pp.6–8); §A.1, p.13 (PDF p.15); §A.4, pp.17–18 (PDF pp.19–20)

import Mathlib
import Definitions.Def_PoSUndirected_ndGame
import Definitions.Def_PoSUndirected_Params

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- The address of a child block inside its parent block: the gadget `g ∈ {0, …, 6}` of the
seven serial gadgets, the recursive segment `s ∈ {0, …, 5} ↦ a, b, j, k, Y, Z`, and the unit
`u ∈ {0, …, 6}` of the seven units of that segment whose unit becomes the child's ceiling. -/
abbrev Addr : Type := Fin 7 × Fin 6 × Fin 7

/-- The six recursive segments `a, b, j, k, Y, Z` as indices of `Params.nominal`. -/
def recSeg : Fin 6 → Fin 13 := ![0, 1, 9, 10, 11, 12]

/-- The endpoints of the thirteen nominal segments on the fourteen gadget positions
`0, …, 13`: floor `σ ↦ (σ, σ + 1)` for `σ = 0, …, 10` (`a = 01, …, k = 10 11`), `Y = (1, 12)`,
`Z = (2, 13)` (§3, p.4 (PDF p.6)). -/
def segEnds : Fin 13 → Fin 14 × Fin 14 :=
  ![(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10), (10, 11),
    (1, 12), (2, 13)]

/-- The endpoints of the six physical chords `A = (0, 8)`, `B = (12, 7)`, `C = (13, 11)`,
`D = (3, 6)`, `E = (4, 10)`, `F = (5, 9)` (§3, p.4 (PDF p.6)). -/
def chordEnds : Fin 6 → Fin 14 × Fin 14 :=
  ![(0, 8), (12, 7), (13, 11), (3, 6), (4, 10), (5, 9)]

/-- The edges of the depth-`d` host (Tsoufis, preprint, sha256 c095d811…, §3, p.4 (PDF p.6);
§A.1, p.13 (PDF p.15)). A block at depth `r < d` is addressed by `β : Fin r → Addr` (the path of
child addresses from the top block, `β 0` first); the top block (depth `0`) hangs under the roof.

* `roof`: the roof edge, of cost one;
* `floor r β g σ u`: unit `u` (of seven) of nominal segment `σ` (of thirteen: `a, …, k, Y, Z`)
  in gadget `g` (of seven serial gadgets) of block `(r, β)`;
* `chord r β g κ`: physical chord `κ` (`A, …, F`) of gadget `g` of block `(r, β)`.

Every edge has its own endpoint owner. A floor unit of a recursive segment at depth `r` with
`r + 1 < d` is the ceiling of a child block at depth `r + 1`. -/
inductive HEdge (d : ℕ) where
  | roof : HEdge d
  | floor (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (σ : Fin 13) (u : Fin 7) : HEdge d
  | chord (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (κ : Fin 6) : HEdge d
  deriving DecidableEq, Fintype

/-- The vertices of the depth-`d` host, without repetitions:

* `roofEnd i`: the two endpoints of the roof;
* `portal r β j`: the shared portal between gadgets `j` and `j + 1` of block `(r, β)`;
* `core r β g p`: the non-portal gadget vertices `1, …, 10, 12, 13` of gadget `g`
  (`p = 0, …, 9 ↦ 1, …, 10`, `p = 10 ↦ 12`, `p = 11 ↦ 13`);
* `sub r β g σ k`: the six strict subdivision vertices of segment `σ` (`k = 0, …, 5` is the
  vertex after unit `k`).

The two outer portals of a block are the endpoints of its ceiling (`blockEnd`). -/
inductive HVtx (d : ℕ) where
  | roofEnd (i : Fin 2) : HVtx d
  | portal (r : Fin d) (β : Fin r → Addr) (j : Fin 6) : HVtx d
  | core (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (p : Fin 12) : HVtx d
  | sub (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (σ : Fin 13) (k : Fin 6) : HVtx d
  deriving DecidableEq, Fintype

variable {d : ℕ}

/-- The vertex at gadget position `p ∈ {0, …, 13}` of gadget `g` of block `(r, β)`, given the
two ceiling endpoints `be` of the block: position `0` of gadget `0` and position `11` of gadget
`6` are the ceiling endpoints, position `11` of gadget `g` and position `0` of gadget `g + 1` are
the same portal. -/
def gvOf (be : Fin 2 → HVtx d) (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (p : Fin 14) :
    HVtx d :=
  if p.val = 0 then
    (if hg : g.val = 0 then be 0 else HVtx.portal r β ⟨g.val - 1, by omega⟩)
  else if p.val = 11 then
    (if hg : g.val = 6 then be 1 else HVtx.portal r β ⟨g.val, by omega⟩)
  else HVtx.core r β g ⟨if p.val < 11 then p.val - 1 else p.val - 2, by split <;> omega⟩

/-- The vertex at position `m ∈ {0, …, 7}` along nominal segment `σ` of gadget `g`: its two ends
(`m = 0`, `m ≥ 7`) are gadget positions and `m = 1, …, 6` are subdivision vertices. -/
def segVOf (be : Fin 2 → HVtx d) (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (σ : Fin 13)
    (m : ℕ) : HVtx d :=
  if m = 0 then gvOf be r β g (segEnds σ).1
  else if hm : m < 7 then HVtx.sub r β g σ ⟨m - 1, by omega⟩
  else gvOf be r β g (segEnds σ).2

/-- The two ceiling endpoints of the block at depth `r` with address `β`: the roof endpoints for
the top block, and otherwise the two endpoints of the floor unit of the parent block that is its
ceiling. -/
def blockEnd : (r : ℕ) → (hr : r < d) → (Fin r → Addr) → Fin 2 → HVtx d
  | 0, _, _, i => HVtx.roofEnd i
  | r + 1, hr, β, i =>
      segVOf (blockEnd r (by omega) (Fin.init β)) ⟨r, by omega⟩ (Fin.init β)
        (β (Fin.last r)).1 (recSeg (β (Fin.last r)).2.1) ((β (Fin.last r)).2.2.val + i.val)

/-- Gadget position `p` of gadget `g` of block `(r, β)`. -/
def gv (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (p : Fin 14) : HVtx d :=
  gvOf (blockEnd r.val r.isLt β) r β g p

/-- Position `m` along segment `σ` of gadget `g` of block `(r, β)`. -/
def segV (r : Fin d) (β : Fin r → Addr) (g : Fin 7) (σ : Fin 13) (m : ℕ) : HVtx d :=
  segVOf (blockEnd r.val r.isLt β) r β g σ m

/-- The endpoints of the edges of the depth-`d` host. Unit `u` of segment `σ` joins positions `u`
and `u + 1` along the segment; chord `κ` joins the two gadget positions `chordEnds κ`. -/
def hostEnds (d : ℕ) : HEdge d → Sym2 (HVtx d)
  | .roof => s(HVtx.roofEnd 0, HVtx.roofEnd 1)
  | .floor r β g σ u => s(segV r β g σ u.val, segV r β g σ (u.val + 1))
  | .chord r β g κ => s(gv r β g (chordEnds κ).1, gv r β g (chordEnds κ).2)

/-- The cost `ρ` of the ceiling of the block at depth `r` with address `β`: `1` for the roof, and
a child's ceiling is a unit of nominal segment cost `s` at scale `λ = ρ/(7α)`, i.e. of cost
`λ s/7 = ρ s/(49α)`. -/
def ceilCostAux (p : Params) : (r : ℕ) → (Fin r → Addr) → ℚ
  | 0, _ => 1
  | r + 1, β => ceilCostAux p r (Fin.init β) *
      (p.nominal (recSeg (β (Fin.last r)).2.1) / (49 * p.α))

/-- The scale `λ = ρ/(7α)` of the seven gadgets of the block `(r, β)` with ceiling cost `ρ`
(§3, p.4 (PDF p.6)). -/
def lam (p : Params) (r : ℕ) (β : Fin r → Addr) : ℚ := ceilCostAux p r β / (7 * p.α)

/-- The cost of every edge of the depth-`d` host at parameters `p`: the roof costs `1`; a floor
unit of nominal segment cost `s` in a block of scale `λ` costs `λ s/7`; a physical chord costs
`λ` times its physical cost `x, y − L_y, z − L_z, u, v, w`. -/
def hostCost (p : Params) {d : ℕ} : HEdge d → ℚ
  | .roof => 1
  | .floor r β _ σ _ => lam p r β * p.nominal σ / 7
  | .chord r β _ κ => lam p r β * p.physChord κ

/-- The owned-edge game on the depth-`d` host at parameters `p` (§3, p.4 (PDF p.6): "Every
physical edge, including every subdivision edge and every ceiling, has its own player"; "the
players may choose any paths in the host"). -/
noncomputable def hostGame (p : Params) (d : ℕ) : CongestionGame (HEdge d) (HEdge d) :=
  ownerGame (hostEnds d) (fun e => (hostCost p e : ℝ))

/-- The all-direct profile: every player uses her own edge. -/
def directProfile {E : Type*} [DecidableEq E] : E → Finset E := fun e => {e}

/-- Whether nominal segment `σ` receives descendants (`a, b, j, k, Y, Z`). -/
def IsRecSeg (σ : Fin 13) : Prop := ∃ s : Fin 6, recSeg s = σ

instance (σ : Fin 13) : Decidable (IsRecSeg σ) := by unfold IsRecSeg; infer_instance

/-- Membership in the tree `T_d` (§A.4, p.17 (PDF p.19)): every expanded ceiling replaced by its
seven serial floor trees. It consists of all floor units that are not ceilings of a block (units
of `c, …, i`, and all units of the last layer), and of the roof when `d = 0`; no chord. -/
def InTree (d : ℕ) : HEdge d → Prop
  | .roof => d = 0
  | .floor r _ _ σ _ => ¬ (IsRecSeg σ ∧ r.val + 1 < d)
  | .chord _ _ _ _ => False

instance (d : ℕ) : DecidablePred (InTree d) := fun e => by
  cases e <;> unfold InTree <;> infer_instance

/-- The edge set of `T_d` (see `InTree`). -/
def treeEdges (d : ℕ) : Finset (HEdge d) := Finset.univ.filter (InTree d)

/-- `E_d`: the cost of the all-direct profile of the depth-`d` host, i.e. the total cost of all
its edges (§3, p.6 (PDF p.8)). -/
def Ed (p : Params) (d : ℕ) : ℚ := ∑ e : HEdge d, hostCost p e

/-- `O_d`: the cost of the tree `T_d` (§3, p.6 (PDF p.8)). -/
def Od (p : Params) (d : ℕ) : ℚ := ∑ e ∈ treeEdges d, hostCost p e

/-- `G_d = Σ_{r=0}^{d-1} B_rec^r` (§3, p.6 (PDF p.8)). -/
def Gd (p : Params) (d : ℕ) : ℚ := ∑ r ∈ Finset.range d, p.Brec ^ r

end PoSUndirected


