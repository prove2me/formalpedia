-- Prove2me | Definitions.Def_PlanarMetricElections_Peer_QuartileGrid
-- name    : PlanarMetricElections_Peer_QuartileGrid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:41.509526+00:00
-- url     : https://prove2.me/theorems/8a276961-38fe-4a96-945e-cc82000bb704
-- title:
--   The exact quartile grid and labeled voter cells
-- statement:
--   For a finite electorate $V$, an exact quartile grid comprises three strictly increasing vertical cuts and three strictly increasing horizontal cuts, avoiding every voter. Voters have pairwise distinct first coordinates and pairwise distinct second coordinates. Each of the four rows and each of the four columns has uniform voter mass $1/4$.
--
--   Rows run north to south and columns west to east. Their intersections are the sixteen cells
--
--   $$\begin{matrix}A&B&C&D\\E&F&G&H\\I&J&K&L\\M&N&O&P\end{matrix}.$$
--
--   The center is $F,G,J,K$, and $p$ is the intersection of the middle cuts. A cell's geometric region, its voter subset, and its mass are separate objects. Define
--
--   $$\tau=\max\{\mu_V(A),\,1/4-\mu_V(F)\}.$$
--
--   This is precisely the intermediate setting for Lemmas A.2–A.9. It does not assert that an arbitrary electorate has such a grid, and contains no net-existence or capture-bound field.
--
--   **Formalization Note** Row and column indices are $0,1,2,3$ in Lean; $A=(0,0)$, $F=(1,1)$, $G=(1,2)$, $J=(2,1)$, $K=(2,2)$. Horizontal cut indices increase south to north, while row indices increase north to south. Cuts themselves have no voters.
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Section 3 and Appendix A, pp. 4–5, 13–14, 19 (PDF pp. 5–6, 14–15, 20)

import Definitions.Def_PlanarMetricElections_Peer_RectangularNet

set_option autoImplicit false
open scoped Classical
noncomputable section

namespace PlanarMetricElections.Peer

/-- Columns are numbered west to east; cuts are increasing. -/
def columnBand (cut : Fin 3 → ℝ) (j : Fin 4) : Set Plane :=
  if j = 0 then {z | z.1 < cut 0}
  else if j = 1 then {z | cut 0 < z.1 ∧ z.1 < cut 1}
  else if j = 2 then {z | cut 1 < z.1 ∧ z.1 < cut 2}
  else {z | cut 2 < z.1}

/-- Rows are numbered north to south; cuts are increasing from south to north. -/
def rowBand (cut : Fin 3 → ℝ) (i : Fin 4) : Set Plane :=
  if i = 0 then {z | cut 2 < z.2}
  else if i = 1 then {z | cut 1 < z.2 ∧ z.2 < cut 2}
  else if i = 2 then {z | cut 0 < z.2 ∧ z.2 < cut 1}
  else {z | z.2 < cut 0}

/-- The standing intermediate setup, not an assumption on the unrestricted headline. -/
structure QuartileGrid (V : Finset Plane) where
  nonempty : V.Nonempty
  xCut : Fin 3 → ℝ
  yCut : Fin 3 → ℝ
  x_order : StrictMono xCut
  y_order : StrictMono yCut
  x_avoids : ∀ v ∈ V, ∀ j : Fin 3, v.1 ≠ xCut j
  y_avoids : ∀ v ∈ V, ∀ i : Fin 3, v.2 ≠ yCut i
  x_distinct : Set.InjOn Prod.fst (↑V : Set Plane)
  y_distinct : Set.InjOn Prod.snd (↑V : Set Plane)
  column_mass : ∀ j : Fin 4, mass V (columnBand xCut j) = 1 / 4
  row_mass : ∀ i : Fin 4, mass V (rowBand yCut i) = 1 / 4

namespace QuartileGrid

variable {V : Finset Plane}

def cell (g : QuartileGrid V) (i j : Fin 4) : Set Plane :=
  rowBand g.yCut i ∩ columnBand g.xCut j

def cellVotes (g : QuartileGrid V) (i j : Fin 4) : Finset Plane :=
  V.filter (fun v => v ∈ g.cell i j)

def cellMass (g : QuartileGrid V) (i j : Fin 4) : ℝ := mass V (g.cell i j)

def middle (g : QuartileGrid V) : Plane := (g.xCut 1, g.yCut 1)

def tau (g : QuartileGrid V) : ℝ := max (g.cellMass 0 0) (1 / 4 - g.cellMass 1 1)

end QuartileGrid
end PlanarMetricElections.Peer


