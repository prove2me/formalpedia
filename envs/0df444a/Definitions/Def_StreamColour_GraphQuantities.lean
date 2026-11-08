-- Prove2me | Definitions.Def_StreamColour_GraphQuantities
-- name    : StreamColour_GraphQuantities
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:52:02.952946+00:00
-- url     : https://prove2.me/theorems/47069428-14dc-44e7-9f2e-c32a58fc1376
-- title:
--   §3 — $N_G$, $N_G[\cdot]$, $a_C$, $e_C$, $d_X$
-- statement:
--   For a finite graph $G$, the open and closed neighbourhoods $N_G(v)$ and $N_G[v]$; for a set $C$ the internal anti-degree $a_C(v)=|C\setminus N_G[v]|$ and external degree $e_C(v)=|N_G(v)\setminus C|$; and $d_X(v)=|N_G(v)\cap X|$, whether or not $v$ belongs to $X$. Also $|C\setminus N(x)|$, and the number of edges with exactly one endpoint in $X$.
--
--   **Formalization Note** These use classical decidability, so the theorems carry no decidability instance for the graph.
-- source:
--   Chakraborty, Chatterjee, Kundu, Mishra, Streaming Graph Colouring Meets Molloy–Reed via Kernelization (STOC 2027 submission, preprint, sha256 31a813b319e4af3fd96deb52ecd284fc2c478368ab1d9064bb951dcc884cc105), §3, p.20 (PDF 22)

import Mathlib

namespace StreamColour

/-! # Neighbourhood quantities

Chakraborty, Chatterjee, Kundu, Mishra (STOC 2027 submission, sha256 31a813b3…), §3, p.20 (PDF 22):
`a_C(v) = |C \ N_G[v]|`, `e_C(v) = |N_G(v) \ C|`, and `d_X(v) = |N_G(v) ∩ X|` "whether or not v belongs to X".

**Formalization Note.** The neighbourhoods are computed with classical decidability, so no statement carries
a decidability instance for the graph. -/

variable {V : Type} [Fintype V]

open Classical in
/-- `N_G(v)`. -/
noncomputable def nbrs (G : SimpleGraph V) (v : V) : Finset V := Finset.univ.filter (G.Adj v)

open Classical in
/-- `N_G[v]`. -/
noncomputable def closedNbrs (G : SimpleGraph V) (v : V) : Finset V := insert v (nbrs G v)

/-- `d_G(v)`. -/
noncomputable def dG (G : SimpleGraph V) (v : V) : ℕ := (nbrs G v).card

open Classical in
/-- The internal anti-degree `a_C(v) = |C \ N_G[v]|`. -/
noncomputable def antiDeg (G : SimpleGraph V) (C : Finset V) (v : V) : ℕ := (C \ closedNbrs G v).card

open Classical in
/-- The external degree `e_C(v) = |N_G(v) \ C|`. -/
noncomputable def extDeg (G : SimpleGraph V) (C : Finset V) (v : V) : ℕ := (nbrs G v \ C).card

open Classical in
/-- `d_X(v) = |N_G(v) ∩ X|`. -/
noncomputable def dIn (G : SimpleGraph V) (X : Finset V) (v : V) : ℕ := (nbrs G v ∩ X).card

open Classical in
/-- The number of vertices of `C` not adjacent to `x`, `|C \ N(x)|`. -/
noncomputable def missing (G : SimpleGraph V) (C : Finset V) (x : V) : ℕ := (C \ nbrs G x).card

open Classical in
/-- The number of edges with exactly one endpoint in `X`. -/
noncomputable def edgesLeaving (G : SimpleGraph V) (X : Finset V) : ℕ :=
  ((X ×ˢ (Finset.univ \ X)).filter fun p => G.Adj p.1 p.2).card

end StreamColour


