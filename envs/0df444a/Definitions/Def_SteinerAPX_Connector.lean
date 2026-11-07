-- Prove2me | Definitions.Def_SteinerAPX_Connector
-- name    : SteinerAPX_Connector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:55.949479+00:00
-- url     : https://prove2.me/theorems/3143da49-96f7-46c4-bb9f-2cf06066f593
-- title:
--   Connectors, attachments near ports, good and bad connectors (Definition 12)
-- statement:
--   Fix a cable layout and $0<\rho\le1/100$. A **connector** with $r$ attachments is a network $S$ with connected carrier together with **attachments** $x_1,\dots,x_r$ on $S$ and pairwise distinct labels $\ell_1,\dots,\ell_r$ such that each $x_j$ lies within distance $\rho$ of the cable $\Gamma_{\ell_j}$.
--
--   An attachment is **near the port** $p_{s,i}$ if it lies within distance $\rho$ of the radial segment $[p_{s,i},\,z_s+20v_{s,i}]$ (the cable segment from the port to the boundary of $B_s$ in (S1)). A connector is
--
--   1. **good at the square** $s$ of a triple $\{u,v,w\}$ if it has exactly four attachments, one near each of the ports $p_{s,0},p_{s,u},p_{s,v},p_{s,w}$;
--   2. **good at the fallback** $s$ of an element $u$ if it has exactly two attachments, one near each of the ports $p_{s,0}$ and $p_{s,u}$;
--   3. **bad** otherwise.
--
--   In the cable reduction, connectors are the pieces of a tree on $P_\rho$ joining the recovered cables; good square connectors encode the triples of a matching.
--
--   **Formalization Note** "One near each port" is a bijection from the attachments onto the labels of the gadget. The paper's connectors are subtrees with leaves on the recovered trees $T_i$ and at least two attachments; the structure keeps only the properties the length bounds use (connected, attachments on it, each near a distinct cable), so it contains the paper's connectors.
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.3 and Definition 12, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_SteinerAPX_CableLayout

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Connectors, attachments near ports, good and bad connectors (Definition 12).**
S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*, STOC 2027 submission (manuscript
sha256 6f78a9ea…), §4.3 and Definition 12, p.17 (PDF p.19): "Removing F decomposes the rest of bT
into connectors: subtrees whose leaves, called attachments, lie on F and whose other points lie
outside F (Figure 11(a)). Every connector has at least two attachments, and it cannot attach twice
to the same Ti … Connectors attach to the trees Ti, so their attachments lie within distance ρ of
the cables. An attachment is near a port p of a gadget s if it lies within distance ρ of the cable
segment from p to the boundary of Bs, as specified in (S1). … A connector is (i) good at the square
s of a triple {u, v, w} if it has exactly four attachments, one near each of the ports ps,0, ps,u,
ps,v, ps,w; (ii) good at the fallback s of an element u if it has exactly two attachments, one near
each of the ports ps,0 and ps,u; (iii) bad otherwise."

A `Connector L ρ` is a network `S` with connected carrier and `r` attachments `x₀, …, x_{r−1}` on
it, where attachment `j` lies within distance `ρ` of the cable `Γ_{lab j}` and the labels
`lab j` are pairwise distinct. It is good at gadget `s` when `r` equals the number of ports of `s`
and some bijection `σ` from the attachments onto the labels of `s` puts each attachment `x_j`
within distance `ρ` of the radial segment of the port `p_{s,σ j}`; bad when it is good at no
gadget.

**Formalization Note** The connector is described by exactly the data its lower bound
(Lemma 13) uses: a connected network through its attachments, each within `ρ` of a distinct
cable. The paper's further properties (leaves on `F`, other points outside `F`, at least two
attachments) are not imposed, so these connectors include the paper's. -/
structure Connector {H : Inst3DM} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (L : CableLayout H V) (ρ : ℝ) where
  /-- The connector's segments. -/
  S : Network V
  /-- The number of attachments. -/
  r : ℕ
  /-- The attachments. -/
  x : Fin r → V
  /-- The cable each attachment lies near. -/
  lab : Fin r → Label H
  connected : IsConnected (carrier S)
  mem : ∀ j, x j ∈ carrier S
  lab_injective : Function.Injective lab
  near_cable : ∀ j, Metric.infDist (x j) (carrier (L.cable (lab j))) ≤ ρ

namespace Connector

variable {H : Inst3DM} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {L : CableLayout H V} {ρ : ℝ}

/-- A point is near the port `p_{s,i}`: within `ρ` of the radial segment from it. -/
def NearPort (L : CableLayout H V) (ρ : ℝ) (x : V) (s : Gadget H) (i : Label H) : Prop :=
  Metric.infDist x (L.radial s i) ≤ ρ

/-- Good at the gadget `s`: one attachment near each port of `s`, and no other attachment. -/
def GoodAt (C : Connector L ρ) (s : Gadget H) : Prop :=
  C.r = (labels H s).card ∧
  ∃ σ : Fin C.r → Label H, Set.BijOn σ Set.univ ↑(labels H s) ∧
    ∀ j, NearPort L ρ (C.x j) s (σ j)

/-- Bad: good at no gadget. -/
def Bad (C : Connector L ρ) : Prop := ∀ s : Gadget H, ¬ C.GoodAt s

end Connector

end SteinerAPX


