-- Prove2me | Definitions.Def_ContractionLemma_Packing
-- name    : ContractionLemma_Packing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:58:10.867308+00:00
-- url     : https://prove2.me/theorems/f7abefca-1085-44d8-933a-423f3a96ef8c
-- title:
--   Labels $\phi(u),\psi(v)$, packets, orientation and small groups
-- statement:
--   A **packing** is a placement of the edges together with labels $\phi(u),\psi(v)\in\{1,\dots,64\}^a$ of the row and column vertices. The level-$k$ group of a vertex is the $k$-th symbol of its label. The module names the properties of Lemma A.9: **orientation** (every packet has, for each coordinate $k<a$, two symbols $g_k,g_k'$; the row vertex at slot $x$ has $k$-th symbol $g_k$ if $x_k=0$ and $g_k'$ if $x_k=1$; the column vertex at slot $y$ has $g_k'$ if $y_k=0$ and $g_k$ if $y_k=1$), its "in particular" clause, **small groups** (at most $3M/64$ edges per symbol on each side) and **few packets** (at most $3M/L$). It also fixes the input and output words of the packing algorithm.
--
--   **Formalization Note** The symbols $\{1,\dots,64\}$ are `Fin 64`, coordinates are `Fin a`, and bit $k$ of a slot is `Nat.testBit`. The bounds are compared in the reals, so $3M/64$ and $3M/L$ are not rounded.
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.4.3, pp.59–61, Lemma A.9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_Placement

set_option autoImplicit false

namespace ContractionLemma

open OAI.Algorithms.SubexponentialSAT

/-- **Labels and packets** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), App. A.4.3, pp.59–60.

A placement of the edges into packets of `L = 2^a` slots, together with labels
`ϕ(u) = rowLabel u` and `ψ(w) = colLabel w` in `{1, …, 64}^a` for the row and column vertices.
The level-`k` group of a vertex is its `k`-th symbol.

**Formalization Note.** The symbols `{1, …, 64}` are `Fin 64`; coordinates `k < a` are
`Fin a`. -/
structure Packing (U W E : Type*) (a : ℕ) extends Placement E a where
  /-- the label `ϕ(u)` of a row vertex -/
  rowLabel : U → Fin a → Fin 64
  /-- the label `ψ(w)` of a column vertex -/
  colLabel : W → Fin a → Fin 64

namespace Packing

variable {U W E : Type*} {a : ℕ}

/-- **Orientation** (Lemma A.9(a), p.60): every packet has, for each coordinate `k < a`, two
symbols `g_k, g′_k` (possibly equal); the row vertex at slot `x` has `k`-th symbol `g_k` if
`x_k = 0` and `g′_k` if `x_k = 1`, and the column vertex at slot `y` has `k`-th symbol `g′_k` if
`y_k = 0` and `g_k` if `y_k = 1`. Here `rowOf e`, `colOf e` are the row and column vertex of the
edge `e`, which sits at slot `slot e`. -/
def Orientation (rowOf : E → U) (colOf : E → W) (pk : Packing U W E a) : Prop :=
  ∀ P : Fin pk.np, ∀ k : Fin a, ∃ g g' : Fin 64, ∀ e, pk.packet e = P →
    pk.rowLabel (rowOf e) k = (if (pk.slot e : ℕ).testBit k then g' else g) ∧
    pk.colLabel (colOf e) k = (if (pk.slot e : ℕ).testBit k then g else g')

/-- The "in particular" clause of Lemma A.9(a): if `v₂(y − x) = k`, the row vertex at slot `x`
and the column vertex at slot `y` of the same packet have the same `k`-th symbol. -/
def SameSymbolOnShift (rowOf : E → U) (colOf : E → W) (pk : Packing U W E a) : Prop :=
  ∀ e f, pk.packet e = pk.packet f → pk.slot e ≠ pk.slot f → ∀ k : Fin a,
    padicValInt 2 ((pk.slot f : ℤ) - (pk.slot e : ℤ)) = k →
    pk.rowLabel (rowOf e) k = pk.colLabel (colOf f) k

/-- **Small groups** (Lemma A.9(b), p.61): for every coordinate `k` and symbol `g`, at most
`3M/64` edges have a row vertex whose `k`-th symbol is `g`, and at most `3M/64` have a column
vertex whose `k`-th symbol is `g` (`M` the number of edges). -/
def SmallGroups [Fintype E] (rowOf : E → U) (colOf : E → W) (pk : Packing U W E a) : Prop :=
  ∀ (k : Fin a) (g : Fin 64),
    ((Finset.univ.filter fun e => pk.rowLabel (rowOf e) k = g).card : ℝ) ≤
        3 * Fintype.card E / 64 ∧
      ((Finset.univ.filter fun e => pk.colLabel (colOf e) k = g).card : ℝ) ≤
        3 * Fintype.card E / 64

/-- **Few packets** (Lemma A.9, p.60): at most `3M/L` packets. -/
def FewPackets [Fintype E] (pk : Packing U W E a) : Prop :=
  (pk.np : ℝ) ≤ 3 * Fintype.card E / 2 ^ a

end Packing

/-- A bipartite multigraph on `Fin nr` row vertices and `Fin nc` column vertices with edges
`Fin M` (the structure of a bipartite network, without tables), as handed to the packing
algorithm of Lemma A.9. -/
structure BipGraph where
  /-- number of row vertices -/
  nr : ℕ
  /-- number of column vertices -/
  nc : ℕ
  /-- number of edges -/
  M : ℕ
  /-- row endpoint of each edge -/
  rowOf : Fin M → Fin nr
  /-- column endpoint of each edge -/
  colOf : Fin M → Fin nc

namespace BipGraph

/-- The input of the packing algorithm: the graph (sizes and edge list in unary), `a` and `∆`
in unary. -/
def inputWord (G : BipGraph) (a Δ : ℕ) : List Bool :=
  Encoding.encodeList id
    [Encoding.encodeNat G.nr, Encoding.encodeNat G.nc, Encoding.encodeNat G.M,
      Encoding.encodeNat a, Encoding.encodeNat Δ,
      Encoding.encodeList (fun e : Fin G.M => Encoding.encodeNat (G.rowOf e) ++
        Encoding.encodeNat (G.colOf e)) (List.finRange G.M)]

/-- The output of the packing algorithm: the labels of the row and column vertices (each as
the list of its `a` symbols), the number of packets, and, for each edge, its packet and slot. -/
def packingWord (G : BipGraph) {a : ℕ} (pk : Packing (Fin G.nr) (Fin G.nc) (Fin G.M) a) :
    List Bool :=
  Encoding.encodeList id
    [Encoding.encodeList (fun u : Fin G.nr => Encoding.encodeList
        (fun k : Fin a => Encoding.encodeNat (pk.rowLabel u k)) (List.finRange a))
        (List.finRange G.nr),
      Encoding.encodeList (fun w : Fin G.nc => Encoding.encodeList
        (fun k : Fin a => Encoding.encodeNat (pk.colLabel w k)) (List.finRange a))
        (List.finRange G.nc),
      Encoding.encodeNat pk.np,
      Encoding.encodeList (fun e : Fin G.M => Encoding.encodeNat (pk.packet e) ++
        Encoding.encodeNat (pk.slot e)) (List.finRange G.M)]

end BipGraph

end ContractionLemma


