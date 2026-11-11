-- Prove2me | Definitions.Def_QMCMatch_Defs
-- name    : QMCMatch_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T15:22:44.962116+00:00
-- url     : https://prove2.me/theorems/1f22f3e0-2113-429e-97d9-9188c1284687
-- title:
--   Matchings on the complete graph: exchange sets, components, maximum-weight matchings
-- statement:
--   Definitions for a proof of Edmonds' matching polytope theorem on the complete graph with vertex set $\{0,\dots,n-1\}$, using the campaign edge type (pairs $i<j$). `IsM M`: the edges of $M$ are pairwise vertex-disjoint. `cov F v`: $v$ is an endpoint of an edge of $F$. `adj F`, `comp F t`: adjacency and the set of vertices reachable from $t$ in the graph with edge set $F$. `inside F C`, `outside F C`: edges of $F$ with both endpoints in, respectively outside, $C$. `swp M N C`: the edge set that agrees with $M$ outside $C$ and with $N$ inside $C$. For integer weights $w$: `supp w` (edges of positive weight), `wt w M` (weight of $M$), `IsMax w M` (a maximum-weight matching among matchings of positive edges), `Sv w` (vertices on a positive edge), `Conn w` (the positive-weight graph is connected on `Sv w`).
-- source:
--   Supporting library for QuantumMaxCutEnergy.matching_polytope_integral_rounding (Prove2me Quantum Max-Cut campaign). Edmonds, Maximum matching and a polyhedron with 0,1-vertices, J. Res. Nat. Bur. Standards 69B, 1965; proof after Schrijver, Short proofs on the matching polyhedron, J. Combin. Theory Ser. B 34, 1983, and Combinatorial Optimization, Section 25.4 (Cunningham-Marsh formula).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Mathlib

/-!
Matchings on the complete graph with vertex set `Fin n`, in the edge type of the
Quantum Max-Cut campaign (`Edge n` = ordered pairs `i < j`).
-/

noncomputable section
open scoped BigOperators
open Classical
open QuantumMaxCutEnergy

namespace QMCMatch

variable {n : ℕ}

/-- Pairwise vertex-disjoint edge set. -/
def IsM (M : Finset (Edge n)) : Prop :=
  ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
    e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2

/-- `v` is an endpoint of some edge of `F`. -/
def cov (F : Finset (Edge n)) (v : Fin n) : Prop :=
  ∃ e ∈ F, v = e.val.1 ∨ v = e.val.2

/-- Adjacency in the graph with edge set `F`. -/
def adj (F : Finset (Edge n)) (a b : Fin n) : Prop :=
  ∃ e ∈ F, (a = e.val.1 ∧ b = e.val.2) ∨ (a = e.val.2 ∧ b = e.val.1)

/-- Vertices reachable from `t` along edges of `F`. -/
def comp (F : Finset (Edge n)) (t : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (adj F) t v)

/-- Edges of `F` with both endpoints in `C`. -/
def inside (F : Finset (Edge n)) (C : Finset (Fin n)) : Finset (Edge n) :=
  F.filter (fun e => e.val.1 ∈ C ∧ e.val.2 ∈ C)

/-- Edges of `F` with both endpoints outside `C`. -/
def outside (F : Finset (Edge n)) (C : Finset (Fin n)) : Finset (Edge n) :=
  F.filter (fun e => e.val.1 ∉ C ∧ e.val.2 ∉ C)

/-- Keep `M` outside `C` and take `N` inside `C`. -/
def swp (M N : Finset (Edge n)) (C : Finset (Fin n)) : Finset (Edge n) :=
  outside M C ∪ inside N C

/-- Edges of positive weight. -/
def supp (w : Edge n → ℕ) : Finset (Edge n) :=
  Finset.univ.filter (fun e => 0 < w e)

/-- Weight of an edge set. -/
def wt (w : Edge n → ℕ) (M : Finset (Edge n)) : ℕ := ∑ e ∈ M, w e

/-- A maximum-weight matching among matchings of positive-weight edges. -/
def IsMax (w : Edge n → ℕ) (M : Finset (Edge n)) : Prop :=
  IsM M ∧ M ⊆ supp w ∧ ∀ M', IsM M' → M' ⊆ supp w → wt w M' ≤ wt w M

/-- Vertices that meet a positive-weight edge. -/
def Sv (w : Edge n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => cov (supp w) v)

/-- The positive-weight graph is connected on its non-isolated vertices. -/
def Conn (w : Edge n → ℕ) : Prop :=
  ∀ u ∈ Sv w, ∀ v ∈ Sv w, Relation.ReflTransGen (adj (supp w)) u v

end QMCMatch


