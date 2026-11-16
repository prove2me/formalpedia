-- Prove2me | Definitions.Def_MinCostArbPacking_Main_Supplement_Pseudoforest
-- name    : MinCostArbPacking_Main_Supplement_Pseudoforest
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:44:58.365758+00:00
-- url     : https://prove2.me/theorems/89992b09-9457-49dc-8d06-188eb7965bc4
-- title:
--   Multigraph pseudoforests, their k-fold unions and ordered greedy scans
-- statement:
--   Let G have vertices 0,…,n−1 and distinct edge identities 0,…,m−1, each with two endpoints. A component is undirected reachability using the selected edges. A pseudoforest X has at most as many edges as vertices in each component, so loops count as one cycle and a parallel pair as a cycle of length two. Independence in the k-fold pseudoforest system means a disjoint partition into k such sets:
--
--   $$X=F_0\mathbin{\dot\cup}\cdots\mathbin{\dot\cup}F_{k-1}.$$
--
--   An arbitrary strict total order is encoded by a permutation enumerating all edge identities once. The greedy scan starts empty and inserts an encountered member of X precisely when the insertion is independent. The same scan and order serve both graphic and pseudoforest independence in Lemma 6.2. These definitions assert no greedy optimality or inclusion.
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §6.2, Eq. (6.2), §6.2.1, p. 28–29

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph
set_option autoImplicit false
noncomputable section
open Classical

namespace MinCostArbPacking.Main.Supplement

/-! Zhou, STOC 2027 submission #1416, §6.2, pp.28–29, Eq. (6.2), Lemma 6.2.
Components and their edge counts retain loop and parallel-edge identities. -/

/-- The vertex component of v in the undirected edge set X. -/
def component {n m : ℕ} (G : Digraph (Fin n) (Fin m)) (X : Finset (Fin m))
    (v : Fin n) : Finset (Fin n) := Finset.univ.filter (G.Conn X v)

/-- Every connected component has at most as many edges as vertices (at most one cycle). -/
def IsPseudoforest {n m : ℕ} (G : Digraph (Fin n) (Fin m)) (X : Finset (Fin m)) : Prop :=
  ∀ v : Fin n, (G.induced X (component G X v)).card ≤ (component G X v).card

/-- A disjoint partition into k actual pseudoforests. -/
def PseudoDecomp {n m : ℕ} (G : Digraph (Fin n) (Fin m)) (k : ℕ)
    (X : Finset (Fin m)) (F : Fin k → Finset (Fin m)) : Prop :=
  (∀ i, IsPseudoforest G (F i)) ∧ (∀ i j, i ≠ j → Disjoint (F i) (F j)) ∧
    X = Finset.univ.biUnion F

/-- Independence in the k-fold pseudoforest matroid. -/
def PseudoIndepK {n m : ℕ} (G : Digraph (Fin n) (Fin m)) (k : ℕ)
    (X : Finset (Fin m)) : Prop := ∃ F, PseudoDecomp G k X F

/-- An arbitrary strict total edge order, encoded by its increasing enumeration. -/
def edgeOrder {m : ℕ} (ord : Equiv.Perm (Fin m)) : List (Fin m) :=
  (List.finRange m).map ord

/-- Scan X in the specified order, accepting exactly the independence-preserving insertions. -/
def greedy {m : ℕ} (ind : Finset (Fin m) → Prop) (ord : Equiv.Perm (Fin m))
    (X : Finset (Fin m)) : Finset (Fin m) :=
  (edgeOrder ord).foldl (fun S e => if e ∈ X ∧ ind (insert e S) then insert e S else S) ∅

end MinCostArbPacking.Main.Supplement


