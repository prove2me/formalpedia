-- Prove2me | Definitions.Def_ConstructiveArboricity_Exact_Supplement_StarNetwork
-- name    : ConstructiveArboricity_Exact_Supplement_StarNetwork
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:15:26.909277+00:00
-- url     : https://prove2.me/theorems/9aa3d748-13aa-4854-b408-59d075327b09
-- title:
--   The full star-insertion flow network with fixed input depths
-- statement:
--   Root every component of each input forest and orient its edges toward the root. Input depths decrease by one on outgoing original edges and are zero at vertices with no outgoing edge of that color. The network has terminals $s,t$ and vertices $q_x,q_{x,i}$ for $x\ne r$ and colors $i$.
--
--   Each star edge $rv$ supplies an arc $s\to q_v$ of capacity one. An original edge $x\to y$ of color $i$ gives $q_{x,i}\to q_{y,i}$ of capacity one. A free color at $x$ gives $q_{x,i}\to t$ of capacity one. For each $(x,i)$, the arcs $q_{x,i}\to q_x$ and $q_x\to q_{x,i}$ have capacity $m+1$; only the former has nonzero cost, namely $2m-d_i(x)$. Depths and costs refer to the input forests throughout.
--
--   The general network and integral-flow predicates are published definitions. Absent node-pair arcs have capacity zero. The maximum flow value is the supremum of the feasible integral values, a nonempty bounded finite set containing zero. It is computed from the network, not supplied as a certificate.
-- source:
--   Gholami, Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani and Shahrezaei, Constructive Arboricity in Almost-Linear Time for Dense Graphs, STOC 2027 submission #1476 (October 2026). This is the pinned submission, not an assertion of conference acceptance. §§2–5 and Appendix A, definition interface, PDF/printed p.18.

import Definitions.Def_ConstructiveArboricity_Exact_Supplement_Interface
import Definitions.Def_OmniThreshold_FlowNetwork
import Definitions.Def_OneTwoThree_Weighting_STFlow

/-! Definition 4.10, pp.18–19, with the input-rooting conventions of pp.14,17–18.
The general capacitated network and integral-flow notions are published imports.
Network values are computed from all feasible integral flows, never supplied
nonexistence certificates. Input depths and costs do not change during recoloring. -/
namespace ConstructiveArboricity.Exact.Supplement
noncomputable section
open Classical

/-- Choosing roots in the input forest components: depths decrease by one
on every oriented edge and are zero at vertices with no outgoing edge. -/
structure Rooting (G : Graph) {k : ℕ} {r : Fin G.n} (a : StarInput G k r) where
  tail : Fin G.m → Fin G.n
  oriented : G.IsOrientation tail
  depth : Fin k → Fin G.n → ℕ
  unique : ∀ i v, {e | a.color e = some i ∧ tail e = v}.Subsingleton
  decrease : ∀ e i, a.color e = some i → depth i (tail e) = depth i (G.head tail e) + 1
  rootZero : ∀ i v, (¬ ∃ e, a.color e = some i ∧ tail e = v) → depth i v = 0

abbrev NonRoot (G : Graph) (r : Fin G.n) := {v : Fin G.n // v ≠ r}

/-- s,t, q_x, q_(x,i), with x distinct from r. -/
abbrev StarNode (G : Graph) (k : ℕ) (r : Fin G.n) :=
  (Unit ⊕ Unit) ⊕ (NonRoot G r ⊕ (NonRoot G r × Fin k))

def sourceNode (G : Graph) (k : ℕ) (r : Fin G.n) : StarNode G k r := .inl (.inl ())
def sinkNode (G : Graph) (k : ℕ) (r : Fin G.n) : StarNode G k r := .inl (.inr ())
def qNode {G : Graph} {k : ℕ} {r : Fin G.n} (v : NonRoot G r) : StarNode G k r := .inr (.inl v)
def qcNode {G : Graph} {k : ℕ} {r : Fin G.n} (v : NonRoot G r) (i : Fin k) : StarNode G k r :=
  .inr (.inr (v,i))

/-- Finite node-pair carrier; absent arcs have zero capacity. The nonzero
capacity arcs are exactly Definition 4.10. Zero arcs carry no feasible flow. -/
def starCapacity (G : Graph) {k : ℕ} {r : Fin G.n} (a : StarInput G k r) (o : Rooting G a)
    (p : StarNode G k r × StarNode G k r) : ℕ :=
  match p with
  | (.inl (.inl _), .inr (.inl v)) =>
      if ∃ e ∈ starEdges G r, G.edge e = s(r, v.val) then 1 else 0
  | (.inr (.inr (x,i)), .inr (.inr (y,j))) =>
      if i = j ∧ ∃ e, a.color e = some i ∧ o.tail e = x.val ∧ G.head o.tail e = y.val then 1 else 0
  | (.inr (.inr (x,i)), .inl (.inr _)) =>
      if ¬ ∃ e, a.color e = some i ∧ o.tail e = x.val then 1 else 0
  | (.inr (.inr (x,_)), .inr (.inl y)) => if x = y then G.m + 1 else 0
  | (.inr (.inl x), .inr (.inr (y,_))) => if x = y then G.m + 1 else 0
  | _ => 0

def starNetwork (G : Graph) {k : ℕ} {r : Fin G.n} (a : StarInput G k r) (o : Rooting G a) :
    OmniThreshold.FlowNetwork (StarNode G k r) (StarNode G k r × StarNode G k r) where
  tail := Prod.fst
  head := Prod.snd
  cap := starCapacity G a o
  cost := fun p => match p with
    | (.inr (.inr (x,i)), .inr (.inl y)) =>
        if x = y then (2 * G.m : ℤ) - (o.depth i x.val : ℤ) else 0
    | _ => 0

/-- All feasible flows form a nonempty finite set: each arc value lies in a
finite interval and the zero assignment is feasible. Nat sSup therefore has
neither the empty-set nor unbounded-set default. -/
def starFlowValue (G : Graph) {k : ℕ} {r : Fin G.n} (a : StarInput G k r) (o : Rooting G a) : ℕ :=
  let D := starNetwork G a o
  sSup {v : ℕ | ∃ f,
    OneTwoThree.Weighting.IsSTFlow D.tail D.head D.cap (sourceNode G k r) (sinkNode G k r) f ∧
    OneTwoThree.Weighting.flowValue D.tail D.head (sourceNode G k r) f = (v : ℤ)}

end
end ConstructiveArboricity.Exact.Supplement


