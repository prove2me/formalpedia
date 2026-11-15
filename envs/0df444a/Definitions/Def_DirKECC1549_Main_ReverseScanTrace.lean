-- Prove2me | Definitions.Def_DirKECC1549_Main_ReverseScanTrace
-- name    : DirKECC1549_Main_ReverseScanTrace
-- status  : Definition
-- author  : @parclytaxel
-- created : 2026-11-14T15:49:42.706774+00:00
-- url     : https://prove2.me/theorems/57ff2b9b-d8d9-4d74-9451-5339f33cb17f
-- title:
--   Abstract reverse edge-scan traces with discovery order and parent updates
-- statement:
--   For a directed multigraph G and a root r, this inductive relation describes finite reverse-search traces. A trace state consists of a vertex-valued parent map P, a list L of discovered vertices, and a set S of scanned edges.
--
--   The initial state is
--
--   $$
--   P=\mathrm{id},\qquad L=[r],\qquad S=\varnothing.
--   $$
--
--   A scan of an edge e=(u,v) is permitted when v already belongs to L. If u belongs to L, the scan only inserts e into S. Otherwise it assigns P(u)=v, appends u to L, and inserts e into S:
--
--   $$
--   (P,L,S)\longmapsto(P[u\mapsto v],\ L\mathbin{+\!+}[u],\ S\cup\{e\}).
--   $$
--
--   Repeated edge scans are permitted. The relation records only finite discovery and parent-update histories; it imposes no scheduling, completion, machine-representation, or running-time condition. It provides the abstract transition system against which the fixed Word-RAM scan loop is to be verified.
-- source:
--   Semantic abstraction of instructions 87–110 of reverseSearchAlgorithm in Definitions.Def_DirKECC1549_Main_ReverseSearchCode, for the partial-correctness obligation https://prove2.me/theorems/c2a72733-62b4-4cbf-9796-d1e147e7ced3. The graph edge identities and directions use Definitions.Def_DirKECC1549_Main_Graph.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main

/-- Finite traces of reverse edge scans. A scan examines an edge whose head has been
found. If its tail is new, the tail is appended and its parent becomes that head.
The edge set records all edges examined so far; repeated scans are permitted. -/
inductive ReverseScanTrace {n m : ℕ} (G : Fin m → Fin n × Fin n) (r : Fin n) :
    (Fin n → Fin n) → List (Fin n) → Finset (Fin m) → Prop
  | initial : ReverseScanTrace G r id [r] ∅
  | seen {par order scanned} (trace : ReverseScanTrace G r par order scanned)
      (e : Fin m) (head_found : (G e).2 ∈ order) (tail_found : (G e).1 ∈ order) :
      ReverseScanTrace G r par order (insert e scanned)
  | fresh {par order scanned} (trace : ReverseScanTrace G r par order scanned)
      (e : Fin m) (head_found : (G e).2 ∈ order) (tail_new : (G e).1 ∉ order) :
      ReverseScanTrace G r (Function.update par (G e).1 (G e).2)
        (order ++ [(G e).1]) (insert e scanned)

end DirKECC1549.Main


