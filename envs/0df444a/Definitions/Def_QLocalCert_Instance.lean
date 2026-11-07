-- Prove2me | Definitions.Def_QLocalCert_Instance
-- name    : QLocalCert_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:14.331753+00:00
-- url     : https://prove2.me/theorems/12a27c8d-093a-48be-a570-a520589a2fb4
-- title:
--   Network instance: connected graph on $n$ nodes with identifiers in $[U]$ and port numbers
-- statement:
--   An **instance** of a graph property on $n$ nodes with identifier bound $U$ consists of
--   1. a connected simple graph $G$ on the node set $\{0,\dots,n-1\}$;
--   2. distinct identifiers $\mathrm{id}(v)\in[U]$, one per node;
--   3. for each node $v$, a numbering of its incident edges by distinct local ports $0,\dots,\deg(v)-1$; the port numbers at the two ends of an edge are independent.
--
--   The paper's sentence (§2.1, p.15): each node knows its own distinct identifier $\mathrm{id}(v)\in[U]$, its incident edges have distinct local port numbers $1,\dots,\deg(v)$, and the port numbers at opposite ends of an edge need not agree. A graph property has no further inputs. A protocol must be correct on every instance, that is, for every graph, every identifier assignment and every port numbering.
--
--   **Formalization Note** Ports are 0-based: port $p$ of $v$ leads to the $p$-th entry of the duplicate-free neighbour list `nbr v`. `backPort u p` is the port of the neighbour $v$ reached through port $p$ of $u$ that leads back to $u$. Identifiers are an injective map into `Fin U`.
-- source:
--   Jauregui, Miyamoto, Quantum Advantage in Local Certification of Graph Properties, STOC 2027 submission (manuscript sha256 b707143b1ab5511bef4c2b77e1b803f28b32cced25a008516898fd11d28c0451), §2, p.14 (graphs connected); §2.1, p.15 (instances, identifiers, ports)

import Mathlib

set_option autoImplicit false

namespace QLocalCert

/-- A network instance for a graph property on `n` nodes with identifier bound `U`.

B. Jauregui, M. Miyamoto, *Quantum Advantage in Local Certification of Graph Properties*,
STOC 2027 submission (manuscript sha256 b707143b…0c51), §2, p.14 ("All graphs are finite, simple,
undirected, and connected") and §2.1, p.15: "An instance is a pair I = (G, x), where G = (V, E) is
a connected graph with n = |V| nodes … For a graph property, there are no additional inputs …
Each node v knows its local input and its own distinct identifier id(v) ∈ [U] … Its incident edges
have distinct local port numbers 1, . . . , deg(v); the port numbers at opposite ends of an edge need
not agree."

**Formalization Note.**
* Nodes are `Fin n`; the graph `G` is a connected simple graph on them. A graph property has no
  local inputs, so an instance is the graph together with its identifier and port assignments.
* Identifiers are an injective map `id : Fin n → Fin U` (`[U]` is 0-based here).
* The port numbering of `v` is the duplicate-free list `nbr v` of the neighbours of `v`: port `p`
  (0-based, `p < deg v`) of `v` leads to `nbr v [p]`. Port numbers at the two ends of an edge are
  independent of each other.
* Correctness of a protocol is always required for **every** instance, i.e. for every graph,
  every identifier assignment and every port numbering. -/
structure Instance (n U : ℕ) where
  /-- The communication graph. -/
  G : SimpleGraph (Fin n)
  /-- The graph is connected. -/
  connected : G.Connected
  /-- The identifier of each node. -/
  id : Fin n → Fin U
  /-- Identifiers are distinct. -/
  id_injective : Function.Injective id
  /-- The neighbours of each node, listed in port order. -/
  nbr : Fin n → List (Fin n)
  /-- Distinct ports lead to distinct neighbours. -/
  nbr_nodup : ∀ v, (nbr v).Nodup
  /-- The ports of `v` lead exactly to the neighbours of `v`. -/
  mem_nbr : ∀ v u, u ∈ nbr v ↔ G.Adj v u

namespace Instance

variable {n U : ℕ} (I : Instance n U)

/-- The degree of `v`, i.e. its number of ports. -/
def deg (v : Fin n) : ℕ := (I.nbr v).length

/-- The neighbour reached from `v` through port `p`. -/
def port (v : Fin n) (p : Fin (I.deg v)) : Fin n := (I.nbr v).get p

/-- If `u` reaches `v := port u p` through its port `p`, then `backPort u p` is the port of `v`
that leads back to `u`, i.e. the port on which `v`'s message to `u` leaves and on which `u`'s
message arrives at `v`. -/
def backPort (u : Fin n) (p : Fin (I.deg u)) : Fin (I.deg (I.port u p)) :=
  ⟨(I.nbr (I.port u p)).idxOf u,
    List.idxOf_lt_length_of_mem ((I.mem_nbr _ _).2 ((I.mem_nbr _ _).1 (List.get_mem _ _)).symm)⟩

end Instance

end QLocalCert


