-- Prove2me | Definitions.Def_FlowAllocationGames_UnitRanking_Game
-- name    : FlowAllocationGames_UnitRanking_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:02:36.642202+00:00
-- url     : https://prove2.me/theorems/3abd77c9-41ec-461e-a847-4c817978560c
-- title:
--   Flow allocation game
-- statement:
--   A **flow allocation game** $\Gamma = (G, (b_v)_{v\in V}, (c_e)_{e\in E})$ consists of a directed graph $G = (V, E)$ with $n$ nodes and $m$ edges, a **fixed supply** $b_v \in \mathbb{Z}_{\ge 0}$ for every node $v$ and a **capacity** $c_e \in \mathbb{Z}_{\ge 0}$ for every edge $e$. Every node is a player. An edge $e = (u, v)$ has tail $u$ and head $v$, and $c_e$ is the maximum amount of flow that $u$ can forward to $v$.
--
--   In financial terms, $b_v$ is the external assets of firm $v$ and an edge $(u, v)$ is a liability of value $c_e$ of $u$ to $v$. All numbers are integers in binary encoding. Every object of the mission is defined over this structure.
--
--   **Formalization Note** Nodes are $\{0,\dots,n-1\}$ and edges $\{0,\dots,m-1\}$, each edge carrying its tail and head. This allows parallel edges and self-loops, which the paper's graph does not have, and allows $n = 0$ or $m = 0$.
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 9

import Mathlib

namespace FlowAllocationGames.UnitRanking

/-- **Flow allocation game** (network model).
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 9:
"In a flow allocation game Γ = (G, (bv)v∈V, (ce)e∈E) we are given a graph G = (V, E) with a node
set V and a set of directed edges E. Each node v ∈ V corresponds to a player and has a fixed supply
bv ≥ 0. The capacity ce ≥ 0 of an edge e = (u, v) is the maximum amount of flow that u can forward
to v." … "we will assume that all numbers in the input, i.e., all bv and ce, are integer numbers in
binary encoding."

A game with `n` players and `m` edges: edge `e : Fin m` goes from `tail e` to `head e`, has
capacity `c e`, and player `v : Fin n` has fixed supply `b v`.

**Formalization Note.** Nodes are `Fin n` and edges `Fin m`, both 0-based. Indexing edges by
`Fin m` allows parallel edges and self-loops (a generalization of the paper's graph `G = (V, E)`);
`n = 0` and `m = 0` are allowed. Supplies and capacities are natural numbers, the paper's
nonnegative integers. -/
structure Game (n m : ℕ) where
  /-- The tail (owner) of each edge. -/
  tail : Fin m → Fin n
  /-- The head of each edge. -/
  head : Fin m → Fin n
  /-- The fixed supply `b_v` of each player. -/
  b : Fin n → ℕ
  /-- The capacity `c_e` of each edge. -/
  c : Fin m → ℕ

end FlowAllocationGames.UnitRanking


