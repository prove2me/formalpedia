-- Prove2me | Definitions.Def_HararySachs_Hyper_Digraph
-- name    : HararySachs_Hyper_Digraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T12:35:47.972116+00:00
-- url     : https://prove2.me/theorems/25a9baeb-008f-41ba-8572-9bb27e15ca0c
-- title:
--   Definitions 3–5 and Theorem 5 — directed multigraph degrees and arborescences
-- statement:
--   A directed multigraph on $[n]$ is represented by the number $m(u,v)$ of distinguishable arcs from $u$ to $v$. Its in-degree and out-degree are the corresponding sums of multiplicities. An Eulerian digraph has at least one arc, balanced degrees, and weakly connected vertices of positive degree.
--
--   $$\tau(D)=\sum_{p}\prod_{u\ne r}m(u,p(u)),$$
--
--   where $r$ is the least vertex of positive degree and the sum is over parent maps whose directed parent chains reach $r$. Thus parallel arcs contribute their multiplicities to the count of arborescences oriented toward $r$. These objects are used in the weights of Veblen hypergraphs and in Euler-tour counting.
--
--   **Formalization Note** Isolated vertices are ignored when selecting the root and forming the product. The least active vertex makes the otherwise unspecified root of the paper's $\tau(D)$ deterministic.
-- source:
--   Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, pp. 5–6, Definitions 3–5 and Theorem 5

import Mathlib

namespace HararySachs.Hyper

abbrev ArcMult (n : ℕ) := Fin n → Fin n → ℕ

def outDeg {n : ℕ} (m : ArcMult n) (u : Fin n) : ℕ :=
  ∑ v : Fin n, m u v

def inDeg {n : ℕ} (m : ArcMult n) (v : Fin n) : ℕ :=
  ∑ u : Fin n, m u v

def active {n : ℕ} (m : ArcMult n) : Finset (Fin n) :=
  Finset.univ.filter (fun v => 0 < outDeg m v + inDeg m v)

def WeakAdjacent {n : ℕ} (m : ArcMult n) (u v : Fin n) : Prop :=
  0 < m u v ∨ 0 < m v u

def IsEulerian {n : ℕ} (m : ArcMult n) : Prop :=
  (active m).Nonempty ∧
  (∀ v : Fin n, outDeg m v = inDeg m v) ∧
  ∀ u ∈ active m, ∀ v ∈ active m,
    Relation.ReflTransGen (WeakAdjacent m) u v

def IsTowardTree {n : ℕ} (m : ArcMult n) (r : Fin n)
    (p : Fin n → Fin n) : Prop :=
  p r = r ∧
  (∀ u ∉ active m, p u = u) ∧
  ∀ u ∈ (active m).erase r,
    p u ∈ active m ∧ p u ≠ u ∧ ∃ t ≤ n, (p^[t]) u = r

noncomputable def numArbAt {n : ℕ} (m : ArcMult n) (r : Fin n) : ℕ := by
  classical
  exact ∑ p : Fin n → Fin n,
    if IsTowardTree m r p then
      ∏ u ∈ (active m).erase r, m u (p u)
    else 0

noncomputable def numArb {n : ℕ} (m : ArcMult n) : ℕ :=
  ∑ r : Fin n,
    if r ∈ active m ∧ ∀ u ∈ active m, r ≤ u then numArbAt m r else 0

end HararySachs.Hyper


