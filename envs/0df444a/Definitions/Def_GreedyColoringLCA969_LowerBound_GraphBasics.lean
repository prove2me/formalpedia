-- Prove2me | Definitions.Def_GreedyColoringLCA969_LowerBound_GraphBasics
-- name    : GreedyColoringLCA969_LowerBound_GraphBasics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T09:42:42.758311+00:00
-- url     : https://prove2.me/theorems/feb1ea43-f8c8-44c2-bf8e-1547c5f5920b
-- title:
--   Simple-graph coloring, degree, girth and directed neighborhoods
-- statement:
--   Let $G$ be a finite simple undirected graph on $n$ labeled vertices. Colors are positive integers. A coloring $c$ is proper if adjacent vertices have different colors. It is greedy if it is proper and every vertex $v$ has a neighbor of each positive color smaller than $c(v)$:
--
--   $$\forall v\ \forall k\in\mathbb Z_{>0},\quad k<c(v)\Longrightarrow\exists u\in N_G(v),\ c(u)=k.$$
--
--   Maximum degree at most $\Delta$ means $|N_G(v)|\le\Delta$ at every vertex. Girth at least $g$ means every cycle has length at least $g$; forests satisfy this for every finite $g$. Every logarithm is base two. The separate directed relation used for Lemma 3.6 allows loops, and $N^+(u)$ is its set of out-neighbors, counting a loop once.
--
--   These concepts supply the graph language shared by the five results. Vertex identifiers use $\mathrm{Fin}(n)$, with one added to recover the source identifiers. Degrees and cycle lengths may be compared with real thresholds; no infinite-set cardinality is used.
--
--   Differences from the source:
--   - encoding: vertex identifiers [n] and positive integer colors → Fin n with zero-based identifiers and positive-integer color type; reason: adding one is a bijection on vertex identifiers; colors remain exactly positive integers
--   - encoding: girth at least a threshold → every cycle has length at least the threshold; reason: this agrees with extended girth, including infinite girth for forests
-- source:
--   Zi Song Yeoh, Krzysztof Onak, Dragos-Florian Ristache, STOC 2027 submission #969 (October 2026), §2.1, p.7 (PDF 8); §3, p.10 (PDF 11); Lemma 3.6, p.12 (PDF 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/969.pdf

import Mathlib

open scoped ENNReal
open MeasureTheory
open Classical

namespace GreedyColoringLCA969.LowerBound

/-- Section 2: every logarithm is base two. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Proper colorings use positive integers, with no predetermined color bound. -/
def IsProper {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℕ+) : Prop :=
  ∀ u v, G.Adj u v → c u ≠ c v

/-- Section 3: properness and the presence of every smaller positive color. -/
def IsGreedy {n : ℕ} (G : SimpleGraph (Fin n)) (c : Fin n → ℕ+) : Prop :=
  IsProper G c ∧ ∀ v (k : ℕ+), k < c v → ∃ u, G.Adj v u ∧ c u = k

/-- All neighbor sets here are finite; the cardinality has no infinite-set default. -/
def MaxDegreeAtMost {n : ℕ} (G : SimpleGraph (Fin n)) (Δ : ℝ) : Prop :=
  ∀ v, (Nat.card {u // G.Adj v u} : ℝ) ≤ Δ

/-- No cycle shorter than g; forests satisfy this for every real g. -/
def GirthAtLeast {n : ℕ} (G : SimpleGraph (Fin n)) (g : ℝ) : Prop :=
  ∀ v (p : G.Walk v v), p.IsCycle → g ≤ (p.length : ℝ)

/-- Lemma 3.6 uses a directed relation, allowing self-loops. -/
abbrev Digraph (N : ℕ) := Fin N → Fin N → Prop

noncomputable def outNeighbors {N : ℕ} (H : Digraph N) (u : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (H u)

end GreedyColoringLCA969.LowerBound


