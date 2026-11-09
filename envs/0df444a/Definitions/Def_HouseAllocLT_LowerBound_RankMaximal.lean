-- Prove2me | Definitions.Def_HouseAllocLT_LowerBound_RankMaximal
-- name    : HouseAllocLT_LowerBound_RankMaximal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:04.842687+00:00
-- url     : https://prove2.me/theorems/8fbc4d79-9d09-4159-a696-e54a7f660c30
-- title:
--   Feasible matchings and the rank-maximal benchmark
-- statement:
--   At a reported profile $P$, a matching uses only acceptable agent–object edges and no vertex twice. Let $s_j(\mu;P)$ count its edges at rank $j$, and let $r(P)$ be the longest report. A rank-maximal matching lexicographically maximizes $(s_1,\ldots,s_{r(P)})$ among all feasible matchings. Its prefix benchmark is
--
--   $$R_h^*(P)=\sum_{j=1}^h s_j^*(P).$$
--
--   The maximum matching size $\nu(G(P))$ is defined separately. These are different objectives on general profiles.
--
--   **Formalization Note** The general bipartite matching predicate is reused from `TwoStageMatch_Bipartite`, with both vertex sets unrestricted and edge relation given by reported acceptability. Finite edge sets provide the ambient carrier; only feasible matchings enter the optimization. The prefix benchmark is the finite maximum of prefix counts among rank-maximal matchings. Finite lexicographic maxima exist and share one signature, so this is the source's value without choosing an algorithm.
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), §2, matchings, signatures and benchmark, PDF p. 6 (printed p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_TwoStageMatch_Bipartite
import Definitions.Def_HouseAllocLT_LowerBound_Preference

open scoped BigOperators
open Classical

namespace HouseAllocLT.LowerBound
noncomputable section

/-- Carrier for edge sets; the matching predicate below imposes both vertex constraints. -/
abbrev Assignment (n m : ℕ) := Finset (Fin n × Fin m)

/-- Reuses the general bipartite matching definition with reported acceptable edges. -/
def Feasible {n m : ℕ} (P : Profile n m) (μ : Assignment n m) : Prop :=
  TwoStageMatch.IsMatching (fun i a => Acceptable (P i) a) Finset.univ Finset.univ μ

/-- The finite nonempty set M(P), including the empty matching. -/
def feasibleMatchings {n m : ℕ} (P : Profile n m) : Finset (Assignment n m) :=
  TwoStageMatch.matchings (fun i a => Acceptable (P i) a) Finset.univ Finset.univ

def rankCount {n m : ℕ} (P : Profile n m) (μ : Assignment n m) (j : ℕ) : ℕ :=
  (μ.filter (fun e => e.2 ∈ (P e.1).classes j)).card

def rankLength {n m : ℕ} (P : Profile n m) : ℕ :=
  Finset.univ.sup (fun i => (P i).length)

def prefixCount {n m : ℕ} (P : Profile n m) (μ : Assignment n m) (h : ℕ) : ℕ :=
  ∑ j ∈ Finset.range h, rankCount P μ j

/-- Lexicographic optimality among every feasible matching, not maximum cardinality. -/
def RankMaximal {n m : ℕ} (P : Profile n m) (μ : Assignment n m) : Prop :=
  Feasible P μ ∧ ∀ ν, Feasible P ν →
    LexGE (rankLength P) (rankCount P μ) (rankCount P ν)

/-- All rank-maximal matchings have the same signature; hence this finite maximum
is exactly the prefix count of any one of them. Finite lexicographic maxima exist. -/
def benchmarkPrefix {n m : ℕ} (P : Profile n m) (h : ℕ) : ℕ :=
  ((feasibleMatchings P).filter (RankMaximal P)).sup (fun μ => prefixCount P μ h)

def maximumSize {n m : ℕ} (P : Profile n m) : ℕ :=
  (feasibleMatchings P).sup Finset.card

end
end HouseAllocLT.LowerBound


