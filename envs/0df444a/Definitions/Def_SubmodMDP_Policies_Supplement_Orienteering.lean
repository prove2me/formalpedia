-- Prove2me | Definitions.Def_SubmodMDP_Policies_Supplement_Orienteering
-- name    : SubmodMDP_Policies_Supplement_Orienteering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:27:32.186191+00:00
-- url     : https://prove2.me/theorems/08c4bb5a-6d79-43fc-a164-415892122a74
-- title:
--   Directed orienteering walks, visited-set optimum and input formats
-- statement:
--   Let $G=(V,A)$ be a finite directed graph with specified vertices $s,t$. A walk is a nonempty finite vertex sequence beginning at $s$, ending at $t$, and following an arc at every step. Its reward and length are
--
--   $$f(W)=f(\{v:v\text{ occurs in }W\}),\qquad w(W)=\sum_{i=1}^{|W|-1}w(v_i,v_{i+1}).$$
--
--   Repeated visits count once for reward and with multiplicity for length. A singleton is a length-zero walk, so coincident endpoints are included. Rewards are nonnegative, monotone and submodular, without normalization. The optimum is the maximum reward among the finitely many visited sets achievable by admissible walks; the family of walks itself need not be finite. On infeasible inputs its default is zero, and every theorem excludes these inputs explicitly.
--
--   The graph uses Mathlib's general Digraph, independently of the orienteering data. Graph, length and path formats are integer lists. The oracle is supplied only to the published machine's query instruction. The parameter $k=\max\{1,\lceil2/\varepsilon\rceil\}$ is an integer; no machine receives a real accuracy parameter. These interfaces support both added companion theorems.
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), §1, p. 1 (PDF p. 2); §2.4, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Machine
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

namespace SubmodMDP.Policies.Supplement

noncomputable section
open Classical

/-- General directed orienteering data (§1, printed p. 1). The graph is the general Mathlib
`Digraph`, allowing loops; endpoints may coincide. Rewards and lengths are separate inputs. -/
structure Ori (n : ℕ) where
  graph : Digraph (Fin n)
  s : Fin n
  t : Fin n

/-- A finite vertex sequence is a walk between the specified endpoints. A singleton is a
zero-length walk. No simplicity, distinct-endpoint or positive-length assumption is imposed. -/
def Walk {n : ℕ} (G : Digraph (Fin n)) (s t : Fin n) (W : List (Fin n)) : Prop :=
  W.head? = some s ∧ W.getLast? = some t ∧ W.IsChain G.Adj

/-- Arc lengths with multiplicity, including repeated arcs; empty and singleton lists cost 0. -/
def walkLength {n : ℕ} (w : Fin n → Fin n → ℕ) (W : List (Fin n)) : ℕ :=
  ((W.zip W.tail).map (fun e => w e.1 e.2)).sum

/-- Nonnegative, monotone submodular rational rewards in the accepted finite oracle model.
There is no normalization or magnitude bound. -/
def Reward {n : ℕ} (f : Finset (Fin n) → ℚ) : Prop :=
  (∀ X, 0 ≤ f X) ∧ SubsamplingSM.Offline.IsMonotoneSetFn (fun X => (f X : ℝ)) ∧
    NonmonotoneSubmod.Shared.Submodular (fun X => (f X : ℝ))

/-- The finitely many visited sets of feasible walks. The set of walks itself can be infinite. -/
def visitedSets {n : ℕ} (I : Ori n) (admissible : List (Fin n) → Prop) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun X => ∃ W, Walk I.graph I.s I.t W ∧ admissible W ∧ W.toFinset = X)

/-- Maximum over visited sets, with default 0 on infeasible inputs. All theorems require a
feasible walk; for nonnegative rewards this fold is the attained maximum, including f(∅)>0. -/
def optimum {n : ℕ} (I : Ori n) (f : Finset (Fin n) → ℚ)
    (admissible : List (Fin n) → Prop) : ℚ :=
  ((visitedSets I admissible).toList.map f).foldl max 0

/-- Graph/endpoints encoding. The general graph is unbundled from the paper-specific data.
The oracle table is never encoded or passed to a program as data. -/
def encOri {n : ℕ} (I : Ori n) : List ℤ :=
  [(n : ℤ), (I.s.val : ℤ), (I.t.val : ℤ)] ++
    (List.finRange n).flatMap (fun u => (List.finRange n).map
      (fun v => if I.graph.Adj u v then 1 else 0))

/-- Length entries only for actual arcs, in lexicographic endpoint order, then the budget. -/
def encWeighted {n : ℕ} (I : Ori n) (w : Fin n → Fin n → ℕ) (C : ℕ) : List ℤ :=
  encOri I ++ ((List.finRange n).flatMap (fun u =>
    ((List.finRange n).filter (fun v => I.graph.Adj u v)).map (fun v => (w u v : ℤ)))) ++ [(C : ℤ)]

/-- ⟨w⟩: total binary encoding length of the arc-length values (one bit for zero). -/
def sizeW {n : ℕ} (I : Ori n) (w : Fin n → Fin n → ℕ) : ℕ :=
  ∑ u, ∑ v ∈ Finset.univ.filter (fun v => I.graph.Adj u v), max 1 (Nat.size (w u v))

/-- Path output format: the length followed by the vertex indices, consuming all input. -/
def encWalk {n : ℕ} (W : List (Fin n)) : List ℤ :=
  [(W.length : ℤ)] ++ W.map (fun v => (v.val : ℤ))

def decodeWalk (n : ℕ) (σ : List ℤ) : Option (List (Fin n)) :=
  parseAll (do let k ← pNat; (List.range k).mapM (fun _ => pFin n)) σ

/-- Integer exponent parameter; ε itself is never supplied to the RAM as a real value. -/
def epsK (ε : ℝ) : ℕ := max 1 ⌈2 / ε⌉₊

/-- Envelopes for the source's two asymptotic running times. -/
def polyTime (n k c : ℕ) : ℕ := (n + 1) ^ (c * k)

def logTime (n c : ℕ) : ℕ := ⌈(n + 1 : ℝ) ^ ((c : ℝ) * (Real.logb 2 n + 1))⌉₊

end
end SubmodMDP.Policies.Supplement


