-- Prove2me | Definitions.Def_HopRamsey_hopStochEmbedding
-- name    : HopRamsey_hopStochEmbedding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:12.813525+00:00
-- url     : https://prove2.me/theorems/d30a9dca-acd2-4891-863a-9fbf85593e4f
-- title:
--   Algorithm 1: Hop-Stochastic-Embedding$(G,X,M,h,\Delta)$
-- statement:
--   Algorithm 1 builds a random HST $U$ over the active set $X$ and a saved set $\hat M$. If $|X|=1$ it returns the one-leaf HST and $\hat M=M$. Otherwise it calls Single-Scale-Partition$(G,X,M,h,\Delta)$, obtaining clusters $(X_i,M_i)_{i=0}^s$, recursively runs Hop-Stochastic-Embedding$(G,X_i,M_i,h,\Delta/2)$ with independent randomness to get $(U_i,\hat M_i)$, and returns the HST with a root of label $\Delta$ whose children are $U_0,\dots,U_s$, together with $\hat M=\bigcup_i\hat M_i$. So $d_U(u,v)=\Delta$ when $u,v$ lie in different clusters and $d_U(u,v)=d_{U_i}(u,v)$ when both lie in $X_i$. The root call is Hop-Stochastic-Embedding$(G,V,V,h,\Phi)$.
--
--   **Formalization Note** The output is the law of $(d_U,\hat M)$, with $d_U:V\times V\to[0,\infty]$ equal to $\infty$ off $X$. The recursion depth is cut at $\lceil\log_2\Delta\rceil_+ +2$; under the call invariant and minimum edge weight $2$ only singleton calls remain at that depth, so the cut-off branch is never reached.
-- source:
--   Filtser, Zuzic, Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with Logarithmic Expected Distortion, STOC 2027 submission (manuscript sha256 1ee73385…), Algorithm 1, p.16 (PDF p.18); §4.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_singleScalePartition

open scoped ENNReal

namespace HopRamsey

open ARTreeCover

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Independent sampling of a list of laws: the law of the list of their outcomes. -/
noncomputable def seqPMF {α : Type} : List (PMF α) → PMF (List α)
  | [] => PMF.pure []
  | p :: ps => p.bind fun a => (seqPMF ps).map fun l => a :: l

/-- The ultrametric of the one-leaf HST on `X` (Algorithm 1, line 2): `0` on `X × X` (which is the
diagonal when `|X| ≤ 1`) and `∞` off `X`. -/
def leafMetric (X : Finset V) (u v : V) : ℝ≥0∞ :=
  if u ∈ X ∧ v ∈ X then 0 else ⊤

/-- Line 7 of Algorithm 1: the HST with a root of label `∆` whose children are the HSTs of the
clusters. For `u, v ∈ X` in a common cluster the value is that cluster's; for `u, v ∈ X` in
different clusters it is `∆`; off `X` it is `∞`. Line 8: the saved set is the union of the
children's saved sets. -/
noncomputable def combine (X : Finset V) (Δ : ℝ)
    (cs : List ((Finset V × Finset V) × ((V → V → ℝ≥0∞) × Finset V))) :
    (V → V → ℝ≥0∞) × Finset V :=
  (fun u v =>
    if u ∈ X ∧ v ∈ X then
      match cs.find? (fun c => decide (u ∈ c.1.1 ∧ v ∈ c.1.1)) with
      | some c => c.2.1 u v
      | none => ENNReal.ofReal Δ
    else ⊤,
   cs.foldr (fun c acc => c.2.2 ∪ acc) ∅)

/-- Algorithm 1 with an explicit recursion depth `fuel`. -/
noncomputable def hseFuel (P : Fig2Params) (G : WGraph V) (h : ℕ) (rule : CenterRule V) :
    ℕ → Finset V → Finset V → ℝ → PMF ((V → V → ℝ≥0∞) × Finset V)
  | fuel, X, M, Δ =>
    if X.card ≤ 1 then PMF.pure (leafMetric X, M)
    else
      match fuel with
      | 0 => PMF.pure (fun u v => if u ∈ X ∧ v ∈ X then (if u = v then 0 else ENNReal.ofReal Δ)
          else ⊤, M)
      | fuel + 1 =>
        (singleScalePartition P G h rule X M Δ).bind fun C =>
          (seqPMF (C.map fun c => hseFuel P G h rule fuel c.1 c.2 (Δ / 2))).map fun outs =>
            combine X Δ (C.zip outs)

/-- Algorithm 1, `(U, M̂) = Hop-Stochastic-Embedding(G, X, M, h, ∆)`, as the law of its output: the
HST `U` over `X`, recorded by its ultrametric `d_U` on `V` (`∞` off `X`), and the saved set `M̂`.

Filtser, Zuzic, *Trees with Benefits: Stochastic Hop-Constrained Ramsey-Type Embeddings with
Logarithmic Expected Distortion*, STOC 2027 submission (manuscript sha256 1ee73385…), Algorithm 1,
p.16 (PDF p.18): "1 if |X| = 1 then 2 let U be the one-leaf HST on X 3 return (U,M) 4 let
((X_i,M_i)_{i=0}^s) = Single-Scale-Partition(G,X,M,h,∆) 5 foreach i ∈ {0,1,...,s} do 6 (U_i, M̂_i) =
Hop-Stochastic-Embedding(G,X_i,M_i,h,∆/2) 7 let U be the HST formed by taking a root r_U with label
∆, and setting the HSTs U_0,U_1,...,U_s as its children 8 M̂ = ⋃_{i=0}^s M̂_i 9 return (U, M̂)".

**Formalization Note.**
1. The recursive calls use independent randomness (`seqPMF`), as in the paper ("fresh independent
   randomness", p.20).
2. The recursion depth is cut at `⌈log₂ ∆⌉₊ + 2`. Under the call invariant
   `diam^{(2k(L+1)h)}_G(X) ≤ ∆` with minimum edge weight `2`, a call with `|X| ≥ 2` has `∆ ≥ 2`,
   and every child call has scale `∆/2` (Corollary 1), so after `⌈log₂ ∆⌉₊ + 2` halvings only
   singleton calls remain and the cut-off branch (which returns label `∆` between distinct
   vertices of `X` and `M̂ = M`) is never reached.
3. The base case is `|X| ≤ 1`; the empty set never occurs as a call (clusters are nonempty), and
   on it the base case returns the empty HST. -/
noncomputable def hopStochEmbedding (P : Fig2Params) (G : WGraph V) (h : ℕ)
    (rule : CenterRule V) (X M : Finset V) (Δ : ℝ) : PMF ((V → V → ℝ≥0∞) × Finset V) :=
  hseFuel P G h rule (⌈Real.logb 2 Δ⌉₊ + 2) X M Δ

end HopRamsey


