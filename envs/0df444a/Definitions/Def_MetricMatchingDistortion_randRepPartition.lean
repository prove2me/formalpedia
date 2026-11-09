-- Prove2me | Definitions.Def_MetricMatchingDistortion_randRepPartition
-- name    : MetricMatchingDistortion_randRepPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:42.300451+00:00
-- url     : https://prove2.me/theorems/50b8034a-c27d-4f33-9892-2a55fb25d380
-- title:
--   Algorithm 2 (RandRepPartition): the random balanced partition
-- statement:
--   Let $\theta=\log_2(3/2)$ and $z(p,q)=(1+q/p)^\theta-1$. Each current agent cluster $S$ has a representative $r_S\in S$ and claims $\mathrm{Top}(r_S,|S|)$. **RandRepPartition** starts with singleton clusters $\{a\}$ represented by $a$. While two claimed prefixes overlap, a selection rule chooses two such clusters $S,T$ with $p=|S|\ge q=|T|$; they merge, keeping $r_T$ with probability $z(p,q)$ and $r_S$ otherwise, and the retained representative claims its first $p+q$ items. When the claimed prefixes are disjoint, the output is $\mathcal P=(A_j,B_j)_j$ with $A_j$ the final clusters and $B_j=\mathrm{Top}(r_{A_j},|A_j|)$.
--
--   The definition gives the law of the output as a probability distribution over labellings, for a given selection rule.
--
--   **Formalization Note** The state is the map sending each agent to its representative. A run is $n$ merge steps (a run has at most $n-1$ merges; a step whose proposed merge is not admissible changes nothing). The coin of probability $z$ is clamped to $[0,1]$, which changes nothing since $0<z(p,q)\le 1/2$ for $p\ge q\ge 1$.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §3.2, p.15 (PDF p.17), Algorithm 2

import Mathlib
import Definitions.Def_MetricMatchingDistortion_Ranking

namespace MetricMatchingDistortion

open Finset

/-- `θ = log₂(3/2)`. Charikar et al., *Sublinear Metric Distortion for Matching*, arXiv:2611.05777
(held version, sha256 fdf3452b…), §3.2, p.15 (PDF p.17): "where θ = log2(3/2)". -/
noncomputable def theta : ℝ := Real.logb 2 (3 / 2)

/-- The probability of keeping the smaller cluster's representative (§3.2, p.15):
"If their sizes are p ≥ q, keep the smaller cluster's representative with probability
z(p, q) = (1 + q/p)^θ − 1." -/
noncomputable def zProb (p q : ℕ) : ℝ := (1 + (q : ℝ) / p) ^ theta - 1

/-- A coin showing `true` with probability `z`. For `z ∈ [0, 1]` (in particular for
`z = z(p, q) ∈ (0, 1/2]` with `p ≥ q ≥ 1`) it is the Bernoulli(`z`) law; the clamp to `[0, 1]`
only makes the expression total. -/
noncomputable def coin (z : ℝ) : PMF Bool :=
  PMF.ofFintype (fun b => if b then min (ENNReal.ofReal z) 1 else 1 - min (ENNReal.ofReal z) 1)
    (by simp [add_tsub_cancel_of_le (min_le_right _ _)])

variable {n : ℕ}

/-- The state of Algorithm 2 is a map `rep : Fin n → Fin n` sending each agent to the
representative of its current cluster; `r` represents a cluster when `rep r = r`. This is the
cluster represented by `r`. -/
def clusterOf (rep : Fin n → Fin n) (r : Fin n) : Finset (Fin n) := univ.filter fun a => rep a = r

/-- The claimed prefix `Top(r_S, |S|)` of the cluster `S` represented by `r` (§3.2, p.15: "Each
current agent cluster S ⊆ A has a representative r_S ∈ S and claims Top(r_S, |S|)"). -/
def claimed (rk : Ranking n) (rep : Fin n → Fin n) (r : Fin n) : Finset (Fin n) :=
  Top rk r (clusterOf rep r).card

/-- Two distinct current clusters, represented by `r` and `r'`, whose claimed prefixes overlap. -/
def Overlap (rk : Ranking n) (rep : Fin n → Fin n) (r r' : Fin n) : Prop :=
  r ≠ r' ∧ rep r = r ∧ rep r' = r' ∧ (claimed rk rep r ∩ claimed rk rep r').Nonempty

/-- An admissible merge `(S, T)` with `S` represented by `r`, `T` by `r'`: the prefixes overlap and
`p = |S| ≥ q = |T|` (Algorithm 2, p.15: "Choose such clusters S, T …, with p = |S| ≥ q = |T|"). -/
def ValidMerge (rk : Ranking n) (rep : Fin n → Fin n) (r r' : Fin n) : Prop :=
  Overlap rk rep r r' ∧ (clusterOf rep r').card ≤ (clusterOf rep r).card

/-- A selection rule proposes, from the current state, the pair `(r_S, r_T)` to merge. -/
abbrev SelectionRule (n : ℕ) := (Fin n → Fin n) → Option (Fin n × Fin n)

/-- "Choose such clusters S, T by a fixed rule" (Algorithm 2, p.15): whenever two claimed prefixes
overlap, the rule returns an admissible merge. What it returns otherwise is irrelevant. -/
def IsSelectionRule (rk : Ranking n) (rule : SelectionRule n) : Prop :=
  ∀ rep : Fin n → Fin n, (∃ r r', Overlap rk rep r r') →
    ∃ r r', rule rep = some (r, r') ∧ ValidMerge rk rep r r'

/-- Merge the clusters represented by `r` and `r'`, keeping the representative `keep`. -/
def mergeInto (rep : Fin n → Fin n) (r r' keep : Fin n) : Fin n → Fin n :=
  fun a => if rep a = r ∨ rep a = r' then keep else rep a

open Classical in
/-- One iteration of the loop of Algorithm 2 (p.15): "Merge them, keeping r_T with probability
z(p, q) and r_S otherwise. The retained representative claims its first p + q items." If the rule
proposes no admissible merge, the state is unchanged. -/
noncomputable def mergeStep (rk : Ranking n) (rule : SelectionRule n) (rep : Fin n → Fin n) :
    PMF (Fin n → Fin n) :=
  match rule rep with
  | none => PMF.pure rep
  | some (r, r') =>
    if ValidMerge rk rep r r' then
      (coin (zProb (clusterOf rep r).card (clusterOf rep r').card)).map
        fun keepT => mergeInto rep r r' (if keepT then r' else r)
    else PMF.pure rep

/-- The output labelling of a final state (Algorithm 2, p.15: "enumerate the final agent clusters
as A1, …, Am. Set Bj = Top(r_{Aj}, |Aj|) for each j"). Agent `a` gets the label `rep a` of its
representative; item `b` gets the representative whose claimed prefix contains it (the least one,
should several; the item's own index, should none). -/
def finalLabel (rk : Ranking n) (rep : Fin n → Fin n) : Fin n ⊕ Fin n → Fin n
  | Sum.inl a => rep a
  | Sum.inr b =>
    if h : (univ.filter fun r => rep r = r ∧ b ∈ claimed rk rep r).Nonempty then
      (univ.filter fun r => rep r = r ∧ b ∈ claimed rk rep r).min' h
    else b

/-- **Algorithm 2, RandRepPartition(σ).** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), §3.2, p.15 (PDF p.17): "Start with
singleton clusters {a}, each represented by a and claiming its favorite item. While two claimed
prefixes overlap: • Choose such clusters S, T by a fixed rule, with p = |S| ≥ q = |T|. Merge them,
keeping r_T with probability z(p, q) and r_S otherwise. • The retained representative claims its
first p + q items. When the claimed prefixes are disjoint, enumerate the final agent clusters as
A1, …, Am. Set Bj = Top(r_{Aj}, |Aj|) for each j and return P = (Aj, Bj)_{j=1}^m."

The law of the returned partition, as a labelling of agents and items (see `IsBalanced`): start
from `rep = id`, apply `mergeStep` `n` times, and label by `finalLabel`.

**Formalization Note.** Every merge removes one cluster, so a run has at most `n − 1` merges; for a
rule satisfying `IsSelectionRule` the claimed prefixes are disjoint after `n` iterations, and
further iterations change nothing. The cluster of `r` claims `Top(r, |S|)` with `|S|` its current
size, which is the page's "its first p + q items" after a merge. -/
noncomputable def randRepPartition (rk : Ranking n) (rule : SelectionRule n) :
    PMF (Fin n ⊕ Fin n → Fin n) :=
  ((fun μ : PMF (Fin n → Fin n) => μ.bind (mergeStep rk rule))^[n] (PMF.pure id)).map
    (finalLabel rk)

end MetricMatchingDistortion


