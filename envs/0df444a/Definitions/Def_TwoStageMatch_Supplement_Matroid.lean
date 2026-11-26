-- Prove2me | Definitions.Def_TwoStageMatch_Supplement_Matroid
-- name    : TwoStageMatch_Supplement_Matroid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:07:29.631315+00:00
-- url     : https://prove2.me/theorems/688d0923-42bc-42ce-9da1-606462ccd0f1
-- title:
--   Maximum-cardinality matchings, the objective of (2), the dual transversal matroid $\bar{\mathcal B}$ and $f^w$
-- statement:
--   Let $G=(D_1\cup D_2,S,E)$ be a two-stage stochastic matching instance with supply weights $w_j\ge 0$ and availability probabilities $\pi_i\in[0,1]$, and let $\tilde D_2$ be the random set of available second-stage demands. This module defines:
--
--   1. a **maximum unweighted matching** between $X$ and $Y$: a matching with the largest number of edges, and $\nu(X,Y)$, the size of such a matching;
--   2. the objective of eq. (2) for a fixed first-stage matching $M_1$ matching the supply set $S_1$:
--   $$\Phi(M_1)=\sum_{j\in S}w_j\mathbb 1\{j\text{ matched in }M_1\}+\mathbb E_{\tilde D_2}\big[\text{Max-WeightMatch}^w(\tilde D_2,S\setminus S_1)\big],$$
--   so that $\mathrm{OPT}_{\mathrm{online}}=\max_{M_1}\Phi(M_1)$;
--   3. the bases $\mathcal B$ of the transversal matroid of $G[D_1,S]$ (supply sets matched by some maximum matching of $G[D_1,S]$) and the bases $\bar{\mathcal B}$ of its dual: $T\in\bar{\mathcal B}$ iff $S\setminus T\in\mathcal B$;
--   4. $f^w(T)=\mathbb E_{\tilde D_2}[\text{Max-WeightMatch}^w(\tilde D_2,T)]$ for $T\subseteq S$ (eq. (8)).
--
--   These are the objects in which the optimum online policy is characterized (Proposition 2) and in which the greedy branch of Algorithm 2 is stated.
--
--   **Formalization Note** Built on the published `TwoStageMatch.Instance` and `TwoStageMatch.Bipartite`; matchings are finite sets of edges, and "maximum unweighted" means maximum cardinality.
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, §2 (2), p.10; Remark 4, p.16; transversal matroid and (8), pp.16–17

import Mathlib
import Definitions.Def_TwoStageMatch_Instance

open Finset

namespace TwoStageMatch.Supplement

/-!
# Maximum-cardinality matchings, the dual transversal matroid `B̄` and `f^w`

Feng, Niazadeh & Saberi, *Two-stage Stochastic Matching and Pricing with Applications to Ride
Hailing*, arXiv:2210.11648v1: the objective of eq. (2), p.10; Remark 4, p.16; the transversal
matroid `M = (S, I, B)`, its dual `M̄ = (S, Ī, B̄)` and the function `f^w` of eq. (8), pp.16–17.

**Formalization Note.** Everything is built on the published `TwoStageMatch.Instance`
(demands `D₁ ⊕ D₂`, supply weights `w ≥ 0`, probabilities `π ∈ [0, 1]`) and on its
`IsMatching`, `matchedSupply`, `weight`, `maxWeightMatch`, `expect`. A "maximum unweighted
matching" is a matching of maximum cardinality (`Finset.card`). A base of `M` is the set of
supplies matched by some maximum-cardinality matching of `G[D₁, S]`; `T ∈ B̄` iff `S \ T` is a base.
-/

variable {D₁ D₂ S : Type*}

/-- `M` is a maximum unweighted (maximum-cardinality) matching between `X` and `Y`: a matching
whose number of edges is at least that of every matching between `X` and `Y`. -/
def IsMaxCardMatching {U V : Type*} (E : U → V → Prop) (X : Finset U) (Y : Finset V)
    (M : Finset (U × V)) : Prop :=
  IsMatching E X Y M ∧ ∀ M', IsMatching E X Y M' → M'.card ≤ M.card

/-- The size of a maximum matching between `X` and `Y` (the unweighted `Max-WeightMatch`, i.e.
`maxWeightMatch` with all supply weights `1`). -/
noncomputable def maxCard {U V : Type*} [Fintype U] [Fintype V] [DecidableEq V]
    (E : U → V → Prop) (X : Finset U) (Y : Finset V) : ℝ :=
  maxWeightMatch E (fun _ => 1) X Y

section
variable [Fintype D₁] [Fintype D₂] [Fintype S] [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]

/-- The objective of eq. (2), p.10, for a given first-stage matching `M₁`:
`Σ_{j ∈ S} w_j 𝟙{j matched in M₁} + 𝔼_{D̃₂}[Max-WeightMatch^w(D̃₂, S \ S₁)]`, where `S₁` is the set
of supplies matched by `M₁`. `OPT_online` is the maximum of this quantity over all `M₁`. -/
noncomputable def onlineValue (I : Instance D₁ D₂ S) (M : Finset ((D₁ ⊕ D₂) × S)) : ℝ :=
  weight I.w M +
    expect I fun A => maxWeightMatch I.E I.w (secondStage A) (Finset.univ \ matchedSupply M)

/-- `T₁ ⊆ S` is a base of the transversal matroid `M = (S, I, B)` of `G[D₁, S]` (p.17): the set of
supplies matched by some maximum (cardinality) matching of `G[D₁, S]`. -/
def IsBase (I : Instance D₁ D₂ S) (T : Finset S) : Prop :=
  ∃ M, IsMaxCardMatching I.E firstStage Finset.univ M ∧ matchedSupply M = T

/-- `T ∈ B̄`, a base of the dual matroid `M̄` (p.17): `S \ T` is a base of `M`. -/
def IsDualBase (I : Instance D₁ D₂ S) (T : Finset S) : Prop :=
  IsBase I (Finset.univ \ T)

/-- `f^w(T) ≜ 𝔼_{D̃₂}[ρ^w(T)]` with `ρ^w(T) ≜ Max-WeightMatch^w(D̃₂, T)`, eq. (8), p.17. -/
noncomputable def fw (I : Instance D₁ D₂ S) (T : Finset S) : ℝ :=
  expect I fun A => maxWeightMatch I.E I.w (secondStage A) T

end

end TwoStageMatch.Supplement


