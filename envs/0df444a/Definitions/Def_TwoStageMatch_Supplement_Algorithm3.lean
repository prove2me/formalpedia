-- Prove2me | Definitions.Def_TwoStageMatch_Supplement_Algorithm3
-- name    : TwoStageMatch_Supplement_Algorithm3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-26T22:10:12.486453+00:00
-- url     : https://prove2.me/theorems/d19a937d-9cda-579f-a749-19d6820da046
-- title:
--   The ex ante relaxation $\mathcal P^{\mathrm{EAR}}$ and Algorithm 3 (Ex Ante Pricing with Simulation & Discarding)
-- statement:
--   The **ex ante relaxation** $\mathcal P^{\mathrm{EAR}}$ maximizes
--   $$\sum_{i\in D_1}\hat w_iy_i+\sum_{i\in D_2}w_i(T_i(y_i))\,y_i+\sum_{j\in S}w_jy_j$$
--   over fractional matchings $x\ge0$ of $G$, where $y_i=\sum_jx_{ij}\le1$ and $y_j=\sum_ix_{ij}\le1$.
--
--   A **run of Algorithm 3** consists of
--
--   1. an optimal solution $x$ of $\mathcal P^{\mathrm{EAR}}$;
--   2. an order of $D_1$; the first-stage matching $M_1$ is produced by the simulation-and-discarding loop: for each $i\in D_1$ in turn, sample $j^\dagger$ with probability $x_{ij^\dagger}$ and, if $j^\dagger$ is still free, match $i$ to $j^\dagger$ with probability $1/(2-\theta_{j^\dagger})$, then set $\theta_j\leftarrow\theta_j+x_{ij}$ for all $j$;
--   3. prices $p_i=T_i(y_i)$ for $i\in D_2$;
--   4. for every $M_1$ and accepting set $\tilde D_2$, a maximum vertex-weighted matching $M_2$ between $\tilde D_2$ and the free supplies, demand $i$ weighing $w_i(p_i)$ and supply $j$ weighing $w_j$.
--
--   Its market efficiency and its demand efficiency $\mathbb E[\sum_{i\in D_2}v_i\mathbb 1\{v_i\ge p_i,\ i\text{ matched by }M_2\}]$ are taken over the law of $M_1$ and the independent values.
--
--   **Formalization Note** The law of $M_1$ is computed step by step. With probability $1-y_i$ demand $i\in D_1$ samples no supply. At $y_i=0$ the paper's $\arg\max\{t:1-F_i(t)\ge0\}$ does not exist, so the price is left free there.
-- source:
--   Feng, Niazadeh & Saberi, Two-stage Stochastic Matching and Pricing with Applications to Ride Hailing, arXiv:2210.11648v1, §5.1 (𝒫^EAR), p.25; §5.2 and Algorithm 3, pp.26–27; §EC.7, p.ec20

import Mathlib
import Definitions.Def_TwoStageMatch_Supplement_Pricing

open Finset MeasureTheory

namespace TwoStageMatch.Supplement

/-!
# The ex ante relaxation `𝒫^EAR` and Algorithm 3 (Ex Ante Pricing with Simulation&Discarding)

Feng, Niazadeh & Saberi, arXiv:2210.11648v1, §5.1, p.25 (program `𝒫^EAR`) and §5.2,
pp.26–27 (Algorithm 3).

**Formalization Note.**
* A point of `𝒫^EAR` is a fractional matching `x : D₁ ⊕ D₂ → S → ℝ` of the whole graph `G` (the
  published `IsFracMatching`), with `y_i = Σ_j x_{ij}` and `y_j = Σ_i x_{ij}`. Its objective is
  `Σ_{i ∈ D₁} ŵ_i y_i + Σ_{i ∈ D₂} w_i(T_i(y_i)) y_i + Σ_{j ∈ S} w_j y_j`; at `y_i = 0` the middle
  term is `0` whatever `T_i(0)` is.
* The first stage of Algorithm 3 (lines 5–11) processes `D₁` in a fixed order (any order: every
  duplicate-free list of `D₁`). For demand `i` it samples `j†` with probability `x_{ij†}` (no
  supply with the remaining probability `1 − y_i`), and if `j†` is still free it matches `i` to `j†`
  with probability `1/(2 − θ_{j†})`; then `θ_j ← θ_j + x_{ij}` for every `j`. `simDist` is the
  resulting law of `M₁`, computed step by step as a weight on `Finset ((D₁ ⊕ D₂) × S)`.
* Line 12 offers `p_i = T_i(y_i)` to `i ∈ D₂`. The paper's `argmax {t : 1 − F_i(t) ≥ 0}` does not
  exist, so at `y_i = 0` the price is left free (every price is allowed).
* Line 15 takes a maximum vertex-weighted matching `M₂` between the accepting set `D̃₂` and the
  free supplies `S̃ = S \ S₁`, demand `i` weighing `w_i(p_i)` and supply `j` weighing `w_j`; a
  run fixes one such maximizer for every `M₁` and `D̃₂` (any choice is allowed).
-/

variable {D₁ D₂ S : Type*}

section
variable [Fintype D₁] [Fintype D₂] [Fintype S]

/-- The load `y_i = Σ_{j ∈ N(i)} x_{ij}` of a demand vertex. -/
def demandLoad (x : D₁ ⊕ D₂ → S → ℝ) (d : D₁ ⊕ D₂) : ℝ := ∑ j, x d j

/-- The load `y_j = Σ_{i ∈ N(j)} x_{ij}` of a supply vertex. -/
def supplyLoad (x : D₁ ⊕ D₂ → S → ℝ) (j : S) : ℝ := ∑ d, x d j

/-- The objective of `𝒫^EAR` (p.25):
`Σ_{i ∈ D₁} ŵ_i y_i + Σ_{i ∈ D₂} w_i(T_i(y_i)) y_i + Σ_{j ∈ S} ŵ_j y_j`. -/
noncomputable def earObjective (I : MPInstance D₁ D₂ S) (x : D₁ ⊕ D₂ → S → ℝ) : ℝ :=
  ∑ i : D₁, I.ŵ₁ i * demandLoad x (Sum.inl i) +
    ∑ i : D₂, condMean (I.F i) (threshold (I.F i) (demandLoad x (Sum.inr i))) *
      demandLoad x (Sum.inr i) +
    ∑ j, I.w j * supplyLoad x j

/-- `x` is an optimal solution of `𝒫^EAR`: a fractional matching of `G` maximizing the objective
over all fractional matchings of `G`. -/
def IsEAROptimal (I : MPInstance D₁ D₂ S) (x : D₁ ⊕ D₂ → S → ℝ) : Prop :=
  IsFracMatching I.E Finset.univ Finset.univ x ∧
    ∀ x', IsFracMatching I.E Finset.univ Finset.univ x' → earObjective I x' ≤ earObjective I x

variable [DecidableEq D₁] [DecidableEq D₂] [DecidableEq S]

/-- One step of the simulation-and-discarding process (Algorithm 3, lines 6–9) for the demand
`i ∈ D₁`, with counters `θ`: the transition weight from the current matching `M` to `M'`. -/
noncomputable def simTrans (x : D₁ ⊕ D₂ → S → ℝ) (θ : S → ℝ) (i : D₁)
    (M M' : Finset ((D₁ ⊕ D₂) × S)) : ℝ :=
  open Classical in
  if M' = M then
    1 - ∑ j, (if j ∈ matchedSupply M then 0 else x (Sum.inl i) j / (2 - θ j))
  else
    ∑ j, (if j ∉ matchedSupply M ∧ M' = insert (Sum.inl i, j) M then
      x (Sum.inl i) j / (2 - θ j) else 0)

/-- The law of `M₁` after the first-stage loop of Algorithm 3 has processed the demands of
`order` in turn, starting from the counters `θ` and the law `ρ` (lines 5–11). -/
noncomputable def simDist (x : D₁ ⊕ D₂ → S → ℝ) :
    List D₁ → (S → ℝ) → (Finset ((D₁ ⊕ D₂) × S) → ℝ) → Finset ((D₁ ⊕ D₂) × S) → ℝ
  | [], _, ρ => ρ
  | i :: l, θ, ρ =>
    simDist x l (fun j => θ j + x (Sum.inl i) j) (fun M' => ∑ M, ρ M * simTrans x θ i M M')

/-- The law of the first-stage matching `M₁` of Algorithm 3 (lines 2–11): `M₁ = ∅` and `θ = 0`
initially, then the demands of `order` are processed in turn. -/
noncomputable def firstStageLaw (x : D₁ ⊕ D₂ → S → ℝ) (order : List D₁) :
    Finset ((D₁ ⊕ D₂) × S) → ℝ :=
  open Classical in simDist x order (fun _ => 0) (fun M => if M = ∅ then 1 else 0)

/-- The second-stage demand weights of Algorithm 3, line 15: `w_i(p_i)` for `i ∈ D₂`. -/
noncomputable def secondStageWeight (I : MPInstance D₁ D₂ S) (p : D₂ → ℝ) : D₁ ⊕ D₂ → ℝ :=
  Sum.elim (fun _ => 0) fun i => condMean (I.F i) (p i)

/-- A run of Algorithm 3 on the instance `I`. -/
structure Run3 (I : MPInstance D₁ D₂ S) where
  /-- line 1: an optimal solution of `𝒫^EAR` -/
  x : D₁ ⊕ D₂ → S → ℝ
  x_opt : IsEAROptimal I x
  /-- the order in which the first-stage demands are processed -/
  order : List D₁
  order_nodup : order.Nodup
  order_complete : ∀ i, i ∈ order
  /-- line 12: the prices `p_i = T_i(y_i)` -/
  p : D₂ → ℝ
  p_eq : ∀ i, 0 < demandLoad x (Sum.inr i) → p i = threshold (I.F i) (demandLoad x (Sum.inr i))
  /-- line 15: the second-stage matching for the first-stage matching `M₁` and accepting set `A` -/
  M₂ : Finset ((D₁ ⊕ D₂) × S) → Finset D₂ → Finset ((D₁ ⊕ D₂) × S)
  M₂_matching : ∀ M A, IsMatching I.E (secondStage A) (Finset.univ \ matchedSupply M) (M₂ M A)
  M₂_max : ∀ M A M', IsMatching I.E (secondStage A) (Finset.univ \ matchedSupply M) M' →
    vwWeight (secondStageWeight I p) I.w M' ≤ vwWeight (secondStageWeight I p) I.w (M₂ M A)

/-- The expected market efficiency `𝔼[OBJ_{D₁∪D₂} + OBJ_S]` of a run of Algorithm 3: the
first-stage matching `M₁` is drawn from `firstStageLaw`, independently of the values. -/
noncomputable def Run3.efficiency {I : MPInstance D₁ D₂ S} (r : Run3 I) : ℝ :=
  ∑ M, firstStageLaw r.x r.order M * ∫ v, marketEff I M (r.M₂ M) r.p v ∂(valueLaw I)

/-- The expected demand efficiency `𝔼[Σ_{i ∈ D₂} v_i 𝟙{v_i ≥ p_i and i is matched by M₂}]` of a
run of Algorithm 3 (§EC.7, p.ec20). -/
noncomputable def Run3.demandEfficiency {I : MPInstance D₁ D₂ S} (r : Run3 I) : ℝ :=
  ∑ M, firstStageLaw r.x r.order M *
    ∫ v, ∑ e ∈ r.M₂ M (acceptSet r.p v), Sum.elim (fun _ => 0) v e.1 ∂(valueLaw I)

end

end TwoStageMatch.Supplement


