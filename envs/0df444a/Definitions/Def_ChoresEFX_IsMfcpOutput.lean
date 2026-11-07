-- Prove2me | Definitions.Def_ChoresEFX_IsMfcpOutput
-- name    : ChoresEFX_IsMfcpOutput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:07:18.655819+00:00
-- url     : https://prove2.me/theorems/a452b29b-6fbd-4241-a961-b28efd17eb2e
-- title:
--   Max-Flow Capped Price: base prices, water level, the flow network (3), residual reachability, runs and outputs
-- statement:
--   Given positive costs $\hat C$ and positive weights $v$, the **base price** of chore $g$ is $r_g(v)=\min_i v_i\hat C_i(g)$. A **water level** is an $s>0$ with $\sum_g\min\{s\,r_g(v),\beta\}=n$, and then $p_g=s\,r_g(v)$ and $q_g=\min\{p_g,\beta\}$.
--
--   The **network (3)** has source edges $s_0\to g$ of capacity $q_g$, edges $g\to i$ of capacity $n$ exactly when $v_i\hat C_i(g)\le(1+t)r_g(v)$, and sink edges $i\to t_0$ of capacity $1+t/n$.
--
--   Residual reachability from $s_0$ is the least set of chores and agents closed under three rules: $g$ is reached if $\sum_i f_{ig}<q_g$; an eligible $i$ is reached from $g$ if $f_{ig}<n$; and $g$ is reached from $i$ if $f_{ig}>0$.
--
--   A **failed run** starts at $v=1$. In each round it takes a water level and any maximum flow of value $F<n$, and multiplies the weights of the reachable agents by $1+t$. An **output** follows some failed run with a maximum flow of value $n$, and sets $w_{ig}=f_{ig}/q_g$ and $\gamma_i=\min_g\hat C_i(g)/p_g$.
--
--   These objects define the first stage of the algorithm.
--
--   **Formalization Note** A flow is the matrix of its middle edges; the outer edges carry its row and column sums. Reachability leaves out edges through $t_0$, which is unreachable for a maximum flow, so this is the paper's set, and the update is only applied to maximum flows. Every choice of a maximum flow is allowed.
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §3.1 pp.6–8; Eqs. (2)–(3), p.7; Algorithm 2, p.8; Lemma 3.2, p.9; Theorem 3.3, p.9

import Mathlib
import Definitions.Def_ChoresEFX_IsCappedPriceStructure

namespace ChoresEFX

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The base price** `r_g(v) = min_i v_i Ĉ_i(g)`, §3.1, p.6.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC
2027 submission (manuscript sha256 b26d14cf…).

**Formalization Note.** A real `⨅` over the finite type `ι`, attained when `ι` is nonempty; on empty `ι`
it is the junk value `0`, excluded by `[Nonempty ι]` in every statement. -/
noncomputable def basePrice (C : ι → κ → ℝ) (v : ι → ℝ) (g : κ) : ℝ := ⨅ i, v i * C i g

/-- **The water level**, Eq. (2), p.7 (Qin et al., STOC 2027 submission): `s > 0` with
`∑_g min{s · r_g(v), β} = n`. -/
def IsWaterLevel (C : ι → κ → ℝ) (β : ℝ) (v : ι → ℝ) (s : ℝ) : Prop :=
  0 < s ∧ ∑ g, min (s * basePrice C v g) β = (Fintype.card ι : ℝ)

/-- **The prices of a round**, `p_g = s · r_g(v)`, Eq. (2), p.7 (Qin et al., STOC 2027 submission). -/
noncomputable def roundPrice (C : ι → κ → ℝ) (v : ι → ℝ) (s : ℝ) (g : κ) : ℝ :=
  s * basePrice C v g

/-- **Eligible pairs**, network (3), p.7 (Qin et al., STOC 2027 submission): the edge `g → i` exists iff
`v_i Ĉ_i(g) ≤ (1 + t) r_g(v)`. -/
def Eligible (C : ι → κ → ℝ) (t : ℝ) (v : ι → ℝ) (i : ι) (g : κ) : Prop :=
  v i * C i g ≤ (1 + t) * basePrice C v g

/-- **Feasible flows in the network (3)**, p.7 (Qin et al., STOC 2027 submission): capacities `q_g` on
`s₀ → g`, `n` on eligible `g → i`, and `1 + t/n` on `i → t₀`.

**Formalization Note.** The network has the fixed layers `s₀ → chores → agents → t₀`, so a flow is the
matrix `f_ig` of its middle edges; the outer edges carry the row and column sums. -/
structure IsFeasibleFlow (C : ι → κ → ℝ) (t β : ℝ) (v : ι → ℝ) (s : ℝ) (f : ι → κ → ℝ) : Prop where
  nonneg : ∀ i g, 0 ≤ f i g
  eligible : ∀ i g, ¬ Eligible C t v i g → f i g = 0
  middle_cap : ∀ i g, f i g ≤ (Fintype.card ι : ℝ)
  source_cap : ∀ g, ∑ i, f i g ≤ capped β (roundPrice C v s) g
  sink_cap : ∀ i, ∑ g, f i g ≤ 1 + t / (Fintype.card ι : ℝ)

/-- The value `F` of a flow in the network (3), p.7 (Qin et al., STOC 2027 submission). -/
def flowValue (f : ι → κ → ℝ) : ℝ := ∑ i, ∑ g, f i g

/-- **Maximum flows** in the network (3): feasible, and no feasible flow has a larger value. -/
def IsMaximumFlow (C : ι → κ → ℝ) (t β : ℝ) (v : ι → ℝ) (s : ℝ) (f : ι → κ → ℝ) : Prop :=
  IsFeasibleFlow C t β v s f ∧
    ∀ f', IsFeasibleFlow C t β v s f' → flowValue f' ≤ flowValue f

/-- **Reachability from `s₀` in the residual network** of the flow `f` (Algorithm 2, line 10, p.8;
Lemma 3.2, p.9; Qin et al., STOC 2027 submission): `inl g` is a chore, `inr i` an agent.

**Formalization Note.** The least set closed under: `s₀ → g` if `∑_i f_ig < q_g`; `g → i` if eligible
and `f_ig < n`; `i → g` if `f_ig > 0`. Edges through `t₀` are left out: for a maximum flow `t₀` is not
reachable, since that would give an augmenting path, so this is the residual reachable set the paper
uses, and the update below is only ever applied to maximum flows. -/
inductive Reach (C : ι → κ → ℝ) (t β : ℝ) (v : ι → ℝ) (s : ℝ) (f : ι → κ → ℝ) : κ ⊕ ι → Prop
  | source (g : κ) : ∑ i, f i g < capped β (roundPrice C v s) g → Reach C t β v s f (Sum.inl g)
  | forward (g : κ) (i : ι) : Reach C t β v s f (Sum.inl g) → Eligible C t v i g →
      f i g < (Fintype.card ι : ℝ) → Reach C t β v s f (Sum.inr i)
  | backward (i : ι) (g : κ) : Reach C t β v s f (Sum.inr i) → 0 < f i g →
      Reach C t β v s f (Sum.inl g)

open Classical in
/-- The set `C` of chores reachable from `s₀`, Lemma 3.2, p.9 (Qin et al., STOC 2027 submission). -/
noncomputable def reachChores (C : ι → κ → ℝ) (t β : ℝ) (v : ι → ℝ) (s : ℝ) (f : ι → κ → ℝ) :
    Finset κ :=
  univ.filter fun g => Reach C t β v s f (Sum.inl g)

open Classical in
/-- The set `S` of agents reachable from `s₀`, Algorithm 2, line 10, p.8 (Qin et al., STOC 2027
submission). -/
noncomputable def reachAgents (C : ι → κ → ℝ) (t β : ℝ) (v : ι → ℝ) (s : ℝ) (f : ι → κ → ℝ) :
    Finset ι :=
  univ.filter fun i => Reach C t β v s f (Sum.inr i)

open Classical in
/-- **The weight update**, Algorithm 2, line 11, p.8 (Qin et al., STOC 2027 submission): for every
reachable agent `i`, `v_i ← (1 + t) v_i`. -/
noncomputable def updatedWeights (C : ι → κ → ℝ) (t β : ℝ) (v : ι → ℝ) (s : ℝ) (f : ι → κ → ℝ) :
    ι → ℝ :=
  fun i => if i ∈ reachAgents C t β v s f then (1 + t) * v i else v i

/-- **`J` failed rounds of MFCP**, Algorithm 2, p.8 (Qin et al., STOC 2027 submission): `v⁰ = 1`, and in
each round `j < J` a water level, any maximum flow of value `F < n`, and the update by its residual
reachable agents.

**Formalization Note.** Every choice of a maximum flow is allowed (paper.md decision 8); the water level
is unique (`water_level_unique`). `v j` for `j > J` is not constrained. -/
def IsFailedRun (C : ι → κ → ℝ) (t β : ℝ) (J : ℕ) (v : ℕ → ι → ℝ) : Prop :=
  (∀ i, v 0 i = 1) ∧
    ∀ j < J, ∃ s f, IsWaterLevel C β (v j) s ∧ IsMaximumFlow C t β (v j) s f ∧
      flowValue f < (Fintype.card ι : ℝ) ∧ v (j + 1) = updatedWeights C t β (v j) s f

/-- **An output of MFCP**, Algorithm 2, lines 6–8, p.8 (Qin et al., STOC 2027 submission): after some
number `J` of failed rounds, a maximum flow of value `n`, and then `w_ig = f_ig / q_g`,
`γ_i = min_g Ĉ_i(g)/p_g`. -/
def IsMfcpOutput (C : ι → κ → ℝ) (t β : ℝ) (p : κ → ℝ) (γ : ι → ℝ) (w : ι → κ → ℝ) : Prop :=
  ∃ (J : ℕ) (v : ℕ → ι → ℝ) (s : ℝ) (f : ι → κ → ℝ),
    IsFailedRun C t β J v ∧ IsWaterLevel C β (v J) s ∧ IsMaximumFlow C t β (v J) s f ∧
      flowValue f = (Fintype.card ι : ℝ) ∧ p = roundPrice C (v J) s ∧
      γ = mpbRatio C p ∧ w = fun i g => f i g / capped β p g

/-- The largest cost, `Ĉ_max = max_{i,g} Ĉ_i(g)`, Theorem 3.3, p.9 (Qin et al., STOC 2027 submission). -/
noncomputable def maxCost (C : ι → κ → ℝ) : ℝ := ⨆ i, ⨆ g, C i g

/-- The smallest cost, `Ĉ_min = min_{i,g} Ĉ_i(g)`, Theorem 3.3, p.9 (Qin et al., STOC 2027 submission). -/
noncomputable def minCost (C : ι → κ → ℝ) : ℝ := ⨅ i, ⨅ g, C i g

end ChoresEFX


