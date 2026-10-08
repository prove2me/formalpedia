-- Prove2me | Definitions.Def_ConstrNestedLogit_Reduce_Problems
-- name    : ConstrNestedLogit_Reduce_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:23.057572+00:00
-- url     : https://prove2.me/theorems/385a8959-8249-4166-a523-759c8dccce6c
-- title:
--   §1, §3, pp. 8, 13–14 — optimality for problem (1), the objective of problem (7), α-approximate solutions of (7), and $u^*_i$
-- statement:
--   Fix a nested logit instance with nests $M$ and products $N = \{1, \dots, n\}$: no-purchase weight $v_0$, preference weights $v_{ij}$, revenues $r_{ij}$ and dissimilarity parameters $\gamma_i$. For an assortment $S_i \subseteq N$ in nest $i$ write $V_i(S_i) = \sum_{j \in S_i} v_{ij}$, $R_i(S_i) = \sum_{j \in S_i} r_{ij} v_{ij} / V_i(S_i)$ (with $R_i(\bar 0) = 0$), and let
--   $$\Pi(S_1, \dots, S_m) = \frac{\sum_{i \in M} V_i(S_i)^{\gamma_i} R_i(S_i)}{v_0 + \sum_{i \in M} V_i(S_i)^{\gamma_i}}$$
--   be the expected revenue. Each nest $i$ has a set $\mathcal C_i$ of feasible assortments. This file defines four objects.
--
--   1. **Optimality for problem (1).** $(S^*_1, \dots, S^*_m)$ is an optimal solution of problem (1) when $S^*_i \in \mathcal C_i$ for every $i$ and $\Pi(S_1, \dots, S_m) \le \Pi(S^*_1, \dots, S^*_m)$ for every $(S_1, \dots, S_m) \in \mathcal C_1 \times \dots \times \mathcal C_m$. Its value $\Pi(S^*_1, \dots, S^*_m)$ is $Z^*$.
--   2. **The objective of problem (7).** For a threshold $u$,
--   $$\max_{S_i \in \mathcal C_i} \Big\{ V_i(S_i)\,\big(R_i(S_i) - u\big) \Big\}. \tag{7}$$
--   The objective $V_i(S_i)(R_i(S_i) - u)$ carries no power $\gamma_i$.
--   3. **$\alpha$-approximate solutions of (7).** An assortment $\hat S_i$ is an $\alpha$-approximate solution of (7) at $u$ when $\hat S_i \in \mathcal C_i$ and
--   $$\alpha\, V_i(\hat S_i)\big(R_i(\hat S_i) - u\big) \ge V_i(S_i)\big(R_i(S_i) - u\big) \quad \text{for every } S_i \in \mathcal C_i,$$
--   which is the form of inequality (5) of the paper.
--   4. **The threshold of Lemma 3.** For an assortment $(S^*_1, \dots, S^*_m)$ with value $Z^* = \Pi(S^*_1, \dots, S^*_m)$,
--   $$u^*_i = \max\big\{Z^*,\ \gamma_i Z^* + (1 - \gamma_i) R_i(S^*_i)\big\}.$$
--
--   These are the objects through which the paper reduces the constrained assortment problem (1) to the single-nest problems (7).
--
--   **Formalization Note** The instance and $V_i$, $R_i$, $V_i^{\gamma_i}$, $\Pi$ are those of the published `NestedLogitVariants.LP.Model`; every statement of this mission sets its within-nest no-purchase weight to zero, so `V` is the paper's $V_i$. Assortments are `Finset (Fin n)` (products indexed from $0$), and the empty set is $\bar 0$. Feasible sets are arbitrary families `C : ι → Set (Finset (Fin n))`. The paper never defines "$\alpha$-approximate solution" separately; item 3 takes inequality (5) and adds feasibility $\hat S_i \in \mathcal C_i$, as "solution to problem (7)" requires.
-- source:
--   Gallego & Topaloglu, Constrained Assortment Optimization for the Nested Logit Model, Management Science (2014), DOI 10.1287/mnsc.2014.1931; authors' manuscript of Sept. 11, 2013, p. 8, problem (1); p. 13, Lemma 3, u*_i and (5); p. 14, problem (7)

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

namespace ConstrNestedLogit.Reduce

open NestedLogitVariants.LP

variable {ι : Type*} {n : ℕ}

/-- `S = (S_1, …, S_m)` is an optimal solution of problem (1) (p. 8): every `S_i` lies in the
feasible set `C_i`, and `Π(S) ≥ Π(S')` for every `S' ∈ C_1 × ⋯ × C_m`. Its objective value
`revenue I S` is the paper's `Z*`. -/
def IsOptimal1 [Fintype ι] (I : Instance ι n) (C : ι → Set (Finset (Fin n)))
    (S : ι → Finset (Fin n)) : Prop :=
  (∀ i, S i ∈ C i) ∧ ∀ S' : ι → Finset (Fin n), (∀ i, S' i ∈ C i) → revenue I S' ≤ revenue I S

/-- The objective `V_i(S_i) (R_i(S_i) − u)` of problem (7) (p. 14) for nest `i`, assortment `S`
and threshold `u`. It carries no power `γ_i`. -/
noncomputable def obj7 (I : Instance ι n) (i : ι) (S : Finset (Fin n)) (u : ℝ) : ℝ :=
  V I i S * (R I i S - u)

/-- `S` is an `α`-approximate solution of problem (7) `max_{S_i ∈ C_i} V_i(S_i)(R_i(S_i) − u)`
for nest `i` (pp. 13–14, the form of (5)): `S ∈ C_i` and
`α V_i(S)(R_i(S) − u) ≥ V_i(S')(R_i(S') − u)` for every `S' ∈ C_i`. -/
def IsApproxSol7 (I : Instance ι n) (C : ι → Set (Finset (Fin n))) (i : ι) (α u : ℝ)
    (S : Finset (Fin n)) : Prop :=
  S ∈ C i ∧ ∀ S' ∈ C i, obj7 I i S' u ≤ α * obj7 I i S u

/-- The threshold `u*_i = max{Z*, γ_i Z* + (1 − γ_i) R_i(S*_i)}` of Lemma 3 (p. 13), with
`Z* = Π(S*_1, …, S*_m)` the revenue of the assortment `Sstar`. -/
noncomputable def uStar [Fintype ι] (I : Instance ι n) (Sstar : ι → Finset (Fin n)) (i : ι) : ℝ :=
  max (revenue I Sstar) (I.γ i * revenue I Sstar + (1 - I.γ i) * R I i (Sstar i))

end ConstrNestedLogit.Reduce


