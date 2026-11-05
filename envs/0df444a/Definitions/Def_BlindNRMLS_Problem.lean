-- Prove2me | Definitions.Def_BlindNRMLS_Problem
-- name    : BlindNRMLS_Problem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:46:57.483752+00:00
-- url     : https://prove2.me/theorems/272f38ac-2155-4ea0-9f4f-bf5ab8c95a75
-- title:
--   §2, §3.1, pp.7–10 — the BNRM problem $(T,\mathbf B,K,d,n,P,A)$, demand distributions and $J^{\mathrm{DLP}}$
-- statement:
--   A **BNRM problem** consists of a horizon of $T$ periods, $d$ resources with initial inventories $B_i\ge 0$, $K$ price vectors $\mathbf p_k=(p_{1,k},\dots,p_{n,k})$ over $n$ products with $p_{j,k}\ge 0$, and a consumption matrix $A=(a_{ij})$ with $a_{ij}\ge 0$: selling one unit of product $j$ depletes $a_{ij}$ units of resource $i$. We write $a_{\max}=\max_{i,j}a_{ij}$ and $B_{\min}=\min_i B_i$.
--
--   **Demand distributions** $Q=(Q_{j,k})$ assign to each product $j$ and price vector $k$ a probability law on $[0,1]$, with mean $q_{j,k}=\mathbb E[Q_{j,k}]$. The demand vector of one period under price vector $k$ has the product law of the $Q_{j,k}$.
--
--   For a mean-demand matrix $q$, the deterministic linear program is
--   $$
--   J^{\mathrm{DLP}}=\max_{x}\ \sum_{k}\sum_{j}p_{j,k}\,q_{j,k}\,x_k\quad\text{s.t.}\quad\sum_{k}\sum_{j}a_{ij}\,q_{j,k}\,x_k\le B_i\ \ \forall i,\quad\sum_k x_k\le T,\quad x_k\ge 0 .
--   $$
--   This is the benchmark of the whole analysis. The same program with empirical means is the last step of the algorithm LS-2SLP.
--
--   **Formalization Note** `p` is an indexed family without injectivity. `amax` and `Bmin` are real suprema and infima over finite types, both $0$ when $d=0$. The maximum is a real `sSup` over the image of a compact set containing $x=0$.
-- source:
--   Simchi-Levi, Xu & Zhao, Blind Network Revenue Management and Bandits with Knapsacks Under Limited Switches, arXiv:1911.01067v5, §2, pp.7–8, §3.1, displays (1)–(4), p.10

import Mathlib

open MeasureTheory

namespace BlindNRMLS

/-- A BNRM problem `𝒫 = (T, B, K, d, n, P, A)`: `T` periods, inventories `B i` of `d` resources,
`K` price vectors `p k` over `n` products with entries `p k j = p_{j,k} ≥ 0`, and the consumption
matrix `A i j = a_{ij} ≥ 0`.
Simchi-Levi, Xu & Zhao, arXiv:1911.01067v5, §2, pp.7–8 and §4, p.13.

**Formalization Note.** `p` is an indexed family; injectivity is not part of the structure. Where
the paper's "finite set of `K` price vectors" matters it is stated in the theorem. Periods
`1, …, T` of the page are `0, …, T - 1` in Lean. Inventories are nonnegative. -/
structure Problem (d n K : ℕ) where
  /-- The horizon. -/
  T : ℕ
  /-- The initial inventories. -/
  B : Fin d → ℝ
  /-- The price `p_{j,k}` of product `j` under price vector `k`. -/
  p : Fin K → Fin n → ℝ
  /-- The consumption `a_{ij}` of resource `i` per unit of product `j`. -/
  A : Fin d → Fin n → ℝ
  B_nonneg : ∀ i, 0 ≤ B i
  p_nonneg : ∀ k j, 0 ≤ p k j
  A_nonneg : ∀ i j, 0 ≤ A i j

variable {d n K : ℕ}

/-- `a_max = max_{i,j} a_{ij}` (p.7).

**Formalization Note.** A real supremum over a finite index type; it is `0` when `d = 0`. -/
noncomputable def Problem.amax (P : Problem d n K) : ℝ := ⨆ ij : Fin d × Fin n, P.A ij.1 ij.2

/-- `B_min = min_i B_i` (p.7).

**Formalization Note.** A real infimum over a finite index type; it is `0` when `d = 0`. In that
case `amax = 0`, so the quotient in `γ` (Algorithm 2) is `0` under any convention. -/
noncomputable def Problem.Bmin (P : Problem d n K) : ℝ := ⨅ i, P.B i

/-- Demand distributions `Q = (Q_{j,k})` (p.8): a probability law on `[0,1]` for every product `j`
and price vector `k`.

**Formalization Note.** The products' demands in one period are independent: the joint law under
price vector `k` is the product measure `DemandLaw.joint`. The model section does not say so; it
is the reading that p.2 ("stochastic, independent"), p.20 (`q` determines a Bernoulli instance) and
the proofs of Lemma EC.6 and of the clean event need. -/
structure DemandLaw (n K : ℕ) where
  /-- The law of `Q_{j,k}`. -/
  law : Fin K → Fin n → Measure ℝ
  prob : ∀ k j, IsProbabilityMeasure (law k j)
  supp : ∀ k j, law k j (Set.Icc (0 : ℝ) 1)ᶜ = 0

attribute [instance] DemandLaw.prob

/-- The mean demand `q_{j,k} = E[Q_{j,k}]` (p.8). -/
noncomputable def DemandLaw.mean (Q : DemandLaw n K) (k : Fin K) (j : Fin n) : ℝ :=
  ∫ x, x ∂(Q.law k j)

/-- The joint law of one period's demand vector under price vector `k`. -/
noncomputable def DemandLaw.joint (Q : DemandLaw n K) (k : Fin K) : Measure (Fin n → ℝ) :=
  Measure.pi (Q.law k)

/-- The feasible set of the deterministic LP with mean-demand matrix `q`: displays (2)–(4), p.10,
and the constraints of line 12 of Algorithm 2, p.16. -/
def DetFeasible (P : Problem d n K) (q : Fin K → Fin n → ℝ) (x : Fin K → ℝ) : Prop :=
  (∀ i, ∑ k, ∑ j, P.A i j * q k j * x k ≤ P.B i) ∧ ∑ k, x k ≤ (P.T : ℝ) ∧ ∀ k, 0 ≤ x k

/-- The objective of the deterministic LP with mean-demand matrix `q`: display (1), p.10. -/
def detObjective (P : Problem d n K) (q : Fin K → Fin n → ℝ) (x : Fin K → ℝ) : ℝ :=
  ∑ k, ∑ j, P.p k j * q k j * x k

/-- `J^DLP` for the true means: the maximum of (1) over (2)–(4), p.10.

**Formalization Note.** A real `sSup` over the image of a compact set that contains `x = 0`, so it
is a maximum. -/
noncomputable def J (P : Problem d n K) (Q : DemandLaw n K) : ℝ :=
  sSup (detObjective P Q.mean '' {x | DetFeasible P Q.mean x})

end BlindNRMLS


