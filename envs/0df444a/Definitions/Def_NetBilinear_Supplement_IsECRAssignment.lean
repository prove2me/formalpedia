-- Prove2me | Definitions.Def_NetBilinear_Supplement_IsECRAssignment
-- name    : NetBilinear_Supplement_IsECRAssignment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:41:16.794169+00:00
-- url     : https://prove2.me/theorems/39521053-0519-4e0e-9c03-37150381b60e
-- title:
--   EC&R assignment $[\mathcal I_1,\dots,\mathcal I_m,\bar{\mathcal I}\,|\,\mathcal J,\bar{\mathcal J}]$ of class $l^\pm$ for general $m$, with conditions (C1) and (C2)
-- statement:
--   Consider the set $\mathcal S=\{(x;y;z)\in\Xi\times\Delta_m\times\mathbb R^\kappa : y^\top A^k x=z_k,\ k\in K\}$ with $\Xi=\{x : Ex\ge f,\ 0\le x\le u\}$ and $\Delta_m=\{y\ge0 : \mathbf 1^\top y\le1\}$, where every $A^k$ has exactly one entry equal to $1$. Fix a class $l$, whose bilinear constraint is the **base equality** $y_{j'}x_{i'}-z_l=0$ (the entry $A^l_{j'i'}=1$), and a sign $\sigma\in\{+,-\}$. Let $T$ be the index set of the rows $E_t x\ge f_t$ of $\Xi$.
--
--   An assignment $[\mathcal I_1,\dots,\mathcal I_m,\bar{\mathcal I}\,|\,\mathcal J,\bar{\mathcal J}]$ consists of row sets $\mathcal I_1,\dots,\mathcal I_m,\bar{\mathcal I}\subseteq T$ and variable index sets $\mathcal J,\bar{\mathcal J}$. With weights $\gamma^j_t,\theta_t,\lambda_k,\mu_k$, the aggregation adds
--   1. the base equality with weight $\sigma=\pm1$,
--   2. each row $t\in\mathcal I_j$ multiplied by $\gamma^j_t\,y_j$,
--   3. each row $t\in\bar{\mathcal I}$ multiplied by $\theta_t\,(1-\sum_{i\in M}y_i)$,
--   4. each bound $x_k\ge0$, $k\in\mathcal J$, multiplied by $\lambda_k(1-\sum_j y_j)$, and each bound $u_k-x_k\ge0$, $k\in\bar{\mathcal J}$, multiplied by $\mu_k(1-\sum_j y_j)$.
--
--   The resulting coefficient of the bilinear term $y_jx_k$ is
--   $$
--   \sigma[(j,k)=(j',i')]+\sum_{t\in\mathcal I_j}\gamma^j_tE_{t,k}-\sum_{t\in\bar{\mathcal I}}\theta_tE_{t,k}-\lambda_k[k\in\mathcal J]+\mu_k[k\in\bar{\mathcal J}].
--   $$
--   A term is **created** by a constraint when that weighted constraint has a nonzero coefficient on it, and **canceled** when some used constraint creates it and its aggregated coefficient is $0$.
--
--   The assignment is an **EC&R assignment of class $l^\sigma$** when $\mathcal I_1\cap\dots\cap\mathcal I_m\cap\bar{\mathcal I}=\emptyset$, $\mathcal J\cap\bar{\mathcal J}=\emptyset$, and there are nonnegative weights for which
--   - **(C1)** at least $\sum_{j\in M}|\mathcal I_j|+|\bar{\mathcal I}|+|\mathcal J|+|\bar{\mathcal J}|$ bilinear terms are canceled, and
--   - **(C2)** if $\bigcup_j\mathcal I_j\cup\bar{\mathcal I}\cup\mathcal J\cup\bar{\mathcal J}\neq\emptyset$, then every constraint used in the aggregation, the base equality included, creates at least one canceled term.
--
--   This is the object Theorem 3 produces for the network polytope, and it generalizes the published $m=1$ notion `NetBilinear.IsECRAssignmentOne`.
--
--   **Formalization Note** The rows are an arbitrary index type with coefficients `E t k`, and the class $l$ is passed as its pair $(i',j')$. The intersection condition is the common intersection (Example 5, p.21, has a row in both $\mathcal I_1$ and $\mathcal I_2$), not pairwise disjointness. A bound in $\mathcal J$ or $\bar{\mathcal J}$ with weight $0$ creates no term, so (C2) then fails for it.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, §1, p.2 (set S, matrices A^k); §2, p.3 (EC&R procedure, Steps 1–3, conditions (C1) and (C2))

import Mathlib
import Definitions.Def_NetBilinear_Network

namespace NetBilinear.Supplement

variable {R N M : Type*}

/-- **The aggregated coefficient of the bilinear term `y_j x_k`** in the EC&R procedure for
general `m`. Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, §2, p.3, Steps 1–3, for the set `S` of p.2.

The constraints aggregated are:
1. the base equality `y_{j'} x_{i'} − z_l = 0` with weight `σ = ±1` (it contributes `σ` to
   the term `y_{j'} x_{i'}`, and to no other bilinear term);
2. each non-bound row `t ∈ I_j` (`E_t·x ≥ f_t`) times `γ^j_t y_j`, contributing `γ^j_t E_{t,k}`
   to `y_j x_k`;
3. each row `t ∈ Ī` times `θ_t (1 − Σ_{i∈M} y_i)`, contributing `−θ_t E_{t,k}` to `y_j x_k`
   for **every** `j ∈ M`;
4. each bound `x_k ≥ 0`, `k ∈ J`, times `λ_k (1 − Σ_j y_j)`, contributing `−λ_k` to `y_j x_k`
   for every `j`;
5. each bound `u_k − x_k ≥ 0`, `k ∈ J̄`, times `µ_k (1 − Σ_j y_j)`, contributing `+µ_k` to
   `y_j x_k` for every `j`. -/
def aggCoef [DecidableEq N] [DecidableEq M] (E : R → N → ℝ) (i' : N) (j' : M) (σ : Sign)
    (I : M → Finset R) (Ibar : Finset R) (J Jbar : Finset N)
    (γ : M → R → ℝ) (θ : R → ℝ) (lam μ : N → ℝ) (j : M) (k : N) : ℝ :=
  (if k = i' ∧ j = j' then σ.toReal else 0) + ∑ t ∈ I j, γ j t * E t k
    - ∑ t ∈ Ibar, θ t * E t k - (if k ∈ J then lam k else 0) + (if k ∈ Jbar then μ k else 0)

/-- **The term `y_j x_k` is created** by some constraint used in the aggregation, i.e. some
weighted constraint of `aggCoef` has a nonzero coefficient on it: the base equality (only for
`(j, k) = (j', i')`), a row of `I_j`, a row of `Ī`, a bound of `J` or a bound of `J̄`.
arXiv:2302.14151v2, (C2), p.3 ("all those created after multiplying that constraint with its
corresponding weight"). -/
def IsCreated [DecidableEq N] [DecidableEq M] (E : R → N → ℝ) (i' : N) (j' : M)
    (I : M → Finset R) (Ibar : Finset R) (J Jbar : Finset N)
    (γ : M → R → ℝ) (θ : R → ℝ) (lam μ : N → ℝ) (j : M) (k : N) : Prop :=
  (k = i' ∧ j = j') ∨ (∃ t ∈ I j, γ j t * E t k ≠ 0) ∨ (∃ t ∈ Ibar, θ t * E t k ≠ 0) ∨
    (k ∈ J ∧ lam k ≠ 0) ∨ (k ∈ Jbar ∧ μ k ≠ 0)

/-- **The term `y_j x_k` is canceled**: it is created by some used constraint and its
aggregated coefficient is `0`. arXiv:2302.14151v2, (C1), p.3 ("bilinear terms are canceled
(i.e., their coefficient becomes zero)").

**Formalization Note.** A term that no used constraint creates also has coefficient `0`; it
is not counted as canceled (as in the published `m = 1` definition `IsECRAssignmentOne`),
otherwise (C1) would hold for free. -/
def IsCancelled [DecidableEq N] [DecidableEq M] (E : R → N → ℝ) (i' : N) (j' : M) (σ : Sign)
    (I : M → Finset R) (Ibar : Finset R) (J Jbar : Finset N)
    (γ : M → R → ℝ) (θ : R → ℝ) (lam μ : N → ℝ) (j : M) (k : N) : Prop :=
  IsCreated E i' j' I Ibar J Jbar γ θ lam μ j k ∧
    aggCoef E i' j' σ I Ibar J Jbar γ θ lam μ j k = 0

/-- **Condition (C1)**: at least `Σ_{j∈M} |I_j| + |Ī| + |J| + |J̄|` bilinear terms `y_j x_k`
are canceled. arXiv:2302.14151v2, §2, p.3, (C1). -/
def CondC1 [Fintype M] [DecidableEq N] [DecidableEq M] (E : R → N → ℝ) (i' : N) (j' : M)
    (σ : Sign) (I : M → Finset R) (Ibar : Finset R) (J Jbar : Finset N)
    (γ : M → R → ℝ) (θ : R → ℝ) (lam μ : N → ℝ) : Prop :=
  (∑ j, (I j).card) + Ibar.card + J.card + Jbar.card ≤
    {p : M × N | IsCancelled E i' j' σ I Ibar J Jbar γ θ lam μ p.1 p.2}.ncard

/-- **Condition (C2)**: if `∪_j I_j ∪ Ī ∪ J ∪ J̄ ≠ ∅`, then for each constraint used in the
aggregation (including the base equality), at least one bilinear term among those it creates
after multiplication with its weight is canceled. arXiv:2302.14151v2, §2, p.3, (C2).

The base equality creates only `y_{j'} x_{i'}`; a row `t ∈ I_j` creates the terms `y_j x_k`
with `γ^j_t E_{t,k} ≠ 0`; a row `t ∈ Ī` creates `y_j x_k` (every `j`) with `θ_t E_{t,k} ≠ 0`;
a bound `k ∈ J` (resp. `J̄`) creates `y_j x_k` for every `j` when `λ_k ≠ 0` (resp. `µ_k ≠ 0`)
and creates nothing when its weight is `0`. -/
def CondC2 [DecidableEq N] [DecidableEq M] (E : R → N → ℝ) (i' : N) (j' : M) (σ : Sign)
    (I : M → Finset R) (Ibar : Finset R) (J Jbar : Finset N)
    (γ : M → R → ℝ) (θ : R → ℝ) (lam μ : N → ℝ) : Prop :=
  ((∃ j, (I j).Nonempty) ∨ Ibar.Nonempty ∨ J.Nonempty ∨ Jbar.Nonempty) →
    IsCancelled E i' j' σ I Ibar J Jbar γ θ lam μ j' i' ∧
    (∀ j, ∀ t ∈ I j, ∃ k, γ j t * E t k ≠ 0 ∧
      IsCancelled E i' j' σ I Ibar J Jbar γ θ lam μ j k) ∧
    (∀ t ∈ Ibar, ∃ j k, θ t * E t k ≠ 0 ∧
      IsCancelled E i' j' σ I Ibar J Jbar γ θ lam μ j k) ∧
    (∀ k ∈ J, lam k ≠ 0 ∧ ∃ j, IsCancelled E i' j' σ I Ibar J Jbar γ θ lam μ j k) ∧
    (∀ k ∈ Jbar, μ k ≠ 0 ∧ ∃ j, IsCancelled E i' j' σ I Ibar J Jbar γ θ lam μ j k)

/-- **An EC&R assignment `[I₁, …, I_m, Ī | J, J̄]` of class `l^σ`, for general `m`.**
Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, §2, p.3 (the EC&R procedure, Steps 1–3, conditions (C1) and (C2)), for the
set `S` of p.2 with `y ∈ Δ_m`.

Given the non-bound constraint rows `E_t·x ≥ f_t` (`t ∈ R`, the index set `T`) on the
variables `x_k` (`k ∈ N`), the class `l` through the unique entry `A^l_{j'i'} = 1` of its
bilinear constraint (base equality `y_{j'} x_{i'} − z_l = 0`), and a sign `σ`, the data
`I : M → Finset R`, `Ī`, `J`, `J̄` form an EC&R assignment of class `l^σ` when
1. `I₁ ∩ ⋯ ∩ I_m ∩ Ī = ∅` (no row lies in every `I_j` and in `Ī`; Step 2),
2. `J ∩ J̄ = ∅` (Step 3), and
3. there are weights `γ^j_t ≥ 0` (`t ∈ I_j`), `θ_t ≥ 0` (`t ∈ Ī`), `λ_k ≥ 0` (`k ∈ J`),
   `µ_k ≥ 0` (`k ∈ J̄`) for which the aggregation satisfies (C1) and (C2).

**Formalization Note.** The class `l` enters only through `(i', j')`, so it is passed as that
pair. The intersection condition of Step 2 is the common intersection ("subsets of T whose
intersection is empty"), not pairwise disjointness: Example 5, p.21, has `1⁻ ∈ I₁ ∩ I₂`. For
`M` a singleton and `J = J̄ = ∅` this is the published `m = 1` predicate
`NetBilinear.IsECRAssignmentOne`. Weight values outside their sets play no role. -/
def IsECRAssignment [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
    (E : R → N → ℝ) (i' : N) (j' : M) (σ : Sign)
    (I : M → Finset R) (Ibar : Finset R) (J Jbar : Finset N) : Prop :=
  (∀ t ∈ Ibar, ¬ ∀ j, t ∈ I j) ∧ Disjoint J Jbar ∧
    ∃ (γ : M → R → ℝ) (θ : R → ℝ) (lam μ : N → ℝ),
      (∀ j, ∀ t ∈ I j, 0 ≤ γ j t) ∧ (∀ t ∈ Ibar, 0 ≤ θ t) ∧
      (∀ k ∈ J, 0 ≤ lam k) ∧ (∀ k ∈ Jbar, 0 ≤ μ k) ∧
      CondC1 E i' j' σ I Ibar J Jbar γ θ lam μ ∧ CondC2 E i' j' σ I Ibar J Jbar γ θ lam μ

end NetBilinear.Supplement


