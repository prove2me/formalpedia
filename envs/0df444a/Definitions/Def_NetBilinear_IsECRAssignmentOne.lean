-- Prove2me | Definitions.Def_NetBilinear_IsECRAssignmentOne
-- name    : NetBilinear_IsECRAssignmentOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:42.106025+00:00
-- url     : https://prove2.me/theorems/add2e242-fee9-4684-91d4-bfe784899153
-- title:
--   EC&R assignment $[\mathcal I_1,\bar{\mathcal I}]$ of class $l^\pm$ for $m=1$, with conditions (C1) and (C2)
-- statement:
--   Consider linear constraints $E_t\cdot x\ge f_t$, $t\in R$, on variables $x_k$, $k\in N$ ($N$ finite), a single variable $y_1$, and the bilinear equalities $y_1x_k=z_k$. Fix a base index $l\in N$ and a sign $\sigma\in\{+,-\}$, and sets of rows $\mathcal I_1,\bar{\mathcal I}\subseteq R$. Aggregate
--
--   1. the base equality $y_1x_l-z_l=0$ with weight $\sigma=\pm1$;
--   2. each row $t\in\mathcal I_1$ multiplied by $\gamma_t\,y_1$;
--   3. each row $t\in\bar{\mathcal I}$ multiplied by $\theta_t\,(1-y_1)$.
--
--   The coefficient of the bilinear term $y_1x_k$ in the aggregate is
--   $$c(k)=\sigma[k=l]+\sum_{t\in\mathcal I_1}\gamma_tE_{t,k}-\sum_{t\in\bar{\mathcal I}}\theta_tE_{t,k}.$$
--   The term is **created** by a used constraint if that constraint's contribution to it is nonzero, and **canceled** if it is created by at least one used constraint and $c(k)=0$.
--
--   The pair $[\mathcal I_1,\bar{\mathcal I}]$ is an **EC&R assignment of class $l^\sigma$** if $\mathcal I_1\cap\bar{\mathcal I}=\emptyset$ and there are weights $\gamma_t\ge0$ ($t\in\mathcal I_1$) and $\theta_t\ge0$ ($t\in\bar{\mathcal I}$) such that
--
--   - **(C1)** at least $|\mathcal I_1|+|\bar{\mathcal I}|$ bilinear terms are canceled, and
--   - **(C2)** if $\mathcal I_1\cup\bar{\mathcal I}\neq\emptyset$, then for every constraint used (the base equality included), at least one bilinear term it creates is canceled.
--
--   This is the extended cancel-and-relax procedure of the paper's §2 for one $y$ variable, in the reduced form $[\mathcal I_1,\bar{\mathcal I}]$ of Remark 1 (bound-constraint multiples merged into the relaxation step). Aggregating with such weights and relaxing the remaining bilinear terms produces the class-$l^\pm$ EC&R inequalities that describe the convex hull.
--
--   **Formalization Note** `baseContrib`, `aggCoef`, `IsCreated`, `IsCancelled`, `CondC1`, `CondC2` spell out the steps above; (C1) counts canceled terms with `Set.ncard` over the finite index type. Weights are real functions on all rows; only their values on $\mathcal I_1$, $\bar{\mathcal I}$ matter.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, §2, p.3 (EC&R procedure Steps 1–3, conditions (C1), (C2)); §3.1, p.4 (m = 1, y1xk = zk for k ∈ K = N); Remark 1, p.5 (reduced form [I1, Ī])

import Mathlib
import Definitions.Def_NetBilinear_Network

namespace NetBilinear

variable {R N : Type*}

/-- **The contribution of the base equality to the bilinear term `y₁x_k`.**
arXiv:2302.14151v2, §2, p.3, Step 1: the base equality `y₁x_l − z_l = 0` (for `m = 1` the
indices of `z` and `x` are matched, §3.1, p.4: "y1xk = zk for all k ∈ K = N") is aggregated
with weight `1` (class `l⁺`) or `−1` (class `l⁻`). Its only bilinear term is `y₁x_l`, with
coefficient `σ = ±1`. -/
def baseContrib [DecidableEq N] (l : N) (σ : Sign) (k : N) : ℝ :=
  if k = l then σ.toReal else 0

/-- **The aggregated coefficient of `y₁x_k`** for `m = 1` and the reduced assignment `[I₁, Ī]`
of Remark 1 (p.5).
arXiv:2302.14151v2, §2, p.3, Steps 1–2: the base equality with sign `σ`; each row `t ∈ I₁`
(the constraint `E_t·x ≥ f_t`) multiplied by `γ_t y₁`, contributing `γ_t E_{t,k}` to the term
`y₁x_k`; each row `t ∈ Ī` multiplied by `θ_t (1 − y₁)`, contributing `−θ_t E_{t,k}` to `y₁x_k`.

`aggCoef E l σ I₁ Ī γ θ k = σ[k = l] + Σ_{t∈I₁} γ_t E_{t,k} − Σ_{t∈Ī} θ_t E_{t,k}`. -/
def aggCoef [DecidableEq N] (E : R → N → ℝ) (l : N) (σ : Sign) (I₁ Ibar : Finset R)
    (γ θ : R → ℝ) (k : N) : ℝ :=
  baseContrib l σ k + ∑ t ∈ I₁, γ t * E t k - ∑ t ∈ Ibar, θ t * E t k

/-- **The term `y₁x_k` is created** by some constraint used in the aggregation: the base
equality, a row of `I₁` times `γ_t y₁`, or a row of `Ī` times `θ_t(1 − y₁)` produces it with a
nonzero coefficient. arXiv:2302.14151v2, (C2), p.3 ("all those created after multiplying that
constraint with its corresponding weight"). -/
def IsCreated [DecidableEq N] (E : R → N → ℝ) (l : N) (σ : Sign) (I₁ Ibar : Finset R)
    (γ θ : R → ℝ) (k : N) : Prop :=
  baseContrib l σ k ≠ 0 ∨ (∃ t ∈ I₁, γ t * E t k ≠ 0) ∨ (∃ t ∈ Ibar, θ t * E t k ≠ 0)

/-- **The term `y₁x_k` is canceled**: it is created by some used constraint and its aggregated
coefficient is zero. arXiv:2302.14151v2, (C1), p.3 ("bilinear terms are canceled (i.e., their
coefficient becomes zero)").

**Formalization Note.** A term no used constraint creates also has coefficient `0`; it is not
counted as canceled, otherwise (C1) would hold for free. -/
def IsCancelled [DecidableEq N] (E : R → N → ℝ) (l : N) (σ : Sign) (I₁ Ibar : Finset R)
    (γ θ : R → ℝ) (k : N) : Prop :=
  IsCreated E l σ I₁ Ibar γ θ k ∧ aggCoef E l σ I₁ Ibar γ θ k = 0

/-- **Condition (C1) for `m = 1`**: at least `|I₁| + |Ī|` bilinear terms are canceled.
arXiv:2302.14151v2, §2, p.3, (C1) ("at least Σ_{j∈M}|I_j|+|Ī|+|J|+|J̄| bilinear terms are
canceled"), with `J = J̄ = ∅` (Remark 1, p.5). -/
def CondC1 [DecidableEq N] (E : R → N → ℝ) (l : N) (σ : Sign) (I₁ Ibar : Finset R)
    (γ θ : R → ℝ) : Prop :=
  I₁.card + Ibar.card ≤ {k : N | IsCancelled E l σ I₁ Ibar γ θ k}.ncard

/-- **Condition (C2) for `m = 1`**: if `I₁ ∪ Ī ≠ ∅`, then for each constraint used in the
aggregation, including the base equality, at least one bilinear term among those it creates is
canceled. arXiv:2302.14151v2, §2, p.3, (C2), with `J = J̄ = ∅` (Remark 1, p.5). -/
def CondC2 [DecidableEq N] (E : R → N → ℝ) (l : N) (σ : Sign) (I₁ Ibar : Finset R)
    (γ θ : R → ℝ) : Prop :=
  (I₁.Nonempty ∨ Ibar.Nonempty) →
    (∃ k, baseContrib l σ k ≠ 0 ∧ IsCancelled E l σ I₁ Ibar γ θ k) ∧
    (∀ t ∈ I₁, ∃ k, γ t * E t k ≠ 0 ∧ IsCancelled E l σ I₁ Ibar γ θ k) ∧
    (∀ t ∈ Ibar, ∃ k, θ t * E t k ≠ 0 ∧ IsCancelled E l σ I₁ Ibar γ θ k)

/-- **An EC&R assignment `[I₁, Ī]` of class `l±` for `m = 1`.**
arXiv:2302.14151v2, §2, p.3 (the EC&R procedure, Steps 1–3, conditions (C1) and (C2)) in the
reduced form of Remark 1, p.5 ("In this case, the characterization of EC&R assignment can be
reduced further to [I1, Ī]").

Given the non-bound constraint rows `E_t·x ≥ f_t` (`t ∈ R`) on the variables `x_k` (`k ∈ N`),
a base index `l ∈ N` and a sign `σ`, the pair `(I₁, Ī)` of row sets is an EC&R assignment of
class `l^σ` when `I₁ ∩ Ī = ∅` and there are weights `γ_t ≥ 0` (`t ∈ I₁`) and `θ_t ≥ 0`
(`t ∈ Ī`) for which the aggregation satisfies (C1) and (C2).

**Formalization Note.** Stated for an arbitrary row family `E` (the general `m = 1` set `S¹`);
the network case is `Network.IsECRAssignment`. Values of `γ`, `θ` off `I₁`, `Ī` play no role. -/
def IsECRAssignmentOne [Fintype N] [DecidableEq N] (E : R → N → ℝ) (l : N) (σ : Sign)
    (I₁ Ibar : Finset R) : Prop :=
  Disjoint I₁ Ibar ∧
    ∃ γ θ : R → ℝ, (∀ t ∈ I₁, 0 ≤ γ t) ∧ (∀ t ∈ Ibar, 0 ≤ θ t) ∧
      CondC1 E l σ I₁ Ibar γ θ ∧ CondC2 E l σ I₁ Ibar γ θ

end NetBilinear


