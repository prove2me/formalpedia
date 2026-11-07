-- Prove2me | Definitions.Def_ReplicableDecisions_hopSeparation
-- name    : ReplicableDecisions_hopSeparation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:34.739039+00:00
-- url     : https://prove2.me/theorems/c7a4fb46-e6f5-4cc7-a97a-ed18d523c611
-- title:
--   Definition 2.1 — hop separation $s_L$ and the budget $L_\rho=2\lceil 2/\rho\rceil$
-- statement:
--   Suppose $A_0,A_1\ne\emptyset$. For an integer $L\ge1$,
--
--   $$
--   s_L=\min\Bigl\{\max_{1\le i\le\ell}h(Q_{i-1},Q_i):\ 1\le\ell\le L,\ Q_0\in A_0,\ Q_\ell\in A_1,\ Q_1,\dots,Q_{\ell-1}\in\mathcal P\Bigr\}.
--   $$
--
--   A chain of $\ell$ hops has $\ell+1$ models, and repetitions are permitted. The hop budget is $L_\rho=2\lceil 2/\rho\rceil$, and $s_\rho=s_{L_\rho}$.
--
--   The scale $s_\rho$ is the single number that pins the replicable sample size in the goal theorem.
--
--   **Formalization Note** The minimum is the `sInf` of a finite set, nonempty under $A_0,A_1\ne\emptyset$ and $L\ge1$, and every statement here carries those hypotheses. A proved sanity check shows that it is attained, positive, and that $s_1=\min_{P\in A_0,Q\in A_1}h(P,Q)$.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), Definition 2.1, (2.3), p.9 (PDF p.11)

import Mathlib
import Definitions.Def_ReplicableDecisions_hellinger
import Definitions.Def_ReplicableDecisions_Experiment
import Definitions.Def_ReplicableDecisions_forcedDist

namespace ReplicableDecisions

/-- **The largest step of a chain,** `max_{1≤i≤ℓ} h(Q_{i−1}, Q_i)`, for a chain `Q₀, …, Q_ℓ` of `ℓ`
hops. Chen, *Replicable Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…),
Definition 2.1, (2.3), p.9 (PDF p.11).

**Formalization Note.** The chain is `Q : Fin (ℓ + 1) → ι`; the supremum over the finite `Fin ℓ` is
the printed maximum when `ℓ ≥ 1`, the only case `chainValues` uses. -/
noncomputable def chainMaxStep {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) {ℓ : ℕ}
    (Q : Fin (ℓ + 1) → ι) : ℝ :=
  ⨆ j : Fin ℓ, hellinger (E.P (Q j.castSucc)) (E.P (Q j.succ))

/-- **The value set of (2.3):** the largest steps of chains of `1 ≤ ℓ ≤ L` hops from `A₀` to `A₁`,
with interior models anywhere in the family and repetitions permitted. Chen, STOC 2027 submission
(sha256 52d181db…), Definition 2.1, p.9 (PDF p.11). -/
def chainValues {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (Γ : ι → Set Bool)
    (L : ℕ) : Set ℝ :=
  {v | ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ L ∧ ∃ Q : Fin (ℓ + 1) → ι,
    Q 0 ∈ forcedClass Γ false ∧ Q (Fin.last ℓ) ∈ forcedClass Γ true ∧ v = chainMaxStep E Q}

/-- **Hop separation** `s_L`. Chen, STOC 2027 submission (sha256 52d181db…), Definition 2.1, (2.3),
p.9 (PDF p.11): the minimum, over chains of at most `L` hops between the forced classes, of the
largest Hellinger step.

**Formalization Note.** The page says "The minimum is over a finite nonempty set" (p.10), which holds
when `A₀, A₁ ≠ ∅` and `L ≥ 1`; every statement here carries those hypotheses. A proved sanity check
shows that `sInf` is then attained and positive. -/
noncomputable def hopSeparation {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z)
    (Γ : ι → Set Bool) (L : ℕ) : ℝ :=
  sInf (chainValues E Γ L)

/-- **The hop budget** `L_ρ = 2⌈2/ρ⌉`. Chen, STOC 2027 submission (sha256 52d181db…), Definition 2.1,
p.9 (PDF p.11). The scale `s_ρ` is `hopSeparation E Γ (hopBudget ρ)`. -/
noncomputable def hopBudget (ρ : ℝ) : ℕ :=
  2 * ⌈2 / ρ⌉₊

end ReplicableDecisions


