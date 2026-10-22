-- Prove2me | Definitions.Def_DynamicAssortment_Separation_AssumptionOne
-- name    : DynamicAssortment_Separation_AssumptionOne
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T10:36:25.947094+00:00
-- url     : https://prove2.me/theorems/052497a0-4b4a-4d79-a9b9-be3d769b516f
-- title:
--   Assumption 1 (Identifiability), per test assortment: an inverse η of p(A_j, ·) that is unique and locally Lipschitz, and Lipschitz choice probabilities
-- statement:
--   For an assortment $A$, let $D(A)=\{\rho\in\mathbb R^N: \rho_i>0\ (i\in A),\ \sum_{i\in A}\rho_i<1\}$ (`etaDomain`). `Identifiability f C eta` says that, for every test assortment $A_j$:
--
--   1. **Inverse.** For every $\rho\in D(A_j)$, $\ p_i\big(A_j,\eta_{A_j}(\rho)\big)=\rho_i$ for all $i\in A_j$.
--   2. **Uniqueness.** If $\rho\in D(A_j)$ and $p_i(A_j,\mu')=\rho_i$ for all $i\in A_j$, then $\mu'_i=\eta_{A_j}(\rho)_i$ for all $i\in A_j$.
--   3. **Local Lipschitz inverse.** For every $\rho\in D(A_j)$ there are $r>0$ and $L$ such that
--   $$\|\eta_{A_j}(\rho')-\eta_{A_j}(\rho'')\|_{A_j}\le L\,\|\rho'-\rho''\|_{A_j}\quad\text{for all }\rho',\rho''\in D(A_j)\text{ with }\|\rho'-\rho\|_{A_j}<r,\ \|\rho''-\rho\|_{A_j}<r.$$
--
--   In addition:
--
--   4. **Lipschitz choice probabilities.** There is one constant $K$ such that $\nu\mapsto(p_i(S,\nu))_{i}$ is $K$-Lipschitz in the sup norm for every $S\in\mathcal S$.
--
--   This is Assumption 1 of Sauré and Zeevi (2013, p. 393). Under it the mean utilities of the products in a test assortment can be recovered from that assortment's purchase probabilities, and recovered stably. The logit model (standard Gumbel $F$) satisfies it, with $\eta_A(\rho)_i=\log\big(\rho_i/(1-\sum_{j\in A}\rho_j)\big)$.
--
--   **Formalization Note** The page states the assumption for $p(\mathcal N,\cdot)$, for vectors $\rho\in\mathbb R^N_+$ with $\sum_i\rho_i<1$. It applies $\eta$ to $\hat p_t(A_j)$, whose coordinates outside $A_j$ are zero, by the convention that such products are "infinitely unattractive" ($\eta(\rho)_i=-\infty$). The per-assortment form above is the finite-valued restatement of that convention on the test assortments, the only sets the estimator uses. Off $D(A_j)$ the function $\eta$ is unconstrained, which corresponds to the paper's $-\infty$ case. Item 4 is stated for every $S\in\mathcal S$, because Step 2 of the proof of Theorem 2 (p. 402) uses the Lipschitz continuity of every $p(S,\cdot)$; the page states it for $p(\mathcal N,\cdot)$ only. This is an added hypothesis. The logit model satisfies it.
-- source:
--   Sauré, Zeevi, Optimal Dynamic Assortment Planning with Demand Learning, Manuf. Serv. Oper. Manag. 15(3), 2013, p. 393, Assumption 1 (Identifiability), and the remark following it (pp. 393–394); Lipschitz continuity of p(S, ·) as used in App. A, Step 2, p. 402

import Mathlib
import Definitions.Def_DynamicAssortment_Separation_ChoiceModel
import Definitions.Def_DynamicAssortment_Separation_SeparationPolicy

namespace DynamicAssortment.Separation

/-- Domain of the inverse on an assortment `A`: purchase-probability vectors that are positive on
`A` and leave positive no-purchase probability, `{ρ | ρ_i > 0 (i ∈ A), ∑_{i ∈ A} ρ_i < 1}`. -/
def etaDomain {N : ℕ} (A : Finset (Fin N)) : Set (Fin N → ℝ) :=
  {ρ | (∀ i ∈ A, 0 < ρ i) ∧ ∑ i ∈ A, ρ i < 1}

/-- Assumption 1 (Identifiability, p. 393), in its per-assortment form on the test assortments,
with `eta A` the inverse of `p(A, ·)`:
1. `inverse`: `p_i(A_j, η(ρ)) = ρ_i` for `i ∈ A_j`, for every `ρ` in the domain;
2. `unique`: any `μ'` with `p_i(A_j, μ') = ρ_i` for all `i ∈ A_j` agrees with `η(ρ)` on `A_j`;
3. `locallyLipschitz`: `η` is Lipschitz (in the max-norm on `A_j`) on a neighbourhood of every
   point of the domain;
4. `lipschitz`: every `p(S, ·)`, `S ∈ 𝒮`, is Lipschitz (sup norms) with one constant `K`. -/
structure Identifiability {N : ℕ} (f : ℝ → ℝ) (C : ℕ)
    (eta : Finset (Fin N) → (Fin N → ℝ) → (Fin N → ℝ)) : Prop where
  inverse : ∀ j < numTests N C, ∀ ρ ∈ etaDomain (testAssortment N C j),
    ∀ i ∈ testAssortment N C j,
      choiceProb f (eta (testAssortment N C j) ρ) (testAssortment N C j) i = ρ i
  unique : ∀ j < numTests N C, ∀ ρ ∈ etaDomain (testAssortment N C j), ∀ μ' : Fin N → ℝ,
    (∀ i ∈ testAssortment N C j, choiceProb f μ' (testAssortment N C j) i = ρ i) →
      ∀ i ∈ testAssortment N C j, μ' i = eta (testAssortment N C j) ρ i
  locallyLipschitz : ∀ j < numTests N C, ∀ ρ ∈ etaDomain (testAssortment N C j),
    ∃ r : ℝ, 0 < r ∧ ∃ L : ℝ, ∀ ρ' ∈ etaDomain (testAssortment N C j),
      ∀ ρ'' ∈ etaDomain (testAssortment N C j),
        normOn (testAssortment N C j) (ρ' - ρ) < r →
        normOn (testAssortment N C j) (ρ'' - ρ) < r →
        normOn (testAssortment N C j)
            (eta (testAssortment N C j) ρ' - eta (testAssortment N C j) ρ'') ≤
          L * normOn (testAssortment N C j) (ρ' - ρ'')
  lipschitz : ∃ K : NNReal, ∀ S ∈ assortments N C,
    LipschitzWith K (fun ν : Fin N → ℝ => fun i => choiceProb f ν S i)

end DynamicAssortment.Separation


