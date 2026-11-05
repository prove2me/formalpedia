-- Prove2me | Definitions.Def_BauerleRiederMDP_ConvexModels_StructureAssumption
-- name    : BauerleRiederMDP_ConvexModels_StructureAssumption
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:58.513483+00:00
-- url     : https://prove2.me/theorems/454b5bd3-0a86-4a4e-a402-1891f83336d6
-- title:
--   The Structure Assumption $(\mathrm{SA}_N)$ for given sets $\mathbb{IM}_n$, $\Delta_n$
-- statement:
--   Let $(E,A,D_n,Q_n,r_n,g_N)$ be a Markov Decision Model with horizon $N$, let $\mathbb{IM}(E)$ be the measurable functions $E\to[-\infty,\infty)$, $F_n$ the decision rules at time $n$, and $T_n$ the maximal reward operator. Sets $\mathbb{IM}_n\subset\mathbb{IM}(E)$ ($n\le N$) and $\Delta_n\subset F_n$ ($n<N$) satisfy the **Structure Assumption** $(\mathrm{SA}_N)$ if for all $n=0,1,\dots,N-1$:
--
--   1. $g_N\in\mathbb{IM}_N$;
--   2. if $v\in\mathbb{IM}_{n+1}$, then $T_nv$ is well defined and $T_nv\in\mathbb{IM}_n$;
--   3. for all $v\in\mathbb{IM}_{n+1}$ there exists a maximizer $f_n$ of $v$ with $f_n\in\Delta_n$.
--
--   Under $(\mathrm{SA}_N)$ the value functions solve the Bellman equation and maximizers form optimal policies (Theorem 2.3.8); the theorems of §2.4 identify concrete sets satisfying it.
--
--   **Formalization Note** "$T_nv$ is well defined" is the existence of every integral $\int v(x')\,Q_n(dx'\mid x,a)$, $(x,a)\in D_n$: the positive or the negative part of $v$ has finite integral. It is spelled out because the platform's `erealIntegral` returns $-\infty$ when both parts are infinite. The model, $\mathbb{IM}(E)$, $T_n$, decision rules and maximizers are the platform's `MDPFinance.StructuredModels` definitions.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Structure Assumption (SAN), p.23 (PDF p.38); Definition 2.3.1, p.19 (PDF p.34)

import Mathlib
import Definitions.Def_MDPFinance_StructuredModels_Model
import Definitions.Def_MDPFinance_StructuredModels_Policy
import Definitions.Def_MDPFinance_StructuredModels_Operators

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.ConvexModels

open MDPFinance.StructuredModels

/-- The **Structure Assumption (SAN)** for given sets `IM_n` and `Δ_n` (Bäuerle & Rieder,
*Markov Decision Processes with Applications to Finance* (2011), Structure Assumption (SAN),
p.23, PDF p.38): `IM_n ⊂ IM(E)` for `n = 0, …, N`, `Δ_n ⊂ F_n` for `n = 0, …, N − 1`, and for
all `n = 0, 1, …, N − 1`:
(i) `g_N ∈ IM_N`;
(ii) if `v ∈ IM_{n+1}` then `T_n v` is well defined and `T_n v ∈ IM_n`;
(iii) for all `v ∈ IM_{n+1}` there exists a maximizer `f_n` of `v` with `f_n ∈ Δ_n`.

The model `M`, the space `IM(E)`, the operator `T_n`, decision rules and maximizers are the
platform's `MDPFinance.StructuredModels` definitions (Definition 2.1.1, p.14; p.19;
Definition 2.3.1, p.19; Definition 2.1.5, p.16; Definition 2.3.6, p.21).

**Formalization Note.** "`T_n v` is well defined" is the existence of every integral
`∫ v(x′) Q_n(dx′|x,a)`, `(x,a) ∈ D_n`, in the operator `L_n` (Definition 2.3.1 a), "whenever
the integral exists"): the integral of the positive part or of the negative part of `v` is
finite. It is stated explicitly because the platform's `erealIntegral` returns `−∞` when both
are infinite. The families `IM_n`, `Δ_n` are indexed by `ℕ`; only `n ≤ N` (resp. `n < N`)
is constrained. -/
def StructureAssumption {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (IMs : ℕ → Set (E → EReal)) (Δ : ℕ → Set (E → A)) :
    Prop :=
  (∀ n ≤ N, IMs n ⊆ IM E) ∧
  (∀ n < N, Δ n ⊆ {f | IsDecisionRule M n f}) ∧
  (fun x => (M.g x : EReal)) ∈ IMs N ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1),
    (∀ xa ∈ M.D n, ∫⁻ x', (v x' ⊔ 0).toENNReal ∂(M.Q n xa) ≠ ⊤ ∨
      ∫⁻ x', ((-v x') ⊔ 0).toENNReal ∂(M.Q n xa) ≠ ⊤) ∧
    T M n v ∈ IMs n) ∧
  (∀ n < N, ∀ v ∈ IMs (n + 1), ∃ f ∈ Δ n, IsMaximizer M n v f)

end BauerleRiederMDP.ConvexModels


