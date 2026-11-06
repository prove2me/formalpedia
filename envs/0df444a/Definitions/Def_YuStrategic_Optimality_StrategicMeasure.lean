-- Prove2me | Definitions.Def_YuStrategic_Optimality_StrategicMeasure
-- name    : YuStrategic_Optimality_StrategicMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:23:59.757135+00:00
-- url     : https://prove2.me/theorems/f84f2125-937c-471b-86b0-caa6769a4288
-- title:
--   The strategic measure $\rho_{p_0}[\pi]$ of a policy and an initial distribution
-- statement:
--   Let $\pi=(\mu_n)$ be a policy and $p_0\in\mathcal P(\mathbb X)$. A probability measure $p$ on the Borel sets of $\Omega$ is the **strategic measure** $\rho_{p_0}[\pi]$ if it is the law of the controlled process started from $p_0$, i.e. if
--   1. $x_0$ has law $p_0$ under $p$;
--   2. for every $n\ge0$ and Borel $B\subseteq H_n$, $C\subseteq\mathbb A$: $\;p\{h_n\in B,\ a_n\in C\}=\int_{\{h_n\in B\}}\mu_n(C\mid h_n)\,dp$;
--   3. for every $n\ge0$ and Borel $B\subseteq H_n'$, $C\subseteq\mathbb X$: $\;p\{h_n'\in B,\ x_{n+1}\in C\}=\int_{\{h_n'\in B\}}q(C\mid x_n,a_n)\,dp$.
--
--   In the paper, $p_0$ together with the kernels $\mu_0(da_0\mid x_0),q(dx_1\mid x_0,a_0),\mu_1(da_1\mid h_1),\dots$ determines a unique probability measure $\mathbb P^\pi_{p_0}$ on the universally measurable sets $\mathcal U(\Omega)$, and $\rho_{p_0}[\pi]$ is its restriction to $\mathcal B(\Omega)$; conditions 1–3 fix all finite-dimensional marginals and so characterize exactly this restriction (compare Lemma 5.1 of the paper). Writing $\rho_x[\pi]$ for $p_0=\delta_x$, strategic measures are the decision variables of the optimization problems of Theorem 3.3.
--
--   **Formalization Note.** The predicate `IsStrategicMeasure M π p₀ P` is the characterization 1–3; existence and uniqueness of such a $P$ is a separate milestone. The integrands $h_n\mapsto\mu_n(C\mid h_n)$ are only universally measurable; Mathlib's lower Lebesgue integral of such a function equals the integral with respect to the completion of $p$, the paper's convention (p. 4).
-- source:
--   Yu, arXiv:2206.06492v3, §2.2, p. 6 (P^π_{p0}, [5, Prop. 7.45]); §3, p. 7 (ρ_{p0}[π] as the restriction to B(Ω)); Lemma 5.1, p. 24

import Mathlib
import Definitions.Def_YuStrategic_Optimality_Policy

namespace YuStrategic.Optimality

open MeasureTheory ProbabilityTheory BertsekasShreve.BorelInfinite

variable {X A : Type} [TopologicalSpace X] [MeasurableSpace X]
  [TopologicalSpace A] [MeasurableSpace A]

/-- `P` is the strategic measure `ρ_{p₀}[π]` of the policy `π` and the initial distribution `p₀`
(Yu, arXiv:2206.06492v3, §2.2, p. 6, and §3, p. 7): the probability measure on the Borel sets of
`Ω = (X × A)^∞` determined by `p₀(dx₀), μ₀(da₀ | x₀), q(dx₁ | x₀, a₀), μ₁(da₁ | h₁), …`. It is
characterized by its finite-dimensional laws:
1. `x₀` has law `p₀`;
2. for every `n` and Borel `B ⊆ Hₙ`, `C ⊆ A`:
   `P{hₙ ∈ B, aₙ ∈ C} = ∫_{hₙ ∈ B} μₙ(C | hₙ) dP`;
3. for every `n` and Borel `B ⊆ H′ₙ = Hₙ × A`, `C ⊆ X`:
   `P{h′ₙ ∈ B, xₙ₊₁ ∈ C} = ∫_{h′ₙ ∈ B} q(C | xₙ, aₙ) dP`.

**Formalization Note.** The paper defines `ρ_{p₀}[π]` as the restriction to `B(Ω)` of the
unique measure `P^π_{p₀}` on `U(Ω)` given by [Bertsekas–Shreve, Prop. 7.45]; conditions 1–3
determine all finite-dimensional marginals and hence that restriction (compare the paper's
Lemma 5.1). Existence and uniqueness of such a `P` is the milestone
`strategicMeasure_existsUnique`. The integrand `hₙ ↦ μₙ(C | hₙ)` is only universally measurable;
Mathlib's lower Lebesgue integral of it equals the integral against the completion of `P`, which
is the paper's convention (p. 4). -/
def IsStrategicMeasure (M : Model X A) (π : Policy M) (p₀ : ProbabilityMeasure X)
    (P : ProbabilityMeasure (Path X A)) : Prop :=
  (P : Measure (Path X A)).map (stateAt 0) = (p₀ : Measure X) ∧
  (∀ (n : ℕ) (B : Set (Hist X A n)) (C : Set A), MeasurableSet B → MeasurableSet C →
    (P : Measure (Path X A)) {ω | histAt n ω ∈ B ∧ actAt n ω ∈ C} =
      ∫⁻ ω in {ω | histAt n ω ∈ B}, (π.μ n).toFun (histAt n ω) C ∂(P : Measure (Path X A))) ∧
  (∀ (n : ℕ) (B : Set (Hist X A n × A)) (C : Set X), MeasurableSet B → MeasurableSet C →
    (P : Measure (Path X A)) {ω | (histAt n ω, actAt n ω) ∈ B ∧ stateAt (n + 1) ω ∈ C} =
      ∫⁻ ω in {ω | (histAt n ω, actAt n ω) ∈ B}, M.q (stateAt n ω, actAt n ω) C
        ∂(P : Measure (Path X A)))

end YuStrategic.Optimality


