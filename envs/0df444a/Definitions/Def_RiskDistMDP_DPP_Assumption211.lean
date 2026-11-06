-- Prove2me | Definitions.Def_RiskDistMDP_DPP_Assumption211
-- name    : RiskDistMDP_DPP_Assumption211
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:54:26.939941+00:00
-- url     : https://prove2.me/theorems/c2b4f395-dfae-4959-8152-17da98a9f3d1
-- title:
--   State–action pairs $\Psi$, Markov association and Assumption 2.11
-- statement:
--   A state–action pair $(\mathfrak X,\mathfrak A)=((X_t),(A_t))$ belongs to the class of $\Psi$ (`InPsiClass`) if $\mathfrak X$ is $\mathbb F$-adapted, $\mathfrak A$ is $\mathbb G$-adapted, $X_1\sim\mu$, $\mathbb P(A_t\in\mathcal A_t(X_t),\ t\in\mathbb N)=1$, and for $t\in\mathbb N$ and Borel $B$
--   $$\mathbb P(X_{t+1}\in B\,|\,\mathcal G_t)=P(t,X_t,A_t,B)\quad\mathbb P\text{-a.s.}$$
--   The action process is **associated with** $\mathfrak p=(\pi_t)\in\Pi$ (`MarkovAssoc`) if $\mathbb P(A_t\in B\,|\,\mathcal U_t)=[\pi_t(X_t)](B)$ a.s. for every $t$ and $B$.
--
--   **Assumption 2.11**: (i) every pair of the given set $\Psi$ is in the class above; (ii) for every $\mathfrak p\in\Pi$ some pair of $\Psi$ is associated with $\mathfrak p$. The set `markovPairs` collects the pairs of $\Psi$ associated with some $\mathfrak p\in\Pi$; the optimization problem (P) is posed over all of $\Psi$, which may contain history-dependent pairs.
--
--   **Formalization Note** The paper's (2.2) and (2.3) are combined into the displayed equation, which is equivalent because $P(t,X_t,A_t,B)$ is $\sigma(X_t)\vee\sigma(A_t)$-measurable and $\sigma(X_t)\vee\sigma(A_t)\subseteq\mathcal G_t$. Association is read as conditioning on $\mathcal U_t$, i.e. the Markovian property (2.4) together with (2.5). The page cites only (2.5), but with (2.5) alone Lemma 3.3 fails (a fair coin $A_1=A_t$ for all $t$ with $\mathcal G_t=\sigma(A_1)$ satisfies (2.5) with uniform $\pi_t$). $\Psi$ is a given set, not all pairs with these properties.
-- source:
--   Cheng & Jaimungal, Risk-Averse Markov Decision Processes through a Distributional Lens, arXiv:2203.09612v4, §2.2, (2.2)–(2.5), pp. 6–7; Assumption 2.11, p. 13

import Mathlib
import Definitions.Def_RiskDistMDP_DPP_IsInfoSetting
import Definitions.Def_RiskDistMDP_DPP_MarkovPolicies

set_option autoImplicit false

open MeasureTheory

namespace RiskDistMDP.DPP

/-- The conditions every state-action pair `(𝔛, 𝔄)` in `Ψ` satisfies (arXiv:2203.09612v4, §2.2,
pp.6–7, and §2.5 with Assumption 2.11 (i), p.13):

* `𝔛 = (X_t)` is `𝔽`-adapted and `𝔄 = (A_t)` is `𝔾`-adapted (§2.2);
* (2.2) and (2.3): `ℙ(X_{t+1} ∈ B | 𝒢_t) = P(t, X_t, A_t, B)` `ℙ`-a.s., `t ∈ ℕ`, `B ∈ ℬ(𝕏)`;
* `ℙ(A_t ∈ 𝒜_t(X_t), t ∈ ℕ) = 1` (§2.5);
* `X₁ ∼ μ` (Assumption 2.11 (i)).

**Formalization Note** (2.2) `ℙ(X_{t+1} ∈ B | 𝒢_t) = ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t))` and (2.3)
`ℙ(X_{t+1} ∈ B | σ(X_t) ∨ σ(A_t)) = P(t, X_t, A_t, B)` are combined into one equation of conditional
expectations. The two forms are equivalent: `P(t, X_t, A_t, B)` is `σ(X_t) ∨ σ(A_t)`-measurable and
`σ(X_t) ∨ σ(A_t) ⊆ 𝒢_t`, so the tower property recovers (2.2) and (2.3) from the combined form. The
pair is `q = (q.1, q.2) = (𝔛, 𝔄)`; only `t ≥ 1` is constrained. -/
structure InPsiClass {Ω 𝕏 𝔸 : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace 𝕏]
    [MeasurableSpace 𝔸] (M : BorelMDP 𝕏 𝔸) (Pr : Measure Ω) (ℱ 𝒢 : ℕ → MeasurableSpace Ω)
    (q : (ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸)) : Prop where
  X_adapted : ∀ t, 1 ≤ t → Measurable[ℱ t] (q.1 t)
  A_adapted : ∀ t, 1 ≤ t → Measurable[𝒢 t] (q.2 t)
  transition : ∀ t, 1 ≤ t → ∀ B : Set 𝕏, MeasurableSet B →
    Pr[(q.1 (t + 1) ⁻¹' B).indicator (fun _ => (1 : ℝ)) | 𝒢 t] =ᵐ[Pr]
      fun ω => ((M.P t (q.1 t ω) (q.2 t ω) : Measure 𝕏) B).toReal
  admissible : ∀ᵐ ω ∂Pr, ∀ t, 1 ≤ t → q.2 t ω ∈ M.adm t (q.1 t ω)
  initial : Pr.map (q.1 1) = (M.μ : Measure 𝕏)

/-- The action process of `q = (𝔛, 𝔄)` is **associated with the Markovian policy** `𝔭 = (π_t)`
(arXiv:2203.09612v4, (2.4) and (2.5), p.7): for every `t ∈ ℕ` and `B ∈ ℬ(𝔸)`,
`ℙ(A_t ∈ B | 𝒰_t) = ℙ(A_t ∈ B | σ(X_t)) = [π_t(X_t)](B)` `ℙ`-a.s.

**Formalization Note** This is the reading R1: association means (2.4) (the action is Markovian
given the decision information `𝒰_t`) together with (2.5), written as one equation
`ℙ(A_t ∈ B | 𝒰_t) = [π_t(X_t)](B)`. It is equivalent to (2.4) ∧ (2.5) because `X_t` is
`ℱ_t ⊆ 𝒰_t`-measurable. Assumption 2.11 (ii) and the sentence after it cite only (2.5); with (2.5)
alone, Lemma 3.3 fails (a fair coin `A₁ = A_t` for all `t` with `𝒢_t = σ(A₁)` satisfies (2.5) with
uniform `π_t` but not (2.4)). -/
def MarkovAssoc {Ω 𝕏 𝔸 : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    (Pr : Measure Ω) (ℱ 𝒢 : ℕ → MeasurableSpace Ω) (𝔭 : ℕ → 𝕏 → ProbabilityMeasure 𝔸)
    (q : (ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸)) : Prop :=
  ∀ t, 1 ≤ t → ∀ B : Set 𝔸, MeasurableSet B →
    Pr[(q.2 t ⁻¹' B).indicator (fun _ => (1 : ℝ)) | decInfo ℱ 𝒢 t] =ᵐ[Pr]
      fun ω => ((𝔭 t (q.1 t ω) : Measure 𝔸) B).toReal

/-- **Assumption 2.11** (arXiv:2203.09612v4, p.13) on the family `{(Ω, ℋ, ℙ), 𝔽, 𝔾, Ψ}` for the
model data `M` (which carries `μ` and `P`): (i) every `(𝔛, 𝔄) ∈ Ψ` satisfies the conditions of
`InPsiClass` (adaptedness, (2.2)–(2.3), admissibility a.s., `X₁ ∼ μ`); (ii) for every Markovian
policy `𝔭 ∈ Π` there is `(𝔛, 𝔄) ∈ Ψ` associated with `𝔭` (`MarkovAssoc`, reading R1).

**Formalization Note** `Ψ` is a given set of pairs, not the set of all pairs satisfying the
conditions. The measurability of `P` required in (i) is part of `BorelMDP.Standing`. -/
def Assumption211 {Ω 𝕏 𝔸 : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    (M : BorelMDP 𝕏 𝔸) (Pr : Measure Ω) (ℱ 𝒢 : ℕ → MeasurableSpace Ω)
    (Ψ : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸))) : Prop :=
  (∀ q ∈ Ψ, InPsiClass M Pr ℱ 𝒢 q) ∧
    ∀ 𝔭 ∈ MarkovPolicies M, ∃ q ∈ Ψ, MarkovAssoc Pr ℱ 𝒢 𝔭 q

/-- The pairs `(𝔛^𝔭, 𝔄^𝔭) ∈ Ψ` associated with some Markovian policy `𝔭 ∈ Π`
(arXiv:2203.09612v4, p.13), over which the infima of Theorem 4.2 (b) and Theorem 5.5 (c) run. -/
def markovPairs {Ω 𝕏 𝔸 : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace 𝕏] [MeasurableSpace 𝔸]
    (M : BorelMDP 𝕏 𝔸) (Pr : Measure Ω) (ℱ 𝒢 : ℕ → MeasurableSpace Ω)
    (Ψ : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸))) : Set ((ℕ → Ω → 𝕏) × (ℕ → Ω → 𝔸)) :=
  {q | q ∈ Ψ ∧ ∃ 𝔭 ∈ MarkovPolicies M, MarkovAssoc Pr ℱ 𝒢 𝔭 q}

end RiskDistMDP.DPP


