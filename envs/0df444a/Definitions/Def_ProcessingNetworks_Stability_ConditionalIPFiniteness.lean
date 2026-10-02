-- Prove2me | Definitions.Def_ProcessingNetworks_Stability_ConditionalIPFiniteness
-- name    : ProcessingNetworks_Stability_ConditionalIPFiniteness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:16:43.377925+00:00
-- url     : https://prove2.me/theorems/884aae1c-4cff-411f-b99d-bc49af81b456
-- title:
--   Assumption 3.8 — finiteness of conditional IP-pair distributions
-- statement:
--   $\Psi$ denotes the SPN's **initial processing variables** (Eq. 2.3): the residual
--   service time and eventual output vector of every service that is already open at time $0$,
--   collectively — an IP pair being one such $(v, \varphi)$.
--
--   **Assumption 3.8.** As $x$ ranges over the countable state space $\mathcal{X}$ of the ambient
--   Markov chain, there are only **finitely many distinct conditional distributions** of the IP pairs
--   $(v, \varphi)$ in $\Psi$, given $X(0) = x$.
--
--   This is a mild supplement to Assumption 3.1, used in Chapter 6 to establish the finiteness of a
--   set $\Pi_0$ needed for the fluid-limit stochastic bound (6.36). It is formalized as
--   `HasFinitelyManyConditionalIPDistributions X0 N0 Psi`: the set of laws
--   $$
--   \big\{\, \mathrm{Law}\big((v_j(\ell), \varphi_j(\ell)) \,\big|\, X(0) = x\big) \;:\; x \in \mathcal{X},\ j \in \mathcal{J},\ \ell < N_j^x(0) \,\big\}
--   $$
--   is finite, where `Psi ω j ℓ` is the $\ell$-th IP pair of activity $j$ and $N_j^x(0) =$ `N0 x j` is the
--   number of type-$j$ services open at time $0$ under initial state $x$ (only those $\ell$ index
--   genuine IP pairs).
--
--   **Formalization note.** The conditional law given $X(0) = x$ is the pushforward of the pair
--   under the conditional probability measure $\Pr(\,\cdot \mid X(0) = x)$ (Mathlib's `ℙ[|s]`), so
--   that states with different initial masses but the same conditional law count once, as in the
--   book; and the assumption is about the laws of the individual IP pairs, exactly as the book's
--   example (four residual-service-time distributions) reads it, not about the joint law of $\Psi$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 59, Assumption 3.8

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation

namespace ProcessingNetworks.Stability

open MeasureTheory ProbabilityTheory

/-- Assumption 3.8 (finiteness of conditional IP-pair distributions), Dai & Harrison, p. 59: as
`x` ranges over the countable state space, the conditional distributions of the IP pairs
`(v, φ)` in `Ψ` (Eq. 2.3), given `X(0) = x`, take only finitely many distinct values. `Psi ω j ℓ`
is the `ℓ`-th IP pair of activity `j` (the residual service time and output vector of a type-`j`
service already open at time `0`), of which only `ℓ < N0 x j` exist under initial state `x`
(`N0 x j = N_j(0)`, the number of type-`j` services open at time `0` when `X(0) = x`); `X0` is
the ambient chain's initial state `X(0)`, and the conditional law given `X(0) = x` is the
pushforward of `Psi · j ℓ` under `ℙ[|{X(0) = x}]`. -/
def HasFinitelyManyConditionalIPDistributions {Xstate : Type*} [Countable Xstate] {Ω : Type*}
    [MeasureSpace Ω] {I J : ℕ} (X0 : Ω → Xstate) (N0 : Xstate → Fin J → ℕ)
    (Psi : Ω → Fin J → ℕ → ℝ × (Fin I → ℕ)) : Prop :=
  {μ : Measure (ℝ × (Fin I → ℕ)) | ∃ (x : Xstate) (j : Fin J) (ℓ : ℕ), ℓ < N0 x j ∧
    μ = Measure.map (fun ω => Psi ω j ℓ) (ℙ[|{ω | X0 ω = x}])}.Finite

end ProcessingNetworks.Stability


