-- Prove2me | Definitions.Def_NonmonotoneSubmod_SmoothLS_BiasedSample
-- name    : NonmonotoneSubmod_SmoothLS_BiasedSample
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:07:17.168852+00:00
-- url     : https://prove2.me/theorems/aca36d7d-6275-45e0-b13d-c66717125dc7
-- title:
--   Definition 3.5 — sampling with bias $\delta$, $\Phi(A)$ and $\omega_{A,\delta}(x)$
-- statement:
--   Let $X$ be a finite ground set, $A \subseteq X$ and $\delta \in [-1,1]$. The random set $\mathcal{R}(A,\delta)$, **sampled with bias $\delta$ based on $A$**, contains each element of $A$ independently with probability $p = \frac{1+\delta}{2}$ and each element outside $A$ independently with probability $q = \frac{1-\delta}{2}$. Its inclusion-probability vector is
--
--   $$
--   x_i = \begin{cases} \frac{1+\delta}{2}, & i \in A,\\ \frac{1-\delta}{2}, & i \notin A,\end{cases}
--   $$
--
--   so that $\mathbf{E}[g(\mathcal{R}(A,\delta))] = G(x)$ for the multilinear extension $G$ of any set function $g$. With this, for a set function $f$:
--
--   1. the **potential** of Algorithm SLS is $\Phi_\delta(A) = \mathbf{E}[f(\mathcal{R}(A,\delta))]$;
--   2. the **smoothed marginal value** of an element $x$ is
--   $$
--   \omega_{A,\delta}(x) = \mathbf{E}[f(\mathcal{R}(A,\delta) \cup \{x\})] - \mathbf{E}[f(\mathcal{R}(A,\delta) \setminus \{x\})].
--   $$
--
--   Algorithm SLS performs local search on $\Phi_\delta$, deciding its moves by (estimates of) $\omega_{A,\delta}$. For $\delta = 1$ the set $\mathcal{R}(A,1)$ is $A$ itself, and for $\delta = -1$ it is $X \setminus A$.
--
--   **Formalization Note** `biasPt A δ` is the vector $x$ above, `Phi f δ A` is $F(x)$ and `omegaB f A δ x` is the difference of the multilinear extensions of $S \mapsto f(S \cup \{x\})$ and $S \mapsto f(S \setminus \{x\})$ at $x$. The definitions accept every real $\delta$; the probabilistic reading needs $\delta \in [-1,1]$, which the statements that use it assume.
-- source:
--   Feige, Mirrokni, Vondrák, Maximizing Non-Monotone Submodular Functions, SIAM J. Comput. 40(4), 2011, p. 1142, Definition 3.5 and Algorithm SLS step 2, and the definition of Φ(A) below the algorithm

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F

namespace NonmonotoneSubmod.SmoothLS

variable {X : Type} [Fintype X] [DecidableEq X]

/-- Definition 3.5 (Feige–Mirrokni–Vondrák 2011, p. 1142): the random set `R(A, δ)` sampled with
bias `δ` based on `A` contains each element of `A` independently with probability
`p = (1 + δ)/2` and each element outside `A` independently with probability `q = (1 - δ)/2`.
`biasPt A δ` is the vector of these inclusion probabilities, so that
`E[g(R(A, δ))] = F g (biasPt A δ)`. -/
noncomputable def biasPt (A : Finset X) (δ : ℝ) : X → ℝ :=
  fun i => if i ∈ A then (1 + δ) / 2 else (1 - δ) / 2

/-- The derived potential of Algorithm SLS (p. 1142): `Φ(A) = E[f(R(A, δ))]`. -/
noncomputable def Phi (f : Finset X → ℝ) (δ : ℝ) (A : Finset X) : ℝ :=
  NonmonotoneSubmod.Shared.F f (biasPt A δ)

/-- Step 2 of Algorithm SLS (p. 1142):
`ω_{A,δ}(x) = E[f(R(A, δ) ∪ {x})] - E[f(R(A, δ) \ {x})]`. -/
noncomputable def omegaB (f : Finset X → ℝ) (A : Finset X) (δ : ℝ) (x : X) : ℝ :=
  NonmonotoneSubmod.Shared.F (fun S => f (insert x S)) (biasPt A δ) - NonmonotoneSubmod.Shared.F (fun S => f (S.erase x)) (biasPt A δ)

end NonmonotoneSubmod.SmoothLS


