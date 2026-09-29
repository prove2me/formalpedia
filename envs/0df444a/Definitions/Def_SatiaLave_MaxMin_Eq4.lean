-- Prove2me | Definitions.Def_SatiaLave_MaxMin_Eq4
-- name    : SatiaLave_MaxMin_Eq4
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T00:36:48.144966+00:00
-- url     : https://prove2.me/theorems/04a89317-a3e2-4d24-8893-a20cc619fd4a
-- title:
--   Right-hand side of the dynamic-programming equations (4): randomized decisions against mixed choices of nature
-- statement:
--   Proposition 1 of Satia and Lave concerns the dynamic-programming equations (4) for the max-min criterion. This file defines their right-hand side.
--
--   Let $v=(v_1,\dots,v_N)$ be a value vector and $j$ a state. A **randomized decision** in state $j$ is a probability vector $\tau=(\tau_k)_{k\in D_j}$ on the decisions available in $j$. For a decision $k$, a **mixed choice of nature** is a probability measure $\alpha$ on row vectors that is carried by the uncertainty set $S_j^k$, i.e. $\alpha(S_j^k)=1$. The operator is
--   $$(Tv)_j=\sup_{\tau}\ \sum_{k\in D_j}\tau_k\ \inf_{\alpha}\ \int \sum_{l} p_l\,\big(r^k_{jl}+\beta v_l\big)\,d\alpha(p),$$
--   and equations (4) read $\bar v_j=(T\bar v)_j$ for every state $j$.
--
--   The operator keeps randomization on both sides, as the paper's (4) does; Propositions 1 and 2 are the statements that nothing is lost by restricting to pure decisions and pure choices of nature.
--
--   **Formalization Note.** The printed display (4) omits the integral sign before $\Sigma$ and has an unmatched closing brace; the "$d\alpha(p_j^k)$" shows that an integral against $\alpha$ is meant, and that is what is formalized. Randomized decisions are the points of `stdSimplex ℝ (D j)`. Mixed choices are `ProbabilityMeasure`s on `S → ℝ` (with its product Borel structure) giving measure $1$ to $S_j^k$. Both families are nonempty (the uniform vector; a Dirac mass at a point of $S_j^k$), and all quantities are bounded: the integrand is a linear function of $p$, bounded on the bounded set $S_j^k$, which carries all of $\alpha$, so it is integrable for every admissible $\alpha$ and the infimum and supremum are never junk values.
-- source:
--   Satia and Lave, Markovian Decision Processes with Uncertain Transition Probabilities, Operations Research 21(3), 1973, p. 730, Proposition 1, Eq. (4)

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model

namespace SatiaLave.MaxMin

open Finset MeasureTheory

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)]

/-- The right-hand side of the dynamic-programming equations (4) (Satia–Lave 1973, p. 730,
Proposition 1), evaluated at a value vector `v` in state `j`: the supremum over randomized
decisions `τ` (a probability vector on the decisions `D j`) of
`Σ_k τ_k · inf_α ∫ Σ_l p_l (r^k_jl + β v_l) dα(p)`, where the infimum runs over all
probability measures `α` on row vectors that are carried by the uncertainty set `S_j^k`. -/
noncomputable def eq4Op (M : UncertainMDP S D) (v : S → ℝ) (j : S) : ℝ :=
  ⨆ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k *
    ⨅ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ))

end SatiaLave.MaxMin


