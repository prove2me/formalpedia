-- Prove2me | Definitions.Def_BewleyGE_IsEqFamily
-- name    : BewleyGE_IsEqFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:34:44.715478+00:00
-- url     : https://prove2.me/theorems/30781e29-1093-4c2a-89c3-ebf573f6f6d2
-- title:
--   The agents' solution at every interior price
-- statement:
--   A family $(x_\pi,V_\pi,g_\pi,\mu_\pi)_{\pi}$ indexed by price–interest vectors $\pi=(p,r)$ **solves the agents' problem on $P$** if at every $(p,r)\in P$ it satisfies Definition 1(i)–(ii): $x_\pi$ is the demand function, $V_\pi$ the value function, $g_\pi$ a savings policy satisfying (1) and $\mu_\pi$ an invariant wealth distribution.
--
--   By Lemmas 1 and 2 these objects are unique (on the state space), so every such family yields the paper's $g(\cdot,p,r)$, $x^*(\cdot,p)$ and $\mu(\cdot;p,r)$, and hence its excess demand.
--
--   **Formalization Note** Results about the excess demand quantify over every such family rather than selecting one.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §3.1, p.10

import Mathlib
import Definitions.Def_BewleyGE_IsPartialEq
import Definitions.Def_BewleyGE_interiorPrices

open MeasureTheory

namespace BewleyGE

/-- **The agents' solution at every interior price**: a family `(x, V, g, μ)` indexed by
`π = (p, r) ∈ P` such that, at each `π ∈ P`, `x π` is the demand function, `V π` the value
function, `g π` the savings policy (1) and `μ π` an invariant wealth distribution.
Light, arXiv:1906.06810v2, §3.1, p.10: "the savings policy function g(a, p, r) is single-valued
and continuous. Furthermore, there exists a unique invariant wealth distribution μ(da; p, r) for
all (p, r) ∈ P".

**Formalization Note.** The paper's `g(·, p, r)`, `x*(·, p)`, `V(·, p, r)`, `μ(·; p, r)` are the
unique such objects (Lemmas 1 and 2, under the milestones' hypotheses). Statements about the
excess demand quantify over every family with this property instead of choosing one, so no
`Classical.choose` enters; by uniqueness every such family gives the paper's excess demand.
Here `p = (π i.castSucc)ᵢ` and `r = π (Fin.last n)`. -/
def IsEqFamily {n : ℕ} (E : Economy n) (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ)
    (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ) (μ : (Fin (n + 1) → ℝ) → Measure ℝ) : Prop :=
  ∀ π ∈ interiorPrices n,
    IsPartialEq E (fun i => π i.castSucc) (π (Fin.last n)) (x π) (V π) (g π) (μ π)

end BewleyGE


