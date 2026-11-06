-- Prove2me | Definitions.Def_CoverModular_FDPInstance_E
-- name    : CoverModular_FDPInstance_E
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:38.18203+00:00
-- url     : https://prove2.me/theorems/fdd9391f-0a0f-41fe-8ebc-364e752fc279
-- title:
--   Surrogate marginal gain $\mathcal E_{ij}(\mathcal S)$ (display (11))
-- statement:
--   Let $x^{\mathcal S}_\omega$ be a primal solution of the LP for $\mathcal S$ in scenario $\omega$ and let $\bar\alpha^{\mathcal S}_{i\omega},\bar\beta^{\mathcal S}_{j\omega}$ be the values (6) computed from it with the constant $P$. The **surrogate** of arc $(i,j)$ is
--
--   $$
--   \mathcal E_{ij}(\mathcal S)=\sum_{\omega\in\Omega}\mu_\omega\,\min(c_{i\omega},d_{j\omega})\bigl(p_{ij}-\bar\alpha^{\mathcal S}_{i\omega}-\bar\beta^{\mathcal S}_{j\omega}\bigr)^+ .
--   $$
--
--   It is a lower bound on the marginal gain $F(\mathcal S\cup\{(i,j)\})-F(\mathcal S)$ and can be computed from one LP solution per scenario.
--
--   **Formalization Note** The set $\mathcal S$ enters only through the scenario-wise solutions $x$, which are an argument; their optimality is a hypothesis of the theorems.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, display (11), p.14

import Mathlib
import Definitions.Def_CoverModular_FDPInstance
import Definitions.Def_CoverModular_alphaBar

namespace CoverModular

namespace FDPInstance

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]

/-- The surrogate `ℰ_ij(𝒮)` of (11) (DeValve, Pekeč, Wei, SSRN 3844987, §3.2, display (11),
p.14): `ℰ_ij(𝒮) = ∑_{ω∈Ω} µ_ω min(c_iω, d_jω) (p_ij − ᾱ^𝒮_iω − β̄^𝒮_jω)^+`, where
`ᾱ^𝒮_iω, β̄^𝒮_jω` are the values (6) in scenario `ω`.

**Formalization Note** The set `𝒮` enters only through the primal solutions: `x ω` is the
paper's `x^𝒮` in scenario `ω` (an optimal solution of the LP for `𝒮` in scenario `ω`, a
hypothesis of the theorems that use `E`), and `P` is the constant of (6). The positive part is
`max · 0`. -/
noncomputable def E (inst : FDPInstance I J Ω) (P : ℝ) (x : Ω → I → J → ℝ) (i : I) (j : J) :
    ℝ :=
  ∑ ω, inst.μ ω * (min (inst.c i ω) (inst.d j ω) *
    max (inst.p i j - alphaBar (fun i' => inst.c i' ω) inst.p P (x ω) i
      - betaBar (fun j' => inst.d j' ω) inst.p P (x ω) j) 0)

end FDPInstance

end CoverModular


