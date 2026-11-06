-- Prove2me | Definitions.Def_CoverModular_FDPInstance_Emax
-- name    : CoverModular_FDPInstance_Emax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:39.856631+00:00
-- url     : https://prove2.me/theorems/cc603d78-e1b3-414d-bb05-f9be9d61e148
-- title:
--   Largest surrogate $\mathcal E_{\max}(\mathcal S)$ over arcs outside $\mathcal S$
-- statement:
--   With $\mathcal E_{ij}(\mathcal S)$ computed from the scenario-wise solutions $x$,
--
--   $$
--   \mathcal E_{\max}(\mathcal S)=\max_{(i,j)\in\mathcal F\setminus\mathcal S}\mathcal E_{ij}(\mathcal S),
--   $$
--
--   where $\mathcal F$ is the set of all arcs.
--
--   **Formalization Note** When $\mathcal S=\mathcal F$ the maximum is over the empty set, which the paper does not define; it is set to $0$. Every $\mathcal E_{ij}$ is nonnegative under the standing conditions, so $0$ is the supremum of the empty family among nonnegative reals.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §3.2, display (11), p.14

import Mathlib
import Definitions.Def_CoverModular_FDPInstance_E

namespace CoverModular

namespace FDPInstance

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]

/-- `ℰ_max(𝒮) = max_{(i,j) ∈ 𝓕 \ 𝒮} ℰ_ij(𝒮)` (DeValve, Pekeč, Wei, SSRN 3844987, §3.2,
display (11), p.14), with `𝓕 = Finset.univ` the set of all arcs and `x` the scenario-wise
primal solutions for `𝒮` that define `ℰ_ij(𝒮)`.

**Formalization Note** If `𝒮 = 𝓕` the maximum is over the empty set, which the paper leaves
undefined; it is set to `0` here. Every `ℰ_ij` is nonnegative under the standing conditions, so
`0` is the supremum of the empty family in the nonnegative reals. -/
noncomputable def Emax (inst : FDPInstance I J Ω) (P : ℝ) (x : Ω → I → J → ℝ)
    (S : Finset (I × J)) : ℝ :=
  if h : (Finset.univ \ S).Nonempty then (Finset.univ \ S).sup' h (fun a => inst.E P x a.1 a.2)
  else 0

end FDPInstance

end CoverModular


