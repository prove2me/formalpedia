-- Prove2me | Definitions.Def_CoverModular_FDPInstance_F
-- name    : CoverModular_FDPInstance_F
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:14:28.56705+00:00
-- url     : https://prove2.me/theorems/bad76eff-f925-4c83-9697-cba511ae241c
-- title:
--   Expected profit $F(\mathcal A)=\sum_\omega\mu_\omega f(\mathcal A,\omega)$
-- statement:
--   For an instance $(\mu,c,d,p)$ and a flexibility structure $\mathcal A$, the **expected profit** is
--
--   $$
--   F(\mathcal A)=\sum_{\omega\in\Omega}\mu_\omega\,f(\mathcal A,\omega),
--   $$
--
--   where $f(\mathcal A,\omega)$ is the second-stage value (LP (1)) with capacities $c_{\cdot\omega}$, demands $d_{\cdot\omega}$ and profits $p$. The budgeted flexibility design problem is $\max\{F(\mathcal A):\mathcal A\subseteq\mathcal F,\ |\mathcal A|\le K\}$.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §2, display (1) and (FDP), p.6

import Mathlib
import Definitions.Def_CoverModular_FDPInstance
import Definitions.Def_CoverModular_lpValue

namespace CoverModular

namespace FDPInstance

variable {I J Ω : Type} [Fintype I] [Fintype J] [Fintype Ω]

/-- The expected profit `F(𝒜) = ∑_{ω∈Ω} µ_ω f(𝒜, ω)` of a flexibility structure `𝒜`
(DeValve, Pekeč, Wei, SSRN 3844987, §2, display (1), p.6), where `f(𝒜, ω)` is the value of the
second-stage LP with capacities `c_·ω` and demands `d_·ω` (`lpValue`). -/
noncomputable def F (inst : FDPInstance I J Ω) (A : Finset (I × J)) : ℝ :=
  ∑ ω, inst.μ ω * lpValue (fun i => inst.c i ω) (fun j => inst.d j ω) inst.p A

end FDPInstance

end CoverModular


