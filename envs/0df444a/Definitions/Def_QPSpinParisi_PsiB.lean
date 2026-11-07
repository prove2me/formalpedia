-- Prove2me | Definitions.Def_QPSpinParisi_PsiB
-- name    : QPSpinParisi_PsiB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:14:50.746987+00:00
-- url     : https://prove2.me/theorems/e2dd77f4-8c61-4c69-b4ee-93fdc7472c23
-- title:
--   The function $\Psi_{\xi,\beta,\alpha}$, by (3.23)
-- statement:
--   For $\alpha\in\mathcal M$,
--   $$\Psi_{\xi,\beta,\alpha}(s,x)=\sup_{u\in D[s,1]}\Big\{\mathbb E\,g_\beta\Big(\Big\|x+\int_s^1\sqrt{\zeta(q)}\,dB_q+\beta\int_s^1\zeta(q)\alpha(q)u(q)\,dq\Big\|\Big)-\frac\beta2\int_s^1\zeta(q)\alpha(q)\mathbb E\|u(q)\|^2\,dq\Big\}.$$
--
--   **Formalization Note** P.17 introduces $\Psi_{\xi,\beta,\alpha}$ as "the solution" of the PDE (3.16), whose coefficient may be discontinuous, and fixes no solution concept. The definition here is the paper's own control formula (3.23).
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.23), p.19 (PDF p.19); p.17 (PDF p.17)

import Mathlib
import Definitions.Def_QPSpinParisi_ctrlValue
import Definitions.Def_QPSpinParisi_alHat
import Definitions.Def_QPSpinParisi_gBeta
import Definitions.Def_QPSpinParisi_zeta

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The function `Ψ_{ξ,β,α}(s, x)`, by the stochastic control formula (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.23), p.19, PDF p.19): terminal function
`g_β(‖·‖)`, drift weight `βζα`.

**Formalization Note** P.17 calls `Ψ_{ξ,β,α}` "the solution" of the PDE (3.16), whose coefficient `α` may be discontinuous, and
fixes no solution concept. P.19 gives (3.23) as its control formula, and the definition is (3.23). -/
noncomputable def PsiB {c : ℕ → ℝ} (W : BrownianNoise c) (β : ℝ) (α : Icc (0 : ℝ) 1 → ℝ) (s : ℝ) (x : E3) : ℝ :=
  ctrlValue W (fun y => gBeta β ‖y‖) (fun q => β * zeta c q * alHat α q) s x

end QPSpinParisi


