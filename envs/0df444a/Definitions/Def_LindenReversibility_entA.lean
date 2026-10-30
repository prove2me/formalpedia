-- Prove2me | Definitions.Def_LindenReversibility_entA
-- name    : LindenReversibility_entA
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:19.907914+00:00
-- url     : https://prove2.me/theorems/d9501e84-e81e-42da-929a-92dce431e7e8
-- title:
--   Alice's entropy $S(A) = S(\mathrm{Tr}_{BC}|\psi\rangle\langle\psi|)$
-- statement:
--   For a pure state $\psi$ of the joint system $\mathbb C^A\otimes(\mathbb C^B\otimes\mathbb C^C)$, let $\rho^A = \operatorname{Tr}_{BC}|\psi\rangle\langle\psi|$ be Alice's reduced state. Alice's entropy is the von Neumann entropy
--
--   $$
--   S(A) = S(\rho^A) = -\operatorname{Tr}\rho^A\ln\rho^A ,
--   $$
--
--   with natural logarithms. Since the joint state is pure, it is Alice's entanglement with the joint Bob–Claire system.
--
--   **Formalization Note** The entropy is the published `QAlgorithms.Papers.Independent.Information100.P56.entropy` (natural logarithms, $0\ln0=0$), the same unit as the relative entropy (9). It is nonnegative on density matrices, so its value in $[0,+\infty]$ is the real entropy.
-- source:
--   Linden, Popescu, Schumacher, Westmoreland, Reversibility of local transformations of multiparticle entanglement, arXiv:quant-ph/9912039v1, eqs. (13), (22), pp.3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

open scoped ENNReal

namespace LindenReversibility

/-- Linden, Popescu, Schumacher, Westmoreland, arXiv:quant-ph/9912039v1, eqs. (13), (22),
pp.3–4: `S(A)`, the von Neumann entropy of Alice's reduced state `ρ^A = Tr_{BC} |ψ⟩⟨ψ|` of a
(normalized) joint pure state `ψ` — Alice's entanglement with the joint Bob-Claire system.

**Formalization Note.** Alice is the first factor `A` of `A × (B × C)`; `QAlgorithms.traceRight`
traces out the second factor `B × C`. The entropy is the published
`QAlgorithms.Papers.Independent.Information100.P56.entropy`, `−Tr ρ ln ρ` with natural logarithms
(the same unit as the relative entropy (9)). It is `≥ 0` on density matrices, so the cast to
`ℝ≥0∞` loses nothing on unit vectors. -/
noncomputable def entA {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B] [Fintype C]
    (ψ : EuclideanSpace ℂ (A × (B × C))) : ℝ≥0∞ :=
  ENNReal.ofReal (QAlgorithms.Papers.Independent.Information100.P56.entropy
    (QAlgorithms.traceRight (QAlgorithms.pureDensity ψ)))

end LindenReversibility


