-- Prove2me | Definitions.Def_QPSpinParisi_stepT
-- name    : QPSpinParisi_stepT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:54.208529+00:00
-- url     : https://prove2.me/theorems/ebb6885e-db4e-4c56-97b1-2bb16c311e53
-- title:
--   The cascade recursion for (3.13) on a step path
-- statement:
--   With $\tau_\ell=\operatorname{Tr}Q_\ell$, define $T_{k+1}(x)=\log\int\exp(x\cdot s-\frac{\beta^2}2\xi'(\tau_{k+1}))\,\nu(ds)$, and for $\ell=k,\dots,0$, with $z_\ell\sim N(0,\beta^2(\xi'(\tau_{\ell+1})-\xi'(\tau_\ell))I_3)$,
--   $$T_\ell(x)=\begin{cases}m_\ell^{-1}\log\mathbb E\exp\{m_\ell T_{\ell+1}(x+z_\ell)\},&m_\ell>0,\\ \mathbb E\,T_{\ell+1}(x+z_\ell),&m_\ell=0.\end{cases}$$
--   This is the Ruelle cascade integral in (3.13) evaluated on a step path. The paper prints the same recursion for scalar paths on p.20.
--
--   **Formalization Note** The argument counts levels from the top, and $\|s\|^2=1$ on $S^2$.
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.13), p.15 (PDF p.15); p.20 (PDF p.20)

import Mathlib
import Definitions.Def_QPSpinParisi_StepPath
import Definitions.Def_QPSpinParisi_gaussE3
import Definitions.Def_QPSpinParisi_xiD
import Definitions.Def_RGGDetect_unifSphere

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- The cascade recursion for the first term of (3.13) on a step path (Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), (3.13), p.15, PDF p.15; the recursion is printed
for scalar paths on p.20, PDF p.20). With `τ_ℓ = Tr Q_ℓ`, `T_{k+1}(x) = log ∫ exp(x·s - (β²/2) ξ'(τ_{k+1})) ν(ds)`, and, for
`z_ℓ ∼ N(0, β²(ξ'(τ_{ℓ+1}) - ξ'(τ_ℓ)) I₃)`, `T_ℓ(x) = m_ℓ⁻¹ log E exp(m_ℓ T_{ℓ+1}(x + z_ℓ))` if `m_ℓ > 0` and
`T_ℓ(x) = E T_{ℓ+1}(x + z_ℓ)` if `m_ℓ = 0`.

**Formalization Note** The argument `j` counts levels from the top: `stepT c β π j = T_{k+1-j}`, and `‖s‖² = 1` on `S²`. -/
noncomputable def stepT (c : ℕ → ℝ) (β : ℝ) (π : StepPath) : ℕ → E3 → ℝ
  | 0, x => Real.log (∫ s : RGGDetect.Sph 3,
      Real.exp (inner ℝ x (s : E3) - (β ^ 2 / 2) * xiD c (Matrix.trace (π.Q (π.k + 1)))) ∂(RGGDetect.unifSphere 3))
  | j + 1, x =>
      let l := π.k - j
      let v := β ^ 2 * (xiD c (Matrix.trace (π.Q (l + 1))) - xiD c (Matrix.trace (π.Q l)))
      if 0 < π.m l then
        (π.m l)⁻¹ * Real.log (∫ z, Real.exp (π.m l * stepT c β π j (x + z)) ∂(gaussE3 v))
      else
        ∫ z, stepT c β π j (x + z) ∂(gaussE3 v)

end QPSpinParisi


