-- Prove2me | Definitions.Def_MultiServerAppt_Tblock
-- name    : MultiServerAppt_Tblock
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:56:07.109002+00:00
-- url     : https://prove2.me/theorems/d2c12507-0f3c-4324-b755-153b1d3582a2
-- title:
--   The block $T^{(\ell)}$, display after Eq. (14)
-- statement:
--   With $t=-S\mathbf 1$ and $\alpha$ the initial phase distribution, the block $T^{(\ell)}$ acts on phase vectors of $\ell$ servers by
--
--   $$T^{(\ell)}_{m,m'}=\sum_{c=1}^{\ell}\mathbf 1\{m_d=m'_d\ \text{for all } d\ne c\}\ t_{m_c}\,\alpha_{m'_c}.$$
--
--   Server $c$ completes a service and the next waiting client starts on it in a phase drawn from $\alpha$. All other servers keep their phases.
--
--   **Formalization Note** Entrywise. The page's recursion with $T^{(1)}=-S\mathbf 1\otimes\alpha$ is proved in the verification file.
-- source:
--   Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, display after Eq. (14), p.13

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MultiServerAppt

/-- The block `T^(ℓ)`: server `c` in phase `m c` completes at rate `t (m c)`, where `t = -S𝟙`, and
the next client starts on it in phase `m' c` with probability `α (m' c)`; the other servers keep
their phases. Kuiper–Lee, Appointment Scheduling for Multiple Servers, SSRN 3975471, display after
Eq. (14), p.13.

**Formalization Note** Entrywise. The page's recursion with `T^(1) = -S𝟙 ⊗ α` is proved in
`Solutions/verification/MultiServerAppt_Sanity.lean`. -/
def Tblock {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℝ) (S : Matrix ι ι ℝ) (ℓ : ℕ) :
    Matrix (Fin ℓ → ι) (Fin ℓ → ι) ℝ :=
  Matrix.of fun m m' =>
    ∑ c, if ∀ d, d ≠ c → m d = m' d then
      MatrixAnalytic.PH.exitRates S (m c) * α (m' c) else 0

end MultiServerAppt


