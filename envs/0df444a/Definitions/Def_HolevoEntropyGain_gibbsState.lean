-- Prove2me | Definitions.Def_HolevoEntropyGain_gibbsState
-- name    : HolevoEntropyGain_gibbsState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:17:50.547195+00:00
-- url     : https://prove2.me/theorems/0b732a8a-b21d-4d01-8179-1422b6b5da3c
-- title:
--   The Gibbs density operator $\rho_\beta = \exp(-\beta F - c(\beta))$
-- statement:
--   For $F$ with spectral data $(e_n,E_n)$ satisfying (5), the **Gibbs (thermal) state** at inverse temperature $\beta>0$ is
--
--   $$
--   \rho_\beta = \exp(-\beta F - c(\beta)) = e^{-c(\beta)}\exp(-\beta F). \tag{6}
--   $$
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (6), p.3

import Mathlib
import Definitions.Def_HolevoEntropyGain_gibbsOperator
import Definitions.Def_HolevoEntropyGain_gibbsConstant

open QAlgorithms.RealRegisters (Hilbert)

namespace HolevoEntropyGain

/-- The Gibbs density operator `ρ_β = exp(-βF - c(β))` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (6), p.3, PDF p.3). -/
noncomputable def gibbsState {I : Type} (e : HilbertBasis I ℂ (Hilbert I)) (E : I → ℝ) (β : ℝ) :
    Matrix I I ℂ :=
  (Real.exp (-gibbsConstant E β) : ℂ) • gibbsOperator e E β

end HolevoEntropyGain


