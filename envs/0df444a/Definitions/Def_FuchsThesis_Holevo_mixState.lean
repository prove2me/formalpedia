-- Prove2me | Definitions.Def_FuchsThesis_Holevo_mixState
-- name    : FuchsThesis_Holevo_mixState
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:55:16.781228+00:00
-- url     : https://prove2.me/theorems/8dbc2054-3e82-480a-a1d2-dd6250ed1605
-- title:
--   Mean density operator $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$
-- statement:
--   A binary quantum communication channel has signal states $\hat\rho_0,\hat\rho_1$ with prior probabilities $\pi_0=1-t$ and $\pi_1=t$, $0\le t\le1$. Its mean density operator is
--
--   $$
--   \hat\rho = (1-t)\hat\rho_0 + t\hat\rho_1 = \hat\rho_0 + t\hat\Delta, \qquad \hat\Delta = \hat\rho_1-\hat\rho_0 .
--   $$
--
--   Every $t$-dependent quantity of §3.5 (mutual information, Holevo quantity, the operator $\mathcal L_{\hat\rho}(\hat\Delta)$) is built from it.
--
--   **Formalization Note** The formula is defined for every real $t$ (real scalar multiples of complex matrices); the statements of the mission use $0\le t\le1$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.139), (3.142)–(3.143), p.64 (PDF p.73)

import Mathlib

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.142), p.64 (PDF p.73): the mean density operator of
the binary channel with priors `π0 = 1 − t`, `π1 = t` (3.139),
`ρ̂ = (1 − t) ρ̂0 + t ρ̂1 = ρ̂0 + t Δ̂` with `Δ̂ = ρ̂1 − ρ̂0` (3.143).

**Formalization Note.** Defined for every real `t` (real scalar multiplication on complex
matrices); the statements use it for `0 ≤ t ≤ 1` only. -/
noncomputable def mixState {d : Type} [Fintype d] (ρ0 ρ1 : Matrix d d ℂ) (t : ℝ) :
    Matrix d d ℂ :=
  (1 - t) • ρ0 + t • ρ1

end FuchsThesis.Holevo


