-- Prove2me | Definitions.Def_FuchsThesis_Holevo_holevoS
-- name    : FuchsThesis_Holevo_holevoS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:50.942674+00:00
-- url     : https://prove2.me/theorems/65e1cb54-da7e-408a-917e-fe126019ef25
-- title:
--   Holevo quantity $S(t)$ of a binary quantum channel
-- statement:
--   For signal states $\hat\rho_0,\hat\rho_1$ with priors $1-t,t$ and mean state $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$, the Holevo upper bound to the accessible information is
--
--   $$
--   S(t) \equiv S(\hat\rho) - (1-t)S(\hat\rho_0) - tS(\hat\rho_1),
--   $$
--
--   with $S$ the von Neumann entropy in nats.
--
--   **Formalization Note** Defined for every real $t$; the theorems use $0\le t\le1$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.149), p.66 (PDF p.75)

import Mathlib
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_vnEntropy

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.149), p.66 (PDF p.75): the Holevo upper bound
`S(t) ≡ S(ρ̂) − (1 − t) S(ρ̂0) − t S(ρ̂1)` with `ρ̂ = (1 − t)ρ̂0 + tρ̂1`, in nats.

**Formalization Note.** Defined for every real `t`; the statements use `0 ≤ t ≤ 1`. -/
noncomputable def holevoS {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (t : ℝ) : ℝ :=
  vnEntropy (mixState ρ0 ρ1 t) - (1 - t) * vnEntropy ρ0 - t * vnEntropy ρ1

end FuchsThesis.Holevo


