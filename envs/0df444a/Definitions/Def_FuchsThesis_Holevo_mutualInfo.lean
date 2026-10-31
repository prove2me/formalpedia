-- Prove2me | Definitions.Def_FuchsThesis_Holevo_mutualInfo
-- name    : FuchsThesis_Holevo_mutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:56:02.729187+00:00
-- url     : https://prove2.me/theorems/2d951610-ca2e-4bf1-875e-dc23ba8b7c6a
-- title:
--   Mutual information $J(t)$ of a binary quantum channel for a fixed measurement
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be the signal states, with priors $1-t$ and $t$, and $\{\hat E_b\}$ a measurement. With $p_k(b)=\mathrm{tr}(\hat\rho_k\hat E_b)$ and $p(b)=\mathrm{tr}(\hat\rho\hat E_b)$, $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$, the Shannon mutual information of the channel with respect to the measurement is
--
--   $$
--   J(t) = J(p_0,p_1;t) = H(p) - (1-t)H(p_0) - tH(p_1),
--   $$
--
--   in nats. It is the information about the message gained by the measurement; its maximum over measurements is the accessible information.
--
--   **Formalization Note** The outcome probabilities are the published `FuchsVdGraaf.outcomeDist` ($b\mapsto\mathrm{Re}\,\mathrm{tr}(\hat\rho\hat E_b)$). The measurement is any family `E : Fin m → Matrix d d ℂ`; that it is a POVM (the published `FuchsVdGraaf.IsPOVM`: positive semidefinite effects summing to the identity) is a hypothesis of each theorem. $J$ is defined for every real $t$, and the theorems use $0\le t\le1$.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.144), p.64 (PDF p.73)

import Mathlib
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsThesis_Holevo_shannonNat
import Definitions.Def_FuchsThesis_Holevo_mixState

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.144), p.64 (PDF p.73): the Shannon mutual
information of the binary channel `{ρ̂0, ρ̂1}` with priors `1 − t, t` with respect to the
measurement `{Ê_b}`,
`J(p0, p1; t) = H(p) − (1 − t) H(p0) − t H(p1)`, where `p_k(b) = tr(ρ̂_k Ê_b)` (3.140) and
`p(b) = tr(ρ̂ Ê_b)` with `ρ̂ = (1 − t)ρ̂0 + tρ̂1` (3.141)–(3.142). Written `J(t)` in §3.5.

**Formalization Note.** Entropies in nats (`shannonNat`, 3.145). Outcome probabilities are the
published `FuchsVdGraaf.outcomeDist` (`b ↦ Re tr(ρ E_b)`, outcomes `Fin m`, same convention as
(3.140)–(3.141)); the measurement is a family `E : Fin m → Matrix d d ℂ` (being a POVM, the
published `FuchsVdGraaf.IsPOVM`, is a hypothesis of the statements). `J` is defined for
every real `t`; the statements use `0 ≤ t ≤ 1`. -/
noncomputable def mutualInfo {d : Type} [Fintype d] {m : ℕ} (ρ0 ρ1 : Matrix d d ℂ)
    (E : Fin m → Matrix d d ℂ) (t : ℝ) : ℝ :=
  shannonNat (FuchsVdGraaf.outcomeDist (mixState ρ0 ρ1 t) E)
    - (1 - t) * shannonNat (FuchsVdGraaf.outcomeDist ρ0 E)
    - t * shannonNat (FuchsVdGraaf.outcomeDist ρ1 E)

end FuchsThesis.Holevo


