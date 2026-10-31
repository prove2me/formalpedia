-- Prove2me | Definitions.Def_FuchsThesis_Holevo_accessibleInfo
-- name    : FuchsThesis_Holevo_accessibleInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:01.583033+00:00
-- url     : https://prove2.me/theorems/58839719-8d53-4575-80d6-097f1fa9b7c6
-- title:
--   Accessible information $I(t)$
-- statement:
--   The accessible information of the binary channel $\{\hat\rho_0,\hat\rho_1\}$ with priors $1-t,t$ is the mutual information maximized over all measurements:
--
--   $$
--   I(t) = I(\hat\rho_0|\hat\rho_1) = \max_{\{\hat E_b\}} J(t),
--   $$
--
--   where $J(t)$ is the mutual information (3.144) of the measurement $\{\hat E_b\}$.
--
--   It is the quantity bounded above by $L(t)$ and the Holevo bound $S(t)$ in (3.167).
--
--   **Formalization Note** The maximum is rendered as the supremum (`sSup`) of the set of values $J(t)$ over every POVM (`FuchsVdGraaf.IsPOVM`) with any finite number $m$ of outcomes. The set is nonempty (the one-outcome POVM $\hat E_1=\hat{\mathbb 1}$ gives $J=0$) and bounded above for density operators and $0\le t\le1$, so the supremum is the true one (and, by Davies' theorem quoted on p.65, it is attained).
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.146), p.65 (PDF p.74)

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Holevo_mutualInfo

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.146), p.65 (PDF p.74): the accessible information
`I(t) = I(ρ̂0|ρ̂1)` of the binary channel, "the mutual information maximized over all
measurements `{Ê_b}`".

**Formalization Note.** The source's `max` is rendered as the supremum `sSup` of the set of
values `J(t)` over **every** POVM (the published `FuchsVdGraaf.IsPOVM`: positive semidefinite
effects summing to the identity) with **any** finite number `m` of outcomes (`Fin m`). The set is
nonempty (the one-outcome POVM `Ê_1 = 1̂` gives `J = 0`) and, for density operators and
`0 ≤ t ≤ 1`, bounded above (by the Holevo bound (3.149)), so `sSup` is the true supremum there;
by Davies' theorem (3.147)–(3.148) it is attained. -/
noncomputable def accessibleInfo {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (t : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix d d ℂ),
    FuchsVdGraaf.IsPOVM E ∧ v = mutualInfo ρ0 ρ1 E t}

end FuchsThesis.Holevo


