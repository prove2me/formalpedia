-- Prove2me | Definitions.Def_CanadaCTP_Analysis
-- name    : CanadaCTP_Analysis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:22:38.085843+00:00
-- url     : https://prove2.me/theorems/30cc4653-35bf-420b-ba63-c6c39d91b3b4
-- title:
--   §3.2, p.16 — the tail probabilities $u_\ell$, $u_{-1}$ and $u^*_\ell$
-- statement:
--   For a CTP instance:
--
--   - $u_\ell$ ($\ell\ge0$) is the probability that ParallelTraveller is not finished by the end of phase $\ell$, and $u_{-1}$ the probability that it is not finished by the end of the preprocessing;
--   - for a policy $\pi$, $u^*_\ell$ is the probability that $\pi$ costs at least $2^\ell$ (in units where the least non-zero realization is $1$), that is, that $\pi$ does not reach $t$ at total cost below $2^\ell\mu$.
--
--   These are the quantities of Lemma 10 and of Eqs. (7)–(8).
--
--   **Formalization Note** The paper defines $u^*_\ell$ for an optimal policy Opt; here it is defined for every policy, Opt being one of them. For a feasible policy, "does not reach $t$ below cost $2^\ell\mu$" is the paper's event "costs at least $2^\ell$". Probabilities are suprema over the horizon.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), §3.2, p.16

import Mathlib
import Definitions.Def_CanadaCTP_ParallelTraveller

namespace CanadaCTP

open scoped ENNReal

/-! # The quantities of the approximation analysis, §3.2, p.16

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
§3.2, p.16: `u_ℓ`, `u*_ℓ` and `u_{−1}`.

**Formalization Note.** Probabilities of events of the whole run are suprema over the horizon
(the events below are absorbing: `t` ends the run and freezes memory and cost). The paper's
thresholds `2^ℓ` are in rescaled units; in original units they are `2^ℓ·μ`. `u*_ℓ` is defined
for every policy `π` (the paper's Opt is one of them): "π costs at least `2^ℓ·μ`" is the
complement of "π reaches `t` at total cost below `2^ℓ·μ`", which for a feasible `π` (reaching `t`
almost surely) is the paper's event. -/

/-- `u_ℓ = P[τ_ℓ]`, the probability that ParallelTraveller is not finished by the end of phase
`ℓ`; `ℓ = −1` gives `u_{−1}`, the probability that it is not finished by the end of the
preprocessing. -/
noncomputable def uAlg (I : Inst) (ℓ : ℤ) : ℝ :=
  1 - (⨆ N : ℕ, ∑ ι : Realz I, I.P ι *
    (lawN I (ptPolicy I) ι N).toOuterMeasure
      {c | c.pos = Pos.t ∧ c.mem.core.phase ≤ ℓ}).toReal

/-- `u*_ℓ = P[τ*_ℓ]` for a policy `π`: the probability that `π` does not reach `t` at total
cost below `2^ℓ` (rescaled), i.e. below `2^ℓ·μ` in original units. -/
noncomputable def uStar (I : Inst) {Mem : Type} (π : Policy I Mem) (ℓ : ℕ) : ℝ :=
  1 - (⨆ N : ℕ, ∑ ι : Realz I, I.P ι *
    (lawN I π ι N).toOuterMeasure
      {c | c.pos = Pos.t ∧ c.cost < ENNReal.ofReal (2 ^ ℓ * mu I)}).toReal

end CanadaCTP


