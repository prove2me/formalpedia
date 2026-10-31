-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_actEU
-- name    : ParallelSmallWorlds_SEU_actEU
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:53:36.590423+00:00
-- url     : https://prove2.me/theorems/1c0c77eb-b4f3-427d-99eb-be735cfbf553
-- title:
--   Subjective expected utility $E(u_w\mid a)$ of an act
-- statement:
--   Let $u:C\to\mathbb R$ be a utility function and $a:\Theta\to C$ an act with finitely many consequences. The **subjective expected utility** of $a$ is
--
--   $$E(u\mid a)=\sum_{c\in a(\Theta)} u(c)\,P_\Theta\bigl(a^{-1}\{c\}\bigr),$$
--
--   where $P_\Theta$ is the calibrated probability. This is the paper's expression $\sum_{\theta\in\Theta_w}u_w(a(\theta))P_{\Theta_w}(\theta)$, rearranged as in its equation (18) by grouping the states by the consequence they lead to.
--
--   **Formalization Note** The sum runs over the range of $a$ and requires the fibres $a^{-1}\{c\}$ to be events, which the theorems assume; it is a `finsum`, which returns $0$ for an act of infinite range, and the theorems assume finite range.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), eq. (5), p.27 (PDF p.28); Theorem 1, p.28 (PDF p.29); eq. (18), p.46 (PDF p.47)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_calib

namespace ParallelSmallWorlds.SEU

/-- **The subjective expected utility `E(uw | a)` of an act.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), eq. (5), p.27 (PDF p.28), Theorem 1, p.28 (PDF p.29),
and its rearrangement (18), p.46 (PDF p.47):
`E(uw | a) = Σ_{θ∈Θw} uw(a(θ)) PΘw(θ) = Σ_{c∈Cw} uw(c) Σ_{θ | c = a(θ)} PΘ(θ)`.

`actEU W u a = Σ_{c ∈ a(Θ)} u(c) · PΘw(a⁻¹{c})`, with `PΘw = calib W`.

**Formalization Note.** The sum over states is read as the paper's own rearrangement (18) over
the consequences in the range of `a`, weighting each by the calibrated probability of its fibre
(reading R2); this needs the fibres `a⁻¹{c}` to be events, which the theorems assume. It agrees
with the printed sum over `θ` when `Θ` is finite and singletons are events. The sum is a `finsum`
over `Set.range a`, which is meaningful only for acts with finitely many consequences (for an act
of infinite range it returns `0`); the theorems assume finite range. -/
noncomputable def actEU {Θ C : Type*} (W : SmallWorld Θ C) (u : C → ℝ) (a : Θ → C) : ℝ :=
  ∑ᶠ c ∈ Set.range a, u c * calib W (a ⁻¹' {c})

end ParallelSmallWorlds.SEU


