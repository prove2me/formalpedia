-- Prove2me | Definitions.Def_ShadowBootstrap_stagesExpect
-- name    : ShadowBootstrap_stagesExpect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:50.096748+00:00
-- url     : https://prove2.me/theorems/a9c0551d-78c9-4c2c-ae48-c8e226db6a89
-- title:
--   Shadow-bootstrapping stages: the update (12)–(13), the error (14), and the expectation over stages
-- statement:
--   Shadow bootstrapping refines a unit vector $|\sigma_0\rangle$ in stages (§4.2, pp.13–14). At stage $t$ the previous estimate $\sigma_{t-1} = |\sigma_{t-1}\rangle\langle\sigma_{t-1}|$ is the reference state of $N_t$ residual estimators $\Delta_{t,i}$, one per freshly sampled basis with $S_t$ shots, and
--   $$|\tilde\sigma_t\rangle := \Big(\sigma_{t-1} + \frac{1}{N_t}\sum_{i=1}^{N_t}\Delta_{t,i}\Big)|\sigma_0\rangle, \tag{12}$$
--   $$|\sigma_t\rangle := \begin{cases} |\tilde\sigma_t\rangle/\||\tilde\sigma_t\rangle\|_2, & \||\tilde\sigma_t\rangle\|_2 > 0,\\ |\sigma_{t-1}\rangle, & \||\tilde\sigma_t\rangle\|_2 = 0,\end{cases} \tag{13}$$
--   with residual estimation error
--   $$|e_t\rangle := \Big(\frac{1}{N_t}\sum_{i=1}^{N_t}\Delta_{t,i} - (\psi - \sigma_{t-1})\Big)|\sigma_0\rangle. \tag{14}$$
--
--   Different stages use independent bases and disjoint copies, so the expectation of a function of the final estimate $\sigma_J$ is computed stage by stage: each stage's data (bases drawn from $E$, shots on $|\psi\rangle$) has its own law, and $\sigma_t$ is a function of $\sigma_{t-1}$ and the stage-$t$ data. The module also provides the run of Algorithm 4 on given histograms.
--
--   **Formalization Note** The update and error are stated for an arbitrary correction operator $D$ in place of $\frac{1}{N_t}\sum_i \Delta_{t,i}$; the stage correction itself reads each basis's histogram as frequencies $h(z)/S_t$.
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §4.2, Eqs. (12)–(14), pp.13–14; Corollary 4.5, p.15; Algorithm 4, p.27

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_residual

open ClassicalShadow.Linear

namespace ShadowBootstrap

/-- The average residual `(1/N_t) Σ_i ∆_{t,i}` of one bootstrapping stage (Eq. (12), p.14): basis
`i` has label `rec i`.1 and histogram `rec i`.2 of `S` shots, its frequencies are `h(z)/S`, and the
reference state is `σ_{t−1} = |σ_{t−1}⟩⟨σ_{t−1}|`. -/
noncomputable def stageCorrection {n N : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (σprev : Bits n → ℂ) (S : ℕ) (rec : Fin N → ι × (Bits n → ℕ)) : Op n :=
  ((1 / (N : ℝ) : ℝ) : ℂ) •
    ∑ i, residual E (ketbra σprev σprev) (rec i).1 (fun z => ((rec i).2 z : ℝ) / S)

/-- Eq. (12), p.14: `|σ̃_t⟩ := (σ_{t−1} + D)|σ₀⟩`, where `D` is the average residual. -/
noncomputable def stageTilde {n : ℕ} (σ₀ σprev : Bits n → ℂ) (D : Op n) : Bits n → ℂ :=
  (ketbra σprev σprev + D).mulVec σ₀

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Eqs. (12)–(13), p.14: the stage update `|σ_t⟩ := |σ̃_t⟩/‖|σ̃_t⟩‖₂` if `‖|σ̃_t⟩‖₂ > 0` and
`|σ_t⟩ := |σ_{t−1}⟩` otherwise, with `|σ̃_t⟩ = (σ_{t−1} + D)|σ₀⟩`. -/
noncomputable def stageUpdate {n : ℕ} (σ₀ σprev : Bits n → ℂ) (D : Op n) : Bits n → ℂ :=
  if 0 < vnormSq (stageTilde σ₀ σprev D) then
    (((Real.sqrt (vnormSq (stageTilde σ₀ σprev D)))⁻¹ : ℝ) : ℂ) • stageTilde σ₀ σprev D
  else σprev

/-- Eq. (14), p.14: the residual estimation error `|e_t⟩ := (D − (ψ − σ_{t−1}))|σ₀⟩`. -/
noncomputable def stageError {n : ℕ} (ψ σ₀ σprev : Bits n → ℂ) (D : Op n) : Bits n → ℂ :=
  (D - (ketbra ψ ψ - ketbra σprev σprev)).mulVec σ₀

/-- The probability of the raw data of one stage: `N` bases `U_{i}` drawn independently from `E`,
each measured on `S` fresh copies of `|ψ⟩`. -/
noncomputable def stageWeight {n N S : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (ψ : Bits n → ℂ) (data : Fin N → ι × (Fin S → Bits n)) : ℝ :=
  ∏ i, E.w.prob (data i).1 * shotsWeight E (ketbra ψ ψ) (data i).1 (data i).2

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §4.2,
pp.13–15: the expectation `E[f(σ_J)]` after the bootstrapping stages listed in `sched`, stage `t`
using `N_t` bases and `S_t` shots per basis (`sched = [(N_1, S_1), …, (N_J, S_J)]`), starting from
the current estimate `σ` with the fixed initial vector `σ₀` of Eq. (12).

**Formalization Note** "Different stages use independent bases and disjoint copies" (p.13): the
data of each stage are drawn from their own law, which depends only on `ψ`, and `σ_t` is a function
of `σ_{t−1}` and the stage-`t` data (Eqs. (12)–(13)). The expectation is therefore the nested finite
sum below, stage by stage. The histogram of the raw outcomes is used, as Algorithm 4 does. -/
noncomputable def stagesExpect {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (ψ σ₀ : Bits n → ℂ) : List (ℕ × ℕ) → (Bits n → ℂ) → ((Bits n → ℂ) → ℝ) → ℝ
  | [], σ, f => f σ
  | (N, S) :: rest, σ, f =>
      ∑ data : Fin N → ι × (Fin S → Bits n), stageWeight E ψ data *
        stagesExpect E ψ σ₀ rest
          (stageUpdate σ₀ σ (stageCorrection E σ S fun i => ((data i).1, histOf (data i).2))) f

/-- The bootstrapping run of Algorithm 4 (p.27) on histogram data: stage records
`(S_t, rec_t)` in order, each `rec_t` listing the `N_t` bases with their histograms. -/
noncomputable def stagesRun {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (σ₀ : Bits n → ℂ) : List (Σ N : ℕ, ℕ × (Fin N → ι × (Bits n → ℕ))) → (Bits n → ℂ) → (Bits n → ℂ)
  | [], σ => σ
  | ⟨_, S, rec⟩ :: rest, σ => stagesRun E σ₀ rest (stageUpdate σ₀ σ (stageCorrection E σ S rec))

end ShadowBootstrap


