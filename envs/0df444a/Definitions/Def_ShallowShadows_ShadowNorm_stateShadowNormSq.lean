-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_stateShadowNormSq
-- name    : ShallowShadows_ShadowNorm_stateShadowNormSq
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:31:11.209244+00:00
-- url     : https://prove2.me/theorems/e9ffa7f6-9425-4ad3-8882-c1a9662f15c3
-- title:
--   State dependent squared shadow norm $\|O\|^2_{s,\sigma}$
-- statement:
--   For a finite ensemble $\mathcal U$ with measurement channel $\mathcal M$ (Eq. (2)), an operator $O$ and a state $\sigma$, the square of the **state dependent shadow norm** is
--
--   $$
--   \|O\|^2_{s,\sigma} = \mathbb E_{U\sim\mathcal U}\Big[\sum_{b\in\{0,1\}^n} \langle b|U\sigma U^\dagger|b\rangle\,\langle b|U\mathcal M^{-1}(O)U^\dagger|b\rangle^2\Big].
--   $$
--
--   It is the second moment of the single-shot estimator $\operatorname{tr}(O\mathcal M^{-1}(U^\dagger|b\rangle\langle b|U))$ of $\operatorname{tr}(O\sigma)$; its maximum over states is the HKP shadow norm.
--
--   **Formalization Note** $\mathcal M^{-1}$ is the reused `ClassicalShadow.Linear.measChannelInv`, the ring inverse of the channel. Real parts of the (real, for Hermitian $\sigma$ and $O$) matrix entries are taken, exactly as in the reused `ClassicalShadow.Linear.shadowNorm`, which equals $\sqrt{\sup_\sigma \|O\|^2_{s,\sigma}}$ by definition.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §VIII, p. 7 (unnumbered display)

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §VIII, p. 7
(unnumbered display): the square of the state dependent shadow norm
`‖O‖²_{s,σ} = E_{U∼𝒰}[Σ_{b∈{0,1}ⁿ} ⟨b|U σ U†|b⟩ ⟨b|U M⁻¹(O) U†|b⟩²]`, for a finite ensemble `𝒰`
with measurement channel `M` (Eq. (2)); the paper takes `𝒰 = 𝒰_d` and `M = M_d`.

**Formalization Note.** `M⁻¹` is `ClassicalShadow.Linear.measChannelInv E = Ring.inverse
(measChannel E)`, the inverse of the channel of Eq. (2) (a genuine inverse for the paper's
ensembles, a milestone). The integrand is exactly the one maximized by the reused
`ClassicalShadow.Linear.shadowNorm` (Eq. (3)), so `shadowNorm E O = √(sup_σ stateShadowNormSq E O σ)`.
For a Hermitian `σ` the Born weight `⟨b|UσU†|b⟩` is real, and for a Hermitian `O` the number
`⟨b|U M⁻¹(O) U†|b⟩` is real (the paper's ensembles); real parts are taken to land in `ℝ`, as in
`shadowNorm`. -/
noncomputable def stateShadowNormSq {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (O σ : Op n) : ℝ :=
  ∑ i, E.w.prob i * ∑ b, (diagEntry E i σ b).re * ((diagEntry E i (measChannelInv E O) b) ^ 2).re

end ShallowShadows.ShadowNorm


