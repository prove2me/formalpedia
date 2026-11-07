-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_entVar
-- name    : OptimalSpectrum_Entangled_entVar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:23:27.304213+00:00
-- url     : https://prove2.me/theorems/cb13000d-5f01-4cd7-b023-b6a834d3cedc
-- title:
--   Variance of the entangled moment estimate: $\mathrm{tr}(F_p^2\rho^{\otimes n})-\mathrm{tr}(F_p\rho^{\otimes n})^2$
-- statement:
--   The entangled estimate $\widehat F_p$ is the measured value of the observable $F_p$ on $\rho^{\otimes n}$. Its variance is
--
--   $$\mathrm{Var}(\widehat F_p)=\mathrm{tr}\big(F_p^2\rho^{\otimes n}\big)-\mathrm{tr}\big(F_p\rho^{\otimes n}\big)^2,$$
--
--   the formula the paper uses for the variance of measuring an observable (Lemma 7.6).
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.2, p. 21, and Lemma 7.6, p. 24 (PDF pp. 23, 26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_OptimalSpectrum_Entangled_Fobs

namespace OptimalSpectrum.Entangled

/-- **Variance of the entangled moment estimate `F̂_p`.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.2, printed p. 21 (PDF p. 23): "The polynomial moment estimate F̂_p = ∑ p_m M̂_m is
therefore the measured value of F_p"; Lemma 7.6, printed p. 24 (PDF p. 26): "the variance of
measuring G in state ρ^⊗n satisfies tr(G²ρ^⊗n) − tr(Gρ^⊗n)²".

`entVar d n Π̄ p ρ = tr(F_p² ρ^{⊗n}) − tr(F_p ρ^{⊗n})²`, the variance of the outcome of measuring the
observable `F_p` in the state `ρ^{⊗n}`.

**Formalization Note.** Real parts of the traces are taken (they are real, `F_p` being Hermitian).
The `M_m` commute (milestone §7.1.2), so this is also the variance of `∑ p_m M̂_m` for their joint
measurement. -/
noncomputable def entVar (d n : ℕ) (Pbar : Matrix (Fin d) (Fin d) ℂ) (p : Polynomial ℝ)
    (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (Matrix.trace (Fobs d n Pbar p * Fobs d n Pbar p * QAlgorithms.piKron n ρ)).re -
    (Matrix.trace (Fobs d n Pbar p * QAlgorithms.piKron n ρ)).re ^ 2

end OptimalSpectrum.Entangled


