-- Prove2me | Definitions.Def_FTPLLinBandit_baseLaw
-- name    : FTPLLinBandit_baseLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:30.934195+00:00
-- url     : https://prove2.me/theorems/190f9926-3634-411d-925b-590416e41fe1
-- title:
--   Standard perturbation draw $W\sim P_I$ of a scheme
-- statement:
--   For a perturbation scheme with radial profile $f$, the **standard draw** is the law $P_I$ on $\mathbb R^d$ with density $P_I(z)\propto f(\|z\|_2)$.
--
--   Each call of SampleAction in Algorithm 1 draws a fresh $W\sim P_I$ and forms its perturbation from it: $\sqrt\lambda\,W\sim P_{\lambda I}=\rho_1$ is the random-weighting initializer (Table 2), and $\Sigma_t^{1/2}W\sim P_{\Sigma_t}$ is the elliptical perturbation (Section 4: "let $Z_t=\Sigma_t^{1/2}SU$", where $SU\sim P_I$).
--
--   **Formalization Note** Lebesgue measure with density $P_I$; a probability measure for each profile with $d\ge1$.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, p.8; §4, p.9; Tables 2 and 4, p.21

import Mathlib
import Definitions.Def_FTPLLinBandit_Scheme
import Definitions.Def_FTPLLinBandit_radialFn
import Definitions.Def_FTPLLinBandit_ellDens

open MeasureTheory

namespace FTPLLinBandit

/-- **The standard draw `P_I` of a scheme.** Wei, arXiv:2610.17818, Figure 2, p.8, §4, p.9, and
Tables 2 and 4, p.21. Each slot of Algorithm 1 draws a fresh `W ∼ P_I`, the law with density
`ellDens f I` (`∝ f(‖z‖)`) of the scheme's profile `f`. The run then sets `Z = √λ W` for random
weighting (`√λ W ∼ P_{λI} = ρ₁`, Table 2) and `Z = B_t W` with `B_t B_tᵀ = Σ_t` for the elliptical
scheme (`B_t W ∼ P_{Σ_t}`; §4, p.9: "let Z_t = Σ_t^{1/2} S U").

**Formalization Note.** The law is Lebesgue measure with density `ellDens f I`; it is a
probability measure for each profile of `radialFn` (with `d ≥ 1`). -/
noncomputable def baseLaw (d : ℕ) (s : Scheme) : Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensity fun z => ENNReal.ofReal (ellDens (radialFn d
    (match s with
     | .randomWeighting f _ => f
     | .elliptical f => f)) (1 : Matrix (Fin d) (Fin d) ℝ) z)

end FTPLLinBandit


