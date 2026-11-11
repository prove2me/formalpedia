-- Prove2me | Definitions.Def_GaussDiffSVP_gaussRef
-- name    : GaussDiffSVP_gaussRef
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T22:00:49.805356+00:00
-- url     : https://prove2.me/theorems/3b8c4e11-6eda-4130-87aa-d58deb5711de
-- title:
--   Gaussian reference $\nu_{p,r,\Upsilon}$ on a coset and shell
-- statement:
--   For $\Gamma = B\mathbb Z^n$, an offset $p$, a width $r$, a shell energy $a$ and a coefficient $\Upsilon$,
--   $$\nu_{p,r,\Upsilon}(x) = \frac{\Upsilon}{V_r}\,\rho_r(x)\,\mathbf 1[x\in(p+\Gamma)\cap S_r(a)],\qquad \rho_r(x) = e^{-\pi\|x\|^2/r^2}.$$
--   The coefficient controls the expected number of records and the remaining factors fix their Gaussian profile. Section 5 uses $a=a_0$; (78) is the same reference at the leaves of a full difference tree.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (40), p.27; (78), p.39

import Mathlib
import Definitions.Def_GaussDiffSVP_shell
import Definitions.Def_GaussDiffSVP_volFactor

open scoped ENNReal

namespace GaussDiffSVP

/-- The Gaussian reference on a coset and shell (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), (40), p.27, and (78), p.39):
`ν_{p,r,Υ}(x) = (Υ / V_r) ρ_r(x) 1[x ∈ (p + Γ) ∩ S_r(a)]`, with `Γ = Bℤⁿ`, `V_r = rⁿ/det Γ`,
`ρ_r(x) = e^{−π‖x‖²/r²}` and `S_r(a)` the shell of relative width `w`. Section 5 uses `a = a₀`.

**Formalization Note.** Values in `ℝ≥0∞`; `x ∈ p + Γ` is `x − p ∈ Γ`. -/
noncomputable def gaussRef {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (r w a Υ : ℝ)
    (p x : SuperlatSVP.E n) : ℝ≥0∞ := by
  classical
  exact if x - p ∈ SuperlatSVP.lat B ∧ x ∈ shell r w a then
    ENNReal.ofReal (Υ / volFactor B r * RegevLWE.GaussConv.rho r x) else 0

end GaussDiffSVP


