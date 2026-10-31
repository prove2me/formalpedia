-- Prove2me | Definitions.Def_FuchsThesis_Holevo_IsIntermediateL
-- name    : FuchsThesis_Holevo_IsIntermediateL
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:57:44.567301+00:00
-- url     : https://prove2.me/theorems/22ece0d1-6660-4f71-aa61-17fcdd0ffde5
-- title:
--   The function $L(t)$: $L''(t)=-\mathrm{tr}(\hat\Delta\mathcal L_{\hat\rho}(\hat\Delta))$, $L(0)=L(1)=0$
-- statement:
--   For signal states $\hat\rho_0,\hat\rho_1$, write $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$ and $\hat\Delta=\hat\rho_1-\hat\rho_0$. A real function $L$ on $[0,1]$ is **Holevo's intermediate function** if
--
--   $$
--   L''(t) = -\mathrm{tr}\big(\hat\Delta\,\mathcal L_{\hat\rho}(\hat\Delta)\big)\quad (0<t<1), \qquad L(0)=L(1)=0 ,
--   $$
--
--   where $\mathcal L_{\hat\rho}$ is the super-operator (3.181). Precisely: $L$ is continuous on $[0,1]$, twice differentiable on $(0,1)$ with that second derivative, and vanishes at $0$ and $1$.
--
--   The function $L''$ is independent of the measurement, lies between $S''$ and every $J''$ ((3.165)), and therefore gives $I(t)\le L(t)\le S(t)$, (3.167).
--
--   **Formalization Note** The source defines $L$ through its second derivative (3.187) and the boundary condition (3.166). The second derivative is required on the open interval only, because $\mathrm{tr}(\hat\Delta\mathcal L_{\hat\rho}(\hat\Delta))$ may be unbounded as $t\to0$ or $t\to1$; continuity on $[0,1]$ makes the boundary condition meaningful. The trace is real for $0<t<1$; its real part is taken to give a real number. Two such functions differ by an affine function vanishing at $0$ and $1$, so $L$ is unique.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eqs. (3.165)–(3.166), pp.67–68 (PDF pp.76–77); eq. (3.187), p.71 (PDF p.80)

import Mathlib
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_lyapInv

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eqs. (3.165)–(3.166), pp.67–68 (PDF pp.76–77), with
(3.187), p.71 (PDF p.80): `L` is the function of `t` whose second derivative is
`L″(t) = −tr(Δ̂ 𝓛_ρ̂(Δ̂))`, `ρ̂ = (1 − t)ρ̂0 + tρ̂1`, `Δ̂ = ρ̂1 − ρ̂0`, subject to the boundary
condition `L(0) = L(1) = 0`.

**Formalization Note.** The source defines `L` through its second derivative and the boundary
condition. Here `IsIntermediateL ρ0 ρ1 L` says: `L` is continuous on `[0, 1]`, differentiable at
every `t ∈ (0, 1)`, its derivative has derivative `−Re tr(Δ̂ 𝓛_ρ̂(Δ̂))` at every `t ∈ (0, 1)`, and
`L 0 = L 1 = 0`. Twice differentiability is required on the open interval only, since
`tr(Δ̂ 𝓛_ρ̂(Δ̂))` may blow up as `t → 0` or `t → 1`. The trace is real for `0 < t < 1` (the
operator (3.181) is Hermitian); `Re` only fixes the type. Such an `L` is unique (two of them
differ by an affine function vanishing at `0` and `1`). -/
def IsIntermediateL {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (L : ℝ → ℝ) : Prop :=
  ContinuousOn L (Set.Icc 0 1) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ L t) ∧
    (∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (deriv L)
      (-(Matrix.trace ((ρ1 - ρ0) * lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0))).re) t) ∧
    L 0 = 0 ∧ L 1 = 0

end FuchsThesis.Holevo


