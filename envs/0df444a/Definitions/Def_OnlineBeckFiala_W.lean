-- Prove2me | Definitions.Def_OnlineBeckFiala_W
-- name    : OnlineBeckFiala_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:58.293429+00:00
-- url     : https://prove2.me/theorems/cd62e6db-e3a1-497a-8e87-91761fe14c3c
-- title:
--   The potential $u=e^{A}$, $A(y)=(1-y^2)^{-2/\eta}$ (12), the law of $Y$, and $W(y)=M\,u(y)A(y)^{2+\eta}$ (14)
-- statement:
--   Fix $\eta>0$. For $|y|<1$ define
--   $$A(y)=(1-y^2)^{-2/\eta},\qquad u(y)=e^{A(y)}=\exp\bigl((1-y^2)^{-2/\eta}\bigr),$$
--   and $u(y)=+\infty$ for $|y|\ge1$ (§3, p.6, and eq. (12), p.7). Let $Z=\int_{-1}^1e^{-u(y)}\,dy$ and let $Y$ have density $Z^{-1}e^{-u}$ on $(-1,1)$ (§3.2, with $L=1$). For a constant $M\ge1$ put
--   $$W(y)=M\,u(y)\,A(y)^{2+\eta}\qquad(14).$$
--   Lemma 3.1 fixes $M=M_\eta$.
--
--   The double-exponential density $Z^{-1}e^{-u}$ is the invariant law of the walk; $W$ dominates the second derivative of $u$ near $y$, and its tail controls how often a state fails to be balanced.
--
--   **Formalization Note** $A$ and $u$ are real functions read only on $(-1,1)$; off it the real power takes Mathlib's default value, and every statement either restricts to $(-1,1)$ or integrates against the law of $Y$, which vanishes there. The multiplier $M$ is a parameter of $W$.
-- source:
--   Altschuler, Tikhomirov, Online Beck–Fiala Down to Logarithmic Sparsity, arXiv:2607.14238 (held version, sha256 5a1529d2…), pp.6–8, §3, eq. (12), §3.2, eq. (14)

import Mathlib
import Definitions.Def_OnlineBeckFiala_IsBalanced

open MeasureTheory

namespace OnlineBeckFiala

/-- `A(y) = (1 − y²)^{−2/η}`, eq. (12), p.7 (Altschuler, Tikhomirov, arXiv:2607.14238, held version,
sha256 5a1529d2…).

**Formalization Note.** Used only for `|y| < 1`; for `|y| ≥ 1` the real power takes Mathlib's junk
value, and every statement about `A` carries `y ∈ (−1, 1)` or only reads `A` there. -/
noncomputable def A (η y : ℝ) : ℝ := (1 - y ^ 2) ^ (-2 / η)

/-- The potential `u(y) = e^{A(y)} = exp((1 − y²)^{−2/η})` for `|y| < 1`, §3, p.6, and (12), p.7.

**Formalization Note.** The paper sets `u = +∞` for `|y| ≥ 1`; here `u` is real-valued and never read
there: the density `potLaw` vanishes off `(−1, 1)`, and statements about `u` assume `y ∈ (−1, 1)`. -/
noncomputable def u (η y : ℝ) : ℝ := Real.exp (A η y)

/-- `Z = ∫_{-1}^{1} e^{-u(y)} dy` for the potential of §3, p.6. -/
noncomputable def Z (η : ℝ) : ℝ := Zu (u η)

/-- The law `ρ` of `Y`, density `Z⁻¹ e^{-u}` on `(−1, 1)` (§3.2, p.7: `L = 1`). -/
noncomputable def rho1 (η : ℝ) : Measure ℝ := potLaw (u η)

/-- `W(y) = M u(y) A(y)^{2+η}`, eq. (14), p.8, with the multiplier `M` as a parameter (Lemma 3.1
chooses `M = M_η`). -/
noncomputable def W (η M y : ℝ) : ℝ := M * u η y * A η y ^ (2 + η)

end OnlineBeckFiala


