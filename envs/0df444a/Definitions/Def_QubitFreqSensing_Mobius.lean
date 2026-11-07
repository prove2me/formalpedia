-- Prove2me | Definitions.Def_QubitFreqSensing_Mobius
-- name    : QubitFreqSensing_Mobius
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:59.877448+00:00
-- url     : https://prove2.me/theorems/adde7204-98f2-482c-a6ee-a3de2aa463d0
-- title:
--   The Möbius maps $L_{\pm,a}$, the signs $s_i$ and the perturbation $\Phi^{(i)}_z$
-- statement:
--   For $|a|<1$ and a sign $\varepsilon\in\{1,-1\}$,
--   $$
--   L_{\varepsilon,a}(z)=\frac{a+\varepsilon z}{1+\varepsilon\bar a z}
--   $$
--   ($L_{+,a}$ and $L_{-,a}$ on p.17). For a frequency index $i$ let $s_i(x)=\operatorname{sign}\cos(\omega_i x)\in\{1,-1\}$, and for $z$ in the unit disc define the perturbation of a function $f$ by
--   $$
--   (\Phi^{(i)}_z f)(x)=L_{s_i(x),\,f(x)}(z).
--   $$
--   Thus $\Phi^{(i)}_0 f=f$, and $\Phi^{(i)}_z$ maps $\mathbb T$ into $\mathbb T$ for $|z|<1$. The random perturbation $z=re^{i\theta}$ increases the potential $J$ in expectation when some correlation is small (Corollary 5.10).
--
--   **Formalization Note** $s_i(x)$ is taken to be $+1$ where $\cos(\omega_i x)=0$ (the page's $\operatorname{sign}$ would give $0$ there, and $L_{0,a}$ is not one of the maps $L_{\pm,a}$); the zero set is countable, so no integral changes. At the pole $1+\varepsilon\bar a z=0$, outside the closed unit disc, Lean's division returns $0$.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), §5, p.17 (L_{±,a}); p.19 (s_i, Φ_z^{(i)})

import Mathlib

open Real

namespace QubitFreqSensing

/-- **The Möbius maps** `L_{±,a}(z) = (a ± z)/(1 ± āz)` (Chen, Coladangelo, Li, Zhang, manuscript
(STOC 2027 submission), §5, p.17), for `|a| < 1`: `mob ε a z = (a + εz)/(1 + ε ā z)` with
`ε ∈ {1, −1}` (`ε = 1` is `L_{+,a}`, `ε = −1` is `L_{−,a}`).

**Formalization Note** The sign `ε` is a real number; the mission only uses `ε = ±1`. At the pole
`1 + ε ā z = 0` (which lies outside the closed unit disc when `|a| < 1`) Lean's division returns
`0`. -/
noncomputable def mob (ε : ℝ) (a z : ℂ) : ℂ :=
  (a + (ε : ℂ) * z) / (1 + (ε : ℂ) * (starRingEnd ℂ) a * z)

/-- The sign `s_i(x) = sign(g_i(x)) = sign(cos(ω_i x))` (p.19), with the value `+1` on the zeros of
`cos(ω_i x)`.

**Formalization Note** The page's `sign` is `0` on the countable zero set of `cos(ω_i x)`, where
`L_{0,a}` is not one of the maps `L_{±,a}`; the value `+1` there changes no integral. -/
noncomputable def sgnCos {N : ℕ} (ω : Fin N → ℝ) (i : Fin N) (x : ℝ) : ℝ :=
  if 0 ≤ Real.cos (ω i * x) then 1 else -1

/-- **The perturbation** `Φ_z^{(i)}` (p.19): `(Φ_z^{(i)} f)(x) = L_{s_i(x), f(x)}(z)`. -/
noncomputable def Phi {N : ℕ} (ω : Fin N → ℝ) (i : Fin N) (z : ℂ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => mob (sgnCos ω i x) (f x) z

end QubitFreqSensing


