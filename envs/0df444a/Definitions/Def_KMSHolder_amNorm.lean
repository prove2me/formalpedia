-- Prove2me | Definitions.Def_KMSHolder_amNorm
-- name    : KMSHolder_amNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:41:50.181213+00:00
-- url     : https://prove2.me/theorems/c3f1a7cd-e2df-4b90-b90f-740457203b19
-- title:
--   Araki–Masuda $L_p$ norm $\|\zeta\|_p = \sup_{\|\xi\|=1}\|\Delta^{1/2-1/p}_{\xi,\Omega}\zeta\|$
-- statement:
--   Let $M$ act on $H$ in standard form with cyclic and separating unit vector $\Omega$. For $2 \le p < \infty$, Araki and Masuda define
--
--   $$
--   \|\zeta\|_p = \sup_{\|\xi\| = 1} \big\| \Delta^{\frac12 - \frac1p}_{\xi,\Omega}\, \zeta \big\|,
--   \qquad
--   L_p(M,\Omega) = \Big\{ \zeta \in \bigcap_{\xi \in H} D\big(\Delta^{\frac12 - \frac1p}_{\xi,\Omega}\big) : \|\zeta\|_p < \infty \Big\},
--   $$
--
--   where $\Delta_{\xi,\Omega}$ is the relative modular operator of the vector functional $\omega_\xi = \langle \xi, \cdot\, \xi\rangle$ on $M$, and the supremum runs over all unit vectors $\xi$ (cyclic or not).
--
--   Here $\|\zeta\|_p$ is valued in $[0, \infty]$: the term for $\xi$ is $+\infty$ when $\zeta$ is not in the domain of $\Delta^{1/2-1/p}_{\xi,\Omega}$. Thus $\zeta \in L_p(M,\Omega)$ exactly when $\|\zeta\|_p < \infty$. These are the non-commutative $L_p$-spaces through which the Hölder inequality for KMS states is proved.
--
--   **Formalization Note** The value lies in `ℝ≥0∞`; the domain condition is an infimum over the empty set (`⊤`) when no image vector exists. Powers follow the support convention. $\omega_\xi$ is the published `HollandsSanders.CFTBound.vecState ξ`. $p$ is real, and the definition is used for $2 \le p < \infty$.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3.2, pp.5–6 (Araki–Masuda [3, Equ. (1.3), p.340])

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
import Definitions.Def_KMSHolder_PosSpectralCalculus
import Definitions.Def_KMSHolder_posPowGraph
import Definitions.Def_KMSHolder_IsRelModular

open OAI.BoundedRecovery
open scoped ENNReal NNReal

namespace KMSHolder

/-- Jäkel–Robl, arXiv:1103.3608v2, §3.2, pp.5–6, quoting Araki–Masuda [3, Equ. (1.3), p.340]: for
`2 ≤ p ≤ ∞`,
`L_p(M, Ω) = {ζ ∈ ⋂_{ξ ∈ H} D(Δ^{1/2 − 1/p}_{ξ,Ω}) : ‖ζ‖_p < ∞}`,
`‖ζ‖_p = sup_{‖ξ‖=1} ‖Δ^{1/2 − 1/p}_{ξ,Ω} ζ‖`.

`amNorm S p ζ` is this supremum in `ℝ≥0∞`, taken over all unit vectors `ξ ∈ H` (cyclic or not)
and the relative modular operator `T = Δ_{ξ,Ω}` of the vector functional `ω_ξ = ⟪ξ, · ξ⟫` on `M`;
the term for `ξ` is `‖T^{1/2−1/p} ζ‖`, and `⊤` when `ζ` is not in the domain of `T^{1/2−1/p}`
(an infimum over the empty set). So `ζ ∈ L_p(M, Ω)` iff `amNorm S p ζ < ⊤`, and then
`‖ζ‖_p = (amNorm S p ζ).toReal`.

**Formalization Note.** `p` is real; the definition is used for `2 ≤ p < ∞`. The power
`T^{1/2−1/p}` follows the support convention of `posPowGraph` (Araki–Masuda's convention for
non-faithful `ω_ξ`). `ω_ξ` is the published `HollandsSanders.CFTBound.vecState ξ`. -/
noncomputable def amNorm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : StandardModularData H) (p : ℝ) (ζ : H) : ℝ≥0∞ :=
  ⨆ (ξ : H) (_ : ‖ξ‖ = 1) (T : PosSpectralCalculus H)
    (_ : IsRelModular S (HollandsSanders.CFTBound.vecState ξ) T),
    ⨅ (y : H) (_ : (ζ, y) ∈ posPowGraph T (((1 / 2 - 1 / p : ℝ)) : ℂ)), (‖y‖₊ : ℝ≥0∞)

end KMSHolder


