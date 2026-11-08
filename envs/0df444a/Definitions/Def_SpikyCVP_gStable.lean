-- Prove2me | Definitions.Def_SpikyCVP_gStable
-- name    : SpikyCVP_gStable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:19.902256+00:00
-- url     : https://prove2.me/theorems/10dab318-1f8c-42e0-b321-ac2f21210555
-- title:
--   The positive $\alpha$-stable density $g_\alpha$ (Zolotarev form) and the constants $q,\kappa_p,\beta$
-- statement:
--   Let $0<\alpha<1$ (in the paper $\alpha=p/2$ with $0<p<2$) and set
--
--   $$q=\frac{\alpha}{1-\alpha},\qquad \kappa_p=(1-\alpha)\alpha^q,\qquad \beta=2^{1/q},$$
--
--   so that $\beta^q=2$ and $(2\beta)^\alpha=2$. For $0<\theta<\pi$ let
--
--   $$A_\alpha(\theta)=\frac{\sin(\alpha\theta)^q\,\sin((1-\alpha)\theta)}{\sin(\theta)^{q+1}} .$$
--
--   The **positive $\alpha$-stable density** is, for $a>0$,
--
--   $$g_\alpha(a)=\frac{q}{\pi a^{q+1}}\int_0^\pi A_\alpha(\theta)\,e^{-A_\alpha(\theta)a^{-q}}\,d\theta,$$
--
--   and $g_\alpha(a)=0$ for $a\le0$. This is Zolotarev's integral representation, differentiated (Equation (2.11)). The density $g_{p/2}$ is the mixing law that writes $e^{-|x|^p}$ as a mixture of Gaussians.
--
--   **Formalization Note** The paper introduces $g_{p/2}$ as the density of the measure that Bernstein's theorem gives for the Laplace transform $e^{-y^{p/2}}$, and derives (2.11) from Zolotarev's (2.10). Here (2.11) is the definition, and the Laplace-transform identity is the milestone (2.7). The constants are written as functions of $\alpha$; $\kappa_p$ is $\texttt{kappa}(p/2)$.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), §2.2, Equations (2.7), (2.9), (2.10), (2.11), pp.12–13 (PDF pp.14–15)

import Mathlib

open Real

namespace SpikyCVP

/-- `q = α/(1 − α)`; with `α = p/2` this is `p/(2 − p)`. Aggarwal, Morolia, *How to Round Spiky Balls into
Submission; And Faster Algorithms For The Closest Vector Problem*, STOC 2027 submission (manuscript sha256
535c3bcc…), §2.2, p.13 (PDF p.15). -/
noncomputable def qExp (α : ℝ) : ℝ := α / (1 - α)

/-- `κp = (1 − α)α^q` (§2.2, p.13), written as a function of `α = p/2`. -/
noncomputable def kappa (α : ℝ) : ℝ := (1 - α) * α ^ qExp α

/-- `β = 2^{1/q}` (§2.2, p.13), so that `β^q = 2` and `(2β)^α = 2` (2.9). -/
noncomputable def betaC (α : ℝ) : ℝ := (2 : ℝ) ^ (1 / qExp α)

/-- `Aα(θ) := sin(αθ)^q sin((1 − α)θ) / sin(θ)^{q+1}` for `0 < θ < π` (§2.2, p.13).

**Formalization Note.** For `0 < α < 1` and `0 < θ < π` every sine is positive, so `Real.rpow` is the
usual power; values at `θ ∈ {0, π}` do not matter, since `Aα` is only integrated. -/
noncomputable def Aalpha (α θ : ℝ) : ℝ :=
  Real.sin (α * θ) ^ qExp α * Real.sin ((1 - α) * θ) / Real.sin θ ^ (qExp α + 1)

/-- The density `gα` of the positive `α`-stable law, given by Zolotarev's representation, Equation (2.11),
p.13:
`gα(a) = q/(π a^{q+1}) ∫_0^π Aα(θ) e^{−Aα(θ)a^{−q}} dθ` for `a > 0`.

**Formalization Note.** The paper defines `g_{p/2}` as the density of the measure that Bernstein's theorem
gives for the Laplace transform `exp(−y^{p/2})` (p.12–13), and derives (2.11) from Zolotarev's (2.10).
Here (2.11) is the definition; that its Laplace transform is `exp(−y^α)` is milestone (2.7). The value
for `a ≤ 0` is `0`, the density of a law on `(0, ∞)`. The integrand is bounded on `(0, π)` for `a > 0`. -/
noncomputable def gStable (α a : ℝ) : ℝ :=
  if 0 < a then
    qExp α / (π * a ^ (qExp α + 1)) *
      ∫ θ in (0 : ℝ)..π, Aalpha α θ * Real.exp (-(Aalpha α θ * a ^ (-qExp α)))
  else 0

end SpikyCVP


