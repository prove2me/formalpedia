-- Prove2me | Definitions.Def_MilnorLambdaHalfShift
-- name    : MilnorLambdaHalfShift
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-01T12:04:38.890468+00:00
-- url     : https://prove2.me/theorems/46b2af40-3f5b-4d4c-baad-3cb9839e2382
-- title:
--   The modular lambda function via the half-shift theta constant (corrected)
-- statement:
--   The modular lambda function $\lambda : \mathbb{H} \to \mathbb{C}$ is declared here as the ratio of theta constants, $$\lambda(\tau) = \frac{\theta_2(\tau)^4}{\theta_3(\tau)^4}, \qquad \theta_3(\tau) = \sum_{n \in \mathbb{Z}} e^{\pi i n^2 \tau}.$$
--
--   This supersedes an earlier version of this definition, which computed the numerator from $\vartheta_2(0,\tau)$ and was therefore identically $1$: in Mathlib the two-variable theta satisfies $\vartheta_2(0,\tau) = \theta_3(\tau)$ exactly, by `tsum_congr`. The classical second constant is the half-shift sum $\theta_2(\tau) = \sum_n e^{\pi i (n+1/2)^2\tau}$, which is obtained instead at the argument $\vartheta_2(\tau/2, \tau)$, so that $\theta_2(\tau) = e^{\pi i \tau/4}\vartheta_2(\tau/2,\tau)$.
--
--   This is the object Milnor's Lemma 2.5 needs: $\lambda$ is a degree-$3$ universal covering from the upper half-plane onto $\mathbb{C}\setminus\{0,1\}$, and its only zeros and poles are the cusps, which lie on the boundary of $\mathbb{H}$ and never in $\mathbb{H}$ itself. Composing $\lambda$ with a biholomorphism from the open unit disc onto $\mathbb{H}$ therefore yields a covering of the thrice-punctured sphere by the disc, which is exactly the content of the milestone's target theorem.
--
--   **Only the definition is claimed.** None of the analytic properties is asserted: holomorphy on $\mathbb{H}$, avoidance of $0$ and $1$, surjectivity, properness, and the covering property remain to be proved as separate theorems.
-- source:
--   Milnor, Dynamics in One Complex Variable I, Princeton University Press, 2006, Lemma 2.5; the theta-constant expression is classical, cf. Apostol, Modular Functions and Dirichlet Series in Number Theory, Vol. 2, Springer, 1990, Chapter 2. The half-shift identity theta2(tau) = exp(pi i tau/4) * jacobiTheta2 (tau/2) tau was verified numerically at revision 0df444a3 and the resulting quotient reproduces lambda(i) = 1/2 and lambda(2i) = (sqrt(2)-1)^4.

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The modular lambda function (corrected)

The classical modular lambda is

$$\lambda(\tau) = \frac{\theta_2(\tau)^4}{\theta_3(\tau)^4}, \qquad \theta_3(\tau) = \sum_{n \in \mathbb{Z}} e^{\pi i n^2 \tau}.$$

**Why the numerator is not `jacobiTheta2 0`.** In Mathlib the two-variable theta is

$$\vartheta_2(z, \tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n z + \pi i n^2 \tau},$$

so at $z = 0$ it collapses onto the one-variable `jacobiTheta`: Mathlib proves
`jacobiTheta τ = jacobiTheta2 0 τ` by `tsum_congr`. An earlier version of this
definition therefore computed `x / x`. The classical second constant is the
half-shift sum, obtained at the argument $z = \tau / 2$:

$$\theta_2(\tau) = e^{\pi i \tau / 4}\, \vartheta_2\!\left(\frac{\tau}{2}, \tau\right).$$

**Only the definition is claimed.** Holomorphy on $\mathbb{H}$, avoidance of $0$ and
$1$, surjectivity onto $\mathbb{C} \setminus \{0,1\}$, properness, and the covering
property remain separate theorems.
-/

open Complex Real

namespace MilnorDynamics

/-- The classical second theta constant $\theta_2(\tau) = \sum_n e^{\pi i (n+1/2)^2 \tau}$,
expressed through Mathlib's two-variable theta at the argument `τ/2`. -/
noncomputable def milnorLambdaHalfShiftTheta₂ (τ : ℂ) : ℂ := cexp (π * I * τ / 4) * jacobiTheta₂ (τ / 2) τ

/-- The first theta constant $\theta_3(\tau) = \sum_{n \in \mathbb{Z}} e^{\pi i n^2 \tau}$. -/
noncomputable def milnorLambdaHalfShiftTheta₃ (τ : ℂ) : ℂ := jacobiTheta τ

/-- The numerator of the modular lambda, $\theta_2(\tau)^4$. -/
noncomputable def milnorLambdaHalfShiftNum (τ : ℂ) : ℂ := milnorLambdaHalfShiftTheta₂ τ ^ 4

/-- The denominator of the modular lambda, $\theta_3(\tau)^4$. -/
noncomputable def milnorLambdaHalfShiftDen (τ : ℂ) : ℂ := milnorLambdaHalfShiftTheta₃ τ ^ 4

/-- The corrected modular lambda function $\lambda(\tau) = \theta_2(\tau)^4 / \theta_3(\tau)^4$,
the degree-$3$ universal covering map from the upper half-plane onto
$\mathbb{C} \setminus \{0, 1\}$. -/
noncomputable def milnorLambdaHalfShift (τ : ℂ) : ℂ := milnorLambdaHalfShiftNum τ / milnorLambdaHalfShiftDen τ

end MilnorDynamics


