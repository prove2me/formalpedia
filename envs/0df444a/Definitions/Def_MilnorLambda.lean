-- Prove2me | Definitions.Def_MilnorLambda
-- name    : MilnorLambda
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-01T11:16:28.509766+00:00
-- url     : https://prove2.me/theorems/81ffb158-208f-4fe4-85f0-794dd288461a
-- title:
--   The modular lambda function via theta constants: $\lambda(\tau) = \theta_2(\tau)^4/\theta_3(\tau)^4$
-- statement:
--   The modular lambda function $\lambda : \mathbb{H} \to \mathbb{C}$ is declared here as the ratio of theta constants,
--
--   $$\lambda(\tau) = \frac{\theta_2(\tau)^4}{\theta_3(\tau)^4}, \qquad \theta_3(\tau) = \sum_{n \in \mathbb{Z}} e^{\pi i n^2 \tau}, \qquad \theta_2(\tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n \tau + \pi i n^2 \tau}.$$
--
--   Equivalently, writing $q = e^{2 \pi i \tau}$, one has $\lambda = 16 q^{1/2} (1-q)^2 / (1 + q^{1/2})^4$. This is the object Milnor's Lemma 2.5 needs: $\lambda$ is a universal covering map from the upper half-plane onto $\mathbb{C} \setminus \{0,1\}$, and its only zeros and poles are the cusps, which lie on the boundary of $\mathbb{H}$ and never in $\mathbb{H}$ itself. Composing $\lambda$ with a biholomorphism from the open unit disc onto $\mathbb{H}$ therefore yields a covering of the thrice-punctured sphere by the disc, which is exactly the content of the milestone's target theorem.
--
--   **Only the definition is claimed.** None of the analytic properties is asserted: holomorphy on $\mathbb{H}$, avoidance of the values $0$ and $1$, surjectivity onto $\mathbb{C} \setminus \{0,1\}$, properness, and the covering property all remain to be proved as separate theorems. Declaring the function first is what makes those statements well posed at all, because each of them is then an assertion *about a named function* rather than an existential quantifier over an unspecified witness.
-- source:
--   Milnor, Dynamics in One Complex Variable I, Princeton University Press, 2006, Lemma 2.5 (the triply-punctured sphere is hyperbolic); the theta-constant expression $\lambda = \theta_2^4/\theta_3^4$ is classical, cf. Apostol, Modular Functions and Dirichlet Series in Number Theory, Vol. 2, Springer, 1990, Chapter 2.

import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# The modular lambda function

This declares the classical modular lambda

$$\lambda(\tau) = \frac{\theta_2(\tau)^4}{\theta_3(\tau)^4}$$

where $\theta_3(\tau) = \sum_{n \in \mathbb{Z}} e^{\pi i n^2 \tau}$ is the one-variable
Jacobi theta function and $\theta_2(\tau) = \sum_{n \in \mathbb{Z}} e^{2 \pi i n \tau + \pi i n^2 \tau}$
is the second Jacobi theta function. Equivalently, with $q = e^{2 \pi i \tau}$,
$\lambda = 16 q^{1/2} (1 - q)^2 / (1 + q^{1/2})^4$.

No analytic property of $\lambda$ is asserted here: this is a *definition*. The leaves
of the Milnor Lemma 2.5 milestone are the theorems that must establish holomorphy
on $\mathbb{H}$, avoidance of $0$ and $1$, surjectivity onto $\mathbb{C} \setminus \{0,1\}$, and
the covering property.
-/

open Complex

namespace MilnorDynamics

/-- The numerator of the modular lambda, $\theta_2(\tau)^4$. -/
noncomputable def milnorLambdaNum (τ : ℂ) : ℂ := jacobiTheta₂ 0 τ ^ 4

/-- The denominator of the modular lambda, $\theta_3(\tau)^4$. -/
noncomputable def milnorLambdaDen (τ : ℂ) : ℂ := jacobiTheta τ ^ 4

/-- The modular lambda function $\lambda(\tau) = \theta_2(\tau)^4 / \theta_3(\tau)^4$,
the universal covering map from the upper half-plane onto $\mathbb{C} \setminus \{0, 1\}$. -/
noncomputable def milnorLambda (τ : ℂ) : ℂ := milnorLambdaNum τ / milnorLambdaDen τ

end MilnorDynamics


