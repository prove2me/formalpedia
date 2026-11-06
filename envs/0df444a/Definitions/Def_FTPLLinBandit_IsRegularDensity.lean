-- Prove2me | Definitions.Def_FTPLLinBandit_IsRegularDensity
-- name    : FTPLLinBandit_IsRegularDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:26.520344+00:00
-- url     : https://prove2.me/theorems/8b133455-ec0c-40a3-9908-3187a34b9441
-- title:
--   Regular perturbation density (Lemma 18)
-- statement:
--   A function $\rho:\mathbb R^d\to\mathbb R$ is a **regular perturbation density** when
--
--   1. $\rho$ is a probability density: $\rho\ge0$ and $\int_{\mathbb R^d}\rho(z)\,dz=1$;
--   2. $\rho$ is locally Lipschitz;
--   3. $\mathbb E_{Z\sim\rho}\|Z\|_2=\int\|z\|_2\,\rho(z)\,dz<\infty$;
--   4. $\int_{\mathbb R^d}\|\nabla\rho(z)\|_2\,dz<\infty$.
--
--   Lemma 18 shows that for a regular $\rho$ the smoothed support function $\Psi(\Theta)=\mathbb E_{Z\sim\rho}[h(\Theta+Z)]$ is twice differentiable with explicit gradient and Hessian; the paper remarks that all its perturbations are regular.
--
--   **Formalization Note** $\nabla\rho$ is Mathlib's gradient, which is $0$ where $\rho$ is not differentiable; a locally Lipschitz $\rho$ is differentiable almost everywhere (Rademacher), so this is the paper's a.e. gradient.
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 18, p.26

import Mathlib

open MeasureTheory

namespace FTPLLinBandit

/-- **Regular perturbation density.** Wei, arXiv:2610.17818, Lemma 18, p.26: "Call a perturbation
density ρ regular if it is locally Lipschitz, E_{Z∼ρ}[‖Z‖₂] < ∞, and ∫‖∇ρ(z)‖₂ dz < ∞".

`IsRegularDensity ρ` says that `ρ` is a probability density on ℝ^d (nonnegative with Lebesgue
integral `1`), locally Lipschitz, with `∫ ‖z‖ ρ(z) dz < ∞` and `∫ ‖∇ρ(z)‖ dz < ∞`.

**Formalization Note.** `gradient ρ` is Mathlib's gradient, defined as `0` where `ρ` is not
differentiable; a locally Lipschitz `ρ` is differentiable Lebesgue-a.e. (Rademacher), so this is
the a.e. gradient the paper integrates. "Density" (nonnegative, integral one) is the paper's
"perturbation density"; the Bochner integral `∫ ρ = 1` also forces `ρ` to be integrable. -/
def IsRegularDensity {d : ℕ} (ρ : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  (∀ z, 0 ≤ ρ z) ∧ ∫ z, ρ z = 1 ∧ LocallyLipschitz ρ ∧
    Integrable (fun z => ‖z‖ * ρ z) ∧ Integrable (fun z => ‖gradient ρ z‖)

end FTPLLinBandit


