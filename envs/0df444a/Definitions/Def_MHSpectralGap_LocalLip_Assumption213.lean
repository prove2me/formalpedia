-- Prove2me | Definitions.Def_MHSpectralGap_LocalLip_Assumption213
-- name    : MHSpectralGap_LocalLip_Assumption213
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:53:59.930116+00:00
-- url     : https://prove2.me/theorems/58cd4977-21aa-414f-98b0-4064dbf6386f
-- title:
--   Assumption 2.13, p. 13 — exp(−Φ) is γ-integrable and the local Lipschitz constant φ(r) grows subexponentially
-- statement:
--   Let $H$ be a normed space with a measure $\gamma$ and $\Phi : H\to\mathbb R$. **Assumption 2.13** holds if $\exp(-\Phi)$ is $\gamma$-integrable and for every $\kappa>0$ there is $M_\kappa$ such that, for every $r>0$,
--
--   $$\varphi(r)=\sup_{x\neq y\in B_r(0)}\frac{|\Phi(x)-\Phi(y)|}{\|x-y\|}\le M_\kappa e^{\kappa r}.$$
--
--   This allows $\Phi$ to be only locally Lipschitz, with a local Lipschitz constant on the ball of radius $r$ that grows more slowly than any exponential $e^{\kappa r}$. It replaces the global Lipschitz condition (Assumption 2.11) of the first half of §2.3.
--
--   **Formalization Note** The supremum is not formed: the bound is stated pointwise, $|\Phi(x)-\Phi(y)|\le M_\kappa e^{\kappa r}\|x-y\|$ for all $x\ne y$ in the open ball $B_r(0)$, which is equivalent and avoids the junk value of a real supremum of an unbounded or empty set.
-- source:
--   Hairer, Stuart and Vollmer, Spectral gaps for a Metropolis–Hastings algorithm in infinite dimensions, arXiv:1112.1392v4, p. 13, Assumption 2.13

import Mathlib

open MeasureTheory

namespace MHSpectralGap.LocalLip

/-- Assumption 2.13 (p. 13). `exp(−Φ)` is `γ`-integrable, and for every `κ > 0` there is `M_κ`
with `φ(r) = sup_{x ≠ y ∈ B_r(0)} |Φ(x) − Φ(y)| / ‖x − y‖ ≤ M_κ e^{κ r}` for every `r > 0`;
the bound on the supremum is stated pointwise for each pair `x ≠ y` in the open ball. -/
def Assumption213 {H : Type} [NormedAddCommGroup H] [MeasurableSpace H] (Φ : H → ℝ)
    (γ : Measure H) : Prop :=
  Integrable (fun x => Real.exp (-Φ x)) γ ∧
    ∀ κ > 0, ∃ M : ℝ, ∀ r > 0, ∀ x ∈ Metric.ball (0 : H) r, ∀ y ∈ Metric.ball (0 : H) r,
      x ≠ y → |Φ x - Φ y| ≤ M * Real.exp (κ * r) * ‖x - y‖

end MHSpectralGap.LocalLip


