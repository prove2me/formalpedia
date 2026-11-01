-- Prove2me | Definitions.Def_ManIAL_IsRetrSmooth
-- name    : ManIAL_IsRetrSmooth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:12:10.155384+00:00
-- url     : https://prove2.me/theorems/992c66a3-1b5b-4cdc-8b5d-a2131172ca87
-- title:
--   Retraction smoothness (Definition 2.6)
-- statement:
--   A function $\psi:\mathbb R^n\to\mathbb R$ is **retraction smooth** (retr-smooth) on $\mathcal M$ with constant $L$ and retraction $R$ if
--
--   $$
--   \psi(R_x(\eta))\le\psi(x)+\langle\operatorname{grad}\psi(x),\eta\rangle+\frac L2\|\eta\|^2\qquad\text{for all }x\in\mathcal M,\ \eta\in T_x\mathcal M,
--   $$
--
--   where $\operatorname{grad}\psi(x)=P_{T_x\mathcal M}(\nabla\psi(x))$ is the Riemannian gradient for the metric inherited from $\mathbb R^n$. This is the manifold analogue of the descent lemma for functions with Lipschitz gradient; it is the hypothesis under which Riemannian gradient descent (Algorithm 2) makes progress.
--
--   **Formalization Note** The Riemannian gradient is the published `ZORiem.RGD.rgrad` (orthogonal projection of Mathlib's `gradient` onto the tangent space). Definition 2.6 quantifies over $x,y\in\mathcal M$ with $y=R_x(\eta)$, $\eta\in T_x\mathcal M$, which is the same condition.
-- source:
--   Deng, Hu, Wu & Wen, Oracle complexities of augmented Lagrangian methods for nonsmooth manifold optimization, arXiv:2404.05121v2, Definition 2.6, display (2.5), p.6; display (3.17), p.10

import Mathlib
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ZORiem_RGD_rgrad

open ProjLikeRetr.Retractor ZORiem.RGD

namespace ManIAL

/-- Retraction smoothness, Definition 2.6 (Deng–Hu–Wu–Wen, arXiv:2404.05121v2, p.6; restated
as (3.17), p.10): `ψ` is retr-smooth on `M` with constant `L` and retraction `R` if
`ψ(R_x(η)) ≤ ψ(x) + ⟨grad ψ(x), η⟩ + (L/2)‖η‖²` for all `x ∈ M` and `η ∈ T_xM`.

**Formalization Note.** `grad ψ(x)` is `rgrad M ψ x`, the orthogonal projection of the
Euclidean gradient onto `T_xM = tangentSpace M x`. Definition 2.6 quantifies over `x, y ∈ M`
with `y = R_x(η)`, `η ∈ T_xM`; that is the same as quantifying over `x ∈ M` and `η ∈ T_xM`. -/
def IsRetrSmooth {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ M, ∀ η ∈ tangentSpace M x,
    ψ (R x η) ≤ ψ x + inner ℝ (rgrad M ψ x) η + L / 2 * ‖η‖ ^ 2

end ManIAL


