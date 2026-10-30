-- Prove2me | Definitions.Def_KatyushaNs_IsQuadProxMin
-- name    : KatyushaNs_IsQuadProxMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:46:11.943233+00:00
-- url     : https://prove2.me/theorems/1c9bb8ec-7acf-452e-a4c0-d70b2d68472b
-- title:
--   Proximal step: minimizer of $\frac{\kappa}{2}\|z - c\|^2 + \langle g, z\rangle + \psi(z)$
-- statement:
--   Let $\psi : \mathbb{R}^d \to \mathbb{R}\cup\{+\infty\}$ have effective domain $D$, and let $\kappa \in \mathbb{R}$ and $c, g \in \mathbb{R}^d$. A point $p$ is a **proximal point** for $(\kappa, c, g)$ if
--   $$p \in \operatorname*{arg\,min}_{z \in \mathbb{R}^d} \Big( \frac{\kappa}{2}\|z - c\|^2 + \langle g, z\rangle + \psi(z) \Big),$$
--   that is, $p \in D$ and the objective at $p$ is at most the objective at every $w \in D$.
--
--   Line 11 of Algorithm 2 is this step with $\kappa = 1/\alpha_s$ and $c = z_k$; line 12 (Option I) is this step with $\kappa = 3L$ and $c = x_{k+1}$.
--
--   **Formalization Note** $\psi$ is given by the set $D$ and real values on $D$. The arg min is a predicate: neither existence nor lower semicontinuity of $\psi$ is assumed. For $\kappa > 0$ and convex $\psi$ the minimizer is unique when it exists. Adding constants to the objective or multiplying it by a positive number (as Lemmas 2.3 and 2.5 do) does not change the minimizer.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Algorithm 2, lines 11 and 12, p. 15

import Mathlib

namespace KatyushaNs

/-- **Proximal step: `p` minimizes `z ↦ (κ/2)‖z − c‖² + ⟨g, z⟩ + ψ(z)`.**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Algorithm 2, p. 15 (PDF p. 16): line 11 "z_{k+1} = arg min_z
{ 1/(2α_s) ‖z − z_k‖² + ⟨∇̃_{k+1}, z⟩ + ψ(z) }" (here `κ = 1/α_s`, `c = z_k`) and line 12
(Option I) "y_{k+1} ← arg min_y { 3L/2 ‖y − x_{k+1}‖² + ⟨∇̃_{k+1}, y⟩ + ψ(y) }" (here `κ = 3L`,
`c = x_{k+1}`).

`IsQuadProxMin D ψ κ c g p` says: `p ∈ D`, and for every `w ∈ D`,
`(κ/2)‖p − c‖² + ⟨g, p⟩ + ψ(p) ≤ (κ/2)‖w − c‖² + ⟨g, w⟩ + ψ(w)`.

**Formalization Note.** The extended-valued `ψ` of the paper is encoded by its effective domain
`D` and its finite values `ψ` on `D` (points off `D` have objective `+∞` and cannot be
minimizers). The argmin is a predicate: no existence is claimed and no closedness or lower
semicontinuity of `ψ` is assumed. For `κ > 0` and convex `ψ` on convex `D` the objective is
strongly convex, so a minimizer is unique when it exists. Lemmas 2.3 and 2.5 write the same
argmins with constants added to the objective or the objective multiplied by `α > 0`, which does
not change the minimizer. -/
def IsQuadProxMin {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (κ : ℝ) (c g p : EuclideanSpace ℝ (Fin d)) : Prop :=
  p ∈ D ∧ ∀ w ∈ D,
    κ / 2 * ‖p - c‖ ^ 2 + inner ℝ g p + ψ p ≤ κ / 2 * ‖w - c‖ ^ 2 + inner ℝ g w + ψ w

end KatyushaNs


