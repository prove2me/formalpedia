-- Prove2me | Definitions.Def_IshamProblemOfTime_DeWitt
-- name    : IshamProblemOfTime_DeWitt
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:10:02.989321+00:00
-- url     : https://prove2.me/theorems/3db54e6b-1603-414b-be47-1de0a7e9ddfa
-- title:
--   DeWitt supermetric, metric traces and the ADM conjugate momentum (Isham §3.3.3)
-- statement:
--   Pointwise algebra of the ADM canonical formalism of general relativity, as in Isham, §3.3.3. Fix a point $x$ of the spatial slice $\Sigma$. The spatial metric at $x$ is a real $3\times 3$ matrix $g=(g_{ab})$ (assumed positive definite in every theorem that uses it), its inverse $g^{ab}$ is the matrix inverse $g^{-1}$, and $|g|=\det g$. Contravariant two-tensors such as the momentum $p^{ab}$ and the extrinsic curvature $K^{ab}$ are real $3\times 3$ matrices.
--
--   * **DeWitt supermetric** (eq. (3.3.21)): the bilinear form
--   $$\mathcal G_g(p,q)=\mathcal G_{ab\,cd}\,p^{ab}q^{cd},\qquad \mathcal G_{ab\,cd}=\tfrac12|g|^{-1/2}\bigl(g_{ac}g_{bd}+g_{bc}g_{ad}-g_{ab}g_{cd}\bigr).$$
--   It is the coefficient of the kinetic term $\kappa^2\mathcal G_{ab\,cd}p^{ab}p^{cd}$ of the super-Hamiltonian $\mathcal H_\perp$ (eq. (3.3.20)).
--   * **Metric trace** $\operatorname{tr}_g T = g_{ab}T^{ab}$ (Isham's $T_c{}^c$) and **metric square** $K_{ab}K^{ab}=g_{ac}g_{bd}K^{ab}K^{cd}$.
--   * **Conjugate momentum** (eq. (3.3.16)): $p^{ab}=-\dfrac{|g|^{1/2}}{\kappa^2}\bigl(K^{ab}-g^{ab}K_c{}^c\bigr)$, where $\kappa^2=8\pi G/c^2$.
--
--   Conventions of the Lean file: $|g|^{-1/2}$ is written $(\sqrt{\det g})^{-1}$; for a matrix with $\det g\le 0$ this evaluates to $0$ (so the form vanishes identically), which is why every theorem assumes $g$ positive definite.
-- source:
--   C. J. Isham, Canonical Quantum Gravity and the Problem of Time, lectures at the NATO ASI "Recent Problems in Mathematical Physics" (Salamanca, 1992), https://arxiv.org/abs/gr-qc/9210011, Section 3.3.3, eqs. (3.3.16), (3.3.19)-(3.3.21), p. 30.

import Mathlib

/-!
# DeWitt supermetric (Isham, *Canonical Quantum Gravity and the Problem of Time*, §3.3.3)

Pointwise (fixed `x ∈ Σ`) algebra of the ADM canonical variables.  A spatial three-metric
at a point is a real `3 × 3` matrix `g` (components `g_{ab}`, assumed positive definite in
the theorems), and contravariant symmetric tensors such as `p^{ab}` and `K^{ab}` are real
`3 × 3` matrices.  The inverse metric `g^{ab}` is the matrix inverse `g⁻¹`, and `|g|` is
`det g`.
-/

namespace IshamProblemOfTime

open Matrix

/-- Isham eq. (3.3.21): the DeWitt supermetric, as a bilinear form on contravariant
two-tensors,
`𝒢_{abcd} p^{ab} q^{cd}` with
`𝒢_{abcd} = ½ |g|^{-1/2} (g_{ac} g_{bd} + g_{bc} g_{ad} - g_{ab} g_{cd})`. -/
noncomputable def deWittSupermetric (g p q : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (1 / 2) * (Real.sqrt g.det)⁻¹ *
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (g a c * g b d + g b c * g a d - g a b * g c d) * p a b * q c d

/-- The trace `g_{ab} T^{ab}` (written `T_c{}^c` in Isham) of a contravariant two-tensor
`T` with respect to the metric `g`. -/
def metricTrace (g T : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, g a b * T a b

/-- The full contraction `K_{ab} K^{ab} = g_{ac} g_{bd} K^{ab} K^{cd}` of a contravariant
two-tensor `K` with itself, indices lowered with `g`. -/
def metricSquare (g K : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3, g a c * g b d * K a b * K c d

/-- Isham eq. (3.3.16): the momentum conjugate to `g_{ab}` expressed through the extrinsic
curvature,
`p^{ab} = -(|g|^{1/2} / κ²) (K^{ab} - g^{ab} K_c{}^c)`. -/
noncomputable def conjugateMomentum (κ : ℝ) (g K : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  (-(Real.sqrt g.det / κ ^ 2)) • (K - metricTrace g K • g⁻¹)

end IshamProblemOfTime


