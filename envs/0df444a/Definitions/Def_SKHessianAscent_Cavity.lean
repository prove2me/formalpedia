-- Prove2me | Definitions.Def_SKHessianAscent_Cavity
-- name    : SKHessianAscent_Cavity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:59:58.707151+00:00
-- url     : https://prove2.me/theorems/857ad532-9048-413e-b729-778431d23ba1
-- title:
--   The replica-symmetric fixed point $(m^*,q^*)$, overlaps, the planted matrix $A+\tfrac\beta nx_0x_0^{\mathsf T}$ and the AMP iterates $m_j$
-- statement:
--   - `cavityMean β t m q g` is $\mathbf E_h\,g(Y^*)$ with $Y^*=\beta^2m+t+\sqrt{\beta^2q+t}\,h$, $h\sim N(0,1)$.
--   - `IsCavityFP β t m q`: $(m,q)=(m^*,q^*)$ solves the fixed-point equations
--   $$q^*=\mathbf E_h\tanh^2\big(\beta^2m^*+t+\sqrt{\beta^2q^*+t}\,h\big),\qquad m^*=\mathbf E_h\tanh\big(\beta^2m^*+t+\sqrt{\beta^2q^*+t}\,h\big).$$
--   - `overlap x z` is $R(x,z)=\tfrac1n\langle x,z\rangle$ for $x,z\in\{\pm1\}^n$: the overlap $R_{12}$ of two replicas, and the magnetization $M=\tfrac1n\sum_i(x_0)_i\sigma_i$ when $z=x_0$ is the planted configuration.
--   - `planted β A x₀` is $A+\tfrac\beta nx_0x_0^{\mathsf T}$; the TAP Hessian of this matrix is the Hessian of the SL-tilted planted model of §4, $\beta^2(1-\|m\|_2^2/n)I_n-\beta A+D(m)-\tfrac{\beta^2}nx_0x_0^{\mathsf T}-\tfrac{2\beta^2}nmm^{\mathsf T}$.
--   - `ampState β J y j` is the pair $(z_j,m_{j-1})$ and `ampMag β J y j` is $m_j=\tanh(z_j)$ of the AMP iteration $m_{-1}=0_n$, $z_0=0_n$,
--   $$z_{j+1}=\beta Jm_j+y-\beta^2\Big(1-\frac{\|m_j\|_2^2}{n}\Big)m_{j-1}.$$
--
--   **Formalization Note** The paper does not give $z_0$; the iteration is that of [AMS22, Algorithm 1], which it cites and which starts from $\widehat m^{-1}=z^0=0$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §4 pp. 19–20 (AMP iterates, planted Hessian) and Appendix B pp. 47–49; fixed-point equations of [DLSS26a, Theorem 5.1] (https://arxiv.org/abs/2605.03718, p. 58); AMP of [AMS22, Algorithm 1] (https://arxiv.org/abs/2203.05093)

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_tilt
import Definitions.Def_SKHessianAscent_Model

open OAI.CriticalSK SKAnnealing.Sampling MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SKHessianAscent

/-!
# Replica-symmetric fixed point, overlaps, the planted matrix and the AMP iteration

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §4 (pp. 19–20) and Appendix B (pp. 47–49).

* The fixed-point equations are those of [DLSS26a, Theorem 5.1] (arXiv:2605.03718, p. 58), which
  the paper cites: `q* = E_h tanh²(β²m* + t + √(β²q* + t) h)`,
  `m* = E_h tanh(β²m* + t + √(β²q* + t) h)`, `h ∼ N(0,1)`; `Y* = β²m* + t + √(β²q* + t) h`
  (Lemma B.4).
* The overlap is `R₁₂ = (1/n)⟨σ¹, σ²⟩`, and the magnetization of Corollary B.1 is
  `M = (1/n) Σ_i (x₀)_i σ_i`, the overlap with the planted configuration `x₀`
  ([DLSS26a, Theorem 5.2]).
* AMP iterates (p. 19): `m_{−1} = 0_n`, `m_j = tanh(z_j)`,
  `z_{j+1} = β(A + (β/n) x₀x₀ᵀ) m_j + y_t − β²(1 − ‖m_j‖²/n) m_{j−1}`.

**Formalization Note.** The paper does not give `z_0`; the iteration is that of
[AMS22, Algorithm 1] (arXiv:2203.05093), which the paper cites and which starts from
`m̂^{−1} = z⁰ = 0`.
-/

noncomputable section

/-- `E_h g(Y*)` with `Y* = β²m + t + √(β²q + t) h`, `h ∼ N(0,1)`. -/
def cavityMean (β t m q : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ h, g (β ^ 2 * m + t + Real.sqrt (β ^ 2 * q + t) * h) ∂(gaussianReal 0 1)

/-- `(m, q) = (m*, q*)` solves the fixed-point equations of [DLSS26a, Theorem 5.1]:
`q = E tanh²(Y*)` and `m = E tanh(Y*)`. -/
def IsCavityFP (β t m q : ℝ) : Prop :=
  q = cavityMean β t m q (fun y => Real.tanh y ^ 2) ∧ m = cavityMean β t m q Real.tanh

/-- The overlap `R(x, z) = (1/n)⟨x, z⟩` of two configurations. -/
def overlap {n : ℕ} (x z : Spin n) : ℝ := (∑ i, spinValue (x i) * spinValue (z i)) / n

/-- The planted matrix `A + (β/n) x₀x₀ᵀ`. -/
def planted {n : ℕ} (β : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x₀ : Spin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  A + (β / n) • Matrix.vecMulVec (spinVec x₀) (spinVec x₀)

/-- The AMP state `(z_j, m_{j−1})` for the matrix `J` and the tilt `y`: `z_0 = 0`, `m_{−1} = 0`,
`z_{j+1} = βJ m_j + y − β²(1 − ‖m_j‖²/n) m_{j−1}` with `m_j = tanh(z_j)`. -/
def ampState {n : ℕ} (β : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    ℕ → (Fin n → ℝ) × (Fin n → ℝ)
  | 0 => (0, 0)
  | j + 1 =>
    let z := (ampState β J y j).1
    let mprev := (ampState β J y j).2
    let m : Fin n → ℝ := fun i => Real.tanh (z i)
    (fun i => β * (J.mulVec m) i + y i - β ^ 2 * (1 - (∑ l, m l ^ 2) / n) * mprev i, m)

/-- The AMP iterate `m_j = tanh(z_j)`. -/
def ampMag {n : ℕ} (β : ℝ) (J : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) (j : ℕ) : Fin n → ℝ :=
  fun i => Real.tanh ((ampState β J y j).1 i)

end

end SKHessianAscent


