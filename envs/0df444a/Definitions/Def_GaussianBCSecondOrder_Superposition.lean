-- Prove2me | Definitions.Def_GaussianBCSecondOrder_Superposition
-- name    : GaussianBCSecondOrder_Superposition
-- status  : Definition
-- author  : @Vincent Tan
-- created : 2026-11-23T07:27:29.767172+00:00
-- url     : https://prove2.me/theorems/d82d0a31-1d2c-47a2-82de-6b0d8538e15d
-- title:
--   Gaussian BC achievability objects: augmented error and information densities
-- statement:
--   This file formalizes the objects used in the achievability part of the paper (Section III).
--
--   **Augmented error.** An augmented code is an $(n,M_1,M_2)$-code in which receiver 1 additionally produces an estimate of $W_2$ from $Y_1^n$. Its conditional augmented error probability $e_n(m_1,m_2)$ is the probability that at least one of the three estimates (receiver 1's estimates of $W_1$ and of $W_2$, receiver 2's estimate of $W_2$) is wrong, and the augmented average error probability $e_n$ is its average over uniform message pairs. Since receiver 1 must decode both messages, $\varepsilon_{n,\mathrm{av}}\le e_n$. A pair $(L_1,L_2)$ is achievable with augmented error at $R^*$ if there is a sequence of augmented codes satisfying the rate conditions of eq. (16) and $\limsup_n e_n\le\varepsilon$.
--
--   **Superposition pair (eq. (48)).** Deterministic vectors $u^n,v^n\in\mathbb R^n$ with $\|u^n\|^2=n(1-\alpha)$, $\|v^n\|^2=n\alpha$ and $\langle u^n,v^n\rangle=0$.
--
--   **Information densities (eq. (49)).** With $x^n=u^n+v^n$, $Y_j^n=x^n+Z_j^n$, $\phi_n(\cdot;t)$ the density of $\mathcal N(0,tI_n)$, $s_j=\alpha+1/S_j$, $q_j(y|u)=\phi_n(y-u;s_j)$, $q_{0,j}(y)=\phi_n(y;1+1/S_j)$ and $\mathsf W_j^n(y|x)=\phi_n(y-x;1/S_j)$,
--   $$\iota_0=\log\frac{q_1(Y_1^n|u^n)}{q_{0,1}(Y_1^n)},\qquad \iota_1=\log\frac{\mathsf W_1^n(Y_1^n|x^n)}{q_1(Y_1^n|u^n)},\qquad \iota_2=\log\frac{q_2(Y_2^n|u^n)}{q_{0,2}(Y_2^n)} .$$
--
--   **Auxiliary constants (eq. (54)).** $C_0(\alpha)=\mathsf C(S_1)-\mathsf C(\alpha S_1)$ and $V_0(\alpha)=\mathsf V(S_1)+\mathsf V(\alpha S_1)-2\mathsf V(\alpha S_1,S_1)$.
--
--   These objects are used to state Lemma 3, Lemma 4, Proposition 5 and Lemma 6.
--
--   **Formalization Note** The information densities are functions of the noise sample, with $u^n,v^n$ fixed; the logarithm of a Gaussian density is written in closed form, $\log\phi_n(y;t)=-\tfrac n2\log(2\pi t)-\|y\|^2/(2t)$.
-- source:
--   Vincent Y. F. Tan, Second-Order Asymptotics for the Scalar Gaussian Broadcast Channel, arXiv:2611.01583v1 (3 Nov 2026), https://arxiv.org/abs/2611.01583, pp. 11-12, Section III-A and III-B, eqs. (48), (49), (54), and the definition of the augmented average error probability after Lemma 3

import Definitions.Def_GaussianBCSecondOrder_Codes
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
Objects used in the achievability proof of the second-order coding region of the scalar Gaussian
broadcast channel (V. Y. F. Tan, arXiv:2611.01583v1, Section III): codes in which receiver 1
estimates both messages (augmented error), the superposition pair `(u^n, v^n)` of eq. (48), and
the information densities of eq. (49).
-/

open MeasureTheory ProbabilityTheory Filter

namespace GaussianBCSecondOrder

/-- A code in which receiver 1 additionally estimates the message `W₂` of receiver 2 from
its own output `Y₁^n` (Section III-A). -/
structure AugCode (n M₁ M₂ : ℕ) extends Code n M₁ M₂ where
  decoder₁₂ : EuclideanSpace ℝ (Fin n) → Fin M₂
  measurable_decoder₁₂ : Measurable decoder₁₂

namespace AugCode

variable {n M₁ M₂ : ℕ}

/-- Conditional augmented error probability `e_n(m₁, m₂)`: the probability that at least one of
the three estimates (receiver 1's estimates of `W₁` and `W₂`, receiver 2's estimate of `W₂`) is
wrong when `(m₁, m₂)` is sent. -/
noncomputable def augCondError (c : AugCode n M₁ M₂) (S₁ S₂ ρ : ℝ) (m₁ : Fin M₁) (m₂ : Fin M₂) :
    ℝ :=
  (noiseLaw S₁ S₂ ρ n).real
    {z | ¬ (c.decoder₁ (c.encoder m₁ m₂ + noiseVec 0 z) = m₁ ∧
            c.decoder₁₂ (c.encoder m₁ m₂ + noiseVec 0 z) = m₂ ∧
            c.decoder₂ (c.encoder m₁ m₂ + noiseVec 1 z) = m₂)}

/-- Augmented average error probability `e_n` for independent uniform messages. -/
noncomputable def augAvgError (c : AugCode n M₁ M₂) (S₁ S₂ ρ : ℝ) : ℝ :=
  (1 / ((M₁ : ℝ) * (M₂ : ℝ))) * ∑ m₁ : Fin M₁, ∑ m₂ : Fin M₂, c.augCondError S₁ S₂ ρ m₁ m₂

end AugCode

/-- Second-order achievability of `L = (L₁, L₂)` at first-order rates `R` with augmented error:
a sequence of codes in which receiver 1 estimates both messages, with
`liminf (log M_{j,n} - n R_j) / √n ≥ L_j` for `j = 1, 2` and `limsup e_n ≤ ε`, where `e_n` is the
augmented average error probability. -/
def AugAchievable (S₁ S₂ ρ ε : ℝ) (R L : ℝ × ℝ) : Prop :=
  ∃ (M₁ M₂ : ℕ → ℕ) (c : ∀ n, AugCode n (M₁ n) (M₂ n)),
    (L.1 : EReal) ≤ liminf (secondOrderRate M₁ R.1) atTop ∧
    (L.2 : EReal) ≤ liminf (secondOrderRate M₂ R.2) atTop ∧
    limsup (fun n => (((c n).augAvgError S₁ S₂ ρ : ℝ) : EReal)) atTop ≤ (ε : EReal)

/-- Condition (48) on the deterministic vectors `u^n, v^n`:
`‖u‖² = n (1 - α)`, `‖v‖² = n α` and `⟨u, v⟩ = 0`. -/
def IsSuperpositionPair {n : ℕ} (α : ℝ) (u v : EuclideanSpace ℝ (Fin n)) : Prop :=
  ‖u‖ ^ 2 = n * (1 - α) ∧ ‖v‖ ^ 2 = n * α ∧ inner ℝ u v = 0

/-- Logarithm of the density `φ_n(y; t)` of `N(0, t I_n)` at `y ∈ ℝⁿ`:
`-(n/2) log (2 π t) - ‖y‖² / (2 t)`. -/
noncomputable def logGaussianDensity (n : ℕ) (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -((n : ℝ) / 2) * Real.log (2 * Real.pi * t) - ‖y‖ ^ 2 / (2 * t)

variable {n : ℕ}

/-- `ι₀(u, Y₁) = log (q₁(Y₁ | u) / q_{0,1}(Y₁))`, eq. (49), as a function of the noise sample,
with `Y₁ = u + v + Z₁`, `q₁(y | u) = φ_n(y - u; s₁)` and `q_{0,1}(y) = φ_n(y; 1 + 1/S₁)`. -/
noncomputable def info₀ (S₁ α : ℝ) (u v : EuclideanSpace ℝ (Fin n))
    (z : Fin n → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  logGaussianDensity n (condVar S₁ α) (u + v + noiseVec 0 z - u) -
    logGaussianDensity n (1 + 1 / S₁) (u + v + noiseVec 0 z)

/-- `ι₁(x, u, Y₁) = log (W₁(Y₁ | x) / q₁(Y₁ | u))`, eq. (49), as a function of the noise sample,
with `x = u + v`, `Y₁ = x + Z₁`, `W₁(y | x) = φ_n(y - x; 1/S₁)` and
`q₁(y | u) = φ_n(y - u; s₁)`. -/
noncomputable def info₁ (S₁ α : ℝ) (u v : EuclideanSpace ℝ (Fin n))
    (z : Fin n → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  logGaussianDensity n (1 / S₁) (u + v + noiseVec 0 z - (u + v)) -
    logGaussianDensity n (condVar S₁ α) (u + v + noiseVec 0 z - u)

/-- `ι₂(u, Y₂) = log (q₂(Y₂ | u) / q_{0,2}(Y₂))`, eq. (49), as a function of the noise sample,
with `Y₂ = u + v + Z₂`, `q₂(y | u) = φ_n(y - u; s₂)` and `q_{0,2}(y) = φ_n(y; 1 + 1/S₂)`. -/
noncomputable def info₂ (S₂ α : ℝ) (u v : EuclideanSpace ℝ (Fin n))
    (z : Fin n → EuclideanSpace ℝ (Fin 2)) : ℝ :=
  logGaussianDensity n (condVar S₂ α) (u + v + noiseVec 1 z - u) -
    logGaussianDensity n (1 + 1 / S₂) (u + v + noiseVec 1 z)

/-- `C₀(α) = C(S₁) - C(α S₁)`, eq. (54). -/
noncomputable def C₀ (S₁ α : ℝ) : ℝ := capacity S₁ - capacity (α * S₁)

/-- `V₀(α) = V(S₁) + V(α S₁) - 2 V(α S₁, S₁)`, eq. (54). -/
noncomputable def V₀ (S₁ α : ℝ) : ℝ :=
  dispersion S₁ + dispersion (α * S₁) - 2 * crossDispersion (α * S₁) S₁

end GaussianBCSecondOrder


