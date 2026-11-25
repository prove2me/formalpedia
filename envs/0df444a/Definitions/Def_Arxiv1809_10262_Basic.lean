-- Prove2me | Definitions.Def_Arxiv1809_10262_Basic
-- name    : Arxiv1809_10262_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-25T14:12:45.48631+00:00
-- url     : https://prove2.me/theorems/d4d109f6-760d-4c0b-afb6-625e49b5d1d5
-- title:
--   VelocityGAN: velocity maps, the generated law, the generator loss (8) and the regularized-inversion objective (9)
-- statement:
--   Objects of Sections III-B.1, III-C and III-D of Zhang and Lin, *Data-driven Seismic Waveform Inversion: A Study on the Robustness and Generalization* (arXiv:1809.10262v8).
--
--   1. **Velocity maps.** A velocity map of width $w$ and height $h$ is an array of real pixel values $v(i,j)$, $1\le i\le w$, $1\le j\le h$. Its $L_1$ norm is $\|m\|_1=\sum_{i,j}|m(i,j)|$ and its squared $L_2$ norm is $\|m\|_2^2=\sum_{i,j}m(i,j)^2$.
--   2. **Generated law.** Seismic data $d$ take values in a measurable space with distribution $\mu$. A generator (inversion operator) $g$ maps seismic data to velocity maps, and $\mathbb{P}_g$ is the distribution of $g(d)$ for $d\sim\mu$, the image measure $g_\#\mu$.
--   3. **Adversarial loss.** For a discriminator $D$ (a real function on velocity maps), the adversarial loss of $g$ is $-\mathbb{E}_{\tilde x\sim\mathbb{P}_g}D(\tilde x)=-\int D\,d(g_\#\mu)$.
--   4. **Generator loss, eq. (8).** For a training pair $(m,d)$ with true map $v=m$ and predicted map $\tilde v=g(d)$,
--   $$L_g=-\mathbb{E}_{\tilde x\sim\mathbb{P}_g}D(\tilde x)+\frac{\lambda_1}{w\,h}\sum_{i=1}^{w}\sum_{j=1}^{h}|\tilde v(i,j)-v(i,j)|+\frac{\lambda_2}{w\,h}\sum_{i=1}^{w}\sum_{j=1}^{h}(\tilde v(i,j)-v(i,j))^2 .$$
--   Over $N$ training pairs $(m_k,d_k)$, the training objective is the mean $\frac1N\sum_{k=1}^N L_g(m_k,d_k)$.
--   5. **Regularized-inversion objective, eq. (9).**
--   $$J_{\lambda_1,\lambda_2}(g)=\lambda_1\sum_{k=1}^{N}\|m_k-g(d_k)\|_1+\lambda_2\sum_{k=1}^{N}\|m_k-g(d_k)\|_2^2-\mathbb{E}_{\tilde x\sim\mathbb{P}_g}D(\tilde x).$$
--
--   **Formalization Note** Pixels are indexed from $0$. The paper writes eq. (8) for a single velocity map. Averaging it over the training pairs is the reading under which eq. (9) is a rewriting of eq. (8): the paper trains on mini-batches of pairs (Section IV-A.2) but never writes the training objective explicitly. $\mathbb{P}_g$ is the image of the seismic-data distribution under $g$. Lean's integral is $0$ when $D$ is not integrable and the image measure is $0$ when $g$ is not measurable; the statement excludes both by hypothesis.
-- source:
--   Z. Zhang and Y. Lin, Data-driven Seismic Waveform Inversion: A Study on the Robustness and Generalization, arXiv:1809.10262v8, Section III-B.1 (velocity maps), Section III-C (eqs. (7)-(8), generated law and generator loss), Section III-D (eq. (9))

import Mathlib

/-!
Z. Zhang and Y. Lin, *Data-driven Seismic Waveform Inversion: A Study on the Robustness and
Generalization* (VelocityGAN), arXiv:1809.10262v8 (2018): the velocity maps of Section III-B.1,
the content losses and the WGAN-GP generator loss of Section III-C (eq. (8)), and the
regularized-inversion objective of Section III-D (eq. (9)).
-/

open MeasureTheory

noncomputable section

namespace Arxiv1809_10262

/-- Section III-B.1 and eq. (8): a velocity map of width `w` and height `h`, given by its pixel
values `v(i,j)`, `1 ≤ i ≤ w`, `1 ≤ j ≤ h` (indexed from `0` here). -/
abbrev VelocityMap (w h : ℕ) : Type := Fin w → Fin h → ℝ

/-- Eq. (9): the `L_1` norm `‖m‖_1 = ∑_{i,j} |m(i,j)|` of a velocity map. -/
def l1Norm {w h : ℕ} (m : VelocityMap w h) : ℝ := ∑ i, ∑ j, |m i j|

/-- Eq. (9): the squared `L_2` norm `‖m‖_2^2 = ∑_{i,j} m(i,j)^2` of a velocity map. -/
def sqL2Norm {w h : ℕ} (m : VelocityMap w h) : ℝ := ∑ i, ∑ j, m i j ^ 2

/-- Section III-C, after eq. (7): `ℙ_g`, the distribution of the velocity maps `g(d)` predicted by
the generator `g` when the seismic data `d` has distribution `μ`. -/
def generatedLaw {Dat : Type*} [MeasurableSpace Dat] {w h : ℕ} (μ : Measure Dat)
    (g : Dat → VelocityMap w h) : Measure (VelocityMap w h) :=
  μ.map g

/-- Section III-C, before eq. (8): the adversarial loss `-𝔼_{x̃ ∼ ℙ_g} D(x̃)` of the generator `g`
against the discriminator `D`. -/
def adversarialLoss {Dat : Type*} [MeasurableSpace Dat] {w h : ℕ} (μ : Measure Dat)
    (D : VelocityMap w h → ℝ) (g : Dat → VelocityMap w h) : ℝ :=
  -∫ x, D x ∂(generatedLaw μ g)

/-- Eq. (8): the generator loss
`L_g = -𝔼_{x̃∼ℙ_g} D(x̃) + λ₁/(w·h) ∑_{i,j} |ṽ(i,j) - v(i,j)| + λ₂/(w·h) ∑_{i,j} (ṽ(i,j) - v(i,j))^2`
for one training pair `(m, d)`, with true map `v = m` and predicted map `ṽ = g(d)`. -/
def generatorLoss {Dat : Type*} [MeasurableSpace Dat] {w h : ℕ} (lam1 lam2 : ℝ)
    (μ : Measure Dat) (D : VelocityMap w h → ℝ) (m : VelocityMap w h) (d : Dat)
    (g : Dat → VelocityMap w h) : ℝ :=
  adversarialLoss μ D g + lam1 / ((w : ℝ) * h) * ∑ i, ∑ j, |g d i j - m i j| +
    lam2 / ((w : ℝ) * h) * ∑ i, ∑ j, (g d i j - m i j) ^ 2

/-- Eq. (8) over the training set (Sections III-C and IV-A.2): the generator loss of eq. (8)
averaged over the `N` training pairs `(m_k, d_k)`, as a function of the generator `g`. -/
def meanGeneratorLoss {Dat : Type*} [MeasurableSpace Dat] {w h N : ℕ} (lam1 lam2 : ℝ)
    (μ : Measure Dat) (D : VelocityMap w h → ℝ) (m : Fin N → VelocityMap w h) (d : Fin N → Dat)
    (g : Dat → VelocityMap w h) : ℝ :=
  (1 / (N : ℝ)) * ∑ k, generatorLoss lam1 lam2 μ D (m k) (d k) g

/-- Eq. (9): the regularized-inversion objective
`λ₁ ∑_{k=1}^N ‖m_k - g(d_k)‖_1 + λ₂ ∑_{k=1}^N ‖m_k - g(d_k)‖_2^2 - 𝔼_{x̃∼ℙ_g} D(x̃)`
of the inversion operator `g` on the `N` pairs `(m_k, d_k)` of velocity maps and seismic data. -/
def regularizedInversionObjective {Dat : Type*} [MeasurableSpace Dat] {w h N : ℕ}
    (lam1 lam2 : ℝ) (μ : Measure Dat) (D : VelocityMap w h → ℝ) (m : Fin N → VelocityMap w h)
    (d : Fin N → Dat) (g : Dat → VelocityMap w h) : ℝ :=
  lam1 * ∑ k, l1Norm (m k - g (d k)) + lam2 * ∑ k, sqL2Norm (m k - g (d k)) +
    adversarialLoss μ D g

end Arxiv1809_10262


