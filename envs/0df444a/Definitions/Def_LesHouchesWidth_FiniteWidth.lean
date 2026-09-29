-- Prove2me | Definitions.Def_LesHouchesWidth_FiniteWidth
-- name    : LesHouchesWidth_FiniteWidth
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-23T21:56:46.742771+00:00
-- url     : https://prove2.me/theorems/5f0a7733-8e6d-4598-b32d-f0faa9f7d365
-- title:
--   Finite-width statistics at a single input: $\langle\cdot\rangle_K$, $\chi_\parallel$, $\kappa_4$, $\Sigma^{(\ell)}$
-- statement:
--   Finite-width statistics of a Gaussian-initialized network at a single input (Lecture 4).
--
--   For the network $z^{(\ell)}$ with Gaussian initialization of Mission I, a single input $x$, constants $C_b,C_W$ and nonlinearity $\sigma$:
--
--   1. $\langle f\rangle_K=\int f\,d\mathcal N(0,K)$ (`gaussAvg`). $\langle g\rangle_K$ for $g$ of $m$ variables is taken against $m$ i.i.d. $\mathcal N(0,K)$ coordinates (`gaussAvgVec`).
--   2. $\mathrm{Var}_K[\sigma^2]=\langle\sigma^4\rangle_K-\langle\sigma^2\rangle_K^2$ (`gaussVarSq`).
--   3. $\chi_\parallel(K)=C_W\,\frac{d}{dK}\langle\sigma^2\rangle_K$ (`chiParallel`), so that $\chi^{(\ell)}_\parallel=\chi_\parallel(K^{(\ell)})=\partial K^{(\ell+1)}/\partial K^{(\ell)}$.
--   4. $\sigma$ is polynomially bounded if $|\sigma(t)|\le C(1+|t|^k)$ (`PolyBounded`).
--   5. $\kappa^{(\ell)}_4=\frac13\big(\mathbb E[(z^{(\ell)}_i)^4]-3\mathbb E[(z^{(\ell)}_i)^2]^2\big)$ (`kappa4`) and $G^{(\ell)}=\mathbb E[(z^{(\ell)}_i)^2]$ (`dressedTwoPoint`).
--   6. $\Sigma^{(\ell)}=C_b+\frac{C_W}{n_\ell}\sum_j\sigma(z^{(\ell)}_j)^2$ as a function of the layer-$\ell$ preactivation vector (`collectiveSigma`).
--
--   **Formalization Note** Variances $K<0$ are treated as $0$ by `gaussAvg`. `chiParallel` uses Mathlib's `deriv`, which is $0$ where the map is not differentiable.
-- source:
--   Bahri, Hanin, Brossollet, Erba, Keup, Pacelli, Simon, *Les Houches Lectures on Deep Learning at Large & Infinite Width*, arXiv:2309.01592v3 (https://arxiv.org/abs/2309.01592), p. 28 (Section 4.2, Gaussian averages), pp. 31–33 (Theorem 4.1, Section 4.8, Theorem 4.2), p. 34 (Lemma 4.4).

import Mathlib
import Definitions.Def_LesHouchesWidth_GaussianMLP

/-!
# Finite-width statistics at a single input (Les Houches lectures, Lecture 4)

Definitions used in Lecture 4 (Sections 4.2, 4.7–4.10) of arXiv:2309.01592v3, for the network
`mlpZ` with Gaussian initialization (eq. (119)) evaluated at a single input `x`.
-/

namespace LesHouchesWidth

open MeasureTheory ProbabilityTheory

/-- `⟨f⟩_K = ∫ f(z) exp(-z²/(2K)) dz / √(2πK)`, the average of `f` against the centered
Gaussian of variance `K` (Section 4.2). -/
noncomputable def gaussAvg (K : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ t, f t ∂(gaussianReal 0 K.toNNReal)

/-- `⟨g⟩_K` for a function of `m` variables, averaged against `m` i.i.d. centered Gaussians of
variance `K` (the Gaussian with covariance `K · I_m`). -/
noncomputable def gaussAvgVec (m : ℕ) (K : ℝ) (g : (Fin m → ℝ) → ℝ) : ℝ :=
  ∫ y, g y ∂(Measure.pi fun _ : Fin m => gaussianReal 0 K.toNNReal)

/-- `Var_K[σ²] = ⟨σ⁴⟩_K - ⟨σ²⟩_K²`. -/
noncomputable def gaussVarSq (σ : ℝ → ℝ) (K : ℝ) : ℝ :=
  gaussAvg K (fun t => σ t ^ 4) - gaussAvg K (fun t => σ t ^ 2) ^ 2

/-- The parallel susceptibility `χ_∥(K) = C_W ∂_K ⟨σ²⟩_K = ∂K^{(ℓ+1)}/∂K^{(ℓ)}` (Theorem 4.1). -/
noncomputable def chiParallel (CW : ℝ) (σ : ℝ → ℝ) (K : ℝ) : ℝ :=
  CW * deriv (fun K' => gaussAvg K' (fun t => σ t ^ 2)) K

/-- `σ` is polynomially bounded: `|σ(t)| ≤ C (1 + |t|^k)` for some `C`, `k`. -/
def PolyBounded (σ : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∃ k : ℕ, ∀ t, |σ t| ≤ C * (1 + |t| ^ k)

/-- The normalized connected four-point function of neuron `i` in layer `ℓ` at input `x`
(Section 4.8): `κ₄^{(ℓ)} = (1/3) (E[(z^{(ℓ)}_i)⁴] - 3 E[(z^{(ℓ)}_i)²]²)`. -/
noncomputable def kappa4 (Cb CW : ℝ) (σ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ) (x : Fin (n 0) → ℝ)
    (ℓ : ℕ) (i : Fin (n ℓ)) : ℝ :=
  (1 / 3) * (∫ θ, (mlpZ Cb CW σ θ x ℓ i) ^ 4 ∂(stdGaussianParams n L) -
    3 * (∫ θ, (mlpZ Cb CW σ θ x ℓ i) ^ 2 ∂(stdGaussianParams n L)) ^ 2)

/-- The dressed two-point function `G^{(ℓ)} = E[(z^{(ℓ)}_i)²]` (Theorem 4.2). -/
noncomputable def dressedTwoPoint (Cb CW : ℝ) (σ : ℝ → ℝ) (n : ℕ → ℕ) (L : ℕ)
    (x : Fin (n 0) → ℝ) (ℓ : ℕ) (i : Fin (n ℓ)) : ℝ :=
  ∫ θ, (mlpZ Cb CW σ θ x ℓ i) ^ 2 ∂(stdGaussianParams n L)

/-- The collective observable `Σ^{(ℓ)} = C_b + (C_W / n_ℓ) ∑_j σ(z^{(ℓ)}_j)²` (Lemma 4.4). -/
noncomputable def collectiveSigma (Cb CW : ℝ) (σ : ℝ → ℝ) (n : ℕ → ℕ) (ℓ : ℕ)
    (z : Fin (n ℓ) → ℝ) : ℝ :=
  Cb + CW / (n ℓ : ℝ) * ∑ j, σ (z j) ^ 2

end LesHouchesWidth


