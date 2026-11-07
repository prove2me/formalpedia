-- Prove2me | Definitions.Def_PolySampIso_BackwardsMRW
-- name    : PolySampIso_BackwardsMRW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:28:33.163878+00:00
-- url     : https://prove2.me/theorems/079c7ba4-d688-4ee8-8106-bfc10bbf52b7
-- title:
--   Algorithm 6 (BackwardsMRW): a lazy Metropolized random walk in H_γ-whitened coordinates
-- statement:
--   **Algorithm 6** (BackwardsMRW$(x_0,\gamma,\tau,t,N)$) runs $N$ iterations from $x_0\in X$. In each, with probability $\tfrac12$ it stays put; otherwise it proposes
--
--   $$x'=x_i+\frac{\tau}{8\sqrt{n(\tau+t)}}\,H_\gamma^{-1/2}\xi,\qquad\xi\sim\mathcal N(0_n,I_n),$$
--
--   and moves to $x'$ with probability
--
--   $$\min\Big\{1,\exp\big(\langle A^\top\gamma,x'-x_i\rangle-(\tau+t)(\psi(x')-\psi(x_i))\big)\Big\}\mathbb 1_{x'\in X}.$$
--
--   It is the $\tfrac12$-lazy Metropolis–Hastings walk with Gaussian proposal and target $\pi^{X|\Gamma=\gamma}_{t,\tau}$, the approximate backwards step of Part II. Its kernel $K(x,\cdot)=\mathrm{Law}(\mathrm{BackwardsMRW}(x,\gamma,\tau,t,N))$ is the object of Lemma 32.
--
--   **Formalization Note** Each iteration reads a fair coin, a standard Gaussian vector and a uniform $u\in[0,1]$ ("with probability $p$" is "$u<p$"); $H_\gamma^{-1/2}$ is the matrix square root of $H_\gamma^{-1}$.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 6, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_DualConditioning
import Definitions.Def_PolySampIso_MarkovKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal MatrixOrder

namespace PolySampIso

/-!
# Algorithm 6: BackwardsMRW(x₀, γ, τ, t, N)

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 6, p.43 (PDF p.45):
"1 Input: previous iterate x0 ∈ X, forward draw γ ∈ Rm>0, regularization parameter τ ∈ N, cooling
parameter t ∈ R≥0, number of iterations N ∈ N
2 for i = 0, . . . , N − 1 do
3   W ∼ Unif([2])
4   xi+1 ← xi
5   if W = 2 then
6     x′ ← xi + τ/(8√(n(τ+t))) H_γ^{−1/2} ξ for a fresh random draw ξ ∼ N(0n, In)
7     xi+1 ← x′ with probability min{1, exp(⟨A⊤γ, x′ − xi⟩ − (τ + t)(ψ(x′) − ψ(xi)))} I_{x′∈X}
8   end
9 end
10 Return: xN"

**Formalization Note.**
* One iteration reads the noise `(w, ξ, u)` with `w` a fair coin (`w = true` is `W = 2`),
  `ξ ∼ N(0, I_n)` (Mathlib's `stdGaussian`) and `u ∼ Unif[0, 1]`; "with probability `p`" is
  "if `u < p`". The `N` iterations read i.i.d. noise. `backwardsMRW A b γ τ t N` is the Markov
  kernel `x ↦ Law(BackwardsMRW(x, γ, τ, t, N))`.
* `H_γ^{−1/2}` is `CFC.sqrt (H_γ⁻¹)` (positive definite `H_γ` for `γ > 0` and full-column-rank `A`).
* `⟨A⊤γ, x′ − x⟩ = Σᵢ γᵢ⟨aᵢ, x′ − x⟩`.
-/

/-- The noise of one iteration of Algorithm 6: coin `W`, Gaussian `ξ`, uniform `u`. -/
abbrev MRWNoise (n : ℕ) := Bool × EuclideanSpace ℝ (Fin n) × unitInterval

/-- The law of the noise of one iteration: fair coin ⊗ `N(0, I_n)` ⊗ `Unif[0, 1]`. -/
noncomputable def mrwNoiseLaw (n : ℕ) : Measure (MRWNoise n) :=
  (PMF.uniformOfFintype Bool).toMeasure.prod
    ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (volume : Measure unitInterval))

/-- The noise law of one iteration is a probability measure (structural instance). -/
instance isProbabilityMeasure_mrwNoiseLaw (n : ℕ) : IsProbabilityMeasure (mrwNoiseLaw n) := by
  unfold mrwNoiseLaw; infer_instance

/-- The step size `τ/(8√(n(τ + t)))` of line 6. -/
noncomputable def mrwStepSize (n τ : ℕ) (t : ℝ) : ℝ :=
  (τ : ℝ) / (8 * Real.sqrt ((n : ℝ) * ((τ : ℝ) + t)))

/-- The proposal `x′ = x + τ/(8√(n(τ+t))) H_γ^{−1/2} ξ` of line 6. -/
noncomputable def mrwProposal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (γ : Fin m → ℝ)
    (τ : ℕ) (t : ℝ) (x ξ : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x + mrwStepSize n τ t • Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (hGamma A γ)⁻¹) ξ

/-- The acceptance probability of line 7:
`min{1, exp(⟨A⊤γ, x′ − x⟩ − (τ + t)(ψ(x′) − ψ(x)))} · 𝕀_{x′ ∈ X}`. -/
noncomputable def mrwAccept {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (γ : Fin m → ℝ) (τ : ℕ) (t : ℝ) (x x' : EuclideanSpace ℝ (Fin n)) : ℝ :=
  open Classical in
  min 1 (Real.exp (∑ i, γ i * ∑ j, A i j * (x' j - x j) -
      ((τ : ℝ) + t) * (logBarrier A b x' - logBarrier A b x))) *
    (if x' ∈ polytope A b then 1 else 0)

/-- One iteration (lines 3–8) of Algorithm 6 from `x` with noise `(w, ξ, u)`. -/
noncomputable def mrwStep {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (γ : Fin m → ℝ) (τ : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (ω : MRWNoise n) :
    EuclideanSpace ℝ (Fin n) :=
  open Classical in
  if ω.1 = true then
    (if ((ω.2.2 : unitInterval) : ℝ) < mrwAccept A b γ τ t x (mrwProposal A γ τ t x ω.2.1)
      then mrwProposal A γ τ t x ω.2.1 else x)
  else x

/-- The output `x_N` of Algorithm 6 from `x₀` on the noise `ω` of its `N` iterations. -/
noncomputable def mrwRun {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (γ : Fin m → ℝ) (τ : ℕ) (t : ℝ) (N : ℕ) (x₀ : EuclideanSpace ℝ (Fin n))
    (ω : Fin N → MRWNoise n) : EuclideanSpace ℝ (Fin n) :=
  (List.finRange N).foldl (fun x i => mrwStep A b γ τ t x (ω i)) x₀

/-- The Markov kernel `K(x, ·) = Law(BackwardsMRW(x, γ, τ, t, N))` of Algorithm 6. -/
noncomputable def backwardsMRW {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (γ : Fin m → ℝ) (τ : ℕ) (t : ℝ) (N : ℕ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  randKernel (mrwRun A b γ τ t N) (Measure.pi fun _ : Fin N => mrwNoiseLaw n)

end PolySampIso


