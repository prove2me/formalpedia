-- Prove2me | Definitions.Def_PolySampIso_LLTProxMRW
-- name    : PolySampIso_LLTProxMRW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:21.027337+00:00
-- url     : https://prove2.me/theorems/e590a22a-2af4-4236-8ec3-34d7e4e4b4d9
-- title:
--   Algorithm 7 (LLTProxMRW): the χ²-to-TV oracle of Part II
-- statement:
--   **Algorithm 7** (LLTProxMRW$(x_0,\tau,t,\delta)$) sets $N=\lceil C_1n\tau\rceil$, with $C_1$ the constant of Lemma 34, and
--
--   $$K=\Big\lceil 32\min\Big\{m\tau,\,1+\frac\tau t\Big\}\log\frac1\delta\Big\rceil,$$
--
--   where $\tau/t=+\infty$ at $t=0$. For $i<K$ it draws $\gamma_i\sim\pi^{\Gamma|X=x_i}_{t,\tau}$ (Algorithm 2, keeping only $\gamma$) and sets $x_{i+1}=\mathrm{BackwardsMRW}(x_i,\gamma_i,\tau,t,N)$; it returns $x_K$. It is Algorithm 1 for the target $\pi_t$ with the exact backwards step replaced by Algorithm 6.
--
--   **Formalization Note** $\gamma_i$ is drawn as $\sum_{l<\tau}e_l/s(x_i)$ with $e_{l}$ i.i.d. $\mathrm{Exp}(1)$ vectors, which has law $\mathrm{Exp}(s(x_i))^{*\tau}$. The $t=0$ case of $K$ is written out, since Lean's $\tau/0=0$ would give $\min\{m\tau,1\}$. The constant $C_1$ is a parameter.
-- source:
--   Gu, Shi, Tian, Yang, Polytope Sampling at the Speed of Isoperimetry, arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 7, p.48 (PDF p.50)

import Mathlib
import Definitions.Def_PolySampIso_LogBarrier
import Definitions.Def_PolySampIso_MarkovKernel
import Definitions.Def_PolySampIso_BackwardsMRW

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PolySampIso

/-!
# Algorithm 7: LLTProxMRW(x₀, τ, t, δ)

A. Gu, B. Shi, K. Tian, H. Yang, *Polytope Sampling at the Speed of Isoperimetry*,
arXiv:2610.23775 (preprint, sha256 b6a79179…), Algorithm 7, p.48 (PDF p.50):
"1 Input: initial x0 ∈ X, regularization parameter τ ∈ N, cooling parameter t ≥ 0, target error
δ ∈ (0, 1/2)
2 N ← ⌈Cnτ⌉ ▷ C is the constant from Lemma 34.
3 K ← ⌈32 min{mτ, 1 + τ/t} log 1/δ⌉
4 for i = 0, . . . , K − 1 do
5   γi ∼ πΓ|X=xi t,τ ▷ See Algorithm 2, retain only γ.
6   xi+1 ← BackwardsMRW(xi, γi, τ, t, N) ▷ See Algorithm 6.
7 end
8 Return: xK"

**Formalization Note.**
* The constant `C` of line 2 (Lemma 34's) is the parameter `C₁`; `N = ⌈C₁nτ⌉`.
* `alg7Iters m τ t δ = K = ⌈32 min{mτ, 1 + τ/t} log(1/δ)⌉`; at `t = 0` the paper's `τ/t` is `+∞`,
  so `K = ⌈32mτ log(1/δ)⌉` (written as an explicit case: Lean's `τ/0 = 0` would give `min{mτ, 1}`).
* Line 5 draws `γᵢ` as `Σ_{l<τ} z^{(l)}` with `z^{(l)}_j = e_{l,j}/s_j(xᵢ)`, `e_{l,j}` i.i.d.
  `Exp(1)`; `e/s` with `e ∼ Exp(1)` has law `Exp(s)`, so `γᵢ ∼ π^{Γ|X=xᵢ}_{t,τ}` (Algorithm 2).
* Each outer iteration reads fresh independent noise: `τ·m` exponential draws and the noise of
  `N` iterations of Algorithm 6. `lltProxMRW A b C₁ τ t δ` is the Markov kernel
  `x₀ ↦ Law(LLTProxMRW(x₀, τ, t, δ))`.
-/

/-- `K = ⌈32 min{mτ, 1 + τ/t} log(1/δ)⌉`, with `τ/0 = +∞`. -/
noncomputable def alg7Iters (m τ : ℕ) (t δ : ℝ) : ℕ :=
  open Classical in
  ⌈32 * (if t = 0 then (m : ℝ) * τ else min ((m : ℝ) * τ) (1 + τ / t)) * Real.log (1 / δ)⌉₊

/-- `N = ⌈C₁ n τ⌉`. -/
noncomputable def alg7Inner (C₁ : ℝ) (n τ : ℕ) : ℕ :=
  ⌈C₁ * n * τ⌉₊

/-- The noise of one outer iteration: `τ × m` exponential draws and the noise of `N` iterations
of Algorithm 6. -/
abbrev Alg7Noise (m n τ N : ℕ) := (Fin τ → Fin m → ℝ) × (Fin N → MRWNoise n)

/-- The law of the noise of one outer iteration: i.i.d. `Exp(1)` ⊗ i.i.d. Algorithm 6 noise. -/
noncomputable def alg7NoiseLaw (m n τ N : ℕ) : Measure (Alg7Noise m n τ N) :=
  haveI := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  (Measure.pi fun _ : Fin τ => Measure.pi fun _ : Fin m => expMeasure 1).prod
    (Measure.pi fun _ : Fin N => mrwNoiseLaw n)

/-- The outer noise law is a probability measure (structural instance). -/
instance isProbabilityMeasure_alg7NoiseLaw (m n τ N : ℕ) :
    IsProbabilityMeasure (alg7NoiseLaw m n τ N) := by
  have := isProbabilityMeasure_expMeasure (one_pos (α := ℝ))
  unfold alg7NoiseLaw; infer_instance

/-- The forwards draw `γ = Σ_{l<τ} e_l / s(x)` of line 5. -/
noncomputable def alg7Gamma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {τ : ℕ} (x : EuclideanSpace ℝ (Fin n)) (e : Fin τ → Fin m → ℝ) : Fin m → ℝ :=
  fun j => ∑ l, e l j / slack A b x j

/-- One outer iteration (lines 5–6) of Algorithm 7 from `x`. -/
noncomputable def alg7Step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (τ : ℕ) (t : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (Fin n)) (ω : Alg7Noise m n τ N) :
    EuclideanSpace ℝ (Fin n) :=
  mrwRun A b (alg7Gamma A b x ω.1) τ t N x ω.2

/-- The output `x_K` of Algorithm 7 from `x₀` on the noise of its `K` outer iterations. -/
noncomputable def alg7Run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (τ : ℕ) (t : ℝ) (N K : ℕ) (x₀ : EuclideanSpace ℝ (Fin n))
    (ω : Fin K → Alg7Noise m n τ N) : EuclideanSpace ℝ (Fin n) :=
  (List.finRange K).foldl (fun x i => alg7Step A b τ t N x (ω i)) x₀

/-- The Markov kernel `x₀ ↦ Law(LLTProxMRW(x₀, τ, t, δ))` of Algorithm 7, with `N = ⌈C₁nτ⌉`. -/
noncomputable def lltProxMRW {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (C₁ : ℝ) (τ : ℕ) (t δ : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  randKernel (alg7Run A b τ t (alg7Inner C₁ n τ) (alg7Iters m τ t δ))
    (Measure.pi fun _ : Fin (alg7Iters m τ t δ) => alg7NoiseLaw m n τ (alg7Inner C₁ n τ))

end PolySampIso


