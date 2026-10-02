-- Prove2me | Definitions.Def_TeschlQM_Algebraic_IsHarmonicOscillator
-- name    : TeschlQM_Algebraic_IsHarmonicOscillator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T01:39:02.678637+00:00
-- url     : https://prove2.me/theorems/45d13755-584d-400b-8431-19719cb33147
-- title:
--   The three-dimensional harmonic oscillator H = H₀ + ω²x² on 𝔇_ω (8.33)–(8.34)
-- statement:
--   Let $\omega > 0$. For a twice differentiable $f : \mathbb R^3 \to \mathbb C$ let $\Delta f = \sum_{j=1}^3 \partial^2 f/\partial x_j^2$. In Teschl's units ($\hbar = 1$, mass $1/2$) the free Hamiltonian is $H_0 = -\Delta$, and the **harmonic oscillator** is the operator
--   $$H = H_0 + \omega^2 x^2, \qquad (Hf)(x) = -\Delta f(x) + \omega^2 |x|^2 f(x),$$
--   in $L^2(\mathbb R^3)$ with domain
--   $$\mathfrak D(H) = \mathfrak D_\omega = \operatorname{span}\{x^\alpha e^{-\omega|x|^2/2} \mid \alpha \in \mathbb N_0^3\}.$$
--   An operator $H$ in $L^2(\mathbb R^3)$ *is the harmonic oscillator* if its domain is $\mathfrak D_\omega$ and, for every $\psi \in \mathfrak D(H)$, there is $f$ in the span of the functions $x^\alpha e^{-\omega|x|^2/2}$ with $\psi = f$ almost everywhere and $H\psi = -\Delta f + \omega^2|x|^2 f$ almost everywhere. Since a continuous function is determined by its class, this fixes $H$ uniquely.
--
--   This is the operator of Theorem 8.5.
--
--   **Formalization Note.** $L^2(\mathbb R^3)$ is `Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))`, and $H$ is a `LinearPMap` on it. The Laplacian is the sum of the second Fréchet derivatives along the standard unit vectors (`iteratedFDeriv ℝ 2 f x (fun _ => eⱼ)`). `IsHarmonicOscillator ω H` characterizes $H$ by its domain and its action as the differential expression $-\Delta + \omega^2|x|^2$; $H$ is not defined through its eigenfunctions. **Deviation:** the book's (8.34) takes the Gaussian $e^{-x^2/2}$ without $\omega$, but its (8.39)–(8.41) and the conclusion $\operatorname{span}\{\psi_n\} = \mathfrak D$ use $e^{-\omega x^2/2}$; these agree only for $\omega = 1$. The domain here is $\mathfrak D_\omega$, which matches (8.39)–(8.41) and the book's argument; for $\omega = 1$ it is (8.34) exactly.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 178, Eqs. (8.33)–(8.34)

import Mathlib
import Definitions.Def_TeschlQM_Algebraic_gaussCore

namespace TeschlQM.Algebraic

open MeasureTheory

/-- The Laplacian `Δf(x) = Σⱼ ∂²f/∂xⱼ²(x)` of `f : ℝⁿ → ℂ`, the sum of the second (real) partial
derivatives along the standard unit vectors `eⱼ`. -/
noncomputable def laplacian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ j : Fin n, iteratedFDeriv ℝ 2 f x (fun _ => EuclideanSpace.single j (1 : ℝ))

/-- Teschl (8.33), p. 178, with `H₀ = −Δ` (units `ℏ = 1`, `m = 1/2`, p. 167): the differential
expression of the harmonic oscillator, `(H f)(x) = −Δf(x) + ω²|x|² f(x)`. -/
noncomputable def oscillatorAction {n : ℕ} (ω : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ) :
    EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => -laplacian f x + ((ω ^ 2 * ‖x‖ ^ 2 : ℝ) : ℂ) * f x

/-- Teschl (8.33)–(8.34), p. 178: `H` is the three-dimensional **harmonic oscillator**
`H = H₀ + ω²x²` on the domain `𝔇_ω = span{x^α e^{−ω|x|²/2} | α ∈ ℕ₀³} ⊆ L²(ℝ³)`: its domain is
`𝔇_ω`, and every `ψ ∈ 𝔇(H)` is (the class of) a function `f` in the span of the
`x^α e^{−ω|x|²/2}` with `Hψ` the class of `−Δf + ω²|x|²f`. This determines `H` uniquely. -/
def IsHarmonicOscillator (ω : ℝ)
    (H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) →ₗ.[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin 3)))) : Prop :=
  H.domain = core 3 ω ∧
    ∀ ψ : H.domain, ∃ f ∈ coreFun 3 ω,
      ((ψ : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] f ∧
        ((H ψ : Lp ℂ 2 volume) : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[volume] oscillatorAction ω f

end TeschlQM.Algebraic


