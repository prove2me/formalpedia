-- Prove2me | Definitions.Def_HighMagSampling_SK_MarkovChain
-- name    : HighMagSampling_SK_MarkovChain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:26:48.770341+00:00
-- url     : https://prove2.me/theorems/86566342-137f-4209-a555-7139323404a3
-- title:
--   Markov chains on a general state space: laziness, $t$-step laws, reversibility, Dirichlet form, $\lambda$-Poincaré inequality
-- statement:
--   Let $\Omega$ be a measurable space. A **Markov chain** $\mathcal T=\{\mathcal T_\omega\}_{\omega\in\Omega}$ on $\Omega$ is a Markov kernel: each $\mathcal T_\omega$ is a probability measure on $\Omega$, measurable in $\omega$. For a probability measure $\mu$ on $\Omega$, $\mathcal T\mu$ is the law of $\omega'$ when $\omega\sim\mu$ and $\omega'\sim\mathcal T_\omega$.
--
--   1. **Laziness.** $\mathrm{lazy}(\mathcal T)$ moves according to $\mathcal T$ with probability $\tfrac12$ and otherwise stays put:
--   $$\mathrm{lazy}(\mathcal T)_\omega=\tfrac12\,\delta_\omega+\tfrac12\,\mathcal T_\omega .$$
--   2. **$t$-step law.** $\mathcal T^0\mu=\mu$ and $\mathcal T^{t+1}\mu=\mathcal T(\mathcal T^t\mu)$ for $t\in\mathbb N$.
--   3. **Reversibility.** $\mathcal T$ is *reversible with stationary measure $\pi$* if $\mathcal T\pi=\pi$ and detailed balance $\pi(d\omega)\,\mathcal T_\omega(d\omega')=\pi(d\omega')\,\mathcal T_{\omega'}(d\omega)$ holds, i.e. $\int_A\mathcal T_\omega(B)\,\pi(d\omega)=\int_B\mathcal T_\omega(A)\,\pi(d\omega)$ for all measurable $A,B$.
--   4. **Dirichlet form.** For $f,g:\Omega\to\mathbb R$,
--   $$\mathcal E_{\mathcal T}(f,g)=\int f g\,d\pi-\iint f(\omega)\,g(\omega')\,\mathcal T_\omega(d\omega')\,\pi(d\omega).$$
--   5. **Poincaré inequality.** For $\lambda\in(0,2]$, $\mathcal T$ satisfies a **$\lambda$-Poincaré inequality** (with respect to $\pi$) if
--   $$\mathrm{Var}_\pi[f]\le\frac1\lambda\,\mathcal E_{\mathcal T}(f,f)\qquad\text{for every }f\in L^2(\pi).$$
--
--   These are the objects through which the paper turns a spectral bound on the down-up walk into a mixing-time bound (Lemma 1).
--
--   **Formalization Note.** The kernel is Mathlib's `ProbabilityTheory.Kernel`; $\mathcal T\mu$ is `μ.bind κ`; stationarity is `Kernel.Invariant` and detailed balance is `Kernel.IsReversible`. The range $\lambda\in(0,2]$ is part of `SatisfiesPoincare`, as on the page. Footnote 4 of the paper restricts the test functions to those for which the integrals make sense; the Lean takes all $f\in L^2(\pi)$ (`MemLp f 2 π`), which on a finite state space is every function. The variance is Mathlib's `ProbabilityTheory.variance`.
-- source:
--   Kumar, Sarkar, Tian, Zhu, High-Magnetization Sampling at Low Temperatures, arXiv:2609.08873v1, p. 10, §2.2 (Markov chains, reversibility, Dirichlet form, λ-Poincaré inequality) and p. 11, Lemma 1 (lazy(T))

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HighMagSampling.SK

/-!
# Markov chains on a general state space: laziness, iterates, reversibility, Poincaré inequalities

Kumar, Sarkar, Tian, Zhu, *High-Magnetization Sampling at Low Temperatures*, arXiv:2609.08873v1,
§2.2, pp. 10–11 (PDF pp. 12–13).

A Markov chain `T = {T_ω}_{ω ∈ Ω}` on a state space `Ω` is a Markov kernel `κ : Kernel Ω Ω` on a
measurable space; `T μ`, the law of `ω'` when `ω ∼ μ` and `ω' ∼ T_ω`, is `μ.bind κ`.

**Formalization Note.**
* `lazy κ` moves according to `κ` with probability `1/2` and otherwise stays put:
  `lazy κ ω = ½ δ_ω + ½ κ ω`.
* `lawAfter κ μ t` is the law after `t` steps from the initial law `μ` (`t = 0` gives `μ`).
* `IsReversibleWith κ π` is the page's definition: `π` is stationary (`T π = π`) and detailed
  balance `π(dω) T_ω(dω') = π(dω') T_{ω'}(dω)` holds, written for measurable sets as in Mathlib's
  `Kernel.IsReversible`.
* `dirichletForm κ π f g = ∫ f g dπ − ∫∫ f(ω) g(ω') T_ω(dω') π(dω)`.
* `SatisfiesPoincare κ π λ` is the page's `λ`-Poincaré inequality: `λ ∈ (0, 2]` and
  `Var_π[f] ≤ (1/λ) E_T(f, f)` for every `f ∈ L²(π)` (footnote 4: the functions considered are
  those for which the integrals make sense; on a finite state space with the discrete σ-algebra
  this is every function).
-/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `lazy(T)`: with probability `1/2` take a step of `κ`, otherwise stay (Lemma 1, p. 11). -/
noncomputable def lazy (κ : Kernel Ω Ω) : Kernel Ω Ω where
  toFun ω := (2 : ℝ≥0∞)⁻¹ • Measure.dirac ω + (2 : ℝ≥0∞)⁻¹ • κ ω
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact (((Measure.measurable_coe hs).comp Measure.measurable_dirac).const_mul _).add
      ((Kernel.measurable_coe κ hs).const_mul _)

/-- The law after `t` steps of the chain `κ` started from `μ`: `T^t μ` (p. 10). -/
noncomputable def lawAfter (κ : Kernel Ω Ω) (μ : Measure Ω) : ℕ → Measure Ω
  | 0 => μ
  | t + 1 => (lawAfter κ μ t).bind κ

/-- `T` is reversible with stationary measure `π` (p. 10): `T π = π` and detailed balance. -/
def IsReversibleWith (κ : Kernel Ω Ω) (π : Measure Ω) : Prop :=
  Kernel.Invariant κ π ∧ Kernel.IsReversible κ π

/-- The Dirichlet form `E_T(f, g) = ∫ f g dπ − ∫∫ f(ω) g(ω') T_ω(dω') π(dω)` (p. 10). -/
noncomputable def dirichletForm (κ : Kernel Ω Ω) (π : Measure Ω) (f g : Ω → ℝ) : ℝ :=
  (∫ ω, f ω * g ω ∂π) - ∫ ω, f ω * (∫ ω', g ω' ∂(κ ω)) ∂π

/-- `T` satisfies a `λ`-Poincaré inequality w.r.t. `π` (p. 10): `λ ∈ (0, 2]` and
`Var_π[f] ≤ (1/λ) E_T(f, f)` for every `f ∈ L²(π)`. -/
def SatisfiesPoincare (κ : Kernel Ω Ω) (π : Measure Ω) (lam : ℝ) : Prop :=
  0 < lam ∧ lam ≤ 2 ∧
    ∀ f : Ω → ℝ, MemLp f 2 π → variance f π ≤ (1 / lam) * dirichletForm κ π f f

end HighMagSampling.SK


