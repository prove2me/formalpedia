-- Prove2me | Definitions.Def_ReflectionlessPotentialDefs
-- name    : ReflectionlessPotentialDefs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T19:44:33.769987+00:00
-- url     : https://prove2.me/theorems/49737460-2293-4a8d-a69d-95f2e1feb897
-- title:
--   The reflectionless potential: Hamiltonian, eigenfunctions, coefficients
-- statement:
--   The formal setting for the mission, following F. Erman and O. T. Turgut, *Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics* (arXiv:2411.14941).
--
--   Units are fixed to $\hbar = m = 1$, so the Hamiltonian of equation (2.1) reads
--   $$H \;=\; -\tfrac12\frac{d^{2}}{dx^{2}} \;-\; \kappa^{2}\operatorname{sech}^{2}(\kappa x),\qquad \kappa>0,$$
--   with bound state energy $-\kappa^{2}/2$ and continuum energies $k^{2}/2$.
--
--   The file provides:
--
--   * the potential $V(x) = -\kappa^{2}\operatorname{sech}^{2}(\kappa x)$;
--   * the predicates "$f$ solves $-\tfrac12 f'' + Vf = Ef$" and "$f$ solves $-\tfrac12 f'' = Ef$", each phrased as the existence of a first and a second derivative function satisfying the equation at every point, so that no notion of weak solution or of operator domain is needed;
--   * the normalized bound state $\psi_{0}(x) = \sqrt{\kappa/2}\,\operatorname{sech}(\kappa x)$ (equation (2.7));
--   * the normalized continuum states $\psi_{k}(x) = e^{ikx}(k+i\kappa\tanh\kappa x)/\bigl(\sqrt{2\pi}(\kappa+ik)\bigr)$ (equation (4.2)) and their parity combinations $\psi^{e/o}_{k} = (\psi_{k}(x)\pm\psi_{k}(-x))/\sqrt2$ (equations (5.1)–(5.2));
--   * the creation operator $a^{\dagger} = \tfrac{1}{\sqrt2}(P + i\kappa\tanh\kappa X)$ of the factorization method (equation (2.2)), applied to a function together with its derivative;
--   * the expansion coefficients $\langle \psi_{k}, f\rangle$, $\langle\psi_{0},f\rangle$, $\langle\psi^{e}_{k},f\rangle$, $\langle\psi^{o}_{k},f\rangle$ used to state the completeness relation in Parseval form.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1, equations (1.1), (2.1)-(2.3), (2.7), (4.2), (5.1)-(5.2)

import Mathlib

/-!
# The reflectionless (Pöschl–Teller, `N = 1`) potential

Definitions for the mission *Completeness of Energy Eigenfunctions for the
Reflectionless Potential*, following F. Erman and O. T. Turgut, arXiv:2411.14941v1.

Units are fixed to `ℏ = m = 1`, so the Hamiltonian of equation (2.1) of the paper reads
`H = -(1/2) d²/dx² - κ² sech²(κ x)`, the bound state energy is `-κ²/2` and the
continuum energies are `k²/2`.
-/

namespace ReflectionlessPotential

open Complex MeasureTheory

/-- The reflectionless potential `V(x) = -κ² sech²(κx)` (equation (1.1) with `N = 1`,
in units `ℏ = m = 1`). -/
noncomputable def V (κ x : ℝ) : ℝ := -κ ^ 2 / Real.cosh (κ * x) ^ 2

/-- `IsEigenstate κ E f` states that the twice differentiable function `f : ℝ → ℂ` solves
the time-independent Schrödinger equation `-(1/2) f''(x) + V κ x * f x = E * f x`. -/
def IsEigenstate (κ E : ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ f' f'' : ℝ → ℂ, (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (f'' x) x) ∧
    ∀ x, -(1 / 2 : ℂ) * f'' x + (V κ x : ℂ) * f x = (E : ℂ) * f x

/-- `IsFreeEigenstate E f` states that the twice differentiable function `f : ℝ → ℂ` solves
the free Schrödinger equation `-(1/2) f''(x) = E * f x`. -/
def IsFreeEigenstate (E : ℝ) (f : ℝ → ℂ) : Prop :=
  ∃ f' f'' : ℝ → ℂ, (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (f'' x) x) ∧
    ∀ x, -(1 / 2 : ℂ) * f'' x = (E : ℂ) * f x

/-- The normalized bound state `ψ₀(x) = √(κ/2) · sech(κx)` (equation (2.7)). -/
noncomputable def psi0 (κ x : ℝ) : ℝ := Real.sqrt (κ / 2) / Real.cosh (κ * x)

/-- The normalized continuum eigenfunction (equation (4.2))
`ψ_k(x) = e^{i k x} (k + i κ tanh κx) / (√(2π) (κ + i k))`. -/
noncomputable def psiC (κ k x : ℝ) : ℂ :=
  Complex.exp (Complex.I * k * x) * ((k : ℂ) + Complex.I * κ * Real.tanh (κ * x)) /
    ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k))

/-- The even-parity continuum state `ψ_k^e(x) = (ψ_k(x) + ψ_k(-x)) / √2` (equation (5.1)). -/
noncomputable def psiEven (κ k x : ℝ) : ℂ :=
  (psiC κ k x + psiC κ k (-x)) / (Real.sqrt 2 : ℂ)

/-- The odd-parity continuum state `ψ_k^o(x) = (ψ_k(x) - ψ_k(-x)) / √2` (equation (5.2)). -/
noncomputable def psiOdd (κ k x : ℝ) : ℂ :=
  (psiC κ k x - psiC κ k (-x)) / (Real.sqrt 2 : ℂ)

/-- The creation operator `a† = (P + i κ tanh(κ X)) / √2` of the factorization method
(equation (2.2), with `P = -i d/dx`), applied to a function `f` with derivative `f'`. -/
noncomputable def creation (κ : ℝ) (f f' : ℝ → ℂ) : ℝ → ℂ := fun x =>
  (-Complex.I * f' x + Complex.I * κ * Real.tanh (κ * x) * f x) / (Real.sqrt 2 : ℂ)

/-- The continuum expansion coefficient `⟨ψ_k, f⟩ = ∫ conj (ψ_k x) * f x dx`. -/
noncomputable def coeffC (κ k : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (starRingEnd ℂ) (psiC κ k x) * f x

/-- The bound state expansion coefficient `⟨ψ₀, f⟩ = ∫ ψ₀ x * f x dx`. -/
noncomputable def coeff0 (κ : ℝ) (f : ℝ → ℂ) : ℂ := ∫ x : ℝ, (psi0 κ x : ℂ) * f x

/-- The even-parity expansion coefficient `⟨ψ_k^e, f⟩ = ∫ conj (ψ_k^e x) * f x dx`. -/
noncomputable def coeffEven (κ k : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (starRingEnd ℂ) (psiEven κ k x) * f x

/-- The odd-parity expansion coefficient `⟨ψ_k^o, f⟩ = ∫ conj (ψ_k^o x) * f x dx`. -/
noncomputable def coeffOdd (κ k : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (starRingEnd ℂ) (psiOdd κ k x) * f x

end ReflectionlessPotential


