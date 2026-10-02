-- Prove2me | Definitions.Def_TeschlQM_Spectral_spectralMeasure
-- name    : TeschlQM_Spectral_spectralMeasure
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:25:40.173812+00:00
-- url     : https://prove2.me/theorems/1735349f-cc10-461d-a531-582a53aba822
-- title:
--   Spectral measure $\mu_\psi$ and the complex measures $\mu_{\varphi,\psi}$ of a projection-valued measure
-- statement:
--   Let $P$ be a projection-valued measure on a complex Hilbert space $\mathfrak H$ and $\psi \in \mathfrak H$. The **spectral measure** of $\psi$ is the finite Borel measure on $\mathbb{R}$
--   $$\mu_\psi(\Omega) = \langle \psi, P(\Omega)\psi\rangle = \|P(\Omega)\psi\|^2 ,$$
--   with total mass $\mu_\psi(\mathbb{R}) = \|\psi\|^2$. For $\varphi, \psi \in \mathfrak H$ the complex Borel measure $\mu_{\varphi,\psi}(\Omega) = \langle \varphi, P(\Omega)\psi\rangle$ is given by the polarization identity (3.15),
--   $$\mu_{\varphi,\psi} = \tfrac14\big(\mu_{\varphi+\psi} - \mu_{\varphi-\psi} + i\,\mu_{\varphi-i\psi} - i\,\mu_{\varphi+i\psi}\big),$$
--   and the file defines the corresponding integral $\int_{\mathbb{R}} f\,d\mu_{\varphi,\psi}$ of a function $f:\mathbb{R}\to\mathbb{C}$ as the same combination of the four integrals $\int f\,d\mu_{\varphi\pm\psi}$, $\int f\,d\mu_{\varphi\pm i\psi}$ (`spectralForm P φ ψ f`).
--
--   **Formalization Note.** `spectralMeasure P ψ` is `Measure.ofMeasurable` applied to $\Omega \mapsto \|P(\Omega)\psi\|^2 \in [0,\infty]$, used whenever this set function vanishes on $\emptyset$ and is countably additive on Borel sets. That is the case for every projection-valued measure (the theorem `spectralMeasure_apply` states the resulting values); for any other $P$ the definition returns the zero measure, a value that never enters a statement of this mission, since every statement assumes $P$ is a projection-valued measure. The inner product is conjugate linear in the first argument, as in the book. Integrals are Bochner integrals; they are used only for bounded functions or for functions in $L^2(\mathbb{R}, d\mu_\psi)$ of a finite measure, where they are genuine integrals.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 89, Section 3.1, Eq. (3.15)

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace TeschlQM.Spectral

open Classical in
/-- Teschl, p. 89: the **spectral measure** `μ_ψ` of the vector `ψ` with respect to the
projection-valued measure `P`, the finite Borel measure with `μ_ψ(Ω) = ⟨ψ, P(Ω)ψ⟩ = ‖P(Ω)ψ‖²`.
It is built with `Measure.ofMeasurable` from `Ω ↦ ‖P(Ω)ψ‖²` whenever that set function vanishes
on `∅` and is countably additive on Borel sets (which holds for every projection-valued
measure); for any other `P` the value is the zero measure, a junk value that never occurs in
the statements of this development, all of which assume `P` is a projection-valued measure. -/
noncomputable def spectralMeasure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (ψ : H) : Measure ℝ :=
  if h : ((‖P ∅ ψ‖₊ : ℝ≥0∞) ^ 2 = 0 ∧
      ∀ ⦃Ω : ℕ → Set ℝ⦄, (∀ n, MeasurableSet (Ω n)) → Pairwise (Function.onFun Disjoint Ω) →
        (‖P (⋃ n, Ω n) ψ‖₊ : ℝ≥0∞) ^ 2 = ∑' n, (‖P (Ω n) ψ‖₊ : ℝ≥0∞) ^ 2) then
    Measure.ofMeasurable (fun Ω _ => (‖P Ω ψ‖₊ : ℝ≥0∞) ^ 2) h.1 (fun _ hΩ hd => h.2 hΩ hd)
  else 0

/-- Teschl, p. 89, (3.15) and (3.17): the integral `∫ f dμ_{φ,ψ}` of `f` against the complex
measure `μ_{φ,ψ}(Ω) = ⟨φ, P(Ω)ψ⟩`, which (3.15) writes by polarization as
`μ_{φ,ψ} = ¼ (μ_{φ+ψ} − μ_{φ−ψ} + i μ_{φ−iψ} − i μ_{φ+iψ})`. The inner product is conjugate
linear in its first argument, as in the book. -/
noncomputable def spectralForm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : Set ℝ → (H →L[ℂ] H)) (φ ψ : H) (f : ℝ → ℂ) : ℂ :=
  (1 / 4 : ℂ) * ((∫ x, f x ∂spectralMeasure P (φ + ψ)) - (∫ x, f x ∂spectralMeasure P (φ - ψ))
    + Complex.I * (∫ x, f x ∂spectralMeasure P (φ - Complex.I • ψ))
    - Complex.I * (∫ x, f x ∂spectralMeasure P (φ + Complex.I • ψ)))

end TeschlQM.Spectral


