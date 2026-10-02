-- Prove2me | Definitions.Def_TeschlQM_Free_timeEvolution
-- name    : TeschlQM_Free_timeEvolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T00:12:13.105864+00:00
-- url     : https://prove2.me/theorems/d048cc63-fc76-4838-a6bd-4f37359d660c
-- title:
--   The free time evolution e^{−itH₀} = F⁻¹ e^{−itp²} F (7.27)
-- statement:
--   For $t \in \mathbb R$ and $\psi \in L^2(\mathbb R^n)$ the **free time evolution** is
--   $$e^{-itH_0}\psi = \mathcal F^{-1}\big(e^{-itp^2} \hat\psi(p)\big),$$
--   the Fourier conjugate of multiplication by the unimodular function $e^{-itp^2}$.
--
--   It solves the free Schrödinger equation $i\dot\psi = H_0\psi$ and is the subject of Lemma 7.10 (long-time asymptotics).
--
--   **Formalization Note.** `timeEvolution n t ψ` is $\mathcal F_{\mathrm M}^{-1}\big(e^{-it\cdot 4\pi^2|\xi|^2}\, \mathcal F_{\mathrm M}\psi\big)$ with Mathlib's unitary $L^2$ Fourier transform $\mathcal F_{\mathrm M}$, under which $p^2$ becomes $4\pi^2|\xi|^2$; it is the same operator as Teschl's $\mathcal F^{-1} e^{-itp^2}\mathcal F$. It is not defined through the integral kernel (7.30).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 169, Section 7.3, Eq. (7.27)

import Mathlib

namespace TeschlQM.Free

open MeasureTheory FourierTransform

/-- Teschl (7.27), p. 169: the **free time evolution** `e^{-itH₀} ψ = F⁻¹ e^{-itp²} ψ̂(p)`
on `L²(ℝⁿ)`, the Fourier conjugate of multiplication by the unimodular symbol `e^{-itp²}`.

Here `𝓕` is Mathlib's unitary Fourier transform on `L²(ℝⁿ)` (normalization `e^{-2πi⟪x, ξ⟫}`),
under which `H₀ = -Δ` is multiplication by `4π²‖ξ‖²`, so the symbol reads
`e^{-it·4π²‖ξ‖²}`; this is the same operator as Teschl's `F⁻¹ e^{-itp²} F` with his
normalization (7.3). It is not defined through the integral kernel (7.30). -/
noncomputable def timeEvolution (n : ℕ) (t : ℝ)
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ).symm
    (MemLp.toLp
      (fun ξ => Complex.exp (((-(t * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) * Complex.I) *
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ ψ) ξ)
      ((Lp.memLp (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin n)) ℂ ψ)).of_le
        ((by fun_prop : Continuous fun ξ : EuclideanSpace ℝ (Fin n) =>
            Complex.exp (((-(t * (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable _))
        (Filter.Eventually.of_forall fun ξ => by
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul])))

end TeschlQM.Free


