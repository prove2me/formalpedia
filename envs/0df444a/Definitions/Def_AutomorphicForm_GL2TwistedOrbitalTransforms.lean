-- Prove2me | Definitions.Def_AutomorphicForm_GL2TwistedOrbitalTransforms
-- name    : AutomorphicForm_GL2TwistedOrbitalTransforms
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/942e6015-c11b-5d6d-8ba7-6b0811da54ea
-- title:
--   Twisted orbital transforms on GL₂(ℂ)
-- statement:
--   Seven definitions in the namespace `AutomorphicForm.GL2Twisted` set up twisted orbital integrals for complex-valued functions on `GL (Fin 2) ℂ`, the twist being entrywise complex conjugation. `unitaryElt ψ η ξ₁ ξ₂` is the invertible matrix $e^{i\psi}\begin{pmatrix}\cos\eta\, e^{i\xi_1} & \sin\eta\, e^{i\xi_2}\\ -\sin\eta\, e^{-i\xi_2} & \cos\eta\, e^{-i\xi_1}\end{pmatrix}$, invertibility being witnessed by the computation that its determinant equals $e^{2i\psi}$. `unitaryAverage F` is $(4\pi^3)^{-1}$ times the iterated interval integral of $\sin\eta\cos\eta\cdot F(\mathrm{unitaryElt}\,\psi\,\eta\,\xi_1\,\xi_2)$ over $\psi\in[0,2\pi]$, $\eta\in[0,\pi/2]$, $\xi_1,\xi_2\in[0,2\pi]$ — the average of $F$ against the stated density on this chart of the unitary group; that this agrees with the Haar average is not part of the definition. `conjEntries g` applies the complex conjugation ring homomorphism to the entries of $g$, via `Matrix.GeneralLinearGroup.map`.
--
--   For the split data, given $0<a_1$ and $0<a_2$ (packaged as a single conjunction hypothesis) and $v\in\mathbb{C}$, `twistedSplitElt a₁ a₂ v h` is the upper-triangular matrix with diagonal $\sqrt{a_1},\sqrt{a_2}$ and upper entry $v$. Then `twistedSplitTransform φ a₁ a₂` is defined by cases on $0<a_1\wedge 0<a_2$: in that case the Lebesgue integral over $v\in\mathbb{C}$ of $\mathrm{unitaryAverage}$ of $k\mapsto \varphi(k^{-1}\cdot \mathrm{twistedSplitElt}\,a_1\,a_2\,v\cdot \overline{k})$, and $0$ otherwise. For the elliptic data, given $0<r$, $0<\rho$, angles $\theta$ and $u\in\mathbb{C}$, `twistedEllipticElt r θ ρ u hr hρ` is $\sqrt{r}$ times $\begin{pmatrix}-u\rho e^{-i\theta/2} & \rho^{-1}e^{i\theta/2}-|u|^2\rho e^{-i\theta/2}\\ \rho e^{-i\theta/2} & \bar u\rho e^{-i\theta/2}\end{pmatrix}$, with determinant $-r$. Finally `twistedEllipticTransform φ r θ` is, when $0<r$, the product of $4\sin^2\theta$ with the integral over $\rho\in(0,\infty)$ and $u\in\mathbb{C}$ of $\rho^{-1}$ times the sum of the two twisted unitary averages of $\varphi$ at `twistedEllipticElt r θ ρ u` and at `twistedEllipticElt r (-θ) ρ u`, the integrand being $0$ where $\rho\le 0$; it is $0$ when $r\le 0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of twisted orbital integral; these are the project's own definitions, built on Mathlib's `Matrix.GeneralLinearGroup` (including `mkOfDetNeZero` and `map`) and on interval and Lebesgue integration.
--
--   **Where it is used.** These transforms provide the analytic side of the twisted trace comparison for $\mathrm{GL}_2$ over $\mathbb{C}$, with the split and elliptic twisted conjugacy classes parametrised separately; the module is imported by the statements and proofs that establish their basic invariance and evaluation properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_GL2TwistedOrbitalTransforms.lean

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.LinearCombination

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

noncomputable section

namespace AutomorphicForm.GL2Twisted

def unitaryElt (ψ η ξ₁ ξ₂ : ℝ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)),
        Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I));
      Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I)))),
        Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))]
    (by
      rw [Matrix.det_fin_two_of]
      have h1 : Complex.exp (ξ₁ * Complex.I) * Complex.exp (-(ξ₁ * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have h2 : Complex.exp (ξ₂ * Complex.I) * Complex.exp (-(ξ₂ * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have h3 : (Real.cos η : ℂ) ^ 2 + (Real.sin η : ℂ) ^ 2 = 1 := by exact_mod_cast Real.cos_sq_add_sin_sq η
      have hE : Complex.exp (ψ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
      have key : Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (ξ₁ * Complex.I)) *
            (Complex.exp (ψ * Complex.I) * (Real.cos η * Complex.exp (-(ξ₁ * Complex.I)))) -
          Complex.exp (ψ * Complex.I) * (Real.sin η * Complex.exp (ξ₂ * Complex.I)) *
            (Complex.exp (ψ * Complex.I) * (-(Real.sin η * Complex.exp (-(ξ₂ * Complex.I))))) =
          Complex.exp (ψ * Complex.I) ^ 2 := by
        linear_combination
          Complex.exp (ψ * Complex.I) ^ 2 * (Real.cos η : ℂ) ^ 2 * h1 +
            Complex.exp (ψ * Complex.I) ^ 2 * (Real.sin η : ℂ) ^ 2 * h2 +
            Complex.exp (ψ * Complex.I) ^ 2 * h3
      rw [key]
      exact pow_ne_zero 2 hE)

def unitaryAverage (F : GL (Fin 2) ℂ → ℂ) : ℂ :=
  (1 / (4 * Real.pi ^ 3) : ℂ) *
    ∫ ψ in (0 : ℝ)..(2 * Real.pi), ∫ η in (0 : ℝ)..(Real.pi / 2),
      ∫ ξ₁ in (0 : ℝ)..(2 * Real.pi), ∫ ξ₂ in (0 : ℝ)..(2 * Real.pi),
        (Real.sin η * Real.cos η : ℂ) * F (unitaryElt ψ η ξ₁ ξ₂)

def conjEntries (g : GL (Fin 2) ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.map (starRingEnd ℂ) g

def twistedSplitElt (a₁ a₂ : ℝ) (v : ℂ) (h : 0 < a₁ ∧ 0 < a₂) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(Real.sqrt a₁ : ℂ), v; 0, (Real.sqrt a₂ : ℂ)]
    (by
      rw [Matrix.det_fin_two_of]
      have h1 : (Real.sqrt a₁ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr h.1).ne'
      have h2 : (Real.sqrt a₂ : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr h.2).ne'
      simpa using mul_ne_zero h1 h2)

def twistedSplitTransform (φ : GL (Fin 2) ℂ → ℂ) (a₁ a₂ : ℝ) : ℂ :=
  if h : 0 < a₁ ∧ 0 < a₂ then
    ∫ v : ℂ, unitaryAverage fun k => φ (k⁻¹ * twistedSplitElt a₁ a₂ v h * conjEntries k)
  else 0

def twistedEllipticElt (r θ ρ : ℝ) (u : ℂ) (hr : 0 < r) (hρ : 0 < ρ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))),
        (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
          (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I)));
      (Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I))),
        (Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))]
    (by
      rw [Matrix.det_fin_two_of]
      have hE : Complex.exp (θ / 2 * Complex.I) * Complex.exp (-(θ / 2 * Complex.I)) = 1 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
      have hρ' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
      have hρi : (ρ : ℂ)⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ'
      have hu : (starRingEnd ℂ) u * u = (Complex.normSq u : ℂ) := by
        rw [mul_comm]; exact Complex.mul_conj u
      have hs : (Real.sqrt r : ℂ) ^ 2 = (r : ℂ) := by exact_mod_cast Real.sq_sqrt hr.le
      have key : (Real.sqrt r : ℂ) * (-(u * ρ * Complex.exp (-(θ / 2 * Complex.I)))) *
            ((Real.sqrt r : ℂ) * ((starRingEnd ℂ) u * ρ * Complex.exp (-(θ / 2 * Complex.I)))) -
          (Real.sqrt r : ℂ) * ((ρ : ℂ)⁻¹ * Complex.exp (θ / 2 * Complex.I) -
            (Complex.normSq u : ℂ) * ρ * Complex.exp (-(θ / 2 * Complex.I))) *
            ((Real.sqrt r : ℂ) * (ρ * Complex.exp (-(θ / 2 * Complex.I)))) = -(r : ℂ) := by
        linear_combination
          (-(ρ : ℂ) ^ 2 * Complex.exp (-(θ / 2 * Complex.I)) ^ 2 * (Real.sqrt r : ℂ) ^ 2) * hu -
            (Real.sqrt r : ℂ) ^ 2 * hρi - (Real.sqrt r : ℂ) ^ 2 * ((ρ : ℂ)⁻¹ * ρ) * hE - hs
      rw [key]
      exact neg_ne_zero.mpr (by exact_mod_cast hr.ne'))

def twistedEllipticTransform (φ : GL (Fin 2) ℂ → ℂ) (r θ : ℝ) : ℂ :=
  if hr : 0 < r then
    (4 * Real.sin θ ^ 2 : ℂ) *
      (∫ ρ in Set.Ioi (0 : ℝ), ∫ u : ℂ,
        if hρ : 0 < ρ then
          (ρ : ℂ)⁻¹ *
            ((unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r θ ρ u hr hρ * conjEntries k)) +
              (unitaryAverage fun k => φ (k⁻¹ * twistedEllipticElt r (-θ) ρ u hr hρ * conjEntries k)))
        else 0)
  else 0

end AutomorphicForm.GL2Twisted

end


