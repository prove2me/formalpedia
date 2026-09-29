-- Prove2me | Definitions.Def_ChatterjeeQFT_ElectronSpace
-- name    : ChatterjeeQFT_ElectronSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-19T21:00:51.128687+00:00
-- url     : https://prove2.me/theorems/c950e958-1d75-454e-a660-c206a40c6dcf
-- title:
--   The one-particle electron space $L^2(X_m, d\lambda_m, \mathbb{C}^2)$ with the weight $V_p^{-2}$
-- statement:
--   An electron of mass $m$ is described by a $\mathbb{C}^2$-valued wave function on the
--   mass shell. The inner product is *not* the unweighted one: with $V_p$ the pure boost taking
--   $p^*=(m,0,0,0)$ to $p$, the source defines
--
--   $$(\psi, \varphi) \;=\; \int_{X_m} d\lambda_m(p)\; \psi(p)^{\dagger} \, V_p^{-2} \, \varphi(p),
--   \qquad \psi, \varphi \in L^2(X_m, d\lambda_m, \mathbb{C}^2),$$
--
--   the weight $V_p^{-2}$ being exactly what makes the spinor representation
--
--   $$(U(a,A)\psi)(p) \;=\; e^{i(a,p)} \, A\, \psi\big(\kappa(A)^{-1}p\big), \qquad A \in SL(2,\mathbb{C}),$$
--
--   unitary. The **one-particle electron space** is accordingly the space of $\mathbb{C}^2$-valued
--   measurable functions on the mass shell with
--   $\int_{X_m} d\lambda_m(p)\, \psi(p)^{\dagger} V_p^{-2} \psi(p) < \infty$, functions agreeing
--   $\lambda_m$-almost everywhere being identified. Because the weight is a measurable field of
--   positive-definite matrices, this is the $L^2$ space of a matrix-weighted measure rather than of a
--   scalar one.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 (The model for free electrons), §25.3, pp. 108-109.

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
import Definitions.Def_ChatterjeeQFT_SL2C

/-!
# The one-particle Hilbert space of an electron

Following S. Chatterjee, *Lectures on Quantum Field Theory*, Lecture 25.
-/

open MeasureTheory Matrix

namespace ChatterjeeQFT

/-- The matrix weight `V_p^{-2}` occurring in the electron inner product. -/
noncomputable def electronWeight (m : ℝ) (p : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (pureBoost m p * pureBoost m p)⁻¹

/-- The pointwise pairing `ψ(p)† V_p^{-2} φ(p)` of two spinor wave functions. -/
noncomputable def electronPairing (m : ℝ) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ))
    (p : Fin 4 → ℝ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (ψ p i) * electronWeight m p i j * φ p j

/-- The electron inner product `(ψ, φ) = ∫_{X_m} dλ_m(p) ψ(p)† V_p^{-2} φ(p)`. -/
noncomputable def electronInner (m : ℝ) (ψ φ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) : ℂ :=
  ∫ p, electronPairing m ψ φ p ∂(massShellMeasure m)

/-- The one-particle state space of an electron of mass `m`: the `C²`-valued functions on the
mass shell that are measurable and have finite norm for the weighted inner product,
`∫_{X_m} dλ_m(p) ψ(p)† V_p^{-2} ψ(p) < ∞`.  The Hilbert space `H = L²(X_m, dλ_m, C²)` is this
space with functions agreeing `λ_m`-almost everywhere identified. -/
noncomputable def ElectronL2 (m : ℝ) : Set ((Fin 4 → ℝ) → (Fin 2 → ℂ)) :=
  {ψ | AEStronglyMeasurable ψ (massShellMeasure m) ∧
    ∫⁻ p, ENNReal.ofReal (electronPairing m ψ ψ p).re ∂(massShellMeasure m) < ⊤}

/-- The action of the Poincaré group on electron wave functions:
`(U(a, A)ψ)(p) = e^{i(a,p)} A ψ(κ(A)⁻¹ p)` for `A ∈ SL(2,C)`. -/
noncomputable def electronAction (a : Fin 4 → ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (ψ : (Fin 4 → ℝ) → (Fin 2 → ℂ)) : (Fin 4 → ℝ) → (Fin 2 → ℂ) :=
  fun p => Complex.exp (Complex.I * (minkowskiInner a p : ℂ)) • (A *ᵥ ψ (kappa A⁻¹ p))

end ChatterjeeQFT


