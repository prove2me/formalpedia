-- Prove2me | Definitions.Def_wdw_canonical_operators
-- name    : wdw_canonical_operators
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-03T21:45:47.029439+00:00
-- url     : https://prove2.me/theorems/5e48a36e-9a44-47bb-a3c8-11aa3e6c7cdc
-- title:
--   Canonical momentum and the ordered Wheeler–DeWitt expression
-- statement:
--   Complex-valued wavefunctionals and a supplied complex-linear functional-derivative interface define momentum as −iℏ times the derivative. The normally ordered canonical Hamiltonian action and the expanded second-derivative expression include all four spatial tensor sums, the curvature/cosmological potential, and a supplied matter energy-density operator. The interface does not construct genuine functional derivatives, a Hilbert-space domain, or a regulated operator.
-- source:
--   Claus Kiefer, Quantum Geometrodynamics: whence, whither?, Gen. Relativ. Gravit. 41 (2009), 877–901, https://arxiv.org/abs/0812.0295, Sections 2.2 and 2.4, equations (3)–(8). Formal algebraic derivation with supplied geometry and complex-linear derivative interface; no analytic realization asserted.

import Definitions.Def_wdw_canonical_geometry
import Mathlib.Algebra.Module.LinearMap.End

set_option autoImplicit false

namespace WheelerDeWitt

noncomputable section

abbrev Wavefunction (C : Type*) := C → ℂ

/-- Formal functional derivative interface. No analytic realization is asserted. -/
abbrev FunctionalDerivative (C X : Type*) :=
  X → Fin 3 → Fin 3 → Module.End ℂ (Wavefunction C)

def momentum {C X : Type*} (D : FunctionalDerivative C X) (hbar : ℝ)
    (x : X) (a b : Fin 3) : Module.End ℂ (Wavefunction C) :=
  (-Complex.I * (hbar : ℂ)) • D x a b

/-- The canonical Hamiltonian with coefficients on the left and both momenta
to their right, acting on a wavefunctional. -/
def quantizedHamiltonian {C X : Type*} (g : Geometry C X)
    (D : FunctionalDerivative C X) (rho : X → Module.End ℂ (Wavefunction C))
    (kappa hbar cosmologicalConstant : ℝ) (psi : Wavefunction C) (q : C) (x : X) : ℂ :=
  (2 * (kappa : ℂ)) *
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (deWittMetric g q x a b c d : ℂ) *
        (momentum D hbar x a b (momentum D hbar x c d psi)) q) -
  ((2 * (kappa : ℂ))⁻¹ * (volumeDensity g q x : ℂ) *
    ((g.scalarCurvature q x : ℂ) - 2 * (cosmologicalConstant : ℂ))) * psi q +
  (volumeDensity g q x : ℂ) * (rho x psi) q

def wheelerDeWittExpression {C X : Type*} (g : Geometry C X)
    (D : FunctionalDerivative C X) (rho : X → Module.End ℂ (Wavefunction C))
    (kappa hbar cosmologicalConstant : ℝ) (psi : Wavefunction C) (q : C) (x : X) : ℂ :=
  (-2 * (kappa : ℂ) * (hbar : ℂ)^2) *
    (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      (deWittMetric g q x a b c d : ℂ) * (D x a b (D x c d psi)) q) -
  ((2 * (kappa : ℂ))⁻¹ * (volumeDensity g q x : ℂ) *
    ((g.scalarCurvature q x : ℂ) - 2 * (cosmologicalConstant : ℂ))) * psi q +
  (volumeDensity g q x : ℂ) * (rho x psi) q

end
end WheelerDeWitt


