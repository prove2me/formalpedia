-- Prove2me | Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
-- name    : Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:43.932368+00:00
-- url     : https://prove2.me/theorems/60b6a698-c5e8-4785-acfb-6740890a5339
-- title:
--   Shear Coefficients
-- statement:
--   Definitions and structural lemmas for Shear Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/ShearCoefficients.lean

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.NormUnitaryCountingLemmas
namespace ShearCoefficients
variable {R : Type*} [CommRing R]
def CoeffHom {σ M : Type*} [AddCommMonoid M] (wt : σ → M) (m : M)
    (P : Polynomial (MvPolynomial σ R)) : Prop :=
  ∀ k, (P.coeff k).IsWeightedHomogeneous wt m
section CoeffHom
variable {σ M : Type*} [AddCommMonoid M] {wt : σ → M}
lemma CoeffHom.C {m : M} {r : MvPolynomial σ R} (h : r.IsWeightedHomogeneous wt m) :
    CoeffHom wt m (Polynomial.C r) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact h
  · exact isWeightedHomogeneous_zero R wt m
lemma CoeffHom.X : CoeffHom (R := R) wt 0 Polynomial.X := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact isWeightedHomogeneous_one R wt
  · exact isWeightedHomogeneous_zero R wt 0
end CoeffHom
end ShearCoefficients
end Formalism.NormUnitaryCountingLemmas


