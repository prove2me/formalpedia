-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
-- name    : KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T05:38:18.592993+00:00
-- url     : https://prove2.me/theorems/7a9ce668-e43b-4e17-a874-4d5d0f6660cd
-- title:
--   Quadratic finite pre-energies
-- statement:
--   `Energy.PreEnergy.Quadratic` records that a finite pre-energy has a linear realization into its ambient space, zero energy at zero, quadratic scaling, and the parallelogram identity. The scaling factor is `‖c‖₊ ^ 2` in NNReal, and the energy values remain finite nonnegative quantities. This structure does not assert lower semicontinuity, closability, density, or quadraticity of a later relaxation.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Form/QuadraticPreEnergy.lean#L25-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Form.QuadraticPreEnergy`, definition bundle `KLS408915f_FunctionalInequalities_Energy_Form_QuadraticPreEnergy`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Form_Functional
import Definitions.Def_KLS408915f_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

namespace FunctionalInequalities
namespace Energy
namespace PreEnergy
universe u v
variable {X : Type u} [AddCommGroup X] [Module ℝ X]
  (P : PreEnergy X) [AddCommGroup P.Test] [Module ℝ P.Test]
/-- A finite pre-energy is quadratic when its realization is linear and its energy satisfies the
finite quadratic identities on the concrete test space.

The scalar factor is written as `‖c‖₊ ^ 2 : NNReal`; over `ℝ` this is exactly `c²`, while keeping
the equality entirely in the finite nonnegative codomain.
-/
structure Quadratic : Prop where
  /-- The zero concrete test realizes the ambient zero vector. -/
  map_zero : P.toAmbient 0 = 0
  /-- Realization preserves addition. -/
  map_add : ∀ f g : P.Test, P.toAmbient (f + g) = P.toAmbient f + P.toAmbient g
  /-- Realization preserves real scalar multiplication. -/
  map_smul : ∀ (c : ℝ) (f : P.Test), P.toAmbient (c • f) = c • P.toAmbient f
  /-- The zero concrete test has zero energy. -/
  energy_zero : P.energy 0 = 0
  /-- Finite energy is homogeneous of degree two. -/
  energy_smul : ∀ (c : ℝ) (f : P.Test),
    P.energy (c • f) = ‖c‖₊ ^ 2 * P.energy f
  /-- The finite parallelogram identity. -/
  parallelogram : ∀ f g : P.Test,
    P.energy (f + g) + P.energy (f - g) = 2 * P.energy f + 2 * P.energy g
end PreEnergy
end Energy
end FunctionalInequalities


