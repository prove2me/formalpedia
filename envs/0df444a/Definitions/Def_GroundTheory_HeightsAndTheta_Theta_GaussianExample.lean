-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
-- name    : GroundTheory_HeightsAndTheta_Theta_GaussianExample
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:19.956444+00:00
-- url     : https://prove2.me/theorems/f040df14-c5e8-4c46-b8dd-806f3e3f9dd3
-- title:
--   Gaussian Example
-- statement:
--   Definitions and structural lemmas for Gaussian Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix
instance fact_gaussQ : Fact (∀ r : ℚ, r ^ 2 ≠ -1 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩
abbrev GaussQ : Type := QuadraticAlgebra ℚ (-1) 0
instance : Algebra.IsQuadraticExtension ℚ GaussQ :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩
instance : NumberField GaussQ where
noncomputable abbrev gaussBasis : Module.Basis (Fin 2) ℚ GaussQ := QuadraticAlgebra.basis (-1 : ℚ) 0
noncomputable def gramAniso : Matrix (Fin 2) (Fin 2) GaussQ := Matrix.diagonal ![1, -3]
noncomputable def gramIso : Matrix (Fin 2) (Fin 2) GaussQ := Matrix.diagonal ![1, -1]
noncomputable def gaussValue (H : Matrix (Fin 2) (Fin 2) GaussQ) (x : Fin 2 → GaussQ) : GaussQ :=
  (fun i => conj ℚ GaussQ (x i)) ⬝ᵥ (H *ᵥ x)
noncomputable def gaussPairing (H : Matrix (Fin 2) (Fin 2) GaussQ) (x y : Fin 2 → GaussQ) : GaussQ :=
  (fun i => conj ℚ GaussQ (x i)) ⬝ᵥ (H *ᵥ y)
end GroundTheory.Heights₂.Theta


