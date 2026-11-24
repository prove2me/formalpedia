-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PSerreGraded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:54:40.436591+00:00
-- url     : https://prove2.me/theorems/5bae9c1a-9608-476d-a313-6b9d11de3737
-- title:
--   PSerre Graded
-- statement:
--   Definitions and structural lemmas for PSerre Graded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PSerreGraded.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSerreGraded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
noncomputable section
namespace SerreGraded
open Polynomial
section Pieces
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
end Pieces
section Action
variable {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω)
def act : MvPolynomial (Fin q) ℤ →+* (Polynomial Ω) :=
  MvPolynomial.eval₂Hom (Int.castRingHom (Polynomial Ω)) (fun j => C (w j) * X)
end Action
def gradedModule (q : ℕ) {Ω : Type} [Field Ω] {r : ℕ} [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
    (d : Fin r → ℕ) (t : Fin r → Ω) : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
  Submodule.span _ (Set.range fun l => C (t l) * X ^ d l)
section Module
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
def shifted (u : Fin q) : Submodule (MvPolynomial (Fin q) ℤ) (Polynomial Ω) :=
  (gradedModule q d t).map (LinearMap.mulLeft _ (C (w u) * X))
end Module
section Torsion
variable {Ω : Type} [Field Ω] {q r : ℕ} (w : Fin q → Ω) (d : Fin r → ℕ) (t : Fin r → Ω)
variable [Algebra (MvPolynomial (Fin q) ℤ) (Polynomial Ω)]
end Torsion
end SerreGraded
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


