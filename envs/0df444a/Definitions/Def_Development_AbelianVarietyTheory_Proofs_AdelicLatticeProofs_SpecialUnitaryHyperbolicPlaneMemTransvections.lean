-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpecialUnitaryHyperbolicPlaneMemTransvections
-- name    : Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SpecialUnitaryHyperbolicPlaneMemTransvections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:40:09.740669+00:00
-- url     : https://prove2.me/theorems/13567475-2e24-43a9-8a13-0f2cd7895c0b
-- title:
--   Special Unitary Hyperbolic Plane Mem Transvections
-- statement:
--   Definitions and structural lemmas for Special Unitary Hyperbolic Plane Mem Transvections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SpecialUnitaryHyperbolicPlaneMemTransvections.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
namespace GlobalTheory.UTrans.Plane
open GlobalTheory.UTrans.Model
def ext2 {E : Type} [CommRing E] {n : ℕ} (U : Matrix (Fin n) (Fin 2) E) (V : Matrix (Fin 2) (Fin n) E)
    (N : Matrix (Fin 2) (Fin 2) E) : Matrix (Fin n) (Fin n) E := 1 + U * (N - 1) * V
variable {E : Type} [Field E] {n : ℕ}
def cols (z w : Fin n → E) : Matrix (Fin n) (Fin 2) E := Matrix.of fun a i => ![z a, w a] i
def what₂ (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (z w : Fin n → E) : Matrix (Fin 2) (Fin n) E :=
  Matrix.of fun i b => ![∑ e, G b e * σ (w e), ∑ e, G b e * σ (z e)] i
end GlobalTheory.UTrans.Plane


