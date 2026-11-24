-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ABridge
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:16.793253+00:00
-- url     : https://prove2.me/theorems/93ec76dc-d130-4da5-9d34-9d509805e158
-- title:
--   ABridge
-- statement:
--   Definitions and structural lemmas for ABridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/ABridge.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
def qa_Phi (R : Type*) [CommRing R] (n : ℕ) (u : GLCoord R n) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] GLCoord R n :=
  (LinearMap.mulLeft R u) ∘ₗ (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (GLCoord R n)).toLinearMap ∘ₗ
    (rename (R := R) (Prod.swap : Fin n × Fin n → Fin n × Fin n)).toLinearMap
def qa_intLin {M N : Type*} [AddCommGroup M] {i1 : Module ℤ M} [AddCommGroup N] {i2 : Module ℤ N}
    (f : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 i2) :
    @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) M N _ _ i1 (AddCommGroup.toIntModule N) ⟨f, f.map_add⟩
    (fun z x => (f.map_smul z x).trans (int_smul_eq_zsmul i2 z (f x)))
def qa_PhiZ (n : ℕ) (u : GLCoord ℤ n) := qa_intLin (qa_Phi ℤ n u)
end Formalism.InvariantFactorPaths.ColumnFamilies


