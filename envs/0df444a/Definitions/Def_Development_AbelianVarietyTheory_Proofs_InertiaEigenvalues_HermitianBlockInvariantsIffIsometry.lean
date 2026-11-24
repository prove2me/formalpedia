-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockInvariantsIffIsometry
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:54:14.445859+00:00
-- url     : https://prove2.me/theorems/92c89305-270e-4ad7-9f93-178e1ea095ae
-- title:
--   Hermitian Block Invariants Iff Isometry
-- statement:
--   Definitions and structural lemmas for Hermitian Block Invariants Iff Isometry, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockInvariantsIffIsometry.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
def bK (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [Fintype.card_fin, hG.2.1])
def bL (hG : A.IsGen τ p) : Module.Basis (Fin r) E A.L := A.push.out.basis (bK A hG)
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
def mat (j : A.L ≃ₗ[E] (Fin r → E)) : Matrix (Fin r) (Fin r) E :=
  LinearMap.toMatrix' (j.toLinearMap ∘ₗ LinearMap.mulLeft E (algebraMap A.K A.L τ) ∘ₗ j.symm.toLinearMap)
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.EtIsom
namespace GlobalTheory.EtIsom
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}
end GlobalTheory.EtIsom


