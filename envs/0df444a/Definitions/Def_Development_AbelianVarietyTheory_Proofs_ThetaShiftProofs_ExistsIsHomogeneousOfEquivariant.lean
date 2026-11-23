-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- name    : Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:35.735782+00:00
-- url     : https://prove2.me/theorems/d4ed98d3-7311-4d83-9c5a-6fcf01d6db9a
-- title:
--   Exists Is Homogeneous Of Equivariant
-- statement:
--   Definitions and structural lemmas for Exists Is Homogeneous Of Equivariant, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsIsHomogeneousOfEquivariant.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
namespace GlobalTheory.BorelAlg
section Blocks
variable {ι : Type} (m : ι → ℕ) (L : Type) [Field L]
abbrev Lt : Type := Σ τ : ι, Fin (m τ) × Fin (m τ)
noncomputable def gen (τ : ι) : Matrix (Fin (m τ)) (Fin (m τ)) (MvPolynomial (Lt m) L) :=
  Matrix.of fun i k => X ⟨τ, i, k⟩
variable [Fintype ι]
def Equivariant (S : Type) [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
    (a : ι × ℕ → ℕ) (f : S) : Prop :=
  ∀ (T : Type) [Field T] (φ ψ : S →+* T) (b : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) T),
    (∀ g : L, φ (algebraMap (MvPolynomial (Lt m) L) _ (C g)) =
      ψ (algebraMap (MvPolynomial (Lt m) L) _ (C g))) →
    (∀ τ i j, i < j → b τ i j = 0) →
    (∀ τ i k, ψ (algebraMap (MvPolynomial (Lt m) L) _ (X ⟨τ, i, k⟩)) =
      ∑ j, b τ i j * φ (algebraMap (MvPolynomial (Lt m) L) _ (X ⟨τ, j, k⟩))) →
    ψ f = (∏ τ, ∏ i, b τ i i ^ a (τ, (i : ℕ))) * φ f
variable {m L} {S : Type} [CommRing S] [Algebra (MvPolynomial (Lt m) L) S]
  [IsLocalization.Away (∏ τ, (gen m L τ).det) S]
end Blocks
end GlobalTheory.BorelAlg


