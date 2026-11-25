-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:06.082823+00:00
-- url     : https://prove2.me/theorems/b74bbb2d-eab6-5b2c-b2b6-afacb0f26cb7
-- title:
--   Omega Scalar
-- statement:
--   Definitions and structural lemmas for Omega Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk
section Poly
variable {A : Type*} [Ring A] [Algebra ℂ A]
def evAt (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) fun a => (Algebra.commutes u a).symm
def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A v) else 0) + C (E a b)
def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A[X]) *
    (List.ofFn fun k : Fin n => tmPoly E ((k : ℕ) : ℂ) (σ k) k).prod
end Poly
end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP


