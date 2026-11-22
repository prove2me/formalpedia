-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_StatementB
-- name    : Formalism_SatakeDualWeyl_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:14:29.017795+00:00
-- url     : https://prove2.me/theorems/c47241cf-00f8-4675-9a16-f9d7863692ce
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/StatementB.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace Formalism.UG
variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
def gram (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) : Matrix n n K :=
  fun i j => h (Pi.single i 1) (Pi.single j 1)
def glEquiv (g : GL n K) : (n → K) ≃ₗ[K] (n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K) (Matrix.GeneralLinearGroup.toLin g)
def GlEquivApply : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (g : GL n K) (x : n → K),
    glEquiv g x = (g : Matrix n n K) *ᵥ x
def HformGram : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K),
    h x y = hform (starRingEnd K) (gram h) x y
def HermBridge : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (g : GL n K),
    g ∈ UJ (starRingEnd K) (gram h) ↔ glEquiv g ∈ Formalism.HermitianLatticesTheory.isom h
def HermBridgeSurj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K), ∀ u ∈ Formalism.HermitianLatticesTheory.isom h, ∃ g : GL n K, glEquiv g = u
def StabGmap : Prop :=
  ∀ (K : Type) [Field K] (R : Type) [CommRing R] [Algebra R K] (n : Type) [Fintype n] [DecidableEq n]
    (Λ : Submodule R (n → K)) (g : GL n K),
    g ∈ stabGL Λ ↔ Formalism.HermitianLatticesTheory.gmap (glEquiv g) Λ = Λ
end Formalism.UG


