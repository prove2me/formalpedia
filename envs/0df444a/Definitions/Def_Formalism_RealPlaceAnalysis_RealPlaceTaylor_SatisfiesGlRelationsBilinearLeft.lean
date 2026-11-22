-- Prove2me | Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
-- name    : Formalism_RealPlaceAnalysis_RealPlaceTaylor_SatisfiesGlRelationsBilinearLeft
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:23.688883+00:00
-- url     : https://prove2.me/theorems/093b75f5-890e-47a1-91b6-baa42637378e
-- title:
--   Satisfies Gl Relations Bilinear Left
-- statement:
--   Definitions and structural lemmas for Satisfies Gl Relations Bilinear Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/SatisfiesGlRelationsBilinearLeft.lean

import Definitions.Def_Formalism_RealPlaceAnalysis_FockPairGl
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
namespace Formalism.REAL
section ops
variable {σ : Type*} [DecidableEq σ]
set_option quotPrecheck false
local notation "D" v => ((pderiv v : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)).toLinearMap :
  Module.End ℂ (MvPolynomial σ ℂ))
local notation "Mx" v => (LinearMap.mulLeft ℂ (X v : MvPolynomial σ ℂ) : Module.End ℂ (MvPolynomial σ ℂ))
end ops
section weyl
variable {A : Type*} [Ring A] {m n : ℕ} (B P : Fin m → Fin n → A)
def bilinearLeft (i j : Fin m) : A := ∑ a, P i a * B j a
def bilinearRight (a b : Fin n) : A := ∑ i, P i b * B i a
def bilinearNumber : A := ∑ i, ∑ a, P i a * B i a
def bilinearQuartic : A := ∑ i, ∑ j, ∑ a, ∑ b, P i a * P j b * B j a * B i b
variable {B P}
variable (hBP : ∀ i j a b, B i a * P j b - P j b * B i a = if i = j ∧ a = b then 1 else 0)
  (hBB : ∀ i j a b, B i a * B j b = B j b * B i a)
  (hPP : ∀ i j a b, P i a * P j b = P j b * P i a)
include hBP hBB hPP
end weyl
end Formalism.REAL


