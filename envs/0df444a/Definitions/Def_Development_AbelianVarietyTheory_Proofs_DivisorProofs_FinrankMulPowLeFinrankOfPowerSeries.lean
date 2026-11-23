-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:04.130663+00:00
-- url     : https://prove2.me/theorems/ccac6f39-61f7-4e2d-82e3-34bfb5b0551f
-- title:
--   Finrank Mul Pow Le Finrank Of Power Series
-- statement:
--   Definitions and structural lemmas for Finrank Mul Pow Le Finrank Of Power Series, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankMulPowLeFinrankOfPowerSeries.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndependentOfDistinctValuationLikeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankLeCardValuesStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory
namespace HilbertSamuelPS
open MvPowerSeries
section LexLemmas
variable {D : ℕ}
end LexLemmas
end HilbertSamuelPS
end GlobalTheory
namespace GlobalTheory
namespace HilbertSamuelPS
open MvPowerSeries
section Valuation
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ))
noncomputable def evalAt (k : ℕ) (u : A) : MvPowerSeries (Fin D) ℂ :=
  if h : k < n then φ ⟨k, h⟩ u else 0
open Classical in

noncomputable def firstIdx (u : A) : ℕ := if h : ∃ k, evalAt φ k u ≠ 0 then Nat.find h else 0
noncomputable def val (u : A) : Lex (ℕ × WithTop (Lex (Fin D →₀ ℕ))) :=
  toLex (firstIdx φ u, lexOrder (evalAt φ (firstIdx φ u) u))
variable {φ}
end Valuation
end HilbertSamuelPS
end GlobalTheory
namespace GlobalTheory
namespace HilbertSamuelPS
open MvPowerSeries
section Vectors
variable {D n : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
  {φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)} {x : Fin D → A} {c : Fin D → ℂ}
end Vectors
end HilbertSamuelPS
end GlobalTheory


