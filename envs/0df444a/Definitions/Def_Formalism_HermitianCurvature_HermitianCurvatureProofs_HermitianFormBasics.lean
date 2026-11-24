-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:02.150508+00:00
-- url     : https://prove2.me/theorems/347977cc-06d7-4852-967e-875af985d500
-- title:
--   Hermitian Form Basics
-- statement:
--   Definitions and structural lemmas for Hermitian Form Basics, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.HermitianProjections
section proj
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
def prj (H : Matrix n n ℂ) (V : Matrix n ι ℂ) : Matrix ι n ℂ := (Vᴴ * H * V)⁻¹ * Vᴴ * H
def rhoOf (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + V * (Φ - 1) * prj H V
end proj
section herm
variable {n : Type*} [Fintype n]
end herm
section uni
variable {n : Type*} [Fintype n] [DecidableEq n]
end uni
section sig
end sig
end Formalism.FourierDecayAlt.P.HermitianProjections


