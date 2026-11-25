-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T04:28:58.140033+00:00
-- url     : https://prove2.me/theorems/c335f696-012f-435e-9c5b-6d1b053e982c
-- title:
--   Tendsto Smul Cocompact
-- statement:
--   Definitions and structural lemmas for Tendsto Smul Cocompact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
section main
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def mainD (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) : H :=
  ∑ z ∈ G.rootSet s (ε * D), G.psi β ((s : ℂ) * z * x) • bt z
def bz (s : ℕ) (bt : ℂ → H) (z : ℂ) : H := (((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • bt z
def pairD (s : ℕ) (β ε : ℂ) (bt bt' : ℂ → H) (x x' ρ : ℂ) : ℂ :=
  ∫ D, ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ
def termZ (s : ℕ) (β : ℂ) (bt bt' : ℂ → H) (x x' ρ ζ z : ℂ) : ℂ :=
  G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) • ⟪bz s bt z, ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)⟫_ℂ
end main
end
end Formalism.FourierDecayAlt.P.PBK


