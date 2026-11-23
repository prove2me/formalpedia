-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetMeetingFibres
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:26.575616+00:00
-- url     : https://prove2.me/theorems/aec1caf7-dacb-48e7-853f-0c89e248995a
-- title:
--   Exists Finset Meeting Fibres
-- statement:
--   Definitions and structural lemmas for Exists Finset Meeting Fibres, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsFinsetMeetingFibres.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_QuadraticCoefficientForms
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_UnipotentMoves_BotMulVecExt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_Frames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.FrameNet
open NumberField ReciprocityTheory.ChartRestriction.G.FD Matrix
noncomputable section
def cell (s δ : ℝ) (z : ℂ) : ℤ × ℤ := (⌊(z.re + s) / δ⌋, ⌊(z.im + s) / δ⌋)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def basisMat (τ : E →+* ℂ) (v : Fin r → Fin r → E) : Matrix (Fin r) (Fin r) ℂ :=
  ((Matrix.of v)ᵀ).map τ
def gramMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i k => herm G (v i) (v k)
variable (X : Data E r)
def shortFrames (v : Fin r → Fin r → E) (B : ℝ) : Set (Frame X.Ψ r) :=
  {x | (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ i, ∑ τ : X.Ψ, X.maj x τ (Data.emb τ.1 (v i)) ≤ B}
end
end GlobalTheory.FrameNet


