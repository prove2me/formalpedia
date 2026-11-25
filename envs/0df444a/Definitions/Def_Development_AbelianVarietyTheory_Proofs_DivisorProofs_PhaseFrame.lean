-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:23:18.307054+00:00
-- url     : https://prove2.me/theorems/04aa5316-8e6c-455c-bb85-303f76bd564c
-- title:
--   Phase Frame
-- statement:
--   Definitions and structural lemmas for Phase Frame, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PhaseFrame.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RiemConst
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def angles (θ : Fin (r - 1) → ℝ) (a : Fin r) : ℝ :=
  if h : (a : ℕ) < r - 1 then θ ⟨a, h⟩ else -∑ k, θ k
def phaseFrame {Ψ : Finset (E →+* ℂ)} (θ : Ψ → Fin (r - 1) → ℝ) : Frame Ψ r :=
  fun τ => Matrix.diagonal fun a => Complex.exp (Complex.I * (angles (θ τ) a : ℂ))
def inFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) (Y : Ψ → Fin r → Fin r → ℂ) (τ : Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  (mat x τ)⁻¹ * Matrix.of (Y τ) * mat x τ
abbrev ChartSp (X : Data E r) : Type := ReciprocityTheory.L2DbarEstimates.V (nd X) × (X.Ψ → Fin (r - 1) → ℝ)
end GlobalTheory.RiemConst


