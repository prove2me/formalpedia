-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_BaseNorm
-- name    : Development_AbelianVarietyTheory_Definitions_RegularCharts_BaseNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:35.352798+00:00
-- url     : https://prove2.me/theorems/253cf087-7955-4850-82cc-17175391ed8f
-- title:
--   Base Norm
-- statement:
--   Definitions and structural lemmas for Base Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/RegularCharts/BaseNorm.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompOrd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FrameNorm
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
def IsUnitFr {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) : Prop := ∀ τ i, ‖dmin X.Gm x τ i‖ = 1
def baseNorm (Dw : Datum H) (x : ℝ) : Ix Dw → ℝ
  | none => 1
  | some _ => Real.sqrt (2 * Real.pi * x)
def conjAlg {K : Type} [Field K] (σ : K →+* ℂ) : CAt σ →ₐ[K] CAt ((starRingEnd ℂ).comp σ) :=
  { (starRingEnd ℂ : ℂ →+* ℂ) with commutes' := fun _ => rfl }
def FnPin {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (x : ℝ)
    (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) : Prop :=
  (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → ∀ k (z : ((U σ).X k).dom), IsUnitFr ((U σ).X k) z.1 →
    ∀ (t : Ix Dw → (CAt σ)ˣ) (y : FrPt Xo c (CAt σ)), FrBor t ((U σ).un k z) y →
      ∀ i, |fn σ y i| = cabs (t i : CAt σ) * baseNorm Dw x i) ∧
  ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))),
    FrMap (conjAlg σ) y y' → ∀ i, |fn _ y' i| = |fn σ y i|
def HasPrinc {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (M : ℕ) : Prop :=
  ∀ k (γ : GL (Fin r) E), IsUStab (U.X k).Gm (U.X k).Λ γ →
    (∀ x ∈ (U.X k).Λ, ∃ y ∈ (U.X k).Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (M : E) • y) →
      γ ∈ (U.X k).Γ
end GlobalTheory.FrameNorm


