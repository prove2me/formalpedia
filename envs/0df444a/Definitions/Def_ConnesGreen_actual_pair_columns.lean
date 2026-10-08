-- Prove2me | Definitions.Def_ConnesGreen_actual_pair_columns
-- name    : ConnesGreen_actual_pair_columns
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-07T04:23:33.325982+00:00
-- url     : https://prove2.me/theorems/39a79531-ade9-43c9-9ef8-81d2c609e9df
-- title:
--   Original multiplicity-weighted reflected Green actors on actual zeta zeros
-- statement:
--   For every actual nontrivial zero $\rho$ of the Riemann zeta function, let $\rho^\sharp=1-\overline\rho$. The classical functional equation supplies this reflection within the same actual-zero carrier. Given Hilbert columns $v_\rho$, define the original multiplicity-weighted pair actors by
--   $$w_\rho=\sqrt{m_\rho}\,v_\rho,\qquad p_\rho=\tfrac12(w_\rho+w_{\rho^\sharp}),\qquad n_\rho=\tfrac12(w_\rho-w_{\rho^\sharp}).$$
--   Here $m_\rho$ is the analytic multiplicity of the actual zeta zero. The factor $1/2$ and the reflection duplication are preserved from the native Connes–Weil actor infrastructure. These definitions make no assumption about RH, positivity, separation, or a marker inequality. The reflection proof reuses the existing analytic zeta seam and does not replace zeta zeros by an abstract zero configuration.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/CanonicalGreenBackground.lean, based on repository commit b019d40205680f9761a4b0a80cbcad56ee1b606b. Exact incremental source and native audit are delivered in Connes_Weil_Green_Background_Custody.zip; the P2M proof reuses the existing canonical model and proved canonical Green realization.

import Definitions.Def_ConnesGreen_canonical_model
import Definitions.Def_Zeta23_ZetaReflect
set_option autoImplicit false
open Complex ConnesRZ ConnesRZFrontier
open scoped BigOperators InnerProductSpace lp ENNReal Classical
noncomputable section
namespace ConnesRZFrontier
/-- The same actual zeta-zero reflection, with its analytic proof supplied by the existing seam. -/
def reflectedZero (ρ : CriticalZeros) : CriticalZeros :=
  ⟨mirror ρ.1, Zeta23.zeta_reflect_zero ρ.1 ρ.2⟩
@[simp] theorem reflectedZero_val (ρ : CriticalZeros) :
    (reflectedZero ρ).1 = mirror ρ.1 := rfl
@[simp] theorem reflectedZero_involutive (ρ : CriticalZeros) :
    reflectedZero (reflectedZero ρ) = ρ := by
  apply Subtype.ext
  simp [reflectedZero, mirror]
end ConnesRZFrontier
namespace WeilDefect.ConnesNative
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def weightedGreenColumn (v : CriticalZeros → H) (ρ : CriticalZeros) : H :=
  (Real.sqrt (zeroMult ρ.1 : ℝ) : ℂ) • v ρ
def positiveGreenColumn (v : CriticalZeros → H) (ρ : CriticalZeros) : H :=
  (1 / 2 : ℂ) • (weightedGreenColumn v ρ + weightedGreenColumn v (reflectedZero ρ))
def negativeGreenColumn (v : CriticalZeros → H) (ρ : CriticalZeros) : H :=
  (1 / 2 : ℂ) • (weightedGreenColumn v ρ - weightedGreenColumn v (reflectedZero ρ))
end WeilDefect.ConnesNative


