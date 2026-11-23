-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:26.570797+00:00
-- url     : https://prove2.me/theorems/b7e986f2-6ad7-4b4a-801d-12eefbd76955
-- title:
--   Prop AA
-- statement:
--   Definitions and structural lemmas for Prop AA, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
def paW (q : ℕ) (v : EuclideanSpace ℂ ι) : ℝ := Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)
def paIP (q : ℕ) (F G : EuclideanSpace ℂ ι → ℂ) : ℂ :=
  ∫ v, F v * (starRingEnd ℂ) (G v) * (paW q v : ℂ)
def paN (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : ℝ := Real.sqrt (paIP q F F).re
def paPF (p : MvPolynomial ι ℂ) : EuclideanSpace ℂ ι → ℂ := fun v => MvPolynomial.eval (fun i => v i) p
def paMono (α : ι →₀ ℕ) : EuclideanSpace ℂ ι → ℂ := paPF (MvPolynomial.monomial α 1)
def paS (c : ℕ) : Finset (ι →₀ ℕ) :=
  ((Fintype.piFinset fun _ : ι => Finset.range (c + 1)).map
    (Finsupp.equivFunOnFinite (α := ι) (M := ℕ)).symm.toEmbedding).filter (fun α => α.degree ≤ c)
def paPoly (c : ℕ) : Submodule ℂ (EuclideanSpace ℂ ι → ℂ) :=
  Submodule.span ℂ (paMono '' ((paS (ι := ι) c : Finset (ι →₀ ℕ)) : Set (ι →₀ ℕ)))
def paU (q : ℕ) (a : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a)
def paD (α : ι →₀ ℕ) (H : EuclideanSpace ℂ ι → ℂ) : ℂ :=
  polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) H 0
def paFact (α : ι →₀ ℕ) : ℕ := ∏ i, (α i).factorial
def paJet (c : ℕ) (H : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  ∑ α ∈ paS c, (paD α H / paFact α) • paMono α
def paPD : (n : ℕ) → (Fin n → ι) → MvPolynomial ι ℂ → MvPolynomial ι ℂ
  | 0, _, p => p
  | n + 1, m, p => paPD n (Fin.init m) (MvPolynomial.pderiv (m (Fin.last n)) p)
end
end ReciprocityTheory.ChartRestriction.G.I2


