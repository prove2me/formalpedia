-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:53.052023+00:00
-- url     : https://prove2.me/theorems/3e35f389-846c-4905-a5a5-c44cdf29f1ea
-- title:
--   Prop ASt
-- statement:
--   Definitions and structural lemmas for Prop ASt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropASt.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
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
def GT.Coc {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) : Prop :=
  ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
    Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I)
open Classical in

def PropAStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Y : GT ι) (q c : ℕ) (R0 : ℝ), 1 ≤ q → Y.Coc q → 0 < R0 →
    (∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖) →
    270 ≤ R0 ^ 2 → 90 * ((Fintype.card ι : ℝ) + c) ≤ R0 ^ 2 →
    ∀ p : MvPolynomial ι ℂ, p.totalDegree ≤ c →
      ∃ β ∈ Y.Sec q,
        (∀ α : ι →₀ ℕ, α.degree ≤ c →
          polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
            polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1)
              (fun v : EuclideanSpace ℂ ι => MvPolynomial.eval (fun i => v i) p) 0) ∧
        Y.l2 q β ≤ 6 * ∫ v : EuclideanSpace ℂ ι, ‖MvPolynomial.eval (fun i => v i) p‖ ^ 2 *
          Real.exp (-(q * Real.pi) * ‖v‖ ^ 2)
end
end ReciprocityTheory.ChartRestriction.G.I2


