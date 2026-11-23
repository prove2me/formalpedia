-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadDiffOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDifference_QuadDiffOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:40.777791+00:00
-- url     : https://prove2.me/theorems/175db00d-7b02-4a54-9888-1d43e71eff79
-- title:
--   Quad Diff Of
-- statement:
--   Definitions and structural lemmas for Quad Diff Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticDifference/QuadDiffOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuadDiff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.QD
open NumberField
def AdjTop : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K) (α : 𝓞 K), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : K) → Algebra.adjoin ℚ {θ} = ⊤ → 2 * (α : K) - 1 = θ →
    Algebra.adjoin ℤ {α} = ⊤
def DiffK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K) (α : 𝓞 K), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : K) → Algebra.adjoin ℚ {θ} = ⊤ → 2 * (α : K) - 1 = θ →
    differentIdeal ℤ (𝓞 K) = Ideal.span {2 * α - 1}
def DiffOfAdj : Prop := AdjTop → DiffK
def MapStep : Prop := DiffK → PI.QuadDiff
def Arith : Prop :=
  ∀ (d : ℕ) (x y : ℚ), Squarefree d → d % 4 = 3 → (∃ u : ℤ, 2 * x = u) →
    (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N) → ∃ a v : ℤ, x = a + v / 2 ∧ y = v / 2
def IntCoeffs : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K) (x y : ℚ), Squarefree d → d % 4 = 3 →
    θ ^ 2 = -(d : K) → IsIntegral ℤ ((x : K) + (y : K) * θ) →
    (∃ u : ℤ, 2 * x = u) ∧ (∃ N : ℤ, x ^ 2 + d * y ^ 2 = N)
def Form : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (θ : K), θ ^ 2 = -(d : K) →
    Algebra.adjoin ℚ {θ} = ⊤ → ∀ z : K, ∃ x y : ℚ, z = x + y * θ
def AdjOfParts : Prop := Form → IntCoeffs → Arith → AdjTop
end PI.QD
end


