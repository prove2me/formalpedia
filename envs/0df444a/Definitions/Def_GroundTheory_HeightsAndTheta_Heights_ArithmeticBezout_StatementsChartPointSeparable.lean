-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartPointSeparable
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartPointSeparable
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:15:04.060963+00:00
-- url     : https://prove2.me/theorems/5057f499-8454-5224-a608-4f2bf0641cad
-- title:
--   Statements Chart Point Separable
-- statement:
--   Definitions and structural lemmas for Statements Chart Point Separable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsChartPointSeparable.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_OfFreeParAlgIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def ChartParAlgebraic.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.IsAlgebraic
        (Algebra.adjoin (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (Set.range fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1)))) L
def ChartFreeParAlgIndep.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K] [Algebra K L]
    [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F) (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    ∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal) →
      AlgebraicIndependent (IntermediateField.adjoin F (Set.range fun m => η m * (η j₀)⁻¹))
          (fun p : Fin e × {j : Fin n // j ≠ j₀} => algebraMap K L (u (p.1, p.2.1))) ∧
        Algebra.IsAlgebraic K L
def ChartPointSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (K L : Type) [Field K] [Field L] [Algebra F K]
    [Algebra K L] [Algebra F L] [IsScalarTower F K L] (u : Fin e × Fin n → K) (t : Fin n → F)
    (η : Fin n → L),
    AlgebraicIndependent F u →
    IntermediateField.adjoin F (Set.range u) = ⊤ → IntermediateField.adjoin K (Set.range η) = ⊤ →
    (∀ i : Fin e, ∑ m, algebraMap K L (u (i, m)) * η m = 0) → ∑ m, algebraMap F L (t m) * η m = 1 →
    (∀ j₀, η j₀ ≠ 0 →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => η m * (η j₀)⁻¹)) ≤ (e : Cardinal)) →
      Algebra.IsSeparable K L
section Inhabitants
namespace ChartPointLine
abbrev KL : Type := FractionRing (MvPolynomial (Fin 1 × Fin 2) ℚ)
def uL : Fin 1 × Fin 2 → KL := fun q => algebraMap (MvPolynomial (Fin 1 × Fin 2) ℚ) KL (X q)
def tL : Fin 2 → ℚ := ![0, 1]
def ηL : Fin 2 → KL := ![-(uL (0, 1)) / uL (0, 0), 1]
end ChartPointLine
open ChartPointLine
end Inhabitants
end
end GroundTheory.Heights₂.Heights


